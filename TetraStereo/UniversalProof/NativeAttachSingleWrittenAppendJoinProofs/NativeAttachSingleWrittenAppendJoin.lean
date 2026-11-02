import TetraStereo.UniversalProof.GeneralWrittenNeighborBridge
import TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeAttachSingleWrittenAppendJoinProofs

open TetraStereo.OneCenter
open TetraStereo.UniversalProof.GeneralParserStateBridge
open TetraStereo.UniversalProof.GeneralWrittenNeighborBridge
open TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery





















/-- Two tables of written rows are equal when they have the same length and agree at every real
index on `getD`.  This is the list-level bridge from pointwise native-append agreement to a
whole-table equality.  It is proved by structural recursion on the left table, so it consumes no
extra logical principle. -/
theorem list_ext_getD {row₁ row₂ : List (List ℕ)}
    (length_eq : row₁.length = row₂.length)
    (getD_eq : ∀ i, i < row₁.length → row₁.getD i [] = row₂.getD i []) :
    row₁ = row₂ := by
  induction row₁ generalizing row₂ with
  | nil =>
      cases row₂ with
      | nil => rfl
      | cons _ _ => simp at length_eq
  | cons head tail ih =>
      cases row₂ with
      | nil => simp at length_eq
      | cons head₂ tail₂ =>
          have head_eq : head = head₂ := by
            have := getD_eq 0 (by simp)
            simpa using this
          subst head_eq
          have tail_eq : tail = tail₂ := by
            apply ih
            · simpa using length_eq
            · intro i hi
              have := getD_eq (i + 1) (by simp only [List.length_cons]; omega)
              simpa using this
          rw [tail_eq]

/-! ## Raw-molecule table projection and the append row count -/

/-- A general molecule with a full stored table realises its written-neighbour projection as the
stored row at every real index.  This is the `RawMolecule`-level analogue of the accepted parser
`molecule_writtenNeighbors_getD`, needed here because `appendFreshChild` returns a bare
`RawMolecule`. -/
theorem rawMolecule_writtenNeighbors_getD (mol : RawMolecule) (index : ℕ)
    (rowCount : mol.neighborOrder.length = mol.atomCount)
    (bounded : index < mol.atomCount) :
    mol.writtenNeighbors index = mol.neighborOrder.getD index [] := by
  have inRows : index < mol.neighborOrder.length := by omega
  change (match mol.neighborOrder[index]? with | some row => row | none => _) = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inRows]
  rfl

/-- The independent fresh-child append always stores exactly one row per real atom.  This is a
raw construction fact, independent of well-formedness. -/
theorem appendFreshChild_row_count (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) :
    (appendFreshChild mol parent child).neighborOrder.length =
      (appendFreshChild mol parent child).atomCount := by
  simp [appendFreshChild, RawMolecule.atomCount]

/-! ## The native append join -/

/-- **Native table join.**  The parser's `List.set`-based written table after one explicit single
append equals the independent `List.range`/`List.map` fresh-child table, as whole lists.  The
construction computes the accepted `attachSingle_order` on the left and the accepted pointwise
`attachSingle_written_pointwise` against `appendedRow` on the right, then lifts pointwise `getD`
agreement to whole-table equality with `list_ext_getD`.  Hypotheses are exactly the independent row
count and parent bound. -/
theorem native_attachSingle_neighborOrder_join (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (rowCount : state.order.length = state.atoms.length)
    (parentBound : parent < state.atoms.length) :
    (attachSingle state parent atom).order =
      (appendFreshChild state.molecule ⟨parent, parentBound⟩ atom).neighborOrder := by
  have newCount : (attachSingle state parent atom).order.length = state.atoms.length + 1 := by
    rw [attachSingle_row_count state parent atom rowCount]
    change (state.atoms ++ [atom]).length = state.atoms.length + 1
    simp
  have molCount : state.molecule.atomCount = state.atoms.length := rfl
  have freshCount :
      (appendFreshChild state.molecule ⟨parent, parentBound⟩ atom).neighborOrder.length =
        state.atoms.length + 1 := by
    rw [appendFreshChild_row_count, appendFreshChild_atomCount, molCount]
  apply list_ext_getD
  · rw [newCount, freshCount]
  · intro i hi
    have bounded : i < state.atoms.length + 1 := by rw [newCount] at hi; exact hi
    have parentPlus : i < state.molecule.atomCount + 1 := bounded
    have newBound : i < (attachSingle state parent atom).atoms.length := by
      change i < (state.atoms ++ [atom]).length
      simp only [List.length_append, List.length_singleton]
      exact bounded
    have freshBound :
        i < (appendFreshChild state.molecule ⟨parent, parentBound⟩ atom).atomCount := by
      rw [appendFreshChild_atomCount]
      exact bounded
    have freshRows := appendFreshChild_row_count state.molecule ⟨parent, parentBound⟩ atom
    rw [← molecule_writtenNeighbors_getD (attachSingle state parent atom) i
        (attachSingle_row_count state parent atom rowCount) newBound]
    rw [attachSingle_written_pointwise state parent atom rowCount parentBound i bounded]
    rw [← rawMolecule_writtenNeighbors_getD
        (appendFreshChild state.molecule ⟨parent, parentBound⟩ atom) i freshRows freshBound]
    rw [appendFreshChild_writtenNeighbors state.molecule ⟨parent, parentBound⟩ atom i parentPlus]

/-- **Full `RawMolecule` join.**  The entire molecule produced by `attachSingle` — atoms, the single
bond record and the complete `neighborOrder` table — equals the independent `appendFreshChild`
molecule when the stored table is row-complete and the parent is a real index.  The atom and bond
fields are definitionally the same single append; the table field is exactly
`native_attachSingle_neighborOrder_join`, so the join is not merely pointwise. -/
theorem native_attachSingle_appendFreshChild (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (rowCount : state.order.length = state.atoms.length)
    (parentBound : parent < state.atoms.length) :
    (attachSingle state parent atom).molecule =
      appendFreshChild state.molecule ⟨parent, parentBound⟩ atom := by
  exact congrArg
    (fun rows => { (appendFreshChild state.molecule ⟨parent, parentBound⟩ atom)
      with neighborOrder := rows })
    (native_attachSingle_neighborOrder_join state parent atom rowCount parentBound)





theorem native_explicit_single_append_join (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (current : state.current? = some parent)
    (rowCount : state.order.length = state.atoms.length)
    (parentBound : parent < state.atoms.length) :
    ((pendingSingle state).addAtom atom).molecule =
      appendFreshChild state.molecule ⟨parent, parentBound⟩ atom := by
  rw [addAtom_after_explicit_single state parent atom current]
  exact native_attachSingle_appendFreshChild state parent atom rowCount parentBound

/-! ## Independent record preservation -/

/-- Chronological raw bond records imply basic parser well-formedness of the stored molecule. -/
theorem wellFormed_of_chronological (state : ParseState) (physical : Chronological state) :
    state.molecule.WellFormed := by
  intro bond membership
  have forward := physical.forward bond membership
  have bounded := physical.bounded bond membership
  change bond.source < state.atoms.length ∧ bond.target < state.atoms.length ∧
    bond.source ≠ bond.target
  exact ⟨by omega, bounded, by omega⟩

/-- **Independent record preservation.**  From only independent old-state inputs — the physical
chronological bond record, the old stored-row exactness, the stored row count and the parent bound —
the explicit single append preserves `StoredRowExact`, preserves `WellFormed`, preserves the
chronological record, and its whole written table is the independent `appendFreshChild` table.  The
conclusion is a conjunction so that the relation-preservation and the table-join stay visibly
separate; no desired parser output is consumed. -/
theorem native_attachSingle_independent_records_preserved (state : ParseState) (parent : ℕ)
    (atom : AtomSpec) (rowCount : state.order.length = state.atoms.length)
    (parentBound : parent < state.atoms.length)
    (physical : Chronological state)
    (oldRows : StoredRowExact state.molecule) :
    StoredRowExact (attachSingle state parent atom).molecule ∧
      (attachSingle state parent atom).molecule.WellFormed ∧
      ChronologicalRecords (attachSingle state parent atom).atoms
        (attachSingle state parent atom).bonds ∧
      (attachSingle state parent atom).order =
        (appendFreshChild state.molecule ⟨parent, parentBound⟩ atom).neighborOrder := by
  have oldWF : state.molecule.WellFormed := wellFormed_of_chronological state physical
  have newPhysical : Chronological (attachSingle state parent atom) :=
    attachSingle_chronological state parent atom physical parentBound
  exact ⟨attachSingle_storedRowExact state parent atom parentBound oldWF oldRows,
    wellFormed_of_chronological (attachSingle state parent atom) newPhysical,
    newPhysical,
    native_attachSingle_neighborOrder_join state parent atom rowCount parentBound⟩

end TetraStereo.UniversalProof.NativeAttachSingleWrittenAppendJoinProofs
