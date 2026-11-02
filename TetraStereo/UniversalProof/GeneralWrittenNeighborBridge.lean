import TetraStereo.UniversalProof.GeneralParserStateBridge
import TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.GeneralWrittenNeighborBridge

open TetraStereo.OneCenter
open TetraStereo.UniversalProof.GeneralParserStateBridge








/-- Elementary written-row append facts use core list recursion, avoiding a broad new import. -/
theorem written_getD_append_before (rows suffix : List (List ℕ)) (index : ℕ)
    (bounded : index < rows.length) :
    (rows ++ suffix).getD index [] = rows.getD index [] := by
  induction rows generalizing index with
  | nil => cases Nat.not_lt_zero index bounded
  | cons _ rows ih =>
      cases index with
      | zero => rfl
      | succ index =>
          exact ih index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using bounded)

theorem written_getD_append_boundary (rows : List (List ℕ)) (row : List ℕ) :
    (rows ++ [row]).getD rows.length [] = row := by
  induction rows with
  | nil => rfl
  | cons _ rows ih => exact ih

/-- Raw chronological append has a canonical old-parent update plus a singleton fresh row.
The only hypotheses are independent physical row count and parent bound. -/
theorem attachSingle_order (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (rowCount : state.order.length = state.atoms.length)
    (parentBound : parent < state.atoms.length) :
    (attachSingle state parent atom).order =
      state.order.set parent (state.order.getD parent [] ++ [state.atoms.length]) ++ [[parent]] := by
  have parentRows : parent < state.order.length := by omega
  have oldParent := written_getD_append_before state.order [[]] parent parentRows
  let updated := state.order.set parent (state.order.getD parent [] ++ [state.atoms.length])
  have updatedLength : updated.length = state.atoms.length := by
    dsimp [updated]
    rw [List.length_set, rowCount]
  have newRow : (updated ++ [[]]).getD state.atoms.length [] = [] := by
    rw [← updatedLength]
    exact written_getD_append_boundary updated []
  change ((state.order ++ [[]]).set parent
    ((state.order ++ [[]]).getD parent [] ++ [state.atoms.length])).set state.atoms.length
    ((((state.order ++ [[]]).set parent
      ((state.order ++ [[]]).getD parent [] ++ [state.atoms.length])).getD
      state.atoms.length []) ++ [parent]) = _
  rw [oldParent, List.set_append_left parent _ parentRows]
  change (updated ++ [[]]).set state.atoms.length
    ((updated ++ [[]]).getD state.atoms.length [] ++ [parent]) = updated ++ [[parent]]
  rw [newRow]
  change (updated ++ [[]]).set state.atoms.length [parent] = updated ++ [[parent]]
  rw [List.set_append_right state.atoms.length [parent] (by omega)]
  rw [updatedLength, Nat.sub_self]
  rfl

theorem attachSingle_row_count (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (rowCount : state.order.length = state.atoms.length) :
    (attachSingle state parent atom).order.length =
      (attachSingle state parent atom).atoms.length := by
  change ((((state.order ++ [[]]).set parent _).set state.atoms.length _).length) =
    (state.atoms ++ [atom]).length
  simp only [List.length_set, List.length_append, List.length_singleton]
  omega

theorem blockResult_row_count (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (rowCount : state.order.length = state.atoms.length) :
    (blockResult state parent parity).order.length =
      (blockResult state parent parity).atoms.length := by
  simp only [blockResult, pendantBranchResult, singleBranchResult, attachSingle,
    List.length_set, List.length_append, List.length_singleton]
  all_goals omega

theorem blocksResult_row_count (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) (rowCount : state.order.length = state.atoms.length) :
    (blocksResult parities state parent).order.length =
      (blocksResult parities state parent).atoms.length := by
  induction parities generalizing state parent with
  | nil => exact rowCount
  | cons parity rest ih =>
      exact ih (blockResult state parent parity) state.atoms.length
        (blockResult_row_count state parent parity rowCount)

theorem familyRaw_row_count (parities : List TetrahedralInputParity) :
    (familyRaw parities).neighborOrder.length = (familyRaw parities).atomCount := by
  exact attachSingle_row_count _ _ _
    (blocksResult_row_count parities initialHydrogenState 0 rfl)

theorem attachSingle_old_row (state : ParseState) (parent : ℕ) (atom : AtomSpec) (index : ℕ)
    (rowCount : state.order.length = state.atoms.length)
    (parentBound : parent < state.atoms.length) (indexBound : index < state.atoms.length)
    (other : parent ≠ index) :
    (attachSingle state parent atom).order.getD index [] = state.order.getD index [] := by
  rw [attachSingle_order state parent atom rowCount parentBound]
  rw [written_getD_append_before _ [[parent]] index (by rw [List.length_set, rowCount]; exact indexBound)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne other]

theorem attachSingle_parent_row (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (rowCount : state.order.length = state.atoms.length)
    (parentBound : parent < state.atoms.length) :
    (attachSingle state parent atom).order.getD parent [] =
      state.order.getD parent [] ++ [state.atoms.length] := by
  rw [attachSingle_order state parent atom rowCount parentBound]
  rw [written_getD_append_before _ [[parent]] parent (by rw [List.length_set, rowCount]; exact parentBound)]
  have parentRows : parent < state.order.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self parentRows]
  rfl

theorem attachSingle_fresh_row (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (rowCount : state.order.length = state.atoms.length)
    (parentBound : parent < state.atoms.length) :
    (attachSingle state parent atom).order.getD state.atoms.length [] = [parent] := by
  rw [attachSingle_order state parent atom rowCount parentBound]
  have count : (state.order.set parent
      (state.order.getD parent [] ++ [state.atoms.length])).length = state.atoms.length := by
    rw [List.length_set, rowCount]
  simpa only [count] using written_getD_append_boundary
    (state.order.set parent (state.order.getD parent [] ++ [state.atoms.length])) [parent]

/-- The actual parity frame is the independent physical row [parent,H,F,Br], in written order.
This local conclusion is derived from four raw appends and is uniform in all previous records. -/
theorem pendantBranchResult_tag_row (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (rowCount : state.order.length = state.atoms.length)
    (parentBound : parent < state.atoms.length) :
    (pendantBranchResult state parent parity).order.getD state.atoms.length [] =
      [parent, state.atoms.length + 1, state.atoms.length + 2, state.atoms.length + 3] := by
  let opened : ParseState := { state with branches := parent :: state.branches }
  let index := state.atoms.length
  let tagged := attachSingle opened parent (atomSpec (.taggedCarbon parity))
  let hydrogen := singleBranchResult tagged index (atomSpec .hydrogen)
  let fluorine := singleBranchResult hydrogen index (atomSpec .fluorine)
  have tagRows : tagged.order.length = tagged.atoms.length :=
    attachSingle_row_count opened parent _ rowCount
  have tagSize : tagged.atoms.length = index + 1 := by
    change (state.atoms ++ [atomSpec (.taggedCarbon parity)]).length = state.atoms.length + 1
    rw [List.length_append, List.length_singleton]
  have tagBound : index < tagged.atoms.length := by rw [tagSize]; omega
  have hydrogenRows : hydrogen.order.length = hydrogen.atoms.length :=
    attachSingle_row_count tagged index _ tagRows
  have hydrogenSize : hydrogen.atoms.length = index + 2 := by
    change (tagged.atoms ++ [atomSpec .hydrogen]).length = index + 2
    rw [List.length_append, List.length_singleton, tagSize]
  have hydrogenBound : index < hydrogen.atoms.length := by rw [hydrogenSize]; omega
  have fluorineRows : fluorine.order.length = fluorine.atoms.length :=
    attachSingle_row_count hydrogen index _ hydrogenRows
  have fluorineSize : fluorine.atoms.length = index + 3 := by
    change (hydrogen.atoms ++ [atomSpec .fluorine]).length = index + 3
    rw [List.length_append, List.length_singleton, hydrogenSize]
  have fluorineBound : index < fluorine.atoms.length := by rw [fluorineSize]; omega
  change (attachSingle fluorine index (atomSpec .bromine)).order.getD index [] =
    [parent, index + 1, index + 2, index + 3]
  have fluorineRow : fluorine.order.getD index [] =
      hydrogen.order.getD index [] ++ [hydrogen.atoms.length] :=
    attachSingle_parent_row hydrogen index (atomSpec .fluorine) hydrogenRows hydrogenBound
  have hydrogenRow : hydrogen.order.getD index [] =
      tagged.order.getD index [] ++ [tagged.atoms.length] :=
    attachSingle_parent_row tagged index (atomSpec .hydrogen) tagRows tagBound
  have taggedRow : tagged.order.getD index [] = [parent] :=
    attachSingle_fresh_row opened parent (atomSpec (.taggedCarbon parity)) rowCount parentBound
  simpa only [fluorineRow, hydrogenRow, taggedRow, tagSize, hydrogenSize, fluorineSize,
    List.cons_append, List.nil_append] using
    attachSingle_parent_row fluorine index (atomSpec .bromine) fluorineRows fluorineBound

theorem blockResult_tag_row (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (rowCount : state.order.length = state.atoms.length) :
    (blockResult state parent parity).order.getD (state.atoms.length + 2) [] =
      [state.atoms.length, state.atoms.length + 3, state.atoms.length + 4,
        state.atoms.length + 5] := by
  let backbone := attachSingle state parent (atomSpec .carbon)
  let hydrogen := singleBranchResult backbone state.atoms.length (atomSpec .hydrogen)
  have backboneRows : backbone.order.length = backbone.atoms.length :=
    attachSingle_row_count state parent _ rowCount
  have hydrogenRows : hydrogen.order.length = hydrogen.atoms.length :=
    attachSingle_row_count backbone state.atoms.length _ backboneRows
  have hydrogenSize : hydrogen.atoms.length = state.atoms.length + 2 := by
    change ((state.atoms ++ [atomSpec .carbon]) ++ [atomSpec .hydrogen]).length = _
    simp only [List.length_append, List.length_singleton]
  have hydrogenBound : state.atoms.length < hydrogen.atoms.length := by
    rw [hydrogenSize]
    omega
  change (pendantBranchResult hydrogen state.atoms.length parity).order.getD
    (state.atoms.length + 2) [] = _
  simpa only [hydrogenSize] using pendantBranchResult_tag_row hydrogen state.atoms.length
    parity hydrogenRows hydrogenBound


/-- At a real stored index the parser's raw written projection is the actual stored row. -/
theorem molecule_writtenNeighbors_getD (state : ParseState) (index : ℕ)
    (rowCount : state.order.length = state.atoms.length)
    (bounded : index < state.atoms.length) :
    state.molecule.writtenNeighbors index = state.order.getD index [] := by
  have inRows : index < state.order.length := by omega
  change (match state.order[index]? with | some row => row | none => _) = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inRows]
  rfl

/-- Native list.set updates implement exactly the general fresh-child row at every real index. -/
theorem attachSingle_written_pointwise (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (rowCount : state.order.length = state.atoms.length)
    (parentBound : parent < state.atoms.length) (index : ℕ)
    (bounded : index < state.atoms.length + 1) :
    (attachSingle state parent atom).molecule.writtenNeighbors index =
      TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.appendedRow state.molecule ⟨parent, parentBound⟩ index := by
  have newRows := attachSingle_row_count state parent atom rowCount
  have newBound : index < (attachSingle state parent atom).atoms.length := by
    change index < (state.atoms ++ [atom]).length
    simpa only [List.length_append, List.length_singleton] using bounded
  rw [molecule_writtenNeighbors_getD _ index newRows newBound]
  by_cases old : index < state.atoms.length
  · rw [TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.appendedRow_old state.molecule ⟨parent, parentBound⟩ old]
    rw [molecule_writtenNeighbors_getD state index rowCount old]
    by_cases same : parent = index
    · subst index
      rw [attachSingle_parent_row state parent atom rowCount parentBound]
      rw [if_pos (show parent = (⟨parent, parentBound⟩ : Fin state.atoms.length).val from rfl)]
      rfl
    · rw [attachSingle_old_row state parent atom index rowCount parentBound old same]
      simp only [if_neg (Ne.symm same), List.append_nil]
  · have fresh : index = state.atoms.length := by omega
    subst index
    rw [attachSingle_fresh_row state parent atom rowCount parentBound]
    exact (TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.appendedRow_fresh state.molecule ⟨parent, parentBound⟩ (Nat.lt_irrefl _)).symm

/-- Positive adjacency ignores the representation of the stored written table. -/
theorem attachSingle_bondOrder (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (parentBound : parent < state.atoms.length) (left right : ℕ) :
    (attachSingle state parent atom).molecule.bondOrder left right =
      (TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.appendFreshChild state.molecule ⟨parent, parentBound⟩ atom).bondOrder left right := rfl

/-- General relational preservation transfers to the actual native list.set constructor. -/
theorem attachSingle_storedRowExact (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (parentBound : parent < state.atoms.length) (wellFormed : state.molecule.WellFormed)
    (oldRows : TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.StoredRowExact state.molecule) :
    TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.StoredRowExact (attachSingle state parent atom).molecule := by
  have newRows := TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.appendFreshChild_storedRowExact state.molecule ⟨parent, parentBound⟩
    atom wellFormed oldRows
  refine ⟨attachSingle_row_count state parent atom oldRows.1, ?_⟩
  intro index
  have bounded : index.val < state.atoms.length + 1 := by
    have bound := index.isLt
    change index.val < (state.atoms ++ [atom]).length at bound
    simpa only [List.length_append, List.length_singleton] using bound
  have genericBound : index.val <
      (TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.appendFreshChild state.molecule ⟨parent, parentBound⟩ atom).atomCount := by
    rw [TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.appendFreshChild_atomCount]
    exact bounded
  have relational := newRows.2 ⟨index.val, genericBound⟩
  have written : (attachSingle state parent atom).molecule.writtenNeighbors index.val =
      (TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.appendFreshChild state.molecule ⟨parent, parentBound⟩ atom).writtenNeighbors index.val := by
    rw [attachSingle_written_pointwise state parent atom oldRows.1 parentBound index.val bounded,
      TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.appendFreshChild_writtenNeighbors state.molecule ⟨parent, parentBound⟩ atom index.val bounded]
  unfold TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.WrittenRowExactAt at relational ⊢
  rw [written]
  refine ⟨relational.1, ?_, ?_⟩
  · intro ligand membership
    exact relational.2.1 ligand membership
  · intro ligand ligandBound
    rw [attachSingle_bondOrder state parent atom parentBound index.val ligand]
    exact relational.2.2 ligand ligandBound

/-- One independent invariant carries chronology and exact stored written adjacency together. -/
def PhysicalStored (state : ParseState) : Prop :=
  Chronological state ∧ TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.StoredRowExact state.molecule

theorem attachSingle_physical_stored (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (physical : PhysicalStored state) (parentBound : parent < state.atoms.length) :
    PhysicalStored (attachSingle state parent atom) :=
  ⟨attachSingle_chronological state parent atom physical.1 parentBound,
    attachSingle_storedRowExact state parent atom parentBound
      (chronological_admissible state physical.1).1 physical.2⟩

theorem singleBranchResult_physical_stored (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (physical : PhysicalStored state) (parentBound : parent < state.atoms.length) :
    PhysicalStored (singleBranchResult state parent atom) :=
  attachSingle_physical_stored state parent atom physical parentBound

theorem pendantBranchResult_physical_stored (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (physical : PhysicalStored state)
    (parentBound : parent < state.atoms.length) :
    PhysicalStored (pendantBranchResult state parent parity) := by
  let opened : ParseState := { state with branches := parent :: state.branches }
  let tagIndex := state.atoms.length
  let tagged := attachSingle opened parent (atomSpec (.taggedCarbon parity))
  let hydrogen := singleBranchResult tagged tagIndex (atomSpec .hydrogen)
  let fluorine := singleBranchResult hydrogen tagIndex (atomSpec .fluorine)
  let bromine := attachSingle fluorine tagIndex (atomSpec .bromine)
  have taggedPhysical : PhysicalStored tagged :=
    attachSingle_physical_stored opened parent _ physical parentBound
  have taggedBound : tagIndex < tagged.atoms.length := by
    change state.atoms.length < (state.atoms ++ [atomSpec (.taggedCarbon parity)]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have hydrogenPhysical : PhysicalStored hydrogen :=
    singleBranchResult_physical_stored tagged tagIndex _ taggedPhysical taggedBound
  have hydrogenBound : tagIndex < hydrogen.atoms.length := by
    change tagIndex < (tagged.atoms ++ [atomSpec .hydrogen]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have fluorinePhysical : PhysicalStored fluorine :=
    singleBranchResult_physical_stored hydrogen tagIndex _ hydrogenPhysical hydrogenBound
  have fluorineBound : tagIndex < fluorine.atoms.length := by
    change tagIndex < (hydrogen.atoms ++ [atomSpec .fluorine]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have brominePhysical : PhysicalStored bromine :=
    attachSingle_physical_stored fluorine tagIndex _ fluorinePhysical fluorineBound
  exact brominePhysical

theorem blockResult_physical_stored (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (physical : PhysicalStored state)
    (parentBound : parent < state.atoms.length) :
    PhysicalStored (blockResult state parent parity) := by
  let backbone := attachSingle state parent (atomSpec .carbon)
  let hydrogen := singleBranchResult backbone state.atoms.length (atomSpec .hydrogen)
  have backbonePhysical : PhysicalStored backbone :=
    attachSingle_physical_stored state parent _ physical parentBound
  have backboneBound : state.atoms.length < backbone.atoms.length := by
    change state.atoms.length < (state.atoms ++ [atomSpec .carbon]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have hydrogenPhysical : PhysicalStored hydrogen :=
    singleBranchResult_physical_stored backbone state.atoms.length _ backbonePhysical backboneBound
  have hydrogenBound : state.atoms.length < hydrogen.atoms.length := by
    change state.atoms.length < (backbone.atoms ++ [atomSpec .hydrogen]).length
    simp only [List.length_append, List.length_singleton]
    omega
  exact pendantBranchResult_physical_stored hydrogen state.atoms.length parity
    hydrogenPhysical hydrogenBound

theorem blocksResult_physical_stored (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) (physical : PhysicalStored state)
    (parentBound : parent < state.atoms.length) :
    PhysicalStored (blocksResult parities state parent) := by
  induction parities generalizing state parent with
  | nil => exact physical
  | cons parity rest ih =>
      apply ih (blockResult state parent parity) state.atoms.length
      · exact blockResult_physical_stored state parent parity physical parentBound
      · rw [blockResult_atom_count]
        omega


theorem initialHydrogenState_physical_stored : PhysicalStored initialHydrogenState := by
  refine ⟨?_, ?_⟩
  · exact ⟨by simp [initialHydrogenState], by simp [initialHydrogenState], by simp [initialHydrogenState]⟩
  · refine ⟨rfl, ?_⟩
    intro index
    have zero : index.val = 0 := by
      have bound := index.isLt
      change index.val < 1 at bound
      omega
    unfold TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.WrittenRowExactAt
    rw [zero]
    simp [initialHydrogenState, ParseState.molecule, RawMolecule.writtenNeighbors,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder]

/-- Every finite parity list independently constructs exact written adjacency. -/
theorem familyRaw_storedRowExact (parities : List TetrahedralInputParity) :
    TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.StoredRowExact (familyRaw parities) := by
  have constructed := blocksResult_physical_stored parities initialHydrogenState 0
    initialHydrogenState_physical_stored (by decide)
  have final := attachSingle_physical_stored
    (blocksResult parities initialHydrogenState 0) (blocksParent parities initialHydrogenState 0)
    (atomSpec .hydrogen) constructed (blocksParent_bounded parities initialHydrogenState 0 (by decide))
  exact final.2

/-- Executable written exactness follows from derived physical rows, without a supplied output. -/
theorem familyRaw_writtenNeighborExact (parities : List TetrahedralInputParity) :
    (familyRaw parities).WrittenNeighborExact := by
  apply RawMolecule.WrittenNeighborExact.of_at
  intro center
  have row := (familyRaw_storedRowExact parities).2 center
  exact ⟨row.1, row.2.1, fun ligand => row.2.2 ligand.val ligand.isLt⟩

theorem parse_family_string_written_exact (parities : List TetrahedralInputParity) :
    parseOpenSMILES (familyString parities) = .ok (familyRaw parities) ∧
      (familyRaw parities).WrittenNeighborExact :=
  ⟨parse_family_string parities, familyRaw_writtenNeighborExact parities⟩

end TetraStereo.UniversalProof.GeneralWrittenNeighborBridge
