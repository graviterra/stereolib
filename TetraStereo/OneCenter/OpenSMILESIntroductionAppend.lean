import TetraStereo.OneCenter.ChemistrySemantics
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.OpenSMILESIntroductionAppend

/-- Source-token history for a row-complete chronological construction. Roots carry `none`;
known predecessors have an actual directed edge and retain the first written-neighbor slot. -/
structure ValidRecords (atoms : List AtomSpec) (bonds : List RawBond)
    (order : List (List Nat)) (predecessors : List (Option Nat)) : Prop where
  count : predecessors.length = atoms.length
  rows : order.length = atoms.length
  parent : ∀ index predecessor,
    predecessors[index]? = some (some predecessor) →
      predecessor < index ∧
      (bonds.any fun bond => bond.source == predecessor && bond.target == index) = true ∧
      (order.getD index []).head? = some predecessor

/-- Current position and branch stacks do not affect already written source records. -/
abbrev Valid (state : ParseState) : Prop :=
  ValidRecords state.atoms state.bonds state.order state.introductionPredecessors

/-- Independent record update shared by the finite-family construction proofs. -/
def append (state : ParseState) (parent : Nat) (atom : AtomSpec) : ParseState :=
  let index := state.atoms.length
  let rows := state.order ++ [[]]
  let updated := rows.set parent (rows.getD parent [] ++ [index])
  { state with
    atoms := state.atoms ++ [atom]
    bonds := state.bonds ++ [{ source := parent, target := index, kind := .single }]
    current? := some index
    pendingBond? := none
    order := updated.set index (updated.getD index [] ++ [parent])
    introductionPredecessors :=
      if state.introductionPredecessors.length = state.atoms.length then
        state.introductionPredecessors ++ [some parent]
      else state.introductionPredecessors }

private theorem getD_append_before (rows suffix : List (List Nat)) (index : Nat)
    (bound : index < rows.length) :
    (rows ++ suffix).getD index [] = rows.getD index [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left bound,
    ← List.getD_eq_getElem?_getD]

private theorem getD_append_boundary (rows : List (List Nat)) (row : List Nat) :
    (rows ++ [row]).getD rows.length [] = row := by
  induction rows with
  | nil => rfl
  | cons _ rows ih => exact ih

private theorem append_order (state : ParseState) (parent : Nat) (atom : AtomSpec)
    (rows : state.order.length = state.atoms.length) (bound : parent < state.atoms.length) :
    (append state parent atom).order =
      state.order.set parent (state.order.getD parent [] ++ [state.atoms.length]) ++ [[parent]] := by
  have parentRows : parent < state.order.length := by omega
  have oldParent := getD_append_before state.order [[]] parent parentRows
  let updated := state.order.set parent (state.order.getD parent [] ++ [state.atoms.length])
  have updatedLength : updated.length = state.atoms.length := by simp [updated, rows]
  have newRow : (updated ++ [[]]).getD state.atoms.length [] = [] := by
    rw [← updatedLength]
    exact getD_append_boundary updated []
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
  rw [List.set_append_right state.atoms.length [parent] (by omega), updatedLength, Nat.sub_self]
  rfl

private theorem append_old_head (state : ParseState) (parent : Nat) (atom : AtomSpec)
    (rows : state.order.length = state.atoms.length) (bound : parent < state.atoms.length)
    (index predecessor : Nat) (old : index < state.atoms.length)
    (head : (state.order.getD index []).head? = some predecessor) :
    ((append state parent atom).order.getD index []).head? = some predecessor := by
  rw [append_order state parent atom rows bound,
    getD_append_before _ [[parent]] index (by simpa [rows] using old)]
  by_cases same : parent = index
  · subst index
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]
    change (state.order.getD parent [] ++ [state.atoms.length]).head? = some predecessor
    have keeps : ∀ row : List Nat, row.head? = some predecessor →
        (row ++ [state.atoms.length]).head? = some predecessor := by
      intro row first
      cases row with
      | nil => simp at first
      | cons head tail => exact first
    exact keeps _ head
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_set_ne same] using head

/-- Appending at a real parent preserves total, internally consistent introduction history. -/
theorem append_valid (state : ParseState) (parent : Nat) (atom : AtomSpec)
    (valid : Valid state) (bound : parent < state.atoms.length) :
    Valid (append state parent atom) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [append, valid.count]
  · simp [append, valid.rows]
  · intro index predecessor observed
    have lookup : (state.introductionPredecessors ++ [some parent])[index]? =
        some (some predecessor) := by simpa only [append, if_pos valid.count] using observed
    have upper : index < state.atoms.length + 1 := by
      have := (List.getElem?_eq_some_iff.mp lookup).1
      simpa [valid.count] using this
    by_cases old : index < state.atoms.length
    · rw [List.getElem?_append_left (by simpa [valid.count] using old)] at lookup
      have previous := valid.parent index predecessor lookup
      refine ⟨previous.1, ?_, append_old_head state parent atom valid.rows bound index predecessor old previous.2.2⟩
      change ((state.bonds ++ [_]).any _) = true
      simp only [List.any_append, previous.2.1, Bool.true_or]
    · have fresh : index = state.atoms.length := by omega
      subst index
      have equal : parent = predecessor := by
        simpa [List.getElem?_append, valid.count] using lookup
      subst predecessor
      refine ⟨bound, ?_, ?_⟩
      · change ((state.bonds ++ [_]).any _) = true
        simp
      · rw [append_order state parent atom valid.rows bound]
        have size : (state.order.set parent
            (state.order.getD parent [] ++ [state.atoms.length])).length = state.atoms.length := by
          simp [valid.rows]
        have freshRow := getD_append_boundary
          (state.order.set parent (state.order.getD parent [] ++ [state.atoms.length])) [parent]
        rw [size] at freshRow
        rw [freshRow]
        rfl

/-- The independent record invariant entails the exact public parser provenance check. -/
theorem Valid.parserIntroductionValid (state : ParseState) (valid : Valid state) :
    state.molecule.parserIntroductionValid? = true := by
  simp only [RawMolecule.parserIntroductionValid?, RawMolecule.introductionPredecessorsValid?,
    ParseState.molecule, RawMolecule.atomCount, valid.count, Nat.le_refl, decide_true,
    Bool.true_and]
  apply List.all_eq_true.mpr
  intro index member
  have bound := List.mem_range.mp member
  have sourceBound : index < state.introductionPredecessors.length := by simpa [valid.count] using bound
  have rowBound : index < state.order.length := by simpa [valid.rows] using bound
  cases observed : state.introductionPredecessors[index]? with
  | none => simp [List.getElem?_eq_getElem sourceBound] at observed
  | some parent =>
      cases parent with
      | none => rfl
      | some predecessor =>
          have facts := valid.parent index predecessor observed
          have written : state.molecule.writtenNeighbors index = state.order.getD index [] := by
            change (match state.order[index]? with | some row => row | none => _) = _
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem rowBound]
            rfl
          change (decide (predecessor < index) &&
            (state.bonds.any fun bond => bond.source == predecessor && bond.target == index) &&
            (state.molecule.writtenNeighbors index).head? == some predecessor) = true
          simp only [facts.1, decide_true, facts.2.1, Bool.true_and, written, facts.2.2, beq_self_eq_true]

end TetraStereo.OneCenter.OpenSMILESIntroductionAppend

assert_kernel_only TetraStereo.OneCenter.OpenSMILESIntroductionAppend.append_valid
assert_kernel_only TetraStereo.OneCenter.OpenSMILESIntroductionAppend.Valid.parserIntroductionValid
