import TetraStereo.UniversalProof.NextFrontier.NativeNitrileParser

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

def appendMethylenes : Nat → ParseState → ParseState
  | 0, state => state
  | n + 1, state => appendMethylenes n (state.addAtom (bracket .C 2))

theorem append_methylenes_succ_right (n : Nat) (state : ParseState) :
    appendMethylenes (n + 1) state =
      (appendMethylenes n state).addAtom (bracket .C 2) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => exact ih _

theorem tail_state_eq_append (n : Nat) (state : ParseState) :
    tailState n state = (appendMethylenes n state).addAtom (bracket .C 3) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => exact ih _

def completedPrefixRows : List (List Nat) :=
  [[1, 2, 4], [0], [0, 3], [2], [0, 5, 6], [4]]

def internalTailRow (offset : Nat) : List Nat := [tailParent offset, offset + 7]

def completedRows (n : Nat) : List (List Nat) :=
  completedPrefixRows ++ (List.range n).map internalTailRow ++ [[tailParent n]]

theorem tail_rows_split (n : Nat) :
    tailRows n = (List.range n).map internalTailRow ++ [[tailParent n]] := by
  unfold tailRows
  rw [List.range_succ, List.map_append]
  have inside : (List.range n).map (fun offset =>
      [tailParent offset] ++ if offset < n then [offset + 7] else []) =
      (List.range n).map internalTailRow := by
    apply List.map_congr_left
    intro offset retained
    simp [List.mem_range.mp retained, internalTailRow]
  rw [inside]
  simp

theorem raw_rows_completed (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).neighborOrder = completedRows n := by
  simp only [raw, tail_rows_split, completedRows, completedPrefixRows, List.append_assoc]

theorem completed_rows_length (n : Nat) : (completedRows n).length = n + 7 := by
  simp [completedRows, completedPrefixRows]

private theorem getD_append_before (rows suffix : List (List Nat)) (index : Nat)
    (bounded : index < rows.length) :
    (rows ++ suffix).getD index [] = rows.getD index [] := by
  induction rows generalizing index with
  | nil => simp only [List.length_nil] at bounded; omega
  | cons row rows ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index (by simpa using bounded)

private theorem getD_append_boundary (rows : List (List Nat)) (row : List Nat) :
    (rows ++ [row]).getD rows.length [] = row := by
  induction rows with
  | nil => rfl
  | cons _ rows ih => exact ih

theorem add_bracket_carbon_bonds (state : ParseState) (parent h : Nat)
    (current : state.current? = some parent) (pending : state.pendingBond? = none) :
    (state.addAtom (bracket .C h)).bonds =
      state.bonds ++ [⟨parent, state.atoms.length, .single⟩] := by
  have fresh : listGet? (state.atoms ++ [bracket .C h]) state.atoms.length =
      some (bracket .C h) := by
    rw [listGet?_append_right_of_length_le _ _ _ (Nat.le_refl _), Nat.sub_self]
    rfl
  simp only [ParseState.addAtom, ParseState.nextAtomId, current, ParseState.addBond,
    pending, ParseState.molecule, atomAt?]
  rw [fresh]
  cases listGet? (state.atoms ++ [bracket .C h]) parent <;>
    simp [defaultBondKind, bracket]

theorem add_bracket_carbon_order (state : ParseState) (parent h : Nat)
    (current : state.current? = some parent)
    (rows : state.order.length = state.atoms.length) (bound : parent < state.atoms.length) :
    (state.addAtom (bracket .C h)).order =
      state.order.set parent (state.order.getD parent [] ++ [state.atoms.length]) ++ [[parent]] := by
  have parentRows : parent < state.order.length := by omega
  let updated := state.order.set parent (state.order.getD parent [] ++ [state.atoms.length])
  have updatedLength : updated.length = state.atoms.length := by
    simp only [updated, List.length_set, rows]
  have newRow : (updated ++ [[]]).getD state.atoms.length [] = [] := by
    rw [← updatedLength]
    exact getD_append_boundary updated []
  simp only [ParseState.addAtom, ParseState.nextAtomId, current, ParseState.addBond,
    ParseState.noteOrder]
  rw [getD_append_before state.order [[]] parent parentRows,
    List.set_append_left parent _ parentRows]
  change (updated ++ [[]]).set state.atoms.length
      ((updated ++ [[]]).getD state.atoms.length [] ++ [parent]) = updated ++ [[parent]]
  rw [newRow]
  change (updated ++ [[]]).set state.atoms.length [parent] = updated ++ [[parent]]
  rw [List.set_append_right state.atoms.length [parent] (by omega)]
  rw [updatedLength, Nat.sub_self]
  rfl

/-- A closed independent parser state after n methylenes and one terminal carbon. The terminal
inline count is a parameter so the induction can use 2 for an intermediate and 3 at the endpoint. -/
def terminalState (parity : TetrahedralInputParity) (n h : Nat) : ParseState :=
  { atoms := prefixAtoms parity ++ List.replicate n (bracket .C 2) ++ [bracket .C h]
    bonds := prefixBonds ++ tailBonds n
    current? := some (n + 6)
    order := completedRows n
    introductionPredecessors := introductionRows n }

theorem terminal_state_atom_length (parity : TetrahedralInputParity) (n h : Nat) :
    (terminalState parity n h).atoms.length = n + 7 := by
  simp [terminalState, prefixAtoms]

theorem introduction_rows_length (n : Nat) : (introductionRows n).length = n + 7 := by
  simp [introductionRows]

private theorem completed_rows_step (n : Nat) :
    (completedRows n).set (n + 6) ((completedRows n).getD (n + 6) [] ++ [n + 7]) ++
      [[n + 6]] = completedRows (n + 1) := by
  let before := completedPrefixRows ++ (List.range n).map internalTailRow
  have count : before.length = n + 6 := by
    simp [before, completedPrefixRows]
  have lookup : (completedRows n).getD (n + 6) [] = [tailParent n] := by
    change (before ++ [[tailParent n]]).getD (n + 6) [] = _
    rw [← count]
    exact getD_append_boundary _ _
  rw [lookup]
  change (before ++ [[tailParent n]]).set (n + 6) [tailParent n, n + 7] ++
    [[n + 6]] = _
  rw [List.set_append_right (n + 6) _ (by omega), count, Nat.sub_self]
  simp only [List.set_cons_zero]
  simp [completedRows, List.range_succ, List.map_append,
    List.append_assoc, internalTailRow, before, tailParent]

private theorem parser_state_eq (left right : ParseState)
    (atoms : left.atoms = right.atoms) (bonds : left.bonds = right.bonds)
    (current : left.current? = right.current?) (branches : left.branches = right.branches)
    (rings : left.rings = right.rings) (pending : left.pendingBond? = right.pendingBond?)
    (order : left.order = right.order)
    (introduction : left.introductionPredecessors = right.introductionPredecessors) :
    left = right := by
  cases left
  cases right
  simp_all

theorem terminal_state_step (parity : TetrahedralInputParity) (n h : Nat) :
    (terminalState parity n 2).addAtom (bracket .C h) = terminalState parity (n + 1) h := by
  have bonds := add_bracket_carbon_bonds (terminalState parity n 2) (n + 6) h rfl rfl
  have order := add_bracket_carbon_order (terminalState parity n 2) (n + 6) h rfl
    (by rw [terminal_state_atom_length]; exact completed_rows_length n)
    (by rw [terminal_state_atom_length]; omega)
  rw [terminal_state_atom_length] at bonds order
  change ((terminalState parity n 2).addAtom (bracket .C h)).bonds =
    (prefixBonds ++ tailBonds n) ++ [⟨n + 6, n + 7, .single⟩] at bonds
  change ((terminalState parity n 2).addAtom (bracket .C h)).order =
    (completedRows n).set (n + 6) ((completedRows n).getD (n + 6) [] ++ [n + 7]) ++
      [[n + 6]] at order
  rw [completed_rows_step] at order
  have bondList : (prefixBonds ++ tailBonds n) ++ [⟨n + 6, n + 7, .single⟩] =
      prefixBonds ++ tailBonds (n + 1) := by
    simp [tailBonds, List.range_succ, List.map_append,
      List.append_assoc, tailParent]
  rw [bondList] at bonds
  refine parser_state_eq _ _ ?_ bonds ?_ ?_ ?_ ?_ order ?_
  all_goals
    simp [ParseState.addAtom, ParseState.nextAtomId, ParseState.addBond, terminalState,
      prefixAtoms, List.replicate_add, List.replicate_one, List.append_assoc,
      introductionRows, List.range_succ, List.map_append, tailParent]

theorem append_terminal_state (parity : TetrahedralInputParity) (n h : Nat) :
    (appendMethylenes n (prefixState parity)).addAtom (bracket .C h) =
      terminalState parity n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
      rw [append_methylenes_succ_right]
      have intermediate := ih 2
      rw [intermediate]
      exact terminal_state_step parity n h

/-- Full independently specified raw equality, including all written rows and parser provenance. -/
theorem actual_final_state_molecule (parity : TetrahedralInputParity) (n : Nat) :
    (finalState parity n).molecule = raw parity n := by
  unfold finalState
  rw [tail_state_eq_append, append_terminal_state]
  simp only [terminalState, ParseState.molecule, raw, tailAtoms,
    completedRows, completedPrefixRows, tail_rows_split, List.append_assoc]

theorem actual_final_state_closed (parity : TetrahedralInputParity) (n : Nat) :
    (finalState parity n).branches = [] ∧ (finalState parity n).rings = [] ∧
      (finalState parity n).pendingBond? = none := by
  unfold finalState
  rw [tail_state_eq_append, append_terminal_state]
  exact ⟨rfl, rfl, rfl⟩

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
