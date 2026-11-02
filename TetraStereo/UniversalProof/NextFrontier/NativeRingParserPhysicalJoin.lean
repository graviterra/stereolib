import TetraStereo.UniversalProof.NextFrontier.NativeRingParserContinuation
import TetraStereo.UniversalProof.NextFrontier.NativeRingPhysicalStructure

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingParserPhysicalJoin

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.NativeRingParserContinuation
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission



theorem add_carbon_bonds (state : ParseState) (parent : Nat)
    (current : state.current? = some parent) (pending : state.pendingBond? = none) :
    (state.addAtom (carbon 2)).bonds = state.bonds ++ [⟨parent, state.atoms.length, .single⟩] := by
  have fresh : listGet? (state.atoms ++ [carbon 2]) state.atoms.length = some (carbon 2) := by
    simpa only [Nat.add_zero] using listGet?_append_right state.atoms [carbon 2] 0
  simp only [ParseState.addAtom, ParseState.nextAtomId, current, ParseState.addBond,
    pending, ParseState.molecule, RawMolecule.atomAt?]
  rw [fresh]
  cases listGet? (state.atoms ++ [carbon 2]) parent <;>
    simp [defaultBondKind, carbon, AtomSpec.aliphatic]

/-- Exact complete bond inventory before ring closure, valid at every chain length. -/
theorem ring_chain_bonds (n : Nat) (parity : TetrahedralInputParity) :
    (appendChain (n + 1) (headState parity)).bonds =
      [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨2, 3, .single⟩] ++
        (List.range (n + 1)).map chainBond := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [appendChain_succ_right]
      rw [add_carbon_bonds _ (n + 4) (ring_chain_current n parity)
        (appendChain_pending n (headState parity)), ih, ring_chain_atoms]
      change _ ++ ([⟨n + 4, (ringRaw n parity).atomCount, .single⟩] : List RawBond) = _
      rw [atom_count]
      simp [List.range_succ, List.append_assoc, chainBond]

private theorem getD_append_left (rows suffix : List (List Nat)) (index : Nat)
    (bounded : index < rows.length) :
    (rows ++ suffix).getD index [] = rows.getD index [] := by
  induction rows generalizing index with
  | nil => exact (Nat.not_lt_zero index bounded).elim
  | cons row rows ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index (by simpa using bounded)

private theorem getD_append_boundary (rows : List (List Nat)) (row : List Nat) :
    (rows ++ [row]).getD rows.length [] = row := by
  induction rows with
  | nil => rfl
  | cons _ rows ih => exact ih

/-- The actual CH2 atom append updates the old parent and appends a fresh singleton row. -/
theorem add_carbon_order (state : ParseState) (parent : Nat)
    (current : state.current? = some parent)
    (rows : state.order.length = state.atoms.length) (bound : parent < state.atoms.length) :
    (state.addAtom (carbon 2)).order =
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
  rw [getD_append_left state.order [[]] parent parentRows,
    List.set_append_left parent _ parentRows]
  change (updated ++ [[]]).set state.atoms.length
      ((updated ++ [[]]).getD state.atoms.length [] ++ [parent]) = updated ++ [[parent]]
  rw [newRow]
  change (updated ++ [[]]).set state.atoms.length [parent] = updated ++ [[parent]]
  rw [List.set_append_right state.atoms.length [parent] (by omega)]
  rw [updatedLength, Nat.sub_self]
  rfl

def openPrefix : List (List Nat) := [[1, 2], [0], [0, 3, 4], [2]]

def internalRow (j : Nat) : List Nat := [if j = 0 then 2 else j + 3, j + 5]

def openRows (n : Nat) : List (List Nat) :=
  openPrefix ++ (List.range n).map internalRow ++ [[if n = 0 then 2 else n + 3]]

theorem openRows_length (n : Nat) : (openRows n).length = n + 5 := by
  simp [openRows, openPrefix]

/-- Exact written-neighbor table after any positive-length chain and before the closing digit. -/
theorem ring_chain_order (n : Nat) (parity : TetrahedralInputParity) :
    (appendChain (n + 1) (headState parity)).order = openRows n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have atoms : (appendChain (n + 1) (headState parity)).atoms.length = n + 5 := by
        rw [ring_chain_atoms]
        exact atom_count n parity
      have rows : (appendChain (n + 1) (headState parity)).order.length =
          (appendChain (n + 1) (headState parity)).atoms.length := by
        rw [ih, openRows_length, atoms]
      rw [appendChain_succ_right, add_carbon_order _ (n + 4)
        (ring_chain_current n parity) rows (by omega), ih, atoms]
      let priorRows := openPrefix ++ (List.range n).map internalRow
      have prefixLength : priorRows.length = n + 4 := by
        simp [priorRows, openPrefix]
      have rowLookup : (openRows n).getD (n + 4) [] =
          [if n = 0 then 2 else n + 3] := by
        change (priorRows ++ [[if n = 0 then 2 else n + 3]]).getD (n + 4) [] = _
        rw [← prefixLength]
        exact getD_append_boundary priorRows _
      rw [rowLookup]
      change (priorRows ++ [[if n = 0 then 2 else n + 3]]).set (n + 4)
        [if n = 0 then 2 else n + 3, n + 5] ++ [[n + 4]] = _
      rw [List.set_append_right (n + 4) _ (by omega), prefixLength, Nat.sub_self]
      simp only [List.set_cons_zero]
      simp only [openRows, List.range_succ, List.map_append, List.map_singleton,
        List.append_assoc, internalRow, priorRows]
      simp

theorem addAtom_introductionPredecessors (state : ParseState) (atom : AtomSpec)
    (complete : state.introductionPredecessors.length = state.atoms.length) :
    (state.addAtom atom).introductionPredecessors =
      state.introductionPredecessors ++ [state.current?] := by
  simp only [ParseState.addAtom, complete, ↓reduceIte]
  cases state.current? <;> rfl

theorem ring_chain_predecessors (n : Nat) (parity : TetrahedralInputParity) :
    (appendChain (n + 1) (headState parity)).introductionPredecessors = ringPredecessors n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have complete : (appendChain (n + 1) (headState parity)).introductionPredecessors.length =
          (appendChain (n + 1) (headState parity)).atoms.length := by
        rw [ih, ring_chain_atoms]
        simp [ringPredecessors, ringRaw]
      rw [appendChain_succ_right, addAtom_introductionPredecessors _ _ complete, ih, ring_chain_current]
      simp only [ringPredecessors, List.range_succ, List.map_append, List.map_singleton,
        List.append_assoc]
      simp

/-- Exact, independently written physical parser state immediately before opening ring digit 1.
The endpoint has only its introducing neighbor at this stage. -/
def openState (n : Nat) (parity : TetrahedralInputParity) : ParseState where
  atoms := (ringRaw n parity).atoms
  bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨2, 3, .single⟩] ++
    (List.range (n + 1)).map chainBond
  current? := some (n + 4)
  branches := [0]
  rings := []
  pendingBond? := none
  order := openRows n
  introductionPredecessors := ringPredecessors n

theorem ring_chain_state (n : Nat) (parity : TetrahedralInputParity) :
    appendChain (n + 1) (headState parity) = openState n parity := by
  have shape := ring_chain_shape n parity
  calc
    appendChain (n + 1) (headState parity) =
      { atoms := (appendChain (n + 1) (headState parity)).atoms
        bonds := (appendChain (n + 1) (headState parity)).bonds
        current? := (appendChain (n + 1) (headState parity)).current?
        branches := (appendChain (n + 1) (headState parity)).branches
        rings := (appendChain (n + 1) (headState parity)).rings
        pendingBond? := (appendChain (n + 1) (headState parity)).pendingBond?
        order := (appendChain (n + 1) (headState parity)).order
        introductionPredecessors :=
          (appendChain (n + 1) (headState parity)).introductionPredecessors } := rfl
    _ = openState n parity := by
      rw [ring_chain_atoms, ring_chain_bonds, ring_chain_current, shape.1, shape.2.1,
        shape.2.2, ring_chain_order, ring_chain_predecessors]
      rfl

def closedState (n : Nat) (parity : TetrahedralInputParity) : ParseState where
  atoms := (ringRaw n parity).atoms
  bonds := (ringRaw n parity).bonds
  current? := some 0
  branches := []
  rings := []
  pendingBond? := none
  order := (ringRaw n parity).neighborOrder
  introductionPredecessors := ringPredecessors n

/-- Exact full raw equality, including source-introduction provenance, once the independently
specified closed state has been reached. -/
theorem closedState_molecule (n : Nat) (parity : TetrahedralInputParity) :
    (closedState n parity).molecule = ringRaw n parity := rfl

private theorem set_append_boundary {α : Type} (priorRows : List α) (a b : α) :
    (priorRows ++ [a]).set priorRows.length b = priorRows ++ [b] := by
  rw [List.set_append_right priorRows.length b (Nat.le_refl _), Nat.sub_self]
  rfl

private theorem noteOrder_append_boundary (priorRows : List (List Nat)) (row : List Nat)
    (neighbor : Nat) :
    ParseState.noteOrder (priorRows ++ [row]) priorRows.length neighbor =
      priorRows ++ [row ++ [neighbor]] := by
  unfold ParseState.noteOrder
  rw [getD_append_boundary, set_append_boundary]

def chainRowPrefix (n : Nat) : List (List Nat) :=
  openPrefix ++ (List.range n).map internalRow

theorem chainRowPrefix_length (n : Nat) : (chainRowPrefix n).length = n + 4 := by
  simp [chainRowPrefix, openPrefix]

theorem openRows_last (n : Nat) :
    (openRows n).getD (n + 4) [] = [if n = 0 then 2 else n + 3] := by
  change (chainRowPrefix n ++ [[if n = 0 then 2 else n + 3]]).getD (n + 4) [] = _
  rw [← chainRowPrefix_length]
  exact getD_append_boundary _ _

theorem openRows_note_last (n neighbor : Nat) :
    ParseState.noteOrder (openRows n) (n + 4) neighbor =
      chainRowPrefix n ++ [[if n = 0 then 2 else n + 3, neighbor]] := by
  change ParseState.noteOrder
    (chainRowPrefix n ++ [[if n = 0 then 2 else n + 3]]) (n + 4) neighbor = _
  rw [← chainRowPrefix_length, noteOrder_append_boundary]
  rfl

def closureOpening (n : Nat) : RingOpening where
  digit := 1
  atom := n + 4
  bond? := none
  bondIndex := n + 4
  orderIndex := 1

def openedState (n : Nat) (parity : TetrahedralInputParity) : ParseState :=
  { openState n parity with
    rings := [closureOpening n]
    bonds := (openState n parity).bonds ++ [⟨n + 4, n + 4, .unspecified⟩]
    order := chainRowPrefix n ++ [[if n = 0 then 2 else n + 3, n + 4]] }

theorem openState_ring_digit (n : Nat) (parity : TetrahedralInputParity) :
    (openState n parity).handleRingDigit 1 = .ok (openedState n parity) := by
  have count : (openState n parity).bonds.length = n + 4 := by
    simp [openState]
  simp only [ParseState.handleRingDigit, openState, ParseState.findRing?, List.find?_nil]
  rw [openRows_last, openRows_note_last]
  have count' : (([⟨0, 1, ParsedBondKind.single⟩, ⟨0, 2, .single⟩, ⟨2, 3, .single⟩] : List RawBond) ++
      (List.range (n + 1)).map chainBond).length = n + 4 := count
  rw [count']
  rfl

def restoredState (n : Nat) (parity : TetrahedralInputParity) : ParseState :=
  { openedState n parity with current? := some 0, branches := [] }

theorem openedState_popBranch (n : Nat) (parity : TetrahedralInputParity) :
    (openedState n parity).popBranch = .ok (restoredState n parity) := rfl

theorem restoredState_resolve (n : Nat) (parity : TetrahedralInputParity) :
    (restoredState n parity).resolveRingBondKind (closureOpening n) 0 = .ok .single := by
  change (match (ringRaw n parity).atomAt? (n + 4), (ringRaw n parity).atomAt? 0 with
    | some left, some right => Except.ok (defaultBondKind left right)
    | _, _ => Except.error "ring closure refers to a missing atom") = _
  rw [ringRaw_atomAt_chain n parity n (Nat.le_refl _), ringRaw_atomAt_zero]
  rfl

theorem ringRows_split (n : Nat) :
    ringRows n =
      [[1, 2, n + 4], [0], [0, 3, 4], [2]] ++
        (List.range n).map internalRow ++ [[if n = 0 then 2 else n + 3, 0]] := by
  have before : (List.range n).map (chainRow n) = (List.range n).map internalRow := by
    apply List.map_congr_left
    intro index member
    simp only [chainRow, internalRow, if_pos (List.mem_range.mp member)]
  simp only [ringRows, List.range_succ, List.map_append, List.map_singleton, before]
  simp only [chainRow, lt_self_iff_false, if_false, List.append_assoc]

theorem restoredState_closed_bonds (n : Nat) (parity : TetrahedralInputParity) :
    (restoredState n parity).bonds.set (n + 4) ⟨n + 4, 0, .single⟩ =
      (ringRaw n parity).bonds := by
  have count : (openState n parity).bonds.length = n + 4 := by
    simp [openState]
  change ((openState n parity).bonds ++ [_]).set (n + 4) _ = _
  rw [← count, set_append_boundary, count]
  rfl

theorem restoredState_closed_order (n : Nat) (parity : TetrahedralInputParity) :
    ParseState.noteOrder
      ((restoredState n parity).order.set (n + 4)
        (((restoredState n parity).order.getD (n + 4) []).set 1 0)) 0 (n + 4) =
      (ringRaw n parity).neighborOrder := by
  have lookup : (restoredState n parity).order.getD (n + 4) [] =
      [if n = 0 then 2 else n + 3, n + 4] := by
    change (chainRowPrefix n ++ [[if n = 0 then 2 else n + 3, n + 4]]).getD (n + 4) [] = _
    rw [← chainRowPrefix_length]
    exact getD_append_boundary _ _
  rw [lookup]
  change ParseState.noteOrder
    ((chainRowPrefix n ++ [[if n = 0 then 2 else n + 3, n + 4]]).set (n + 4)
      [if n = 0 then 2 else n + 3, 0]) 0 (n + 4) = _
  rw [← chainRowPrefix_length n, set_append_boundary, chainRowPrefix_length]
  rw [ringRaw_neighborOrder, ringRows_split]
  rfl

/-- Ring closure yields the independent physical ring, with the complete written table and the
original source-introduction history. Both ordinary and ring edges are checked in the join. -/
theorem restoredState_ring_digit (n : Nat) (parity : TetrahedralInputParity) :
    (restoredState n parity).handleRingDigit 1 = .ok (closedState n parity) := by
  have current : (restoredState n parity).current? = some 0 := rfl
  have found : (restoredState n parity).findRing? 1 = some (closureOpening n) := rfl
  simp only [ParseState.handleRingDigit, current, found]
  rw [restoredState_resolve]
  change Except.ok
    { (restoredState n parity).eraseRing 1 with
      bonds := (restoredState n parity).bonds.set (n + 4) ⟨n + 4, 0, .single⟩
      order := ParseState.noteOrder
        ((restoredState n parity).order.set (n + 4)
          (((restoredState n parity).order.getD (n + 4) []).set 1 0)) 0 (n + 4)
      pendingBond? := none } = _
  rw [restoredState_closed_bonds, restoredState_closed_order]
  rfl

theorem closeChain_actual (n : Nat) (parity : TetrahedralInputParity) :
    closeChain (appendChain (n + 1) (headState parity)) = .ok (closedState n parity) := by
  rw [ring_chain_state]
  unfold closeChain
  rw [openState_ring_digit]
  change (do
    let restored ← (openedState n parity).popBranch
    restored.handleRingDigit 1) = _
  rw [openedState_popBranch]
  exact restoredState_ring_digit n parity

/-- Uniform successful interpretation of every complete family member by the actual parser core.
The grammar preflight and physical finalizer are separate, explicitly identified obligations. -/
theorem parse_ring_state (n fuel : Nat) (parity : TetrahedralInputParity) :
    parseCharsFuel ((fuel + 1) + n + 13) (ringSyntax n parity).toList {} =
      .ok (closedState n parity) := by
  rw [parse_ring_core, closeChain_actual]
  rfl

end TetraStereo.UniversalProof.NativeRingParserPhysicalJoin
