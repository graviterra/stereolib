import TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport
import TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport
import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization

set_option autoImplicit false

namespace TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
















/-- The production source-aware predecessor predicate, including its documented legacy fallback.
Named separately so the slot law can be stated without unfolding the materialization step. -/
def materializationHasPreceding (molecule : RawMolecule) (center : ℕ) : Bool :=
  molecule.hydrogenHasPreceding center

/-- Atom-index base of the hydrogen block materialized at a centre by the committed ascending range
fold: the initial accumulator already contains every original atom, and every centre strictly below
this one has already appended exactly its computed hydrogen count. -/
def hydrogenExpansionBase (molecule : RawMolecule) (center : ℕ) : ℕ :=
  molecule.atomCount + ((List.range center).map molecule.hydrogenCountAt).sum

/-- The production insertion slot: after the first stored neighbor when source history records a
predecessor (or the legacy fallback infers one), otherwise first. -/
def insertionSlot (order : List ℕ) (hasPreceding : Bool) : ℕ :=
  if hasPreceding then (if order.isEmpty then 0 else 1) else 0

/-- A materialization step with no computed hydrogen is literally the identity on the written order,
so the slot law below is uniform and needs no nonempty-block side condition. -/
theorem insertHydrogenInOrder_empty_block (order : List ℕ) (hasPreceding : Bool) :
    insertHydrogenInOrder order hasPreceding [] = order := by
  cases hasPreceding <;> cases order <;> rfl

/-- On the true branch, the fresh block follows the first stored neighbor and the remaining original
neighbors keep their relative written order. Parser predecessor fidelity is not assumed or proved. -/
theorem insertHydrogenInOrder_cons_true (first : ℕ) (rest hydrogens : List ℕ) :
    insertHydrogenInOrder (first :: rest) true hydrogens = first :: (hydrogens ++ rest) := rfl

/-- On the false branch, the fresh block comes first and the complete original row follows it. -/
theorem insertHydrogenInOrder_cons_false (first : ℕ) (rest hydrogens : List ℕ) :
    insertHydrogenInOrder (first :: rest) false hydrogens = hydrogens ++ first :: rest := rfl

@[simp] theorem insertionSlot_nil_true : insertionSlot [] true = 0 := by
  rfl

@[simp] theorem insertionSlot_nil_false : insertionSlot [] false = 0 := by
  rfl

@[simp] theorem insertionSlot_cons_true (first : ℕ) (rest : List ℕ) :
    insertionSlot (first :: rest) true = 1 := by
  rfl

@[simp] theorem insertionSlot_cons_false (first : ℕ) (rest : List ℕ) :
    insertionSlot (first :: rest) false = 0 := by
  rfl

/-- The `i`-th fresh hydrogen occupies written slot `insertionSlot + i`.  This is the exact
attachment-slot statement: the block is consecutive and starts at the definite production insertion slot. -/
theorem insertHydrogenInOrder_slot_getElem?
    (order : List ℕ) (hasPreceding : Bool) (hydrogens : List ℕ) (index : ℕ)
    (bound : index < hydrogens.length) :
    (insertHydrogenInOrder order hasPreceding hydrogens)[insertionSlot order hasPreceding + index]? = hydrogens[index]? := by
  cases hasPreceding with
  | false =>
      cases order with
      | nil =>
          rw [insertionSlot_nil_false, Nat.zero_add]
          change (hydrogens ++ [])[index]? = hydrogens[index]?
          rw [List.append_nil]
      | cons first rest =>
          rw [insertHydrogenInOrder_cons_false, insertionSlot_cons_false, Nat.zero_add]
          rw [List.getElem?_append_left bound]
  | true =>
      cases order with
      | nil =>
          rw [insertionSlot_nil_true, Nat.zero_add]
          rfl
      | cons first rest =>
          rw [insertHydrogenInOrder_cons_true, insertionSlot_cons_true]
          have slotEq : 1 + index = index + 1 := by omega
          rw [slotEq, List.getElem?_cons_succ]
          rw [List.getElem?_append_left bound]

/-- A member of the fresh block has its derived consecutive attachment slot. -/
theorem insertHydrogenInOrder_slot_mem
    (order : List ℕ) (hasPreceding : Bool) (hydrogens : List ℕ) (hydrogen : ℕ)
    (member : hydrogen ∈ hydrogens) :
    ∃ index, index < hydrogens.length ∧
      (insertHydrogenInOrder order hasPreceding hydrogens)[insertionSlot order hasPreceding + index]? = some hydrogen := by
  obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp lookup
  exact ⟨index, bound,
    (insertHydrogenInOrder_slot_getElem? order hasPreceding hydrogens index bound).trans lookup⟩

/-- On the true branch, the first stored neighbor keeps slot zero. -/
theorem insertHydrogenInOrder_head_of_preceding
    (first : ℕ) (rest hydrogens : List ℕ) :
    (insertHydrogenInOrder (first :: rest) true hydrogens)[0]? = some first := by
  rw [insertHydrogenInOrder_cons_true, List.getElem?_cons_zero]

/-- On the false branch, the complete original row survives as the tail after the fresh block. -/
theorem insertHydrogenInOrder_tail_of_no_preceding
    (order hydrogens : List ℕ) :
    (insertHydrogenInOrder order false hydrogens) = hydrogens ++ order := rfl

/-- `insertAfterFirst` performs one exact insertion: the result is the untouched prefix, the first
matching bond, the extra records and the untouched suffix.  The committed library records only a
`Perm`; this pins the position, so no other bond record changes its relative order. -/
theorem insertAfterFirst_eq_some_position
    (p : RawBond → Bool) (extra bonds out : List RawBond)
    (observed : insertAfterFirst p extra bonds = some out) :
    ∃ pre bond post, bonds = pre ++ bond :: post ∧
      out = pre ++ bond :: (extra ++ post) ∧
      p bond = true ∧ ∀ earlier, earlier ∈ pre → p earlier = false := by
  induction bonds generalizing out with
  | nil => simp [insertAfterFirst] at observed
  | cons head tail inductionHypothesis =>
      simp only [insertAfterFirst] at observed
      split at observed
      · rename_i matchedHead
        cases observed
        exact ⟨[], head, tail, rfl, rfl, matchedHead, by simp⟩
      · rename_i noMatch
        cases mapped : insertAfterFirst p extra tail with
        | none => simp [mapped] at observed
        | some inner =>
            simp [mapped] at observed
            cases observed
            obtain ⟨pre, bond, post, tailEq, innerEq, matched, earlierFalse⟩ :=
              inductionHypothesis inner mapped
            refine ⟨head :: pre, bond, post, by simp [tailEq], by simp [innerEq], matched, ?_⟩
            intro earlier member
            rcases List.mem_cons.mp member with rfl | inPre
            · exact Bool.eq_false_of_not_eq_true noMatch
            · exact earlierFalse earlier inPre

/-- `insertBeforeFirst` performs one exact insertion immediately before the first matching bond. -/
theorem insertBeforeFirst_eq_some_position
    (p : RawBond → Bool) (extra bonds out : List RawBond)
    (observed : insertBeforeFirst p extra bonds = some out) :
    ∃ pre bond post, bonds = pre ++ bond :: post ∧
      out = pre ++ extra ++ bond :: post ∧
      p bond = true ∧ ∀ earlier, earlier ∈ pre → p earlier = false := by
  induction bonds generalizing out with
  | nil => simp [insertBeforeFirst] at observed
  | cons head tail inductionHypothesis =>
      simp only [insertBeforeFirst] at observed
      split at observed
      · rename_i matchedHead
        cases observed
        exact ⟨[], head, tail, rfl, rfl, matchedHead, by simp⟩
      · rename_i noMatch
        cases mapped : insertBeforeFirst p extra tail with
        | none => simp [mapped] at observed
        | some inner =>
            simp [mapped] at observed
            cases observed
            obtain ⟨pre, bond, post, tailEq, innerEq, matched, earlierFalse⟩ :=
              inductionHypothesis inner mapped
            refine ⟨head :: pre, bond, post, by simp [tailEq], by simp [innerEq], matched, ?_⟩
            intro earlier member
            rcases List.mem_cons.mp member with rfl | inPre
            · exact Bool.eq_false_of_not_eq_true noMatch
            · exact earlierFalse earlier inPre

/-- The legacy fallback splice is exactly one insertion of the fresh hydrogen bonds into the existing
bond list: every original bond record survives in its original relative order, and the fresh block
is contiguous.  This is the order-strengthening of `spliceHydrogenBonds_perm`. -/
theorem spliceHydrogenBonds_insertion
    (bonds : List RawBond) (idx : ℕ) (extra : List RawBond) :
    ∃ pre post, bonds = pre ++ post ∧ spliceHydrogenBonds bonds idx extra = pre ++ extra ++ post := by
  unfold spliceHydrogenBonds
  by_cases empty : extra.isEmpty
  · rw [if_pos empty]
    have extraNil : extra = [] := List.isEmpty_iff.mp empty
    rw [extraNil]
    exact ⟨bonds, [], by simp, by simp⟩
  · rw [if_neg empty]
    cases after : insertAfterFirst (fun bond => bond.target == idx) extra bonds with
    | some out =>
        obtain ⟨pre, bond, post, bondsEq, outEq, _matched, _earlier⟩ :=
          insertAfterFirst_eq_some_position _ _ _ _ after
        exact ⟨pre ++ [bond], post, by simp [bondsEq], by simp [outEq]⟩
    | none =>
        cases before : insertBeforeFirst (fun bond => bond.source == idx) extra bonds with
        | some out =>
            obtain ⟨pre, bond, post, bondsEq, outEq, _matched, _earlier⟩ :=
              insertBeforeFirst_eq_some_position _ _ _ _ before
            exact ⟨pre, bond :: post, by simp [bondsEq], by simp [outEq]⟩
        | none => exact ⟨bonds, [], by simp only [List.append_nil], by simp only [List.append_nil]⟩

/-- The materialization step reads an atom's stored row through `List.getD`.  When the row is known
to be the `some` branch of the indexed lookup, `List.getD` returns exactly that row. -/
theorem getD_eq_of_getElem?_eq_some {α : Type*} (values : List α) (index : ℕ) (value fallback : α)
    (observed : values[index]? = some value) : values.getD index fallback = value := by
  rw [List.getD_eq_getElem?_getD, observed]
  rfl

/-- The accumulator reached once the production range fold has processed exactly the indices strictly
below `n`.  `expansionPrefix molecule molecule.atomCount` is literally the intermediate accumulator
of `RawMolecule.withExplicitHydrogens`. -/
def expansionPrefix (molecule : RawMolecule) (n : ℕ) : HydrogenExpansionState :=
  (List.range n).foldl (withExplicitHydrogensStep molecule) (initialHydrogenExpansionState molecule)

/-- One more processed index is exactly one production step applied to the running accumulator. -/
theorem expansionPrefix_succ (molecule : RawMolecule) (n : ℕ) :
    expansionPrefix molecule (n + 1) =
      withExplicitHydrogensStep molecule (expansionPrefix molecule n) n := by
  unfold expansionPrefix
  rw [List.range_succ, List.foldl_append]
  rfl

/-- One production step appends exactly the computed hydrogen count to the atom list. -/
theorem withExplicitHydrogensStep_atomListLength
    (molecule : RawMolecule) (state : HydrogenExpansionState) (index : ℕ) :
    (withExplicitHydrogensStep molecule state index).1.length =
      state.1.length + molecule.hydrogenCountAt index := by
  exact TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.withExplicitHydrogensStep_atoms_length
    molecule state index

/-- A production step never removes an atom. -/
theorem withExplicitHydrogensStep_atomListLength_le
    (molecule : RawMolecule) (state : HydrogenExpansionState) (index : ℕ) :
    state.1.length ≤ (withExplicitHydrogensStep molecule state index).1.length := by
  rw [withExplicitHydrogensStep_atomListLength]
  exact Nat.le_add_right _ _

/-- An arbitrary schedule appends exactly the total computed hydrogen count of its indices. -/
theorem fold_withExplicitHydrogensStep_atomListLength
    (molecule : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState) :
    (indices.foldl (withExplicitHydrogensStep molecule) state).1.length =
      state.1.length + (indices.map molecule.hydrogenCountAt).sum := by
  exact TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.fold_withExplicitHydrogensStep_atoms_length
    molecule indices state

/-- The ascending production range raises the accumulator's atom list monotonically. -/
theorem expansionPrefix_length_mono (molecule : RawMolecule) (n : ℕ) :
    (expansionPrefix molecule n).1.length ≤ (expansionPrefix molecule (n + 1)).1.length := by
  rw [expansionPrefix_succ]
  exact withExplicitHydrogensStep_atomListLength_le molecule (expansionPrefix molecule n) n

/-- Monotonicity of the accumulator's atom list along the whole ascending range. -/
theorem expansionPrefix_length_le (molecule : RawMolecule) (m n : ℕ) (bound : m ≤ n) :
    (expansionPrefix molecule m).1.length ≤ (expansionPrefix molecule n).1.length := by
  induction bound with
  | refl => exact Nat.le_refl _
  | step h ih => exact le_trans ih (expansionPrefix_length_mono molecule _)

/-- Exact atom-list length of every prefix accumulator. -/
theorem expansionPrefix_atomListLength (molecule : RawMolecule) (n : ℕ) :
    (expansionPrefix molecule n).1.length =
      molecule.atomCount + ((List.range n).map molecule.hydrogenCountAt).sum := by
  unfold expansionPrefix
  rw [fold_withExplicitHydrogensStep_atomListLength]
  simp [initialHydrogenExpansionState, atomCount]

/-- Every prefix accumulator keeps one stored order row per atom. -/
theorem expansionPrefix_shapeInvariant (molecule : RawMolecule) (n : ℕ) :
    (expansionPrefix molecule n).ShapeInvariant molecule := by
  unfold expansionPrefix
  exact fold_withExplicitHydrogensStep_preserves_shapeInvariant molecule (List.range n)
    (initialHydrogenExpansionState molecule) (initialHydrogenExpansionState_shapeInvariant molecule)

/-- The named hydrogen base is exactly the accumulator's atom-list length at that centre's step. -/
theorem hydrogenExpansionBase_eq_prefix_length (molecule : RawMolecule) (center : ℕ) :
    hydrogenExpansionBase molecule center = (expansionPrefix molecule center).1.length := by
  rw [expansionPrefix_atomListLength]
  rfl

/-! ## 4. Row-level effect of one production step -/

/-- One production step rewrites exactly its target's stored written row: the fresh hydrogen block is
inserted at the production insertion slot of the target's source row. -/
theorem withExplicitHydrogensStep_neighborOrder_getElem?_self
    (molecule : RawMolecule) (state : HydrogenExpansionState) (index : ℕ) (row : List ℕ)
    (shape : state.ShapeInvariant molecule) (indexBound : index < molecule.atomCount)
    (rowObserved : state.2.2[index]? = some row) :
    (withExplicitHydrogensStep molecule state index).toRawMolecule.neighborOrder[index]? =
      some (insertHydrogenInOrder row (materializationHasPreceding molecule index)
        ((List.range (molecule.hydrogenCountAt index)).map
          (fun offset => state.1.length + offset))) := by
  have rowBound : index < state.2.2.length := by
    rw [shape.fullOrder]
    exact lt_of_lt_of_le indexBound shape.originalAtoms
  have rowGet : state.2.2.getD index [] = row :=
    getD_eq_of_getElem?_eq_some state.2.2 index row [] rowObserved
  by_cases zero : molecule.hydrogenCountAt index == 0
  · have countZero : molecule.hydrogenCountAt index = 0 := by simpa using zero
    have insertEmpty :
        insertHydrogenInOrder row (materializationHasPreceding molecule index)
          ((List.range (molecule.hydrogenCountAt index)).map
            (fun offset => state.1.length + offset)) = row := by
      rw [countZero]
      exact insertHydrogenInOrder_empty_block row _
    simp [withExplicitHydrogensStep, zero, HydrogenExpansionState.toRawMolecule, insertEmpty,
      rowObserved]
  · show ((withExplicitHydrogensStep molecule state index).2.2)[index]? =
      some (insertHydrogenInOrder row (materializationHasPreceding molecule index)
        ((List.range (molecule.hydrogenCountAt index)).map
          (fun offset => state.1.length + offset)))
    simp only [withExplicitHydrogensStep, if_neg zero]
    rw [List.getElem?_append_left (by simpa only [List.length_set] using rowBound)]
    rw [List.getElem?_set_self rowBound, rowGet]
    rfl

/-- One production step leaves every other atom's stored written row untouched. -/
theorem withExplicitHydrogensStep_neighborOrder_getElem?_of_ne
    (molecule : RawMolecule) (state : HydrogenExpansionState) (index target : ℕ)
    (distinct : index ≠ target) (targetBound : target < state.2.2.length) :
    (withExplicitHydrogensStep molecule state index).toRawMolecule.neighborOrder[target]? =
      state.2.2[target]? := by
  show ((withExplicitHydrogensStep molecule state index).2.2)[target]? = state.2.2[target]?
  by_cases zero : molecule.hydrogenCountAt index == 0
  · simp [withExplicitHydrogensStep, zero]
  · simp only [withExplicitHydrogensStep, if_neg zero]
    rw [List.getElem?_append_left (by simpa only [List.length_set] using targetBound)]
    rw [List.getElem?_set_ne distinct]

/-- An index outside a schedule leaves that atom's stored written row untouched. -/
theorem fold_withExplicitHydrogensStep_neighborOrder_of_not_mem
    (molecule : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState) (target : ℕ)
    (shape : state.ShapeInvariant molecule) (absent : target ∉ indices)
    (targetBound : target < state.2.2.length) :
    ((indices.foldl (withExplicitHydrogensStep molecule) state).2.2)[target]? =
      state.2.2[target]? := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      have indexAbsent : index ≠ target := by
        intro equal
        exact absent (by simp [equal])
      have restAbsent : target ∉ rest := by
        intro member
        exact absent (by simp [member])
      have nextShape :=
        withExplicitHydrogensStep_preserves_shapeInvariant molecule state index shape
      have nextBound : target < (withExplicitHydrogensStep molecule state index).2.2.length := by
        have oldAtomBound : target < state.1.length := by
          simpa only [shape.fullOrder] using targetBound
        rw [nextShape.fullOrder, withExplicitHydrogensStep_atomListLength]
        omega
      rw [List.foldl_cons,
        inductionHypothesis (withExplicitHydrogensStep molecule state index) nextShape
          restAbsent nextBound]
      exact withExplicitHydrogensStep_neighborOrder_getElem?_of_ne molecule state index target
        indexAbsent targetBound

/-! ## 5. The materialized written frame at a centre -/

/-- The stored written row at a centre after the ascending production range fold to `n` is its
source written row with the fresh hydrogen block spliced in at the production insertion slot.  The block holds
exactly the atom indices the centre's own step appends, based at `hydrogenExpansionBase`. -/
theorem expansionPrefix_neighborOrder_self (molecule : RawMolecule) :
    ∀ n t, t < n → t < molecule.atomCount →
      (expansionPrefix molecule n).2.2[t]? =
        some (insertHydrogenInOrder (molecule.writtenNeighbors t)
          (materializationHasPreceding molecule t)
          ((List.range (molecule.hydrogenCountAt t)).map
            (fun offset => hydrogenExpansionBase molecule t + offset))) := by
  intro n
  induction n with
  | zero => intro t bound _; omega
  | succ n inductionHypothesis =>
      intro t bound atomBound
      have prefixLength : (expansionPrefix molecule n).1.length =
          hydrogenExpansionBase molecule n := (hydrogenExpansionBase_eq_prefix_length molecule n).symm
      have prefixShape := expansionPrefix_shapeInvariant molecule n
      have prefixBound : t < (expansionPrefix molecule n).2.2.length := by
        rw [prefixShape.fullOrder]
        exact lt_of_lt_of_le atomBound prefixShape.originalAtoms
      by_cases same : t = n
      · subst t
        have rowSource : (expansionPrefix molecule n).2.2[n]? =
            some (molecule.writtenNeighbors n) := by
          unfold expansionPrefix
          rw [fold_withExplicitHydrogensStep_neighborOrder_of_not_mem molecule (List.range n)
            (initialHydrogenExpansionState molecule) n
            (initialHydrogenExpansionState_shapeInvariant molecule) (by simp)
            (by simpa only [initialHydrogenExpansionState, List.length_map, List.length_range] using atomBound)]
          exact getElem?_map_range molecule.writtenNeighbors molecule.atomCount n atomBound
        rw [expansionPrefix_succ]
        have selfStep := withExplicitHydrogensStep_neighborOrder_getElem?_self molecule
          (expansionPrefix molecule n) n (molecule.writtenNeighbors n) prefixShape atomBound rowSource
        simp only [HydrogenExpansionState.toRawMolecule] at selfStep
        simpa only [prefixLength] using selfStep
      · have earlier : t < n := by omega
        rw [expansionPrefix_succ]
        have otherStep := withExplicitHydrogensStep_neighborOrder_getElem?_of_ne molecule
          (expansionPrefix molecule n) n t (Ne.symm same) prefixBound
        simp only [HydrogenExpansionState.toRawMolecule] at otherStep
        rw [otherStep]
        exact inductionHypothesis t earlier atomBound

/-- The committed written-neighbour view of the prefix accumulator, in the same form. -/
theorem expansionPrefix_writtenNeighbors_self (molecule : RawMolecule) (n t : ℕ)
    (bound : t < n) (atomBound : t < molecule.atomCount) :
    (expansionPrefix molecule n).toRawMolecule.writtenNeighbors t =
      insertHydrogenInOrder (molecule.writtenNeighbors t) (materializationHasPreceding molecule t)
        ((List.range (molecule.hydrogenCountAt t)).map
          (fun offset => hydrogenExpansionBase molecule t + offset)) := by
  unfold writtenNeighbors
  simp only [HydrogenExpansionState.toRawMolecule]
  rw [expansionPrefix_neighborOrder_self molecule n t bound atomBound]
  rfl

/-- The exact numerical block appended by a center's actual production step. -/
def materializedHydrogenIds (molecule : RawMolecule) (center : ℕ) : List ℕ :=
  (List.range (molecule.hydrogenCountAt center)).map
    (fun offset => hydrogenExpansionBase molecule center + offset)

/-- The post-step original-center row, specified only using actual input data and demand. -/
def materializedWrittenRow (molecule : RawMolecule) (center : ℕ) : List ℕ :=
  insertHydrogenInOrder (molecule.writtenNeighbors center)
    (materializationHasPreceding molecule center) (materializedHydrogenIds molecule center)

theorem hydrogenExpansionBase_original_count_le (molecule : RawMolecule) (center : ℕ) :
    molecule.atomCount ≤ hydrogenExpansionBase molecule center :=
  Nat.le_add_right _ _

/-- Actual bond membership of every prefix, with each generated bond tied to its demand owner and
its exact running-prefix base. This is stronger than the endpoint shape alone. -/
theorem expansionPrefix_bonds_mem_iff (molecule : RawMolecule) (n : ℕ) (bond : RawBond) :
    bond ∈ (expansionPrefix molecule n).2.1 ↔
      bond ∈ molecule.bonds ∨
        ∃ parent, parent < n ∧ ∃ hydrogen,
          hydrogen ∈ materializedHydrogenIds molecule parent ∧
          bond = { source := parent, target := hydrogen, kind := ParsedBondKind.single } := by
  induction n with
  | zero => simp [expansionPrefix, initialHydrogenExpansionState]
  | succ n inductionHypothesis =>
      rw [expansionPrefix_succ]
      have step := TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport.withExplicitHydrogensStep_bonds_mem_iff
        molecule (expansionPrefix molecule n) n bond
      simp only [HydrogenExpansionState.toRawMolecule] at step
      change bond ∈ (withExplicitHydrogensStep molecule (expansionPrefix molecule n) n).2.1 ↔ _
      rw [step, inductionHypothesis]
      have fresh : bond ∈ TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport.freshHydrogenBonds
          n (expansionPrefix molecule n).1.length (molecule.hydrogenCountAt n) ↔
          ∃ hydrogen, hydrogen ∈ materializedHydrogenIds molecule n ∧
            bond = { source := n, target := hydrogen, kind := ParsedBondKind.single } := by
        rw [← hydrogenExpansionBase_eq_prefix_length]
        unfold TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport.freshHydrogenBonds
          TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport.freshHydrogenIds
        change bond ∈ (materializedHydrogenIds molecule n).map
          (fun hydrogen => { source := n, target := hydrogen, kind := ParsedBondKind.single }) ↔ _
        constructor
        · rintro member
          obtain ⟨hydrogen, inBlock, equal⟩ := List.mem_map.mp member
          exact ⟨hydrogen, inBlock, equal.symm⟩
        · rintro ⟨hydrogen, inBlock, rfl⟩
          exact List.mem_map.mpr ⟨hydrogen, inBlock, rfl⟩
      rw [fresh]
      constructor
      · rintro ((old | ⟨parent, bound, hydrogen, member, equal⟩) | ⟨hydrogen, member, equal⟩)
        · exact Or.inl old
        · exact Or.inr ⟨parent, by omega, hydrogen, member, equal⟩
        · exact Or.inr ⟨n, by omega, hydrogen, member, equal⟩
      · rintro (old | ⟨parent, bound, hydrogen, member, equal⟩)
        · exact Or.inl (Or.inl old)
        · by_cases last : parent = n
          · subst parent
            exact Or.inr ⟨hydrogen, member, equal⟩
          · exact Or.inl (Or.inr ⟨parent, by omega, hydrogen, member, equal⟩)

/-- Exact returned bond membership, retaining the demanding parent's actual block provenance
through the production canonicalizer, which changes only neighbor-order rows. -/
theorem withExplicitHydrogens_bonds_mem_iff (molecule : RawMolecule) (bond : RawBond) :
    bond ∈ molecule.withExplicitHydrogens.bonds ↔
      bond ∈ molecule.bonds ∨
        ∃ parent, parent < molecule.atomCount ∧ ∃ hydrogen,
          hydrogen ∈ materializedHydrogenIds molecule parent ∧
          bond = { source := parent, target := hydrogen, kind := ParsedBondKind.single } :=
  expansionPrefix_bonds_mem_iff molecule molecule.atomCount bond

/-- Each actually demanded offset produces a returned bond from its demanding source parent,
without an expected record, output lookup or successful expansion supplied by a caller. -/
theorem withExplicitHydrogens_createdBond_mem (molecule : RawMolecule)
    (parent offset : ℕ) (parentBound : parent < molecule.atomCount)
    (offsetBound : offset < molecule.hydrogenCountAt parent) :
    ({ source := parent, target := hydrogenExpansionBase molecule parent + offset, kind := ParsedBondKind.single } : RawBond) ∈ molecule.withExplicitHydrogens.bonds := by
  apply (withExplicitHydrogens_bonds_mem_iff molecule _).mpr
  refine Or.inr ⟨parent, parentBound, hydrogenExpansionBase molecule parent + offset, ?_, rfl⟩
  exact List.mem_map.mpr ⟨offset, List.mem_range.mpr offsetBound, rfl⟩

/-- Exact source row membership for all numerical indices; well-formedness excludes positive
bonds to out-of-range atoms. No output-order condition is assumed. -/
theorem source_writtenNeighbors_mem_iff (molecule : RawMolecule)
    (well : molecule.WellFormed) (exact : molecule.WrittenNeighborExact)
    (center : ℕ) (centerBound : center < molecule.atomCount) (ligand : ℕ) :
    ligand ∈ molecule.writtenNeighbors center ↔ 0 < molecule.bondOrder center ligand := by
  have clauses := WrittenNeighborExact.at molecule exact ⟨center, centerBound⟩
  constructor
  · intro member
    exact (clauses.2.2 ⟨ligand, clauses.2.1 ligand member⟩).mp member
  · intro positive
    have distinct : center ≠ ligand := by
      intro equal
      subst ligand
      have impossible : 0 < (0 : ℕ) := by
        simpa only [molecule.bondOrder_self center] using positive
      exact (Nat.lt_irrefl 0) impossible
    obtain ⟨bond, member, connects⟩ := (molecule.bondOrder_pos_iff_exists_bond distinct).mp positive
    have endpoints := well bond member
    have ligandBound : ligand < molecule.atomCount := by
      simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
      rcases connects with ⟨_, rfl⟩ | ⟨rfl, _⟩
      · exact endpoints.2.1
      · exact endpoints.1
    exact (clauses.2.2 ⟨ligand, ligandBound⟩).mpr positive

/-- At an original center, the final pre-canonicalization graph has exactly its original neighbors
and the block demanded by that center. Other centers' blocks cannot point back into the old range. -/
theorem completePrefix_bondOrder_positive_iff (molecule : RawMolecule)
    (center ligand : ℕ) (centerBound : center < molecule.atomCount) (distinct : center ≠ ligand) :
    0 < (expansionPrefix molecule molecule.atomCount).toRawMolecule.bondOrder center ligand ↔
      0 < molecule.bondOrder center ligand ∨ ligand ∈ materializedHydrogenIds molecule center := by
  rw [RawMolecule.bondOrder_pos_iff_exists_bond _ distinct]
  constructor
  · rintro ⟨bond, member, connects⟩
    rcases (expansionPrefix_bonds_mem_iff molecule molecule.atomCount bond).mp member with
      old | ⟨parent, _, hydrogen, inBlock, rfl⟩
    · exact Or.inl ((molecule.bondOrder_pos_iff_exists_bond distinct).mpr ⟨bond, old, connects⟩)
    · have hydrogenLower : molecule.atomCount ≤ hydrogen := by
        have bounds := freshHydrogenId_bounds (hydrogenExpansionBase molecule parent)
          (molecule.hydrogenCountAt parent) hydrogen inBlock
        exact le_trans (hydrogenExpansionBase_original_count_le molecule parent) bounds.1
      have hydrogenNeCenter : hydrogen ≠ center := by omega
      simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
      rcases connects with ⟨rfl, rfl⟩ | ⟨_, impossible⟩
      · exact Or.inr inBlock
      · exact (hydrogenNeCenter impossible).elim
  · rintro (oldPositive | inBlock)
    · obtain ⟨bond, member, connects⟩ := (molecule.bondOrder_pos_iff_exists_bond distinct).mp oldPositive
      exact ⟨bond,
        (expansionPrefix_bonds_mem_iff molecule molecule.atomCount bond).mpr (Or.inl member),
        connects⟩
    · refine ⟨{ source := center, target := ligand, kind := ParsedBondKind.single }, ?_, ?_⟩
      · exact (expansionPrefix_bonds_mem_iff molecule molecule.atomCount _).mpr
          (Or.inr ⟨center, centerBound, ligand, inBlock, rfl⟩)
      · simp [RawBond.connects]

/-- The actual complete prefix has an exact original-center row, before the canonicalizer. -/
theorem completePrefix_original_row_exact (molecule : RawMolecule)
    (well : molecule.WellFormed) (exact : molecule.WrittenNeighborExact)
    (center : ℕ) (centerBound : center < molecule.atomCount) :
    (materializedWrittenRow molecule center).Nodup ∧
      (∀ ligand, ligand ∈ materializedWrittenRow molecule center →
        ligand < (expansionPrefix molecule molecule.atomCount).toRawMolecule.atomCount) ∧
      ∀ ligand, ligand ∈ materializedWrittenRow molecule center ↔
        0 < (expansionPrefix molecule molecule.atomCount).toRawMolecule.bondOrder center ligand := by
  have original := WrittenNeighborExact.at molecule exact ⟨center, centerBound⟩
  have perm := insertHydrogenInOrder_perm (molecule.writtenNeighbors center)
    (materializationHasPreceding molecule center) (materializedHydrogenIds molecule center)
  have blockLower : ∀ hydrogen, hydrogen ∈ materializedHydrogenIds molecule center →
      molecule.atomCount ≤ hydrogen := by
    intro hydrogen member
    exact le_trans (hydrogenExpansionBase_original_count_le molecule center)
      (freshHydrogenId_bounds _ _ _ member).1
  have finalShape := expansionPrefix_shapeInvariant molecule molecule.atomCount
  have blockUpper : ∀ hydrogen, hydrogen ∈ materializedHydrogenIds molecule center →
      hydrogen < (expansionPrefix molecule molecule.atomCount).toRawMolecule.atomCount := by
    intro hydrogen member
    have upper := (freshHydrogenId_bounds _ _ _ member).2
    have nextLength : (expansionPrefix molecule (center + 1)).1.length =
        hydrogenExpansionBase molecule center + molecule.hydrogenCountAt center := by
      rw [expansionPrefix_succ, withExplicitHydrogensStep_atomListLength,
        ← hydrogenExpansionBase_eq_prefix_length]
    have mono := expansionPrefix_length_le molecule (center + 1) molecule.atomCount (by omega)
    rw [nextLength] at mono
    exact lt_of_lt_of_le upper mono
  refine ⟨?_, ?_, ?_⟩
  · change (insertHydrogenInOrder _ _ _).Nodup
    rw [perm.nodup_iff, List.nodup_append]
    refine ⟨freshHydrogenIds_nodup _ _, original.1, ?_⟩
    intro hydrogen inBlock ligand inOriginal equal
    have lower := blockLower hydrogen inBlock
    have upper := original.2.1 ligand inOriginal
    omega
  · intro ligand member
    rcases List.mem_append.mp (perm.mem_iff.mp member) with inBlock | inOriginal
    · exact blockUpper ligand inBlock
    · exact lt_of_lt_of_le (original.2.1 ligand inOriginal) finalShape.originalAtoms
  · intro ligand
    change ligand ∈ insertHydrogenInOrder _ _ _ ↔ _
    rw [perm.mem_iff, List.mem_append]
    by_cases distinct : center ≠ ligand
    · rw [completePrefix_bondOrder_positive_iff molecule center ligand centerBound distinct,
        ← source_writtenNeighbors_mem_iff molecule well exact center centerBound ligand]
      exact or_comm
    · have equal : ligand = center := (not_ne_iff.mp distinct).symm
      subst ligand
      have absentBlock : center ∉ materializedHydrogenIds molecule center := by
        intro member
        have lower := blockLower center member
        omega
      have absentOriginal : center ∉ molecule.writtenNeighbors center := by
        intro member
        have positive := (original.2.2 ⟨center, centerBound⟩).mp member
        have impossible : 0 < (0 : ℕ) := by
          simpa only [molecule.bondOrder_self center] using positive
        exact (Nat.lt_irrefl 0) impossible
      rw [RawMolecule.bondOrder_self]
      simp only [absentBlock, absentOriginal, false_or, Nat.lt_irrefl]

/-- Local exactness of a real row makes the final normalizer observationally preserve it. The
hypotheses are independent graph membership clauses, not an assumed normalization result. -/
theorem exactWrittenNeighbors_eq_of_local (molecule : RawMolecule) (center : ℕ)
    (nodup : (molecule.writtenNeighbors center).Nodup)
    (bounded : ∀ ligand, ligand ∈ molecule.writtenNeighbors center → ligand < molecule.atomCount)
    (membership : ∀ ligand, ligand ∈ molecule.writtenNeighbors center ↔
      0 < molecule.bondOrder center ligand) :
    molecule.exactWrittenNeighbors center = molecule.writtenNeighbors center := by
  unfold exactWrittenNeighbors
  have preferredFilter :
      (molecule.writtenNeighbors center).filter (fun ligand =>
        decide (ligand < molecule.atomCount ∧ 0 < molecule.bondOrder center ligand)) =
        molecule.writtenNeighbors center := by
    apply List.filter_eq_self.mpr
    intro ligand member
    exact decide_eq_true ⟨bounded ligand member, (membership ligand).mp member⟩
  rw [preferredFilter, List.dedup_eq_self.mpr nodup]
  have missingNil :
      ((List.range molecule.atomCount).filter (fun ligand =>
        decide (0 < molecule.bondOrder center ligand))).filter (fun ligand =>
          decide (ligand ∉ molecule.writtenNeighbors center)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro ligand inBonded
    have positive := of_decide_eq_true (List.mem_filter.mp inBonded).2
    have present := (membership ligand).mpr positive
    intro accepted
    exact (of_decide_eq_true accepted) present
  simp only [missingNil, List.append_nil]

/-- General actual final written-row transport, including positive demand. Both input conditions
are structural source predicates; no final row, output success or descriptor is supplied. -/
theorem withExplicitHydrogens_writtenNeighbors (molecule : RawMolecule)
    (well : molecule.WellFormed) (exact : molecule.WrittenNeighborExact)
    (center : ℕ) (centerBound : center < molecule.atomCount) :
    molecule.withExplicitHydrogens.writtenNeighbors center = materializedWrittenRow molecule center := by
  let state := expansionPrefix molecule molecule.atomCount
  have row : state.toRawMolecule.writtenNeighbors center = materializedWrittenRow molecule center :=
    expansionPrefix_writtenNeighbors_self molecule molecule.atomCount center centerBound centerBound
  have clauses := completePrefix_original_row_exact molecule well exact center centerBound
  have centerExpanded : center < state.toRawMolecule.atomCount :=
    lt_of_lt_of_le centerBound (expansionPrefix_shapeInvariant molecule molecule.atomCount).originalAtoms
  have normalized := withExactWrittenNeighbors_writtenNeighbors state.toRawMolecule
    ⟨center, centerExpanded⟩
  change state.toRawMolecule.withExactWrittenNeighbors.writtenNeighbors center = _
  rw [normalized, exactWrittenNeighbors_eq_of_local state.toRawMolecule center]
  · exact row
  · rw [row]
    exact clauses.1
  · rw [row]
    exact clauses.2.1
  · rw [row]
    exact clauses.2.2

/-- Each actually demanded hydrogen retains its consecutive final written attachment slot. -/
theorem withExplicitHydrogens_hydrogen_slot (molecule : RawMolecule)
    (well : molecule.WellFormed) (exact : molecule.WrittenNeighborExact)
    (center : ℕ) (centerBound : center < molecule.atomCount) (offset : ℕ)
    (offsetBound : offset < molecule.hydrogenCountAt center) :
    (molecule.withExplicitHydrogens.writtenNeighbors center)[insertionSlot (molecule.writtenNeighbors center)
        (materializationHasPreceding molecule center) + offset]? = some (hydrogenExpansionBase molecule center + offset) := by
  rw [withExplicitHydrogens_writtenNeighbors molecule well exact center centerBound]
  unfold materializedWrittenRow
  rw [insertHydrogenInOrder_slot_getElem?]
  · exact getElem?_map_range (fun i => hydrogenExpansionBase molecule center + i)
      (molecule.hydrogenCountAt center) offset offsetBound
  · simpa only [materializedHydrogenIds, List.length_map, List.length_range] using offsetBound

/-- The actual inline-hydrogen record also has exact source written rows. -/
theorem bracketCarbonHalide_writtenNeighborExact :
    TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide.WrittenNeighborExact := by
  unfold WrittenNeighborExact
  decide

/-- Closed positive-demand final-row witness; no descriptor or parser-construction claim. -/
theorem bracketCarbonHalide_final_writtenNeighbors :
    TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide.withExplicitHydrogens.writtenNeighbors 0 =
      [4, 1, 2, 3] := by
  rw [withExplicitHydrogens_writtenNeighbors _
    TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide_wellFormed
    bracketCarbonHalide_writtenNeighborExact 0 (by decide)]
  decide

/-- Well-formed bond endpoints alone do not validate an omitted written neighbor. -/
def omittedNeighborSource : RawMolecule :=
  { atoms := [AtomSpec.aliphatic Element.H, AtomSpec.aliphatic Element.H]
    bonds := [⟨0, 1, .single⟩]
    neighborOrder := [[], []] }

theorem omittedNeighborSource_wellFormed_not_exact :
    omittedNeighborSource.WellFormed ∧ ¬ omittedNeighborSource.WrittenNeighborExact := by
  constructor
  · rw [wellFormed_iff_all_bondEndpointsOK]
    decide
  · unfold WrittenNeighborExact
    decide

/-- The real canonicalizer repairs the omission, so an unconditional source-row identity is false. -/
theorem omittedNeighborSource_final_row_differs :
    omittedNeighborSource.withExplicitHydrogens.writtenNeighbors 0 ≠
      materializedWrittenRow omittedNeighborSource 0 := by
  decide

end TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery
