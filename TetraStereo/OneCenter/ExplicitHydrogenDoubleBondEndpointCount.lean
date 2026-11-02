import TetraStereo.OneCenter.AuthoritativeParserMaterializedEndpointRefinement

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace RawMolecule

/-!
# Exact hydrogen count at ordinary carbon double-bond endpoints

This file isolates the arithmetic and list-update facts needed to prove the remaining
`withExplicitHydrogens` degree-three postcondition.  The chemical domain says that an unbracketed,
nonaromatic carbon has one extra unit of bond order beyond its number of constitutional
neighbours—the extra unit is its single ordinary double bond—and does not exceed valence four.
-/

/-- Parser-side carbon endpoint domain for standard valence-four hydrogen filling. -/
def CarbonOrdinaryDoubleBondHydrogenFillAt
    (molecule : RawMolecule) (endpoint : ℕ) : Prop :=
  ∃ spec,
    molecule.atomAt? endpoint = some spec ∧
      spec.element = .C ∧
      spec.explicitHydrogens? = none ∧
      spec.aromatic = false ∧
      molecule.incidentBondOrderSum endpoint =
        (molecule.writtenNeighbors endpoint).length + 1 ∧
      molecule.incidentBondOrderSum endpoint ≤ 4

/-- On the carbon ordinary-double-bond domain, the exact OpenSMILES hydrogen count fills the
constitutional degree to three. -/
theorem writtenNeighbors_length_add_hydrogenCountAt_eq_three
    (molecule : RawMolecule) (endpoint : ℕ)
    (eligible : molecule.CarbonOrdinaryDoubleBondHydrogenFillAt endpoint) :
    (molecule.writtenNeighbors endpoint).length + molecule.hydrogenCountAt endpoint = 3 := by
  rcases eligible with
    ⟨spec, atomObserved, carbon, unbracketed, nonaromatic, used, usedAtMostFour⟩
  have hydrogenCount : molecule.hydrogenCountAt endpoint =
      4 - molecule.incidentBondOrderSum endpoint := by
    simp [hydrogenCountAt, atomObserved, unbracketed, defaultValences,
      carbon, nonaromatic, elementDefaultValences, usedAtMostFour]
  rw [hydrogenCount, used]
  omega

/-- Inserting the fresh hydrogen block changes only order, so its length contribution is exact. -/
theorem insertHydrogenInOrder_length
    (order : List ℕ) (hasPreceding : Bool) (hydrogens : List ℕ) :
    (insertHydrogenInOrder order hasPreceding hydrogens).length =
      hydrogens.length + order.length := by
  simpa using (insertHydrogenInOrder_perm order hasPreceding hydrogens).length_eq

/-- Length of one stored neighbour row in an expansion accumulator. -/
def HydrogenExpansionState.neighborRowLength
    (state : HydrogenExpansionState) (atom : ℕ) : ℕ :=
  (state.2.2[atom]?.getD []).length

/-- One expansion step changes the row length of exactly its target original atom, by exactly the
computed hydrogen count. -/
theorem withExplicitHydrogensStep_neighborRowLength
    (molecule : RawMolecule) (state : HydrogenExpansionState)
    (shape : state.ShapeInvariant molecule)
    (index target : ℕ) (targetBound : target < molecule.atomCount) :
    (withExplicitHydrogensStep molecule state index).neighborRowLength target =
      state.neighborRowLength target +
        (if index = target then molecule.hydrogenCountAt index else 0) := by
  have targetOrderBound : target < state.2.2.length := by
    rw [shape.fullOrder]
    exact lt_of_lt_of_le targetBound shape.originalAtoms
  by_cases zero : molecule.hydrogenCountAt index == 0
  · have countZero : molecule.hydrogenCountAt index = 0 := by
      simpa using zero
    simp [withExplicitHydrogensStep, countZero,
      HydrogenExpansionState.neighborRowLength]
  · by_cases same : index = target
    · subst index
      simp [withExplicitHydrogensStep, zero,
        HydrogenExpansionState.neighborRowLength, targetOrderBound]
      rw [List.getElem?_append_left (by simpa using targetOrderBound)]
      rw [List.getElem?_set_self targetOrderBound]
      simp [insertHydrogenInOrder_length]
      omega
    · simp [withExplicitHydrogensStep, zero,
        HydrogenExpansionState.neighborRowLength, same, targetOrderBound]
      rw [List.getElem?_append_left (by simpa using targetOrderBound)]
      rw [List.getElem?_set_ne same]
      simp [List.getElem?_eq_getElem targetOrderBound]

/-- A duplicate-free expansion schedule adds the target's hydrogen count exactly once when the
target occurs in the schedule. -/
theorem fold_withExplicitHydrogensStep_neighborRowLength
    (molecule : RawMolecule) (indices : List ℕ)
    (state : HydrogenExpansionState)
    (shape : state.ShapeInvariant molecule)
    (indicesNodup : indices.Nodup)
    (indicesBound : ∀ index ∈ indices, index < molecule.atomCount)
    (target : ℕ) (targetBound : target < molecule.atomCount) :
    (indices.foldl (withExplicitHydrogensStep molecule) state).neighborRowLength target =
      state.neighborRowLength target +
        (if target ∈ indices then molecule.hydrogenCountAt target else 0) := by
  induction indices generalizing state with
  | nil => simp
  | cons index rest inductionHypothesis =>
      have indexBound : index < molecule.atomCount := indicesBound index (by simp)
      have restBound : ∀ item ∈ rest, item < molecule.atomCount := by
        intro item present
        exact indicesBound item (by simp [present])
      have separated : index ∉ rest := (List.nodup_cons.mp indicesNodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp indicesNodup).2
      have nextShape :=
        withExplicitHydrogensStep_preserves_shapeInvariant molecule state index shape
      rw [List.foldl_cons,
        inductionHypothesis (withExplicitHydrogensStep molecule state index)
          nextShape restNodup restBound]
      rw [withExplicitHydrogensStep_neighborRowLength
        molecule state shape index target targetBound]
      by_cases same : index = target
      · subst index
        simp [separated]
      · by_cases targetInRest : target ∈ rest
        · simp [same, Ne.symm same, targetInRest]
        · simp [same, Ne.symm same, targetInRest]

/-- The complete production expansion schedule adds exactly the computed hydrogen count to every
original atom's stored neighbour row. -/
theorem completeHydrogenExpansion_neighborRowLength
    (molecule : RawMolecule) (target : ℕ) (targetBound : target < molecule.atomCount) :
    ((List.range molecule.atomCount).foldl (withExplicitHydrogensStep molecule)
        (initialHydrogenExpansionState molecule)).neighborRowLength target =
      (molecule.writtenNeighbors target).length + molecule.hydrogenCountAt target := by
  rw [fold_withExplicitHydrogensStep_neighborRowLength molecule
    (List.range molecule.atomCount) (initialHydrogenExpansionState molecule)
    (initialHydrogenExpansionState_shapeInvariant molecule) List.nodup_range
    (by intro index present; exact List.mem_range.mp present) target targetBound]
  have initialRow :
      (initialHydrogenExpansionState molecule).neighborRowLength target =
        (molecule.writtenNeighbors target).length := by
    simp [HydrogenExpansionState.neighborRowLength,
      initialHydrogenExpansionState, targetBound]
  rw [initialRow]
  simp [targetBound]

/-- The finite set of real atom indices with positive bond order to one center. -/
def bondedAtomFinset (molecule : RawMolecule) (center : ℕ) : Finset ℕ :=
  (Finset.range molecule.atomCount).filter fun neighbor =>
    decide (0 < molecule.bondOrder center neighbor)

@[simp] theorem mem_bondedAtomFinset_iff
    (molecule : RawMolecule) (center neighbor : ℕ) :
    neighbor ∈ molecule.bondedAtomFinset center ↔
      neighbor < molecule.atomCount ∧ 0 < molecule.bondOrder center neighbor := by
  simp [bondedAtomFinset]

/-- Exact-neighbour canonicalization has exactly the cardinality of the positive-bond finite set. -/
theorem exactWrittenNeighbors_length_eq_bondedAtomFinset_card
    (molecule : RawMolecule) (center : ℕ) (centerBound : center < molecule.atomCount) :
    (molecule.exactWrittenNeighbors center).length =
      (molecule.bondedAtomFinset center).card := by
  have exactNodup := molecule.exactWrittenNeighbors_nodup center
  rw [← List.toFinset_card_of_nodup exactNodup]
  congr 1
  ext neighbor
  constructor
  · intro present
    have neighborBound := molecule.exactWrittenNeighbors_bound center neighbor
      (by simpa using present)
    let centerFin : Fin molecule.atomCount := ⟨center, centerBound⟩
    let neighborFin : Fin molecule.atomCount := ⟨neighbor, neighborBound⟩
    have positive := (molecule.mem_exactWrittenNeighbors_iff centerFin neighborFin).mp
      (by simpa [centerFin, neighborFin] using present)
    exact (molecule.mem_bondedAtomFinset_iff center neighbor).mpr
      ⟨neighborBound, by simpa [centerFin, neighborFin] using positive⟩
  · intro present
    obtain ⟨neighborBound, positive⟩ :=
      (molecule.mem_bondedAtomFinset_iff center neighbor).mp present
    let centerFin : Fin molecule.atomCount := ⟨center, centerBound⟩
    let neighborFin : Fin molecule.atomCount := ⟨neighbor, neighborBound⟩
    apply List.mem_toFinset.mpr
    exact (molecule.mem_exactWrittenNeighbors_iff centerFin neighborFin).mpr
      (by simpa [centerFin, neighborFin] using positive)

/-- Any admitted exact written-neighbour row has the cardinality of the positive-bond set it
represents. -/
theorem writtenNeighbors_length_eq_bondedAtomFinset_card
    (molecule : RawMolecule) (exact : molecule.WrittenNeighborExact)
    (center : ℕ) (centerBound : center < molecule.atomCount) :
    (molecule.writtenNeighbors center).length =
      (molecule.bondedAtomFinset center).card := by
  let centerFin : Fin molecule.atomCount := ⟨center, centerBound⟩
  have exactAt := WrittenNeighborExact.at molecule exact centerFin
  rw [← List.toFinset_card_of_nodup exactAt.1]
  congr 1
  ext neighbor
  constructor
  · intro present
    have neighborBound := exactAt.2.1 neighbor (by simpa using present)
    let neighborFin : Fin molecule.atomCount := ⟨neighbor, neighborBound⟩
    exact (molecule.mem_bondedAtomFinset_iff center neighbor).mpr
      ⟨neighborBound, (by
        simpa [centerFin, neighborFin] using
          (exactAt.2.2 neighborFin).mp (by simpa using present))⟩
  · intro present
    obtain ⟨neighborBound, positive⟩ :=
      (molecule.mem_bondedAtomFinset_iff center neighbor).mp present
    let neighborFin : Fin molecule.atomCount := ⟨neighbor, neighborBound⟩
    apply List.mem_toFinset.mpr
    exact (exactAt.2.2 neighborFin).mpr
      (by simpa [centerFin, neighborFin] using positive)

/-- Fresh atom indices allocated by one expansion step. -/
def HydrogenExpansionState.freshHydrogenIds
    (state : HydrogenExpansionState) (count : ℕ) : List ℕ :=
  (List.range count).map fun offset => state.1.length + offset

/-- At an original target atom, one expansion step preserves every old positive bond and adds
exactly the fresh hydrogen block when the step is the target's own step. -/
theorem withExplicitHydrogensStep_bondOrder_pos_iff
    (molecule : RawMolecule) (state : HydrogenExpansionState)
    (shape : state.ShapeInvariant molecule)
    (index target neighbor : ℕ)
    (indexBound : index < molecule.atomCount)
    (targetBound : target < molecule.atomCount)
    (distinct : target ≠ neighbor) :
    0 < (withExplicitHydrogensStep molecule state index).toRawMolecule.bondOrder
        target neighbor ↔
      0 < state.toRawMolecule.bondOrder target neighbor ∨
        (index = target ∧
          neighbor ∈ state.freshHydrogenIds (molecule.hydrogenCountAt index)) := by
  by_cases zero : molecule.hydrogenCountAt index == 0
  · have countZero : molecule.hydrogenCountAt index = 0 := by
      simpa using zero
    simp [withExplicitHydrogensStep, countZero,
      HydrogenExpansionState.freshHydrogenIds]
  · let count := molecule.hydrogenCountAt index
    let base := state.1.length
    let hydrogenIds := state.freshHydrogenIds count
    let newBonds := hydrogenIds.map fun hydrogen =>
      { source := index, target := hydrogen, kind := ParsedBondKind.single : RawBond }
    have indexLessBase : index < base :=
      lt_of_lt_of_le indexBound shape.originalAtoms
    have targetLessBase : target < base :=
      lt_of_lt_of_le targetBound shape.originalAtoms
    have permuted :
        (spliceHydrogenBondsWithPredecessor (molecule.introductionPredecessors[index]?) state.2.1 index newBonds).Perm (state.2.1 ++ newBonds) :=
      spliceHydrogenBondsWithPredecessor_perm _ _ _ _
    rw [RawMolecule.bondOrder_pos_iff_exists_bond _ distinct,
      RawMolecule.bondOrder_pos_iff_exists_bond _ distinct]
    constructor
    · rintro ⟨bond, present, connects⟩
      have presentSpliced : bond ∈ spliceHydrogenBondsWithPredecessor (molecule.introductionPredecessors[index]?) state.2.1 index newBonds := by
        simpa [withExplicitHydrogensStep, zero, HydrogenExpansionState.toRawMolecule,
          count, base, hydrogenIds, newBonds,
          HydrogenExpansionState.freshHydrogenIds] using present
      rcases List.mem_append.mp (permuted.mem_iff.mp presentSpliced) with old | fresh
      · exact Or.inl ⟨bond, old, connects⟩
      · rcases List.mem_map.mp fresh with ⟨hydrogen, hydrogenPresent, rfl⟩
        have hydrogenBounds := freshHydrogenId_bounds base count hydrogen (by
          simpa [hydrogenIds, HydrogenExpansionState.freshHydrogenIds] using hydrogenPresent)
        unfold RawBond.connects at connects
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
        rcases connects with forward | reverse
        · exact Or.inr ⟨forward.1, by
            simpa [hydrogenIds] using forward.2.symm ▸ hydrogenPresent⟩
        · exfalso
          have hydrogenEq : hydrogen = target := reverse.2
          subst hydrogen
          exact (Nat.not_le_of_gt targetLessBase) hydrogenBounds.1
    · rintro (old | ⟨indexEq, hydrogenPresent⟩)
      · rcases old with ⟨bond, present, connects⟩
        refine ⟨bond, ?_, connects⟩
        have appended : bond ∈ state.2.1 ++ newBonds := List.mem_append_left _ present
        have spliced := permuted.mem_iff.mpr appended
        simpa [withExplicitHydrogensStep, zero, HydrogenExpansionState.toRawMolecule,
          count, base, hydrogenIds, newBonds,
          HydrogenExpansionState.freshHydrogenIds] using spliced
      · subst index
        let bond : RawBond :=
          { source := target, target := neighbor, kind := ParsedBondKind.single }
        refine ⟨bond, ?_, by simp [bond, RawBond.connects]⟩
        have fresh : bond ∈ newBonds := by
          apply List.mem_map.mpr
          exact ⟨neighbor, by
            simpa [hydrogenIds, count] using hydrogenPresent, rfl⟩
        have appended : bond ∈ state.2.1 ++ newBonds := List.mem_append_right _ fresh
        have spliced := permuted.mem_iff.mpr appended
        simpa [withExplicitHydrogensStep, zero, HydrogenExpansionState.toRawMolecule,
          count, base, hydrogenIds, newBonds,
          HydrogenExpansionState.freshHydrogenIds] using spliced

/-- A positive bond from a well-formed raw molecule cannot point outside its atom list. -/
theorem neighbor_lt_atomCount_of_bondOrder_pos
    (molecule : RawMolecule) (well : molecule.WellFormed)
    (center neighbor : ℕ) (distinct : center ≠ neighbor)
    (positive : 0 < molecule.bondOrder center neighbor) :
    neighbor < molecule.atomCount := by
  rcases (molecule.bondOrder_pos_iff_exists_bond distinct).mp positive with
    ⟨bond, present, connects⟩
  have endpoints := well bond present
  unfold RawBond.connects at connects
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
  rcases connects with forward | reverse
  · simpa [forward.2] using endpoints.2.1
  · simpa [reverse.1] using endpoints.1

/-- The finite positive-neighbour set after one expansion step is the old set plus precisely the
fresh hydrogen block at the step's own original atom. -/
theorem withExplicitHydrogensStep_bondedAtomFinset
    (molecule : RawMolecule) (state : HydrogenExpansionState)
    (shape : state.ShapeInvariant molecule)
    (well : state.toRawMolecule.WellFormed)
    (index target : ℕ)
    (indexBound : index < molecule.atomCount)
    (targetBound : target < molecule.atomCount) :
    (withExplicitHydrogensStep molecule state index).toRawMolecule.bondedAtomFinset target =
      state.toRawMolecule.bondedAtomFinset target ∪
        if index = target then
          (state.freshHydrogenIds (molecule.hydrogenCountAt index)).toFinset
        else ∅ := by
  have targetLessBase : target < state.1.length :=
    lt_of_lt_of_le targetBound shape.originalAtoms
  have targetNotFresh :
      target ∉ state.freshHydrogenIds (molecule.hydrogenCountAt index) := by
    intro present
    have bounds := freshHydrogenId_bounds state.1.length
      (molecule.hydrogenCountAt index) target (by
        simpa [HydrogenExpansionState.freshHydrogenIds] using present)
    exact (Nat.not_le_of_gt targetLessBase) bounds.1
  have nextWell := withExplicitHydrogensStep_preserves_wellFormed
    molecule state index shape indexBound well
  ext neighbor
  by_cases same : target = neighbor
  · subst neighbor
    by_cases indexEq : index = target
    · have targetNotFreshAtTarget :
          target ∉ state.freshHydrogenIds (molecule.hydrogenCountAt target) := by
        simpa [indexEq] using targetNotFresh
      simp [mem_bondedAtomFinset_iff, RawMolecule.bondOrder_self,
        indexEq, targetNotFreshAtTarget]
    · simp [mem_bondedAtomFinset_iff, RawMolecule.bondOrder_self, indexEq]
  · have oldBound_of_positive :
        ∀ positive : 0 < state.toRawMolecule.bondOrder target neighbor,
          neighbor < state.toRawMolecule.atomCount := by
      intro positive
      exact neighbor_lt_atomCount_of_bondOrder_pos state.toRawMolecule well
        target neighbor same positive
    have nextBound_of_positive :
        ∀ positive : 0 < (withExplicitHydrogensStep molecule state index).toRawMolecule.bondOrder
            target neighbor,
          neighbor < (withExplicitHydrogensStep molecule state index).toRawMolecule.atomCount := by
      intro positive
      exact neighbor_lt_atomCount_of_bondOrder_pos
        (withExplicitHydrogensStep molecule state index).toRawMolecule nextWell
        target neighbor same positive
    have stepCharacterization := withExplicitHydrogensStep_bondOrder_pos_iff
      molecule state shape index target neighbor indexBound targetBound same
    have nextBound_of_alternative :
        ∀ alternative :
            0 < state.toRawMolecule.bondOrder target neighbor ∨
              (index = target ∧
                neighbor ∈ state.freshHydrogenIds (molecule.hydrogenCountAt index)),
          neighbor < (withExplicitHydrogensStep molecule state index).toRawMolecule.atomCount := by
      intro alternative
      exact nextBound_of_positive (stepCharacterization.mpr alternative)
    rw [mem_bondedAtomFinset_iff, Finset.mem_union, mem_bondedAtomFinset_iff]
    rw [stepCharacterization]
    by_cases indexEq : index = target
    · subst index
      simp only [if_pos, List.mem_toFinset, true_and]
      constructor
      · rintro ⟨_neighborBound, old | fresh⟩
        · exact Or.inl ⟨oldBound_of_positive old, old⟩
        · exact Or.inr fresh
      · rintro (⟨_neighborBound, old⟩ | fresh)
        · exact ⟨nextBound_of_alternative (Or.inl old), Or.inl old⟩
        · exact ⟨nextBound_of_alternative (Or.inr ⟨rfl, fresh⟩), Or.inr fresh⟩
    · simp only [if_neg indexEq, Finset.notMem_empty, or_false]
      constructor
      · rintro ⟨_neighborBound, old | fresh⟩
        · exact ⟨oldBound_of_positive old, old⟩
        · exact (indexEq fresh.1).elim
      · rintro ⟨_neighborBound, old⟩
        exact ⟨nextBound_of_alternative (Or.inl old), Or.inl old⟩

/-- Consequently, one expansion step increases the positive-neighbour cardinality of exactly its
own target by exactly the computed hydrogen count. -/
theorem withExplicitHydrogensStep_bondedAtomFinset_card
    (molecule : RawMolecule) (state : HydrogenExpansionState)
    (shape : state.ShapeInvariant molecule)
    (well : state.toRawMolecule.WellFormed)
    (index target : ℕ)
    (indexBound : index < molecule.atomCount)
    (targetBound : target < molecule.atomCount) :
    ((withExplicitHydrogensStep molecule state index).toRawMolecule.bondedAtomFinset target).card =
      (state.toRawMolecule.bondedAtomFinset target).card +
        if index = target then molecule.hydrogenCountAt index else 0 := by
  rw [withExplicitHydrogensStep_bondedAtomFinset molecule state shape well
    index target indexBound targetBound]
  by_cases indexEq : index = target
  · have separated : Disjoint (state.toRawMolecule.bondedAtomFinset target)
        (state.freshHydrogenIds (molecule.hydrogenCountAt index)).toFinset := by
      rw [Finset.disjoint_left]
      intro neighbor oldMember freshMember
      have oldBound :=
        (state.toRawMolecule.mem_bondedAtomFinset_iff target neighbor).mp oldMember |>.1
      have freshBounds := freshHydrogenId_bounds state.1.length
        (molecule.hydrogenCountAt index) neighbor (by
          simpa [HydrogenExpansionState.freshHydrogenIds] using
            (List.mem_toFinset.mp freshMember))
      simp [HydrogenExpansionState.toRawMolecule, atomCount] at oldBound
      omega
    rw [if_pos indexEq, if_pos indexEq, Finset.card_union_of_disjoint separated]
    rw [List.toFinset_card_of_nodup]
    · simp [HydrogenExpansionState.freshHydrogenIds]
    · simpa [HydrogenExpansionState.freshHydrogenIds] using
        freshHydrogenIds_nodup state.1.length (molecule.hydrogenCountAt index)
  · simp [indexEq]

/-- Along a duplicate-free bounded schedule, neighbour-set cardinality receives the target's
hydrogen contribution exactly once if and only if that target occurs in the schedule. -/
theorem fold_withExplicitHydrogensStep_bondedAtomFinset_card
    (molecule : RawMolecule) (indices : List ℕ)
    (state : HydrogenExpansionState)
    (shape : state.ShapeInvariant molecule)
    (well : state.toRawMolecule.WellFormed)
    (indicesNodup : indices.Nodup)
    (indicesBound : ∀ index ∈ indices, index < molecule.atomCount)
    (target : ℕ) (targetBound : target < molecule.atomCount) :
    (((indices.foldl (withExplicitHydrogensStep molecule) state).toRawMolecule.bondedAtomFinset
        target).card) =
      (state.toRawMolecule.bondedAtomFinset target).card +
        if target ∈ indices then molecule.hydrogenCountAt target else 0 := by
  induction indices generalizing state with
  | nil => simp
  | cons index rest inductionHypothesis =>
      have indexBound : index < molecule.atomCount := indicesBound index (by simp)
      have restBound : ∀ item ∈ rest, item < molecule.atomCount := by
        intro item present
        exact indicesBound item (by simp [present])
      have separated : index ∉ rest := (List.nodup_cons.mp indicesNodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp indicesNodup).2
      have nextShape :=
        withExplicitHydrogensStep_preserves_shapeInvariant molecule state index shape
      have nextWell := withExplicitHydrogensStep_preserves_wellFormed
        molecule state index shape indexBound well
      rw [List.foldl_cons,
        inductionHypothesis (withExplicitHydrogensStep molecule state index)
          nextShape nextWell restNodup restBound]
      rw [withExplicitHydrogensStep_bondedAtomFinset_card
        molecule state shape well index target indexBound targetBound]
      by_cases same : index = target
      · subst index
        simp [separated]
      · by_cases targetInRest : target ∈ rest
        · simp [same, Ne.symm same, targetInRest]
        · simp [same, Ne.symm same, targetInRest]

/-- The production range schedule raises every original atom's positive-neighbour cardinality by
exactly its computed implicit-hydrogen count. -/
theorem completeHydrogenExpansion_bondedAtomFinset_card
    (molecule : RawMolecule) (well : molecule.WellFormed)
    (target : ℕ) (targetBound : target < molecule.atomCount) :
    ((((List.range molecule.atomCount).foldl (withExplicitHydrogensStep molecule)
        (initialHydrogenExpansionState molecule)).toRawMolecule.bondedAtomFinset target).card) =
      (molecule.bondedAtomFinset target).card + molecule.hydrogenCountAt target := by
  have initialWell :
      (initialHydrogenExpansionState molecule).toRawMolecule.WellFormed := by
    intro bond member
    simpa [BondEndpointsOK] using well bond member
  rw [fold_withExplicitHydrogensStep_bondedAtomFinset_card molecule
    (List.range molecule.atomCount) (initialHydrogenExpansionState molecule)
    (initialHydrogenExpansionState_shapeInvariant molecule) initialWell List.nodup_range
    (by intro index present; exact List.mem_range.mp present) target targetBound]
  have initialSet :
      (initialHydrogenExpansionState molecule).toRawMolecule.bondedAtomFinset target =
        molecule.bondedAtomFinset target := by
    ext neighbor
    simp [bondedAtomFinset]
  rw [initialSet]
  simp [targetBound]

/-- For an exact admitted source molecule, standard valence-four carbon endpoint filling produces
literal degree three in the final canonicalized materialized molecule. -/
theorem withExplicitHydrogens_writtenNeighbors_length_eq_three_of_carbonOrdinaryDoubleBond
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    (endpoint : ℕ) (endpointBound : endpoint < molecule.atomCount)
    (eligible : molecule.CarbonOrdinaryDoubleBondHydrogenFillAt endpoint) :
    (molecule.withExplicitHydrogens.writtenNeighbors endpoint).length = 3 := by
  let result : HydrogenExpansionState :=
    (List.range molecule.atomCount).foldl (withExplicitHydrogensStep molecule)
      (initialHydrogenExpansionState molecule)
  have resultShape : result.ShapeInvariant molecule := by
    exact fold_withExplicitHydrogensStep_preserves_shapeInvariant molecule
      (List.range molecule.atomCount) (initialHydrogenExpansionState molecule)
      (initialHydrogenExpansionState_shapeInvariant molecule)
  have endpointResultBound : endpoint < result.toRawMolecule.atomCount := by
    change endpoint < result.1.length
    exact lt_of_lt_of_le endpointBound resultShape.originalAtoms
  let endpointFin : Fin result.toRawMolecule.withExactWrittenNeighbors.atomCount :=
    ⟨endpoint, by simpa using endpointResultBound⟩
  calc
    (molecule.withExplicitHydrogens.writtenNeighbors endpoint).length =
        (result.toRawMolecule.exactWrittenNeighbors endpoint).length := by
      -- Written rows are independent of the preserved parser-provenance prefix.
      change (result.toRawMolecule.withExactWrittenNeighbors.writtenNeighbors endpoint).length = _
      exact congrArg List.length
        (withExactWrittenNeighbors_writtenNeighbors result.toRawMolecule endpointFin)
    _ = (result.toRawMolecule.bondedAtomFinset endpoint).card :=
      exactWrittenNeighbors_length_eq_bondedAtomFinset_card result.toRawMolecule
        endpoint endpointResultBound
    _ = (molecule.bondedAtomFinset endpoint).card + molecule.hydrogenCountAt endpoint := by
      exact completeHydrogenExpansion_bondedAtomFinset_card molecule admitted.1.1
        endpoint endpointBound
    _ = (molecule.writtenNeighbors endpoint).length + molecule.hydrogenCountAt endpoint := by
      rw [writtenNeighbors_length_eq_bondedAtomFinset_card molecule admitted.2
        endpoint endpointBound]
    _ = 3 := writtenNeighbors_length_add_hydrogenCountAt_eq_three
      molecule endpoint eligible

/-- A step can add only single bonds, so every double-bond record after the step was already in
the incoming accumulator. -/
theorem withExplicitHydrogensStep_doubleBond_mem_previous
    (molecule : RawMolecule) (state : HydrogenExpansionState) (index : ℕ)
    (bond : RawBond)
    (present : bond ∈ (withExplicitHydrogensStep molecule state index).2.1)
    (double : bond.kind = .double) :
    bond ∈ state.2.1 := by
  by_cases zero : molecule.hydrogenCountAt index == 0
  · simpa [withExplicitHydrogensStep, zero] using present
  · let count := molecule.hydrogenCountAt index
    let base := state.1.length
    let hydrogenIds := (List.range count).map fun offset => base + offset
    let newBonds := hydrogenIds.map fun hydrogen =>
      { source := index, target := hydrogen, kind := ParsedBondKind.single : RawBond }
    have permuted :
        (spliceHydrogenBondsWithPredecessor (molecule.introductionPredecessors[index]?) state.2.1 index newBonds).Perm (state.2.1 ++ newBonds) :=
      spliceHydrogenBondsWithPredecessor_perm _ _ _ _
    have spliced : bond ∈ spliceHydrogenBondsWithPredecessor (molecule.introductionPredecessors[index]?) state.2.1 index newBonds := by
      simpa [withExplicitHydrogensStep, zero, count, base, hydrogenIds, newBonds] using present
    rcases List.mem_append.mp (permuted.mem_iff.mp spliced) with old | fresh
    · exact old
    · rcases List.mem_map.mp fresh with ⟨hydrogen, _hydrogenPresent, equality⟩
      subst bond
      simp at double

/-- No range fold of expansion steps can invent a double-bond record. -/
theorem fold_withExplicitHydrogensStep_doubleBond_mem_initial
    (molecule : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (bond : RawBond)
    (present : bond ∈ (indices.foldl (withExplicitHydrogensStep molecule) state).2.1)
    (double : bond.kind = .double) :
    bond ∈ state.2.1 := by
  induction indices generalizing state with
  | nil => exact present
  | cons index rest inductionHypothesis =>
      have inNext := inductionHypothesis
        (withExplicitHydrogensStep molecule state index) present
      exact withExplicitHydrogensStep_doubleBond_mem_previous
        molecule state index bond inNext double

/-- Every double-bond record in the production materialized molecule is literally an original
raw bond record. -/
theorem withExplicitHydrogens_doubleBond_mem_original
    (molecule : RawMolecule) (bond : RawBond)
    (present : bond ∈ molecule.withExplicitHydrogens.bonds)
    (double : bond.kind = .double) :
    bond ∈ molecule.bonds := by
  apply fold_withExplicitHydrogensStep_doubleBond_mem_initial molecule
    (List.range molecule.atomCount) (initialHydrogenExpansionState molecule) bond
  · simpa [withExplicitHydrogens, HydrogenExpansionState.toRawMolecule] using present
  · exact double

/-- A positive result of the first-record localized-order lookup is witnessed by that exact
key/order record. -/
theorem localizedBondOrderAtKey_eq_positive_exists
    (records : List ((ℕ × ℕ) × ℕ)) (key : ℕ × ℕ) (order : ℕ)
    (positive : 0 < order)
    (observed : SemanticMolecule.localizedBondOrderAtKey records key = order) :
    (key, order) ∈ records := by
  induction records with
  | nil =>
      simp [SemanticMolecule.localizedBondOrderAtKey] at observed
      omega
  | cons head tail inductionHypothesis =>
      by_cases sameKey : head.1 = key
      · have sameOrder : head.2 = order := by
          simpa [SemanticMolecule.localizedBondOrderAtKey, sameKey] using observed
        rcases head with ⟨headKey, headOrder⟩
        simp only at sameKey sameOrder
        subst headKey
        subst headOrder
        simp
      · have tailObserved :
          SemanticMolecule.localizedBondOrderAtKey tail key = order := by
          simpa [SemanticMolecule.localizedBondOrderAtKey, sameKey] using observed
        exact List.mem_cons_of_mem _ (inductionHypothesis tailObserved)

/-- A semantic localized record of order two produced by the parser bridge is exactly a raw
double-bond record with the same unordered key. -/
theorem toSemanticInteraction_localizedRecord_two_iff
    (bond : RawBond) (key : ℕ × ℕ) :
    bond.toSemanticInteraction.localizedCovalentRecord? = some (key, 2) ↔
      bond.kind = .double ∧ semanticEdgeKey bond.source bond.target = key := by
  rcases bond with ⟨source, target, kind⟩
  cases kind <;>
    simp [RawBond.toSemanticInteraction,
      SemanticInteraction.localizedCovalentRecord?]

/-- Every semantic canonical ordinary double bond coming from a converted raw molecule is backed
by an actual raw double-bond record on the same two atom indices. -/
theorem rawDoubleBond_of_aromaticCanonicalOrdinaryDoubleBond
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    {left right : source.AromaticCanonicalAtom}
    (ordinary : source.AromaticCanonicalOrdinaryDoubleBond left right) :
    ∃ bond ∈ molecule.bonds,
      bond.kind = .double ∧ bond.connects left.val right.val = true := by
  have distinct : left.val ≠ right.val := by
    intro equal
    exact ordinary.1.1 (Fin.ext equal)
  have notAromatic := ordinary.not_aromaticPair
  have localizedOrder : source.molecule.localizedBondOrder left.val right.val = 2 := by
    simpa [SemanticMolecule.aromaticCanonicalBondOrder, notAromatic] using ordinary.2
  have lookupOrder : SemanticMolecule.localizedBondOrderAtKey
      source.molecule.localizedCovalentRecords (semanticEdgeKey left.val right.val) = 2 := by
    simpa [SemanticMolecule.localizedBondOrder, distinct] using localizedOrder
  have recordPresent :
      (semanticEdgeKey left.val right.val, 2) ∈ source.molecule.localizedCovalentRecords :=
    localizedBondOrderAtKey_eq_positive_exists source.molecule.localizedCovalentRecords
      (semanticEdgeKey left.val right.val) 2 (by omega) lookupOrder
  rw [SemanticMolecule.localizedCovalentRecords, List.mem_filterMap] at recordPresent
  rcases recordPresent with ⟨interaction, interactionPresent, recordObserved⟩
  have interactionImage := molecule.toSemanticMolecule?_interactions
    source.molecule converted
  rw [interactionImage, List.mem_map] at interactionPresent
  rcases interactionPresent with ⟨bond, bondPresent, rfl⟩
  have classified :=
    (toSemanticInteraction_localizedRecord_two_iff bond
      (semanticEdgeKey left.val right.val)).mp recordObserved
  refine ⟨bond, bondPresent, classified.1, ?_⟩
  exact (bond.semanticEdgeKey_eq_iff_connects left.val right.val distinct).mp classified.2

/-- Hydrogen materialization cannot create an ordinary-double-bond endpoint: both endpoints of
every converted canonical ordinary double bond lie in the original raw atom list. -/
theorem aromaticCanonicalOrdinaryDoubleBond_endpoints_lt_originalAtomCount
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.withExplicitHydrogens.toSemanticMolecule? = some source.molecule)
    {left right : source.AromaticCanonicalAtom}
    (ordinary : source.AromaticCanonicalOrdinaryDoubleBond left right) :
    left.val < molecule.atomCount ∧ right.val < molecule.atomCount := by
  rcases rawDoubleBond_of_aromaticCanonicalOrdinaryDoubleBond
      molecule.withExplicitHydrogens source converted ordinary with
    ⟨bond, materializedPresent, double, connects⟩
  have originalPresent := molecule.withExplicitHydrogens_doubleBond_mem_original
    bond materializedPresent double
  have endpoints := admitted.1.1 bond originalPresent
  unfold RawBond.connects at connects
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
  rcases connects with forward | reverse
  · exact ⟨by simpa [forward.1] using endpoints.1,
      by simpa [forward.2] using endpoints.2.1⟩
  · exact ⟨by simpa [reverse.2] using endpoints.2.1,
      by simpa [reverse.1] using endpoints.1⟩

/-- Hydrogen insertion cannot introduce an unresolved bond kind. -/
theorem withExplicitHydrogensStep_preserves_noUnspecified
    (molecule : RawMolecule) (state : HydrogenExpansionState) (index : ℕ)
    (resolved : ∀ bond, bond ∈ state.2.1 → bond.kind ≠ .unspecified) :
    ∀ bond, bond ∈ (withExplicitHydrogensStep molecule state index).2.1 →
      bond.kind ≠ .unspecified := by
  by_cases zero : molecule.hydrogenCountAt index == 0
  · simpa [withExplicitHydrogensStep, zero] using resolved
  · let count := molecule.hydrogenCountAt index
    let base := state.1.length
    let hydrogenIds := (List.range count).map fun offset => base + offset
    let newBonds := hydrogenIds.map fun hydrogen =>
      { source := index, target := hydrogen, kind := ParsedBondKind.single : RawBond }
    have permuted :
        (spliceHydrogenBondsWithPredecessor (molecule.introductionPredecessors[index]?) state.2.1 index newBonds).Perm (state.2.1 ++ newBonds) :=
      spliceHydrogenBondsWithPredecessor_perm _ _ _ _
    intro bond present
    have spliced : bond ∈ spliceHydrogenBondsWithPredecessor (molecule.introductionPredecessors[index]?) state.2.1 index newBonds := by
      simpa [withExplicitHydrogensStep, zero, count, base, hydrogenIds, newBonds] using present
    rcases List.mem_append.mp (permuted.mem_iff.mp spliced) with old | fresh
    · exact resolved bond old
    · rcases List.mem_map.mp fresh with ⟨hydrogen, _hydrogenPresent, rfl⟩
      simp

/-- The complete expansion fold preserves resolution of every bond kind. -/
theorem fold_withExplicitHydrogensStep_preserves_noUnspecified
    (molecule : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (resolved : ∀ bond, bond ∈ state.2.1 → bond.kind ≠ .unspecified) :
    ∀ bond, bond ∈ (indices.foldl (withExplicitHydrogensStep molecule) state).2.1 →
      bond.kind ≠ .unspecified := by
  induction indices generalizing state with
  | nil => exact resolved
  | cons index rest inductionHypothesis =>
      exact inductionHypothesis (withExplicitHydrogensStep molecule state index)
        (withExplicitHydrogensStep_preserves_noUnspecified molecule state index resolved)

/-- Production hydrogen materialization preserves the resolved-bond-kind contract. -/
theorem withExplicitHydrogens_preserves_noUnspecified
    (molecule : RawMolecule)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified) :
    ∀ bond, bond ∈ molecule.withExplicitHydrogens.bonds → bond.kind ≠ .unspecified := by
  intro bond present
  exact fold_withExplicitHydrogensStep_preserves_noUnspecified molecule
    (List.range molecule.atomCount) (initialHydrogenExpansionState molecule)
    (by simpa [initialHydrogenExpansionState] using resolved) bond (by
      simpa [withExplicitHydrogens, HydrogenExpansionState.toRawMolecule] using present)

/-- Concrete source-wide domain saying that every canonical individual-double-bond endpoint in
the materialized semantic source came from an original standard carbon endpoint eligible for the
valence-four hydrogen fill theorem. -/
def CarbonFilledCanonicalIndividualDoubleBondEndpoints
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (_converted : molecule.withExplicitHydrogens.toSemanticMolecule? = some source.molecule) : Prop :=
  ∀ endpoint partner,
    source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner →
      molecule.CarbonOrdinaryDoubleBondHydrogenFillAt endpoint.val

/-- Parser-local form of the chemical premise: both endpoints of every original raw double-bond
record lie in the standard carbon hydrogen-fill domain. -/
def OriginalDoubleBondEndpointsCarbonFilled (molecule : RawMolecule) : Prop :=
  ∀ bond, bond ∈ molecule.bonds → bond.kind = .double →
    molecule.CarbonOrdinaryDoubleBondHydrogenFillAt bond.source ∧
      molecule.CarbonOrdinaryDoubleBondHydrogenFillAt bond.target

/-- Exact parser-to-source refinement of the carbon-fill premise. No source endpoint indices or
post-materialization bounds need be supplied: ordinary order two traces to an original raw double
record, and that record's local endpoint certificate transports along undirected incidence. -/
theorem carbonFilledCanonicalIndividualDoubleBondEndpoints_of_originalDoubleBonds
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.withExplicitHydrogens.toSemanticMolecule? = some source.molecule)
    (eligible : molecule.OriginalDoubleBondEndpointsCarbonFilled) :
    molecule.CarbonFilledCanonicalIndividualDoubleBondEndpoints source converted := by
  intro endpoint partner directed
  have ordinary := source.aromaticCanonicalOrdinaryDoubleBond_of_directedEndpoint directed
  rcases rawDoubleBond_of_aromaticCanonicalOrdinaryDoubleBond
      molecule.withExplicitHydrogens source converted ordinary with
    ⟨bond, materializedPresent, double, connects⟩
  have originalPresent := molecule.withExplicitHydrogens_doubleBond_mem_original
    bond materializedPresent double
  have endpointFill := eligible bond originalPresent double
  unfold RawBond.connects at connects
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
  rcases connects with forward | reverse
  · simpa [forward.1] using endpointFill.1
  · simpa [reverse.2] using endpointFill.2

/-- The materializer itself discharges the parser degree-three postcondition throughout that
source-wide carbon ordinary-double-bond domain. -/
theorem withExplicitHydrogens_materializedCanonicalIndividualDoubleBondEndpoints
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.withExplicitHydrogens.toSemanticMolecule? = some source.molecule)
    (eligible : molecule.CarbonFilledCanonicalIndividualDoubleBondEndpoints source converted) :
    molecule.withExplicitHydrogens.MaterializedCanonicalIndividualDoubleBondEndpoints
      source converted := by
  intro endpoint partner directed
  have ordinary := source.aromaticCanonicalOrdinaryDoubleBond_of_directedEndpoint directed
  have endpointBound :=
    molecule.aromaticCanonicalOrdinaryDoubleBond_endpoints_lt_originalAtomCount
      admitted source converted ordinary |>.1
  simpa [originalAtomIndex] using
    molecule.withExplicitHydrogens_writtenNeighbors_length_eq_three_of_carbonOrdinaryDoubleBond
      admitted endpoint.val endpointBound (eligible endpoint partner directed)

/-- End-to-end finite virtual-endpoint certificate constructed from a checked parser molecule,
its production explicit-hydrogen materialization, and the carbon fill domain—without hand-written
endpoint-completion records. -/
noncomputable def certifiedVirtualEndpointsOfCarbonFilledMaterializedParser
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.withExplicitHydrogens.toSemanticMolecule? = some source.molecule)
    (sourceWellFormed : source.StructurallyWellFormed)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (eligible : molecule.OriginalDoubleBondEndpointsCarbonFilled) :
    CertifiedAuthoritativeChemicalInputWithVirtualEndpoints :=
  molecule.withExplicitHydrogens.certifiedVirtualEndpointsOfMaterializedParser source converted
    sourceWellFormed molecule.withExplicitHydrogens_writtenNeighborExact
    (molecule.withExplicitHydrogens_preserves_noUnspecified resolved)
    (molecule.withExplicitHydrogens_materializedCanonicalIndividualDoubleBondEndpoints
      admitted source converted
      (molecule.carbonFilledCanonicalIndividualDoubleBondEndpoints_of_originalDoubleBonds
        source converted eligible))

end RawMolecule
end TetraStereo.OneCenter
