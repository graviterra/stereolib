import TetraStereo.OneCenter.IR9TrigonalPrismSourceIndexCompleteness
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Permutation

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.BipyramidalSourceIndexCompleteness

open TrigonalPrismSourceIndexCompleteness
open FiniteSymmetry

abbrev PriorityNumber := BlueBookP93.PriorityNumber
abbrev PriorityDigit := CanonicalPriorityDigit

private local instance priorityDigitWordDecidableLT : DecidableLT (List PriorityDigit) :=
  LinearOrder.toDecidableLT

/-- The source candidates used to canonicalize an equatorial polygon: every cyclic frame in
both traversal directions. -/
def cycleCandidates (priorities : List PriorityNumber) : List (List PriorityNumber) :=
  BlueBookP93.cyclicRotations priorities ++
    BlueBookP93.cyclicRotations priorities.reverse

/-- Two cyclic words describe the same unoriented polygon exactly when one is a rotation of the
other in either traversal direction.  This is the dihedral equivalence appropriate to an
equatorial polygon of a bipyramid. -/
def DihedrallyEquivalent (left right : List PriorityNumber) : Prop :=
  left ~r right ∨ left.reverse ~r right

theorem cyclicRotations_eq_map_rotate (priorities : List PriorityNumber) :
    BlueBookP93.cyclicRotations priorities =
      (List.range priorities.length).map priorities.rotate := by
  unfold BlueBookP93.cyclicRotations
  apply List.map_congr_left
  intro offset offsetMember
  rw [List.mem_range] at offsetMember
  exact (List.rotate_eq_drop_append_take offsetMember.le).symm

theorem mem_cyclicRotations_iff_isRotated
    {priorities candidate : List PriorityNumber} (nonempty : priorities ≠ []) :
    candidate ∈ BlueBookP93.cyclicRotations priorities ↔ priorities ~r candidate := by
  rw [cyclicRotations_eq_map_rotate]
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨offset, _, same⟩
    exact ⟨offset, same⟩
  · rintro ⟨offset, rfl⟩
    have lengthPositive : 0 < priorities.length := List.length_pos_iff.mpr nonempty
    refine List.mem_map.mpr ⟨offset % priorities.length, ?_, ?_⟩
    · exact List.mem_range.mpr (Nat.mod_lt _ lengthPositive)
    · exact List.rotate_mod priorities offset

theorem dihedrallyEquivalent_refl (priorities : List PriorityNumber) :
    DihedrallyEquivalent priorities priorities :=
  Or.inl (List.IsRotated.refl priorities)

theorem dihedrallyEquivalent_symm {left right : List PriorityNumber}
    (equivalent : DihedrallyEquivalent left right) :
    DihedrallyEquivalent right left := by
  rcases equivalent with rotated | reflected
  · exact Or.inl rotated.symm
  · exact Or.inr (by simpa using reflected.reverse.symm)

theorem dihedrallyEquivalent_trans {left middle right : List PriorityNumber}
    (first : DihedrallyEquivalent left middle)
    (second : DihedrallyEquivalent middle right) :
    DihedrallyEquivalent left right := by
  rcases first with first | first <;> rcases second with second | second
  · exact Or.inl (first.trans second)
  · exact Or.inr (first.reverse.trans second)
  · exact Or.inr (first.trans second)
  · exact Or.inl (by simpa using first.reverse.trans second)

theorem dihedrallyEquivalent_equivalence : Equivalence DihedrallyEquivalent :=
  ⟨dihedrallyEquivalent_refl, dihedrallyEquivalent_symm,
    dihedrallyEquivalent_trans⟩

theorem dihedrallyEquivalent_perm {left right : List PriorityNumber}
    (equivalent : DihedrallyEquivalent left right) : left.Perm right := by
  rcases equivalent with rotated | reflected
  · exact rotated.perm
  · exact left.reverse_perm.symm.trans reflected.perm

theorem mem_cycleCandidates_iff
    {priorities candidate : List PriorityNumber} (nonempty : priorities ≠ []) :
    candidate ∈ cycleCandidates priorities ↔
      DihedrallyEquivalent priorities candidate := by
  simp only [cycleCandidates, List.mem_append]
  have reverseNonempty : priorities.reverse ≠ [] := by simpa using nonempty
  rw [mem_cyclicRotations_iff_isRotated nonempty,
    mem_cyclicRotations_iff_isRotated reverseNonempty]
  rfl

theorem cycleCandidates_nonempty {priorities : List PriorityNumber}
    (nonempty : priorities ≠ []) : cycleCandidates priorities ≠ [] := by
  have lengthPositive : 0 < priorities.length := List.length_pos_iff.mpr nonempty
  have zeroMember : 0 ∈ List.range priorities.length := List.mem_range.mpr lengthPositive
  have member : priorities ∈ BlueBookP93.cyclicRotations priorities := by
    rw [cyclicRotations_eq_map_rotate]
    exact List.mem_map.mpr ⟨0, zeroMember, by simp⟩
  intro empty
  have candidateMember : priorities ∈ cycleCandidates priorities := by
    exact List.mem_append_left _ member
  rw [empty] at candidateMember
  simp at candidateMember

theorem length_of_mem_cycleCandidates
    {priorities candidate : List PriorityNumber}
    (member : candidate ∈ cycleCandidates priorities) :
    candidate.length = priorities.length := by
  simp only [cycleCandidates, List.mem_append] at member
  rcases member with member | member
  · rw [cyclicRotations_eq_map_rotate] at member
    rcases List.mem_map.mp member with ⟨offset, _, rfl⟩
    exact List.length_rotate priorities offset
  · rw [cyclicRotations_eq_map_rotate] at member
    rcases List.mem_map.mp member with ⟨offset, _, rfl⟩
    simpa only [List.length_reverse] using List.length_rotate priorities.reverse offset

theorem canonicalCycle_eq_mostSeniorPrioritySequence (priorities : List PriorityNumber) :
    BlueBookP93.canonicalCycle priorities =
      BlueBookP93.mostSeniorPrioritySequence (cycleCandidates priorities) := by
  rfl

theorem canonicalCycle_mem_cycleCandidates
    {priorities : List PriorityNumber} (nonempty : priorities ≠ []) :
    BlueBookP93.canonicalCycle priorities ∈ cycleCandidates priorities := by
  rw [canonicalCycle_eq_mostSeniorPrioritySequence]
  exact mostSeniorPrioritySequence_mem _ (cycleCandidates_nonempty nonempty)

/-- After the injective priority encoding, the source canonical cycle is the ordinary
lexicographic minimum of all rotations in both traversal directions. -/
theorem encodeWord_canonicalCycle_eq_minimum
    {priorities : List PriorityNumber} (nonempty : priorities ≠ []) :
    (encodeWord (BlueBookP93.canonicalCycle priorities) :
        WithTop (List PriorityDigit)) =
      ((cycleCandidates priorities).map encodeWord).minimum := by
  rw [canonicalCycle_eq_mostSeniorPrioritySequence]
  unfold BlueBookP93.mostSeniorPrioritySequence
  cases candidatesEq : cycleCandidates priorities with
  | nil => exact (cycleCandidates_nonempty nonempty candidatesEq).elim
  | cons first rest =>
      change (encodeWord (rest.foldl seniorChoice first) : WithTop (List PriorityDigit)) =
        (encodeWord first :: rest.map encodeWord).minimum
      rw [encodeWord_foldl_seniorChoice rest first priorities.length]
      · rw [foldl_min_eq_minimum_of_cons (encodeWord first) (rest.map encodeWord)]
        simp only [List.coe_minimum_of_length_pos]
      · exact length_of_mem_cycleCandidates (candidatesEq ▸ List.mem_cons_self)
      · intro candidate member
        exact length_of_mem_cycleCandidates
          (candidatesEq ▸ List.mem_cons.mpr (Or.inr member))

theorem cycleCandidates_membership_invariant
    {left right candidate : List PriorityNumber}
    (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ [])
    (equivalent : DihedrallyEquivalent left right) :
    candidate ∈ cycleCandidates left ↔ candidate ∈ cycleCandidates right := by
  rw [mem_cycleCandidates_iff leftNonempty, mem_cycleCandidates_iff rightNonempty]
  constructor
  · intro leftToCandidate
    exact dihedrallyEquivalent_trans (dihedrallyEquivalent_symm equivalent) leftToCandidate
  · intro rightToCandidate
    exact dihedrallyEquivalent_trans equivalent rightToCandidate

/-- The source `canonicalCycle` is a complete invariant of an unoriented equatorial polygon:
equal outputs occur exactly for words related by a rotation or reflection.  No distinctness
assumption is imposed, so repeated and primed priority numbers are covered. -/
theorem canonicalCycle_eq_iff_dihedrallyEquivalent
    {left right : List PriorityNumber}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ []) :
    BlueBookP93.canonicalCycle left = BlueBookP93.canonicalCycle right ↔
      DihedrallyEquivalent left right := by
  constructor
  · intro same
    have leftMember := canonicalCycle_mem_cycleCandidates leftNonempty
    have rightMember := canonicalCycle_mem_cycleCandidates rightNonempty
    have leftToCanonical :=
      (mem_cycleCandidates_iff leftNonempty).mp leftMember
    have rightToCanonical :=
      (mem_cycleCandidates_iff rightNonempty).mp rightMember
    rw [same] at leftToCanonical
    exact dihedrallyEquivalent_trans leftToCanonical
      (dihedrallyEquivalent_symm rightToCanonical)
  · intro equivalent
    apply (List.map_injective_iff.mpr priorityDigit_injective)
    apply WithTop.coe_injective
    change (encodeWord (BlueBookP93.canonicalCycle left) :
        WithTop (List PriorityDigit)) =
      (encodeWord (BlueBookP93.canonicalCycle right) :
        WithTop (List PriorityDigit))
    rw [encodeWord_canonicalCycle_eq_minimum leftNonempty,
      encodeWord_canonicalCycle_eq_minimum rightNonempty]
    apply le_antisymm
    · apply List.minimum_anti
      intro digits member
      rcases List.mem_map.mp member with ⟨candidate, candidateMember, rfl⟩
      exact List.mem_map.mpr ⟨candidate,
        (cycleCandidates_membership_invariant leftNonempty rightNonempty equivalent).mpr
          candidateMember,
        rfl⟩
    · apply List.minimum_anti
      intro digits member
      rcases List.mem_map.mp member with ⟨candidate, candidateMember, rfl⟩
      exact List.mem_map.mpr ⟨candidate,
        (cycleCandidates_membership_invariant leftNonempty rightNonempty equivalent).mp
          candidateMember,
        rfl⟩

/-! ## Complete bipyramidal source index -/

/-- Equality of the two axial positions modulo their geometric interchange. -/
def UnorderedPairEquivalent
    (leftFirst leftSecond rightFirst rightSecond : PriorityNumber) : Prop :=
  (leftFirst = rightFirst ∧ leftSecond = rightSecond) ∨
    (leftFirst = rightSecond ∧ leftSecond = rightFirst)

theorem orderedPair_comm (first second : PriorityNumber) :
    BlueBookP93.orderedPair first second = BlueBookP93.orderedPair second first := by
  unfold BlueBookP93.orderedPair
  by_cases secondSenior : second.seniorTo first = true
  · have firstNotSenior : first.seniorTo second = false := by
      apply Bool.eq_false_iff.mpr
      intro firstSenior
      have secondLess := (priorityDigit_senior_iff second first).mp secondSenior
      have firstLess := (priorityDigit_senior_iff first second).mp firstSenior
      exact (LT.lt.false (firstLess.trans secondLess))
    simp [secondSenior, firstNotSenior]
  · have secondNotSenior : second.seniorTo first = false := by
      exact Bool.eq_false_iff.mpr secondSenior
    by_cases firstSenior : first.seniorTo second = true
    · simp [secondNotSenior, firstSenior]
    · have firstNotSenior : first.seniorTo second = false :=
        Bool.eq_false_iff.mpr firstSenior
      have decisionEq : BlueBookP93.priorityDecision first second = .eq := by
        simp [BlueBookP93.priorityDecision, firstNotSenior, secondNotSenior]
      have same := (priorityDecision_eq_eq_iff first second).mp decisionEq
      subst second
      simp [BlueBookP93.PriorityNumber.seniorTo]

/-- The source senior-first axial pair loses exactly the irrelevant interchange of the two
geometrically equivalent axial positions. -/
theorem orderedPair_eq_iff_unorderedPairEquivalent
    (leftFirst leftSecond rightFirst rightSecond : PriorityNumber) :
    BlueBookP93.orderedPair leftFirst leftSecond =
        BlueBookP93.orderedPair rightFirst rightSecond ↔
      UnorderedPairEquivalent leftFirst leftSecond rightFirst rightSecond := by
  constructor
  · unfold BlueBookP93.orderedPair
    split <;> split <;> simp_all [UnorderedPairEquivalent]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact orderedPair_comm _ _

/-- Relative equivalence of two bipyramidal ligand placements in the source coordinates: the
axial pair may be interchanged and the equatorial polygon may be rotated or reflected. -/
def BipyramidalEquivalent
    (leftFirstAxial leftSecondAxial : PriorityNumber)
    (leftPlane : List PriorityNumber)
    (rightFirstAxial rightSecondAxial : PriorityNumber)
    (rightPlane : List PriorityNumber) : Prop :=
  UnorderedPairEquivalent leftFirstAxial leftSecondAxial
      rightFirstAxial rightSecondAxial ∧
    DihedrallyEquivalent leftPlane rightPlane

/-- For every nonempty equatorial polygon, equality of the complete source bipyramidal index is
equivalent to geometric equivalence of the ligand placements.  This is the direct completeness
theorem for `BlueBookP93.bipyramidalIndex`, covering repeated and primed priority numbers. -/
theorem bipyramidalIndex_eq_iff_bipyramidalEquivalent
    (leftFirstAxial leftSecondAxial : PriorityNumber)
    (leftPlane : List PriorityNumber)
    (rightFirstAxial rightSecondAxial : PriorityNumber)
    (rightPlane : List PriorityNumber)
    (leftPlaneNonempty : leftPlane ≠ [])
    (rightPlaneNonempty : rightPlane ≠ []) :
    BlueBookP93.bipyramidalIndex leftFirstAxial leftSecondAxial leftPlane =
        BlueBookP93.bipyramidalIndex rightFirstAxial rightSecondAxial rightPlane ↔
      BipyramidalEquivalent leftFirstAxial leftSecondAxial leftPlane
        rightFirstAxial rightSecondAxial rightPlane := by
  unfold BlueBookP93.bipyramidalIndex BipyramidalEquivalent
  simp only [List.cons.injEq, and_true]
  rw [orderedPair_eq_iff_unorderedPairEquivalent,
    canonicalCycle_eq_iff_dihedrallyEquivalent leftPlaneNonempty rightPlaneNonempty]

/-- The actual two-entry trigonal-bipyramidal source index is likewise exact for its axial pair.
The omitted three-site equatorial triangle is reconstructed separately from the complete ligand
multiset at the molecular integration boundary. -/
theorem trigonalBipyramidIndex_eq_iff_unorderedPairEquivalent
    (leftFirstAxial leftSecondAxial rightFirstAxial rightSecondAxial : PriorityNumber) :
    BlueBookP93.trigonalBipyramidIndex leftFirstAxial leftSecondAxial =
        BlueBookP93.trigonalBipyramidIndex rightFirstAxial rightSecondAxial ↔
      UnorderedPairEquivalent leftFirstAxial leftSecondAxial
        rightFirstAxial rightSecondAxial := by
  exact orderedPair_eq_iff_unorderedPairEquivalent _ _ _ _

/-- An equivalent axial pair has the same multiset, including when the two priorities coincide. -/
theorem unorderedPairEquivalent_perm
    {leftFirst leftSecond rightFirst rightSecond : PriorityNumber}
    (equivalent :
      UnorderedPairEquivalent leftFirst leftSecond rightFirst rightSecond) :
    [leftFirst, leftSecond].Perm [rightFirst, rightSecond] := by
  rcases equivalent with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact List.Perm.refl _
  · exact List.Perm.swap _ _ []

/-- Cancellation of equal prefix multisets from a whole-list multiset equality. -/
theorem perm_suffix_of_perm_prefix_and_perm_append
    {prefixLeft prefixRight suffixLeft suffixRight : List PriorityNumber}
    (prefixPerm : prefixLeft.Perm prefixRight)
    (wholePerm : (prefixLeft ++ suffixLeft).Perm (prefixRight ++ suffixRight)) :
    suffixLeft.Perm suffixRight := by
  rw [List.perm_iff_count]
  intro priority
  have prefixCount := (List.perm_iff_count.mp prefixPerm) priority
  have wholeCount := (List.perm_iff_count.mp wholePerm) priority
  simp only [List.count_append] at wholeCount
  omega

/-- For a three-site equatorial triangle, every multiset permutation is a geometric dihedral
symmetry.  This is the mathematical fact that `D₃ = S₃`; no distinctness assumption is needed. -/
theorem length_three_perm_implies_dihedrallyEquivalent
    {left right : List PriorityNumber}
    (leftLength : left.length = 3) (permuted : left.Perm right) :
    DihedrallyEquivalent left right := by
  rcases List.length_eq_three.mp leftLength with ⟨a, b, c, rfl⟩
  have member : right ∈ [a, b, c].permutations :=
    List.mem_permutations.mpr permuted.symm
  simp [List.permutations] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨0, by simp⟩
  · exact Or.inr ⟨1, by simp⟩
  · exact Or.inr ⟨0, by simp⟩
  · exact Or.inl ⟨1, by simp⟩
  · exact Or.inl ⟨2, by simp⟩
  · exact Or.inr ⟨2, by simp⟩

/-- The source's omitted TBPY-5 equatorial segment is information preserving once the complete
five-ligand priority multiset is fixed.  Equality of the actual two-entry source index is then
equivalent to the full bipyramidal geometric equivalence: axial interchange and `D₃` action on
the equatorial triangle. -/
theorem trigonalBipyramidIndex_eq_iff_bipyramidalEquivalent_of_samePriorityMultiset
    (leftFirstAxial leftSecondAxial : PriorityNumber)
    (leftPlane : List PriorityNumber)
    (rightFirstAxial rightSecondAxial : PriorityNumber)
    (rightPlane : List PriorityNumber)
    (leftPlaneLength : leftPlane.length = 3)
    (samePriorityMultiset :
      (leftFirstAxial :: leftSecondAxial :: leftPlane).Perm
        (rightFirstAxial :: rightSecondAxial :: rightPlane)) :
    BlueBookP93.trigonalBipyramidIndex leftFirstAxial leftSecondAxial =
        BlueBookP93.trigonalBipyramidIndex rightFirstAxial rightSecondAxial ↔
      BipyramidalEquivalent leftFirstAxial leftSecondAxial leftPlane
        rightFirstAxial rightSecondAxial rightPlane := by
  constructor
  · intro sameIndex
    have axialEquivalent :=
      (trigonalBipyramidIndex_eq_iff_unorderedPairEquivalent _ _ _ _).mp sameIndex
    have axialPerm := unorderedPairEquivalent_perm axialEquivalent
    have wholePerm :
        ([leftFirstAxial, leftSecondAxial] ++ leftPlane).Perm
          ([rightFirstAxial, rightSecondAxial] ++ rightPlane) := by
      simpa using samePriorityMultiset
    have planePerm :=
      perm_suffix_of_perm_prefix_and_perm_append axialPerm wholePerm
    exact ⟨axialEquivalent,
      length_three_perm_implies_dihedrallyEquivalent leftPlaneLength planePerm⟩
  · intro equivalent
    exact (trigonalBipyramidIndex_eq_iff_unorderedPairEquivalent _ _ _ _).mpr
      equivalent.1

/-! ## Production refinement -/

theorem priorityOfProduction_injective :
    Function.Injective BlueBookP93.priorityOfProduction := by
  intro left right same
  cases left
  cases right
  simp [BlueBookP93.priorityOfProduction] at same
  simp_all

/-- The executable production bipyramidal index has exactly the same collision boundary as the
independent source index. -/
theorem productionBipyramidalConfigurationIndex_eq_iff
    (leftFirstAxial leftSecondAxial : PolyhedralPriorityNumber)
    (leftPlane : List PolyhedralPriorityNumber)
    (rightFirstAxial rightSecondAxial : PolyhedralPriorityNumber)
    (rightPlane : List PolyhedralPriorityNumber)
    (leftPlaneNonempty : leftPlane ≠ [])
    (rightPlaneNonempty : rightPlane ≠ []) :
    bipyramidalConfigurationIndex leftFirstAxial leftSecondAxial leftPlane =
        bipyramidalConfigurationIndex rightFirstAxial rightSecondAxial rightPlane ↔
      BipyramidalEquivalent
        (BlueBookP93.priorityOfProduction leftFirstAxial)
        (BlueBookP93.priorityOfProduction leftSecondAxial)
        (leftPlane.map BlueBookP93.priorityOfProduction)
        (BlueBookP93.priorityOfProduction rightFirstAxial)
        (BlueBookP93.priorityOfProduction rightSecondAxial)
        (rightPlane.map BlueBookP93.priorityOfProduction) := by
  have leftMappedNonempty :
      leftPlane.map BlueBookP93.priorityOfProduction ≠ [] := by simpa using leftPlaneNonempty
  have rightMappedNonempty :
      rightPlane.map BlueBookP93.priorityOfProduction ≠ [] := by simpa using rightPlaneNonempty
  let mapIndex := List.map (List.map BlueBookP93.priorityOfProduction)
  have mapIndexInjective : Function.Injective mapIndex :=
    List.map_injective_iff.mpr
      (List.map_injective_iff.mpr priorityOfProduction_injective)
  constructor
  · intro same
    have mappedSame := congrArg mapIndex same
    have mappedSame' :
        (bipyramidalConfigurationIndex leftFirstAxial leftSecondAxial leftPlane).map
            (List.map BlueBookP93.priorityOfProduction) =
          (bipyramidalConfigurationIndex rightFirstAxial rightSecondAxial rightPlane).map
            (List.map BlueBookP93.priorityOfProduction) := by
      simpa [mapIndex] using mappedSame
    rw [bipyramidalConfigurationIndex_conforms_IR9,
      bipyramidalConfigurationIndex_conforms_IR9] at mappedSame'
    exact (bipyramidalIndex_eq_iff_bipyramidalEquivalent
      _ _ _ _ _ _ leftMappedNonempty rightMappedNonempty).mp mappedSame'
  · intro equivalent
    apply mapIndexInjective
    change
      (bipyramidalConfigurationIndex leftFirstAxial leftSecondAxial leftPlane).map
          (List.map BlueBookP93.priorityOfProduction) =
        (bipyramidalConfigurationIndex rightFirstAxial rightSecondAxial rightPlane).map
          (List.map BlueBookP93.priorityOfProduction)
    rw [bipyramidalConfigurationIndex_conforms_IR9,
      bipyramidalConfigurationIndex_conforms_IR9]
    exact (bipyramidalIndex_eq_iff_bipyramidalEquivalent
      _ _ _ _ _ _ leftMappedNonempty rightMappedNonempty).mpr equivalent

/-- The executable two-entry TBPY-5 index loses exactly axial interchange, and nothing else in
the supplied axial pair. -/
theorem productionTrigonalBipyramidConfigurationIndex_eq_iff
    (leftFirstAxial leftSecondAxial rightFirstAxial rightSecondAxial :
      PolyhedralPriorityNumber) :
    trigonalBipyramidConfigurationIndex leftFirstAxial leftSecondAxial =
        trigonalBipyramidConfigurationIndex rightFirstAxial rightSecondAxial ↔
      UnorderedPairEquivalent
        (BlueBookP93.priorityOfProduction leftFirstAxial)
        (BlueBookP93.priorityOfProduction leftSecondAxial)
        (BlueBookP93.priorityOfProduction rightFirstAxial)
        (BlueBookP93.priorityOfProduction rightSecondAxial) := by
  have mapPairInjective :
      Function.Injective (List.map BlueBookP93.priorityOfProduction) :=
    List.map_injective_iff.mpr priorityOfProduction_injective
  constructor
  · intro same
    have mappedSame := congrArg (List.map BlueBookP93.priorityOfProduction) same
    rw [trigonalBipyramidConfigurationIndex_conforms_P93,
      trigonalBipyramidConfigurationIndex_conforms_P93] at mappedSame
    exact (trigonalBipyramidIndex_eq_iff_unorderedPairEquivalent _ _ _ _).mp mappedSame
  · intro equivalent
    apply mapPairInjective
    rw [trigonalBipyramidConfigurationIndex_conforms_P93,
      trigonalBipyramidConfigurationIndex_conforms_P93]
    exact (trigonalBipyramidIndex_eq_iff_unorderedPairEquivalent _ _ _ _).mpr equivalent

/-- Production-level version of the TBPY-5 omission theorem.  The molecular integration layer
fixes the complete five-priority multiset, so the emitted axial pair is a complete invariant of
the whole relative placement. -/
theorem productionTrigonalBipyramidConfigurationIndex_eq_iff_full
    (leftFirstAxial leftSecondAxial : PolyhedralPriorityNumber)
    (leftPlane : List PolyhedralPriorityNumber)
    (rightFirstAxial rightSecondAxial : PolyhedralPriorityNumber)
    (rightPlane : List PolyhedralPriorityNumber)
    (leftPlaneLength : leftPlane.length = 3)
    (samePriorityMultiset :
      (leftFirstAxial :: leftSecondAxial :: leftPlane).Perm
        (rightFirstAxial :: rightSecondAxial :: rightPlane)) :
    trigonalBipyramidConfigurationIndex leftFirstAxial leftSecondAxial =
        trigonalBipyramidConfigurationIndex rightFirstAxial rightSecondAxial ↔
      BipyramidalEquivalent
        (BlueBookP93.priorityOfProduction leftFirstAxial)
        (BlueBookP93.priorityOfProduction leftSecondAxial)
        (leftPlane.map BlueBookP93.priorityOfProduction)
        (BlueBookP93.priorityOfProduction rightFirstAxial)
        (BlueBookP93.priorityOfProduction rightSecondAxial)
        (rightPlane.map BlueBookP93.priorityOfProduction) := by
  have mappedLength :
      (leftPlane.map BlueBookP93.priorityOfProduction).length = 3 := by
    simpa using leftPlaneLength
  have mappedMultiset :
      (BlueBookP93.priorityOfProduction leftFirstAxial ::
          BlueBookP93.priorityOfProduction leftSecondAxial ::
          leftPlane.map BlueBookP93.priorityOfProduction).Perm
        (BlueBookP93.priorityOfProduction rightFirstAxial ::
          BlueBookP93.priorityOfProduction rightSecondAxial ::
          rightPlane.map BlueBookP93.priorityOfProduction) := by
    simpa using samePriorityMultiset.map BlueBookP93.priorityOfProduction
  rw [productionTrigonalBipyramidConfigurationIndex_eq_iff]
  constructor
  · intro axialEquivalent
    have sourceIndexSame :=
      (trigonalBipyramidIndex_eq_iff_unorderedPairEquivalent _ _ _ _).mpr
        axialEquivalent
    exact (trigonalBipyramidIndex_eq_iff_bipyramidalEquivalent_of_samePriorityMultiset
      _ _ _ _ _ _ mappedLength mappedMultiset).mp sourceIndexSame
  · intro fullEquivalent
    exact fullEquivalent.1

end TetraStereo.OneCenter.RedBookIR9.BipyramidalSourceIndexCompleteness
