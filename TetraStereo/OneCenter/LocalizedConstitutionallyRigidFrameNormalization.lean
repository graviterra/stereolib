import TetraStereo.OneCenter.LocalizedOccurrenceRule45Exact
import TetraStereo.OneCenter.LocalizedConstitutionalFrameNormalization
import TetraStereo.OneCenter.LocalizedCompoundRankConvexity
import TetraStereo.OneCenter.TrackedLocalizedLigandSortCompleteness
import TetraStereo.OneCenter.LocalizedAcyclicPhysicalPseudoFidelity
import TetraStereo.OneCenter.LocalizedRule4aPrecedenceFidelity
import TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
import TetraStereo.OneCenter.AuthoritativeLocalizedCIPAnalysis
import TetraStereo.OneCenter.MultiCenterDetection
import TetraStereo.OneCenter.LocalizedNoDoubleWholeStateRule45Bridge
import TetraStereo.KernelOnly

set_option autoImplicit false

noncomputable section

namespace TetraStereo.OneCenter

open AcyclicCutBranchAutomorphism

namespace CertifiedLocalizedCIPInput

















































/-! ## Actual compound keys at the production occurrence fuel -/

/-- The actual compound Rules-4a--5 key built at one slot of an exact four-ligand frame, at the
production occurrence fuel `localizedOccurrenceRerootEvaluationFuel carrierFuel`.

The key is extracted from the actual fuel-completeness theorem
`exists_buildLocalizedRerootCompoundRule45Key?_at_twice` applied to the slot's cursor validity; no
key value and no key success is assumed. -/
def LocalizedOccurrenceFourLigandFrame.compoundKeyAt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (index : Fin 4) : input.LocalizedRerootCompoundRule45Key :=
  Classical.choose
    (input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
      target view (frame.cursorAt index)
      (frame.cursorAt_valid input target derived index))

/-- The slot key of `compoundKeyAt` is exactly the key the production builder returns at that slot,
at the production occurrence fuel. -/
theorem LocalizedOccurrenceFourLigandFrame.compoundKeyAt_built
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (index : Fin 4) :
    input.buildLocalizedRerootCompoundRule45Key? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
      some (frame.compoundKeyAt input target view derived index) :=
  Classical.choose_spec
    (input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
      target view (frame.cursorAt index)
      (frame.cursorAt_valid input target derived index))

/-! ## The actual-comparator reduction for constitutionally separated keys -/

/-- The actual complete prior Rules-4b/4c comparison separates every distinct pair of frame-slot
compound keys.  This is the exact comparator-level form of constitutional rigidity: it speaks only
about the actual keys built from the carrier, and mentions no label, rank, sort success or desired
classification. -/
def ConstitutionallySeparatedActualKeys
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) : Prop :=
  ∀ left right : Fin 4, left ≠ right →
    input.compareLocalizedRerootCompoundRule4bcKeys (keys left).prior (keys right).prior ≠
      Ordering.eq

/-- Prior separation of the actual keys makes the complete compound comparator off-diagonal
strict.  The decisive-prior lexicographic projection and the `pseudo = false` law are the existing
`compareLocalizedRerootCompoundRule45Keys_eq_prior_of_prior_ne` and
`compoundThroughRule5_pseudo_eq_false_of_not_tie`. -/
theorem compoundKeyOffDiagonalStrict_of_priorSeparated
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (separated : ConstitutionallySeparatedActualKeys input keys) :
    input.CompoundKeyOffDiagonalStrict keys := by
  intro left right different
  have h := input.compoundKeyComparison_eq_prior_of_prior_ne
    (keys := keys) (i := left) (j := right) (separated left right different)
  rw [h]
  exact separated left right different

/-- The production pair comparison at a frame slot pair is exactly the record of the two actual
slot keys. -/
theorem compareLocalizedOccurrenceThroughRule5At?_eq_some_record
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index))
    (left right : Fin 4) :
    input.compareLocalizedOccurrenceThroughRule5At? target view frame left right =
      some (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 (keys left) (keys right))) := by
  simp only [compareLocalizedOccurrenceThroughRule5At?]
  rw [built left, built right]
  rfl

/-- **Strict-rank bridge.**  Off the diagonal, the actual production occurrence comparator is
literally the strict rank comparator of the count-smaller-elements rank of the actual compound
keys.  No rank, priority or atomic number is supplied. -/
theorem compareLocalizedOccurrenceThroughRule5At?_eq_strictRankComparison
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index))
    (separated : ConstitutionallySeparatedActualKeys input keys)
    (left right : Fin 4) (different : left ≠ right) :
    input.compareLocalizedOccurrenceThroughRule5At? target view frame left right =
      strictRankComparison (input.compoundKeyRank keys) left right := by
  have offDiagonal : input.CompoundKeyOffDiagonalStrict keys :=
    input.compoundKeyOffDiagonalStrict_of_priorSeparated keys separated
  have comparisonEq : input.compareLocalizedRerootCompoundRule45Keys (keys left) (keys right) =
      compare (input.compoundKeyRank keys left) (input.compoundKeyRank keys right) := by
    have h := input.compoundKeyComparison_eq_compare_rank keys offDiagonal left right
    simpa [compoundKeyComparison, Ordering.byKey] using h
  have priorEq : input.compareLocalizedRerootCompoundRule4bcKeys
        (keys left).prior (keys right).prior =
      compare (input.compoundKeyRank keys left) (input.compoundKeyRank keys right) := by
    rw [← input.compareLocalizedRerootCompoundRule45Keys_eq_prior_of_prior_ne
      (keys left) (keys right) (separated left right different)]
    exact comparisonEq
  rw [input.compareLocalizedOccurrenceThroughRule5At?_eq_some_record
    target view frame keys built left right]
  rw [input.compareLocalizedRerootCompoundThroughRule5_eq_of_prior_ne
    (keys left) (keys right) (separated left right different)]
  simp [strictRankComparison, localizedOccurrenceRule45ComparisonRecord, priorEq]

/-! ## Total tracked and safe sorts without root-`Z` separation -/

/-- **Strict tracked sort.**  Prior separation of the actual compound keys makes the production
tracked four-ligand sort total, with exact slot preservation, strict descending computed rank, and
zero pseudo comparisons. -/
theorem exists_trackedOrder_of_constitutionallySeparatedActualKeys
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (_derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index))
    (separated : ConstitutionallySeparatedActualKeys input keys) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      tracked.highestFirst.Pairwise (fun left right =>
        input.compoundKeyRank keys right < input.compoundKeyRank keys left) ∧
      tracked.pseudoComparisons = 0 := by
  have offDiagonal : input.CompoundKeyOffDiagonalStrict keys :=
    input.compoundKeyOffDiagonalStrict_of_priorSeparated keys separated
  have injective : Function.Injective (input.compoundKeyRank keys) :=
    input.compoundKeyRank_injective keys offDiagonal
  have total := sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne
    (input.compoundKeyRank keys) injective
    (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
    (fun left right different =>
      input.compareLocalizedOccurrenceThroughRule5At?_eq_strictRankComparison
        target view frame keys built separated left right different)
  simpa [localizedOccurrenceRule45TrackedOrder?] using total

/-- **Safe tracked sort.**  The same prior separation also makes the all-pairs coherence gate
accept, so the safe order is the tracked order, every earlier/later actual comparison strictly
decreases, and the pseudo history remains empty. -/
theorem exists_safeTrackedOrder_of_constitutionallySeparatedActualKeys
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index))
    (separated : ConstitutionallySeparatedActualKeys input keys) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      input.CanonicalLocalizedOccurrenceRule45Sort
        target view frame (List.finRange 4) [] 0 tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      tracked.highestFirst.Pairwise (fun left right =>
        ∃ result,
          input.compareLocalizedOccurrenceThroughRule5At?
            target view frame left right = some result ∧
          result.ordering = Ordering.gt) ∧
      tracked.pseudoComparisons = 0 := by
  obtain ⟨tracked, trackedComputed, permutation, strict, pseudo⟩ :=
    input.exists_trackedOrder_of_constitutionallySeparatedActualKeys
      target view frame derived keys built separated
  have canonicalSort : input.CanonicalLocalizedOccurrenceRule45Sort
      target view frame (List.finRange 4) [] 0 tracked :=
    (input.localizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
      target view frame tracked).mp trackedComputed
  have strictStep : ∀ left right : Fin 4,
      input.compoundKeyRank keys right < input.compoundKeyRank keys left →
      ∃ result,
        input.compareLocalizedOccurrenceThroughRule5At? target view frame left right =
          some result ∧
        result.ordering = Ordering.gt := by
    intro left right higher
    have different : left ≠ right := by
      rintro rfl
      exact Nat.lt_irrefl _ higher
    refine ⟨{ ordering := compare (input.compoundKeyRank keys left) (input.compoundKeyRank keys right), pseudo := false }, ?_, ?_⟩
    · simpa [strictRankComparison] using
        input.compareLocalizedOccurrenceThroughRule5At?_eq_strictRankComparison
          target view frame keys built separated left right different
    · show compare (input.compoundKeyRank keys left) (input.compoundKeyRank keys right) = Ordering.gt
      exact compare_gt_iff_gt.mpr higher
  have canonicalStrict : tracked.highestFirst.Pairwise (fun left right =>
      ∃ result,
        input.CanonicalLocalizedOccurrenceThroughRule5At
          target view frame left right result ∧
        result.ordering = Ordering.gt) :=
    List.Pairwise.imp (by
      intro left right higher
      obtain ⟨result, computed, orderingEq⟩ := strictStep left right higher
      exact ⟨result,
        (input.compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
          target view frame left right result).mp computed,
        orderingEq⟩) strict
  have coherent : input.localizedOccurrenceRule45OrderCoherent?
      target view frame tracked.highestFirst = true :=
    (input.localizedOccurrenceRule45OrderCoherent?_eq_true_iff
      target view frame tracked.highestFirst).mpr
      (List.Pairwise.imp (by
        intro left right canonical
        obtain ⟨result, canonicalCompared, higher⟩ := canonical
        exact ⟨result,
          (input.compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
            target view frame left right result).mpr canonicalCompared,
          higher⟩) canonicalStrict)
  have safeComputed : input.safeLocalizedOccurrenceRule45TrackedOrder?
      target view frame = some tracked := by
    simp [safeLocalizedOccurrenceRule45TrackedOrder?, trackedComputed, coherent]
  exact ⟨tracked, safeComputed, canonicalSort, permutation,
    List.Pairwise.imp (by intro left right higher; exact strictStep left right higher) strict,
    pseudo⟩

/-! ## Descriptor normalization from physical geometry -/

/-- **Geometry normalization without root-`Z` separation.**  At an actual compound-key separated
frame with a real tetrahedral centre, if the actual priority-ordered coordinates of the tracked
order have rational orientation `normalizedRS`, then the production Rules-4a--5 descriptor is the
uppercase `.chiral normalizedRS` label and every comparison in the tracked history had zero pseudo
weight.

The geometry hypothesis is stated for the actual tracked order produced by the executable sorter,
so it cannot presuppose the label it explains. -/
theorem localizedConstitutionalRigidFrame_descriptor_eq_chiral_of_geometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index))
    (separated : ConstitutionallySeparatedActualKeys input keys)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (normalizedRS : RS)
    (geometry : ∀ tracked : TrackedLocalizedLigandOrder,
      input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked →
      ∃ points : List CartesianPoint3,
        List.Forall₂
          (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
            (frame.cursorAt index) point)
          tracked.highestFirst points ∧
        RationalTetrahedralDescriptor points normalizedRS) :
    input.localizedOccurrenceRule45Descriptor? target view =
      some (.chiral normalizedRS) := by
  obtain ⟨tracked, safeComputed, _canonicalSort, _permutation, _canonicalStrict, pseudo⟩ :=
    input.exists_safeTrackedOrder_of_constitutionallySeparatedActualKeys
      target view frame derived keys built separated
  have trackedComputed : input.localizedOccurrenceRule45TrackedOrder?
      target view frame = some tracked :=
    input.localizedConstitutionalFrame_trackedOrder_of_safe
      target view frame tracked safeComputed
  obtain ⟨points, pointsDeclared, rational⟩ := geometry tracked trackedComputed
  let evidence : input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel :=
    { center := center, frame := frame, tracked := tracked, points := points }
  have canonical : input.CanonicalLocalizedOccurrenceRule45Descriptor
      target view (.chiral normalizedRS) := by
    refine ⟨evidence, normalizedRS, ?_, rational, ?_⟩
    · exact ⟨centerReal, derived,
        (input.safeLocalizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
          target view frame tracked).mp safeComputed,
        pointsDeclared⟩
    · simp [evidence, pseudo]
  exact (input.localizedOccurrenceRule45Descriptor?_eq_some_iff_canonical
    target view (.chiral normalizedRS)).mpr canonical

/-- The `map` of a list is the `ofFn` of the same function read through `List.getElem`. -/
private theorem map_eq_ofFn_getElem {α β : Type} (list : List α) (function : α → β) :
    list.map function =
      List.ofFn (fun index : Fin list.length => function (list[index])) :=
  (List.ofFn_getElem_eq_map list function).symm

/-- **Physical frame join without root-`Z` separation.**  Suppose the four actual neighbour slots
of the frame have exact physical coordinates in the original slot order (`pointsAt`), and the
written-order configuration has parity `parity` with nonzero determinant (`writtenParity`).  Then
the executable tracked sort exposes the actual priority permutation
`tracked.highestFirst.map Fin.val`, and the production Rules-4a--5 descriptor is the uppercase
chiral label whose `RS` sign is the written parity adjusted by the inversion parity of exactly that
permutation.

No positions list, no sorted-point equality, and no label is supplied: the permutation is read off
the actual sort and the sorted coordinates are the actual `mapM` image of the four frame points. -/
theorem localizedConstitutionalRigidFrame_descriptor_eq_chiral_of_physicalFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index))
    (separated : ConstitutionallySeparatedActualKeys input keys)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      input.localizedOccurrenceRule45Descriptor? target view =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) := by
  obtain ⟨tracked, trackedComputed, permutation, _strict, pseudo⟩ :=
    input.exists_trackedOrder_of_constitutionallySeparatedActualKeys
      target view frame derived keys built separated
  have lengthEq : tracked.highestFirst.length = 4 := by
    simpa using permutation.length_eq
  let positions : List Nat := tracked.highestFirst.map Fin.val
  have positionsPermutation : positions.Perm (List.range 4) := by
    have mapped := permutation.map Fin.val
    simpa [positions, List.map_coe_finRange_eq_range] using mapped
  let ordering : Equiv.Perm (Fin 4) :=
    Rule6HandednessSemantics.finFourEquivOfPermutationList positions positionsPermutation
  have orderingList : Rule6HandednessSemantics.finFourPermutationList ordering = positions :=
    Rule6HandednessSemantics.finFourPermutationList_equivOfPermutationList
      positions positionsPermutation
  let getAt : Fin 4 → Fin 4 := fun index =>
    tracked.highestFirst[Fin.cast lengthEq.symm index]
  have orderingEq : ∀ index : Fin 4, ordering index = getAt index := by
    intro index
    apply Fin.ext
    have functionsEq : (fun position : Fin 4 => (ordering position).val) =
        (fun position : Fin 4 => (getAt position).val) := by
      apply List.ofFn_inj.mp
      calc List.ofFn (fun position : Fin 4 => (ordering position).val)
          = Rule6HandednessSemantics.finFourPermutationList ordering := rfl
        _ = positions := orderingList
        _ = tracked.highestFirst.map Fin.val := rfl
        _ = List.ofFn (fun position : Fin tracked.highestFirst.length =>
              (tracked.highestFirst[position]).val) :=
            map_eq_ofFn_getElem tracked.highestFirst Fin.val
        _ = List.ofFn (fun position : Fin 4 => (getAt position).val) := by
            simpa [getAt] using List.ofFn_congr lengthEq
              (fun position : Fin tracked.highestFirst.length =>
                (tracked.highestFirst[position]).val)
    exact congrFun functionsEq index
  have pointVectorEq : ∀ index : Fin 4,
      RationalTetrahedralPermutation.pointVector
        (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) index = pointsAt index := by
    intro index
    fin_cases index <;> rfl
  have permutedEq : RationalTetrahedralPermutation.permutedPoints
        (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ordering =
      List.ofFn (fun index : Fin 4 =>
        RationalTetrahedralPermutation.pointVector
          (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) (ordering index)) := by
    simp [RationalTetrahedralPermutation.permutedPoints, List.ofFn_succ]
  have bridge : tracked.highestFirst.map pointsAt =
      RationalTetrahedralPermutation.permutedPoints
        (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ordering := by
    calc tracked.highestFirst.map pointsAt
        = List.ofFn (fun index : Fin 4 => pointsAt (getAt index)) := by
          rw [map_eq_ofFn_getElem tracked.highestFirst pointsAt]
          simpa [getAt] using List.ofFn_congr lengthEq
            (fun position : Fin tracked.highestFirst.length =>
              pointsAt (tracked.highestFirst[position]))
      _ = List.ofFn (fun index : Fin 4 =>
            RationalTetrahedralPermutation.pointVector
              (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) (ordering index)) := by
          apply List.ofFn_inj.mpr
          funext index
          rw [orderingEq index]
          exact (pointVectorEq (getAt index)).symm
      _ = RationalTetrahedralPermutation.permutedPoints
            (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ordering :=
          permutedEq.symm
  have pointsDeclared : ∀ order : List (Fin 4),
      List.Forall₂
        (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
          (frame.cursorAt index) point) order (order.map pointsAt) := by
    intro order
    induction order with
    | nil => exact .nil
    | cons head tail inductionHypothesis =>
        exact .cons
          ((input.localizedRerootCursorSpatialPoint?_eq_some_iff
            (frame.cursorAt head) (pointsAt head)).mp (spatial head))
          inductionHypothesis
  obtain ⟨first, second, third, fourth, writtenEq, volume⟩ := writtenParity
  have splitFirst : pointsAt 0 = first ∧
      [pointsAt 1, pointsAt 2, pointsAt 3] = [second, third, fourth] :=
    (List.cons.injEq _ _ _ _).mp writtenEq
  have splitSecond : pointsAt 1 = second ∧
      [pointsAt 2, pointsAt 3] = [third, fourth] :=
    (List.cons.injEq _ _ _ _).mp splitFirst.2
  have splitThird : pointsAt 2 = third ∧ [pointsAt 3] = [fourth] :=
    (List.cons.injEq _ _ _ _).mp splitSecond.2
  have firstEq : pointsAt 0 = first := splitFirst.1
  have secondEq : pointsAt 1 = second := splitSecond.1
  have thirdEq : pointsAt 2 = third := splitThird.1
  have fourthEq : pointsAt 3 = fourth :=
    ((List.cons.injEq _ _ _ _).mp splitThird.2).1
  have pointsEqPermuted : RationalTetrahedralPermutation.permutedPoints
        (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ordering =
      RationalTetrahedralPermutation.permutedPoints
        first second third fourth ordering := by
    simp [RationalTetrahedralPermutation.permutedPoints,
      firstEq, secondEq, thirdEq, fourthEq]
  have labelEq : RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven
          (Rule6HandednessSemantics.finFourPermutationList ordering)) =
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven positions) := by
    rw [orderingList]
  have rational : RationalTetrahedralDescriptor (tracked.highestFirst.map pointsAt)
      (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven positions)) := by
    rw [bridge, pointsEqPermuted, ← labelEq]
    exact RationalTetrahedralPermutation.rationalTetrahedralDescriptor_permutedPoints
      first second third fourth ordering parity volume
  refine ⟨tracked, trackedComputed, pseudo, ?_⟩
  refine input.localizedConstitutionalRigidFrame_descriptor_eq_chiral_of_geometry
    target view frame derived keys built separated center centerReal
    (RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven positions)) ?_
  intro observed computed
  have observedEq : observed = tracked := by
    rw [computed] at trackedComputed
    exact Option.some.inj trackedComputed
  subst observedEq
  exact ⟨observed.highestFirst.map pointsAt,
    pointsDeclared observed.highestFirst, rational⟩

end CertifiedLocalizedCIPInput












def CenterFixingGraphAutIsMultiCenter {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (d : m.Center) : Prop :=
  ∀ e : m.mol.Aut, (e : Equiv.Perm V) d.1 = d.1 →
    m.PreservesCenters (e : Equiv.Perm V)

/-- **Rigidity gives pointwise fixedness.**  If the distinguished centre is constitutionally rigid
and centre-fixing graph automorphisms are multi-center automorphisms, then every graph automorphism
fixing the centre atom fixes *every* neighbour of the centre.

The proof is the actual carrier bridge `ligandAtomAt_ligandPermAt`: a graph automorphism is also a
multi-center automorphism, rigidity forces its ligand permutation to be the identity, and the
ligand enumeration is surjective onto the neighbours. -/
theorem constitutionallyRigid_pointwise_fixed {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (d : m.Center)
    (rigid : ConstitutionallyRigid m d)
    (centerInvariant : CenterFixingGraphAutIsMultiCenter m d) :
    ∀ e : m.mol.Aut, (e : Equiv.Perm V) d.1 = d.1 →
      ∀ x, m.mol.Adj d.1 x → (e : Equiv.Perm V) x = x := by
  intro e hcenter x hadj
  let em : m.Aut :=
    ⟨(e : Equiv.Perm V), e.property, centerInvariant e hcenter⟩
  have hcenterPerm : m.centerPerm em d = d :=
    (RootedTetrahedralBranchSymmetry.centerPerm_eq_iff m em d).mpr (by simpa using hcenter)
  have hlig : m.ligandPermAt em d = 1 := rigid em hcenterPerm
  obtain ⟨i, rfl⟩ := m.ligandAtomAt_surjective d x hadj
  have hbridge := m.ligandAtomAt_ligandPermAt em d i
  simp only [hcenterPerm, hlig, Equiv.Perm.one_apply] at hbridge
  exact hbridge.symm

/-- **Genuine constitutional rigidity at a graph vertex.**  No graph automorphism that fixes the
attachment root moves any neighbour of the root.  Because a root-fixing automorphism permutes the
neighbour set, this is exactly the statement that no root-fixing automorphism swaps two distinct
neighbours.  It mentions only the graph automorphism group, with no centre inventory and no
stereochemical classification. -/
def ConstitutionallyRigidGraphAt {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (root : V) : Prop :=
  ∀ e : m.Aut, (e : Equiv.Perm V) root = root →
    ∀ x, m.Adj root x → (e : Equiv.Perm V) x = x

/-- The detected exact-degree-four centre inventory is invariant under every graph automorphism,
so the centre-preservation bridge is discharged outright there. -/
theorem detectedMultiCenter_centerFixingGraphAutIsMultiCenter
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (d : m.detectedMultiCenterMolecule.Center) :
    CenterFixingGraphAutIsMultiCenter m.detectedMultiCenterMolecule d := by
  intro e _hcenter
  exact m.detectedMultiCenterMolecule_preservesCenters_of_aut e






theorem constitutionallyRigidGraphAt_of_constitutionallyRigid_detected
    (input : CertifiedLocalizedCIPInput)
    (d : input.detectedMultiCenterMolecule.Center)
    (rigid : ConstitutionallyRigid input.detectedMultiCenterMolecule d) :
    ConstitutionallyRigidGraphAt input.moleculeGraph d.1 := by
  have h := constitutionallyRigid_pointwise_fixed input.detectedMultiCenterMolecule d rigid
    (detectedMultiCenter_centerFixingGraphAutIsMultiCenter input.moleculeGraph d)
  simpa [ConstitutionallyRigidGraphAt, CertifiedLocalizedCIPInput.detectedMultiCenterMolecule,
    MoleculeGraph.detectedMultiCenterMolecule] using h








def PriorTieYieldsRootedCutBranchIso
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (root : V) (branchAtom : Fin 4 → V) : Prop :=
  ∀ left right : Fin 4, left ≠ right →
    input.compareLocalizedRerootCompoundRule4bcKeys (keys left).prior (keys right).prior =
        Ordering.eq →
      Nonempty (RootedCutBranchIso m root (branchAtom left) (branchAtom right))




def FrameKeyTableIsoInterface
    (input : CertifiedLocalizedCIPInput)
    (m : MoleculeGraph input.Atom) (root : input.Atom)
    (branchAtom : Fin 4 → input.Atom) : Prop :=
  ∀ {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame),
    (∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? = some (branchAtom index)) →
    ∀ left right : Fin 4, left ≠ right →
      input.compareLocalizedRerootCompoundRule4bcKeys
          ((frame.compoundKeyAt input target view derived) left).prior
          ((frame.compoundKeyAt input target view derived) right).prior =
        Ordering.eq →
      Nonempty (RootedCutBranchIso m root (branchAtom left) (branchAtom right))

/-- The frame-level interface, instantiated at an actual frame and slot link, is the keys-level
interface consumed by the separation argument. -/
theorem priorTieYieldsRootedCutBranchIso_of_frame
    (input : CertifiedLocalizedCIPInput)
    (m : MoleculeGraph input.Atom) (root : input.Atom)
    (branchAtom : Fin 4 → input.Atom)
    (interface : FrameKeyTableIsoInterface input m root branchAtom)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? = some (branchAtom index)) :
    PriorTieYieldsRootedCutBranchIso input
      (frame.compoundKeyAt input target view derived) m root branchAtom :=
  interface target view frame derived ligandLink





theorem priorKey_ne_of_rootedCutBranchIso_refusal
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (root : V) (branchAtom : Fin 4 → V)
    (hacyc : m.Acyclic) (hsimple : m.SimpleBonded) (hcharge : ConstantFormalCharge m)
    (hfix : ∀ e : m.Aut, (e : Equiv.Perm V) root = root →
      ∀ x, m.Adj root x → (e : Equiv.Perm V) x = x)
    (hadj : ∀ i : Fin 4, m.Adj root (branchAtom i))
    (hinj : ∀ i j : Fin 4, branchAtom i = branchAtom j → i = j)
    (interface : PriorTieYieldsRootedCutBranchIso input keys m root branchAtom)
    (left right : Fin 4) (different : left ≠ right) :
    input.compareLocalizedRerootCompoundRule4bcKeys (keys left).prior (keys right).prior ≠
      Ordering.eq := by
  intro tie
  have distinct : branchAtom left ≠ branchAtom right := by
    intro same
    exact different (hinj left right same)
  exact no_rootedCutBranchIso_of_pointwise_fixed m root (branchAtom left) (branchAtom right)
    hacyc (hadj left) (hadj right) distinct hsimple hcharge hfix
    (interface left right different tie)





theorem constitutionallySeparatedActualKeys_of_graphRigid
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (m : MoleculeGraph input.Atom) (root : input.Atom)
    (rigid : ConstitutionallyRigidGraphAt m root)
    (hacyc : m.Acyclic) (hsimple : m.SimpleBonded) (hcharge : ConstantFormalCharge m)
    (branchAtom : Fin 4 → input.Atom)
    (hadj : ∀ i : Fin 4, m.Adj root (branchAtom i))
    (hinj : ∀ i j : Fin 4, branchAtom i = branchAtom j → i = j)
    (interface : PriorTieYieldsRootedCutBranchIso input keys m root branchAtom) :
    CertifiedLocalizedCIPInput.ConstitutionallySeparatedActualKeys input keys := by
  intro left right different
  exact priorKey_ne_of_rootedCutBranchIso_refusal input keys m root branchAtom
    hacyc hsimple hcharge rigid hadj hinj interface left right different





theorem constitutionallySeparatedActualKeys_of_constitutionallyRigid_detected
    (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (center : input.TetrahedralCenter)
    (rigid : ConstitutionallyRigid input.detectedMultiCenterMolecule
      ⟨center.1, center.2⟩)
    (hacyc : input.moleculeGraph.Acyclic)
    (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (alpha : Equiv.Perm (Fin 4))
    (interface : PriorTieYieldsRootedCutBranchIso input keys input.moleculeGraph center.1
      (fun i => input.canonicalLigandAtom center (alpha i))) :
    CertifiedLocalizedCIPInput.ConstitutionallySeparatedActualKeys input keys :=
  constitutionallySeparatedActualKeys_of_graphRigid input keys input.moleculeGraph center.1
    (constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input
      ⟨center.1, center.2⟩ rigid)
    hacyc hsimple hcharge
    (fun i => input.canonicalLigandAtom center (alpha i))
    (fun i => input.canonicalLigandAtom_adj center (alpha i))
    (fun _ _ same => alpha.injective (input.canonicalLigandAtom_injective center same))
    interface

/-! ## The final physical endpoint -/











theorem localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_physicalFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.moleculeGraph center.1)
    (hacyc : input.moleculeGraph.Acyclic) (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.canonicalLigandAtom center (alpha index)))
    (interface : FrameKeyTableIsoInterface input input.moleculeGraph center.1
      (fun i => input.canonicalLigandAtom center (alpha i)))
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      input.localizedOccurrenceRule45Descriptor? target view =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) := by
  have separated : CertifiedLocalizedCIPInput.ConstitutionallySeparatedActualKeys input
      (frame.compoundKeyAt input target view derived) :=
    constitutionallySeparatedActualKeys_of_graphRigid input
      (frame.compoundKeyAt input target view derived) input.moleculeGraph center.1
      rigid hacyc hsimple hcharge
      (fun i => input.canonicalLigandAtom center (alpha i))
      (fun i => input.canonicalLigandAtom_adj center (alpha i))
      (fun _ _ same => alpha.injective (input.canonicalLigandAtom_injective center same))
      (priorTieYieldsRootedCutBranchIso_of_frame input input.moleculeGraph center.1
        (fun i => input.canonicalLigandAtom center (alpha i)) interface
        target view frame derived ligandLink)
  exact input.localizedConstitutionalRigidFrame_descriptor_eq_chiral_of_physicalFrame
    target view frame derived (frame.compoundKeyAt input target view derived)
    (fun index => frame.compoundKeyAt_built input target view derived index)
    separated center centerReal pointsAt spatial parity writtenParity






theorem localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_detectedRigid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigid input.detectedMultiCenterMolecule
      ⟨center.1, center.2⟩)
    (hacyc : input.moleculeGraph.Acyclic) (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.canonicalLigandAtom center (alpha index)))
    (interface : FrameKeyTableIsoInterface input input.moleculeGraph center.1
      (fun i => input.canonicalLigandAtom center (alpha i)))
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      input.localizedOccurrenceRule45Descriptor? target view =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) :=
  localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_physicalFrame input target view
    frame derived center centerReal
    (constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input
      ⟨center.1, center.2⟩ rigid)
    hacyc hsimple hcharge alpha ligandLink interface pointsAt spatial parity writtenParity





















theorem referenceState_reader_eq_chiral_of_constitutionallyRigidFrame
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.certified.moleculeGraph center.1)
    (hacyc : input.certified.moleculeGraph.Acyclic)
    (hsimple : input.certified.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.canonicalLigandAtom center (alpha index)))
    (interface : FrameKeyTableIsoInterface input.certified input.certified.moleculeGraph
      center.1 (fun i => input.certified.canonicalLigandAtom center (alpha i)))
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
        some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.certified.localizedOccurrenceRule45TrackedOrder? target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      LocalizedUniversalReference.referenceState input target =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) := by
  obtain ⟨tracked, trackedComputed, pseudo, descriptorEq⟩ :=
    localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_physicalFrame
      input.certified target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target)
      frame derived center centerReal rigid hacyc hsimple hcharge alpha ligandLink
      interface pointsAt spatial parity writtenParity
  refine ⟨tracked, trackedComputed, pseudo, ?_⟩
  exact input.certified.localizedCIPModel_reader_eq_chiral_of_rule45_descriptor
    (input.certified.localizedOccurrenceRule45AuxiliarySemantics
      (LocalizedUniversalReference.carrierFuel input))
    (LocalizedUniversalReference.referenceState input)
    (LocalizedUniversalReference.referenceState_bareRule45CIPModel_of_noDoubleRecords
      input noDouble)
    target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target)
    (RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))
    rfl descriptorEq





theorem referenceState_reader_eq_chiral_of_detectedRigid
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigid input.certified.detectedMultiCenterMolecule
      ⟨center.1, center.2⟩)
    (hacyc : input.certified.moleculeGraph.Acyclic)
    (hsimple : input.certified.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.canonicalLigandAtom center (alpha index)))
    (interface : FrameKeyTableIsoInterface input.certified input.certified.moleculeGraph
      center.1 (fun i => input.certified.canonicalLigandAtom center (alpha i)))
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
        some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.certified.localizedOccurrenceRule45TrackedOrder? target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      LocalizedUniversalReference.referenceState input target =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) :=
  referenceState_reader_eq_chiral_of_constitutionallyRigidFrame input noDouble target frame
    derived center centerReal
    (constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified
      ⟨center.1, center.2⟩ rigid)
    hacyc hsimple hcharge alpha ligandLink interface pointsAt spatial parity writtenParity

/-! ## Public kernel guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedOccurrenceFourLigandFrame.compoundKeyAt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedOccurrenceFourLigandFrame.compoundKeyAt_built
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ConstitutionallySeparatedActualKeys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundKeyOffDiagonalStrict_of_priorSeparated
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceThroughRule5At?_eq_some_record
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceThroughRule5At?_eq_strictRankComparison
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_trackedOrder_of_constitutionallySeparatedActualKeys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_safeTrackedOrder_of_constitutionallySeparatedActualKeys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalRigidFrame_descriptor_eq_chiral_of_geometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalRigidFrame_descriptor_eq_chiral_of_physicalFrame
assert_kernel_only TetraStereo.OneCenter.CenterFixingGraphAutIsMultiCenter
assert_kernel_only TetraStereo.OneCenter.constitutionallyRigid_pointwise_fixed
assert_kernel_only TetraStereo.OneCenter.ConstitutionallyRigidGraphAt
assert_kernel_only TetraStereo.OneCenter.detectedMultiCenter_centerFixingGraphAutIsMultiCenter
assert_kernel_only TetraStereo.OneCenter.constitutionallyRigidGraphAt_of_constitutionallyRigid_detected
assert_kernel_only TetraStereo.OneCenter.PriorTieYieldsRootedCutBranchIso
assert_kernel_only TetraStereo.OneCenter.FrameKeyTableIsoInterface
assert_kernel_only TetraStereo.OneCenter.priorTieYieldsRootedCutBranchIso_of_frame
assert_kernel_only TetraStereo.OneCenter.priorKey_ne_of_rootedCutBranchIso_refusal
assert_kernel_only TetraStereo.OneCenter.constitutionallySeparatedActualKeys_of_graphRigid
assert_kernel_only TetraStereo.OneCenter.constitutionallySeparatedActualKeys_of_constitutionallyRigid_detected
assert_kernel_only TetraStereo.OneCenter.localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_physicalFrame
assert_kernel_only TetraStereo.OneCenter.localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_detectedRigid
assert_kernel_only TetraStereo.OneCenter.referenceState_reader_eq_chiral_of_constitutionallyRigidFrame
assert_kernel_only TetraStereo.OneCenter.referenceState_reader_eq_chiral_of_detectedRigid

end TetraStereo.OneCenter
