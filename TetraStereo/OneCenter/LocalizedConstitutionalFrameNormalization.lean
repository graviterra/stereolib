import TetraStereo.OneCenter.LocalizedOccurrenceRule45Exact
import TetraStereo.OneCenter.LocalizedEndpointSemanticCompletion
import TetraStereo.OneCenter.LocalizedCumulativeConstitutionalCoherence
import TetraStereo.OneCenter.TrackedLocalizedLigandSortCompleteness
import TetraStereo.OneCenter.CIPRationalTetrahedralParityPermutation

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput








































/-! ## Root atomic-number separation -/

/-- The atomic-number observation of one slot of an exact four-ligand occurrence frame. -/
def LocalizedOccurrenceFourLigandFrame.rootAtomicNumberAt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (index : Fin 4) : Nat :=
  input.localizedRerootCursorRootAtomicNumber (frame.cursorAt index)

/-- The four ligand branches carry pairwise distinct atomic numbers.  This is a physical
separation premise about the actual carrier, not a statement about any comparison key. -/
def ConstitutionallyAtomicNumberSeparatedFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) : Prop :=
  ∀ left right : Fin 4, left ≠ right →
    frame.rootAtomicNumberAt input left ≠ frame.rootAtomicNumberAt input right

/-- Every declaratively derived compound Rules-4a--5 key retains its cursor's atomic number as the
singleton first sphere of the constitutional Rule-1a layer. -/
theorem declarative_compoundRule45Key_constitutional_rule1a_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key)
    (derived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor key) :
    key.prior.rule4aKey.constitutional.rule1a.head? =
      some [([], input.localizedRerootCursorRootAtomicNumber cursor)] := by
  have cumulative : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor key.prior.rule4aKey := derived.1.1
  have major : input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor
      key.prior.rule4aKey.constitutional :=
    input.DeclarativeLocalizedRerootCumulativeRule45Key_constitutional_derived
      .rule4a target view fuel cursor key.prior.rule4aKey cumulative
  exact input.declarative_constitutional_rule1a_head cursor fuel
    key.prior.rule4aKey.constitutional major

/-- A lower root atomic number on the left decides the actual through-Rule-5 occurrence comparison
strictly, with `pseudo = false`, before any descriptor label is read. -/
theorem localizedConstitutionalFrame_compare_eq_lt_of_rootAtomicNumber_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (left right : Fin 4)
    (lower : frame.rootAtomicNumberAt input left < frame.rootAtomicNumberAt input right) :
    ∃ result,
      input.compareLocalizedOccurrenceThroughRule5At? target view frame left right =
        some result ∧
      result = { ordering := Ordering.lt, pseudo := false } := by
  obtain ⟨result, computed⟩ :=
    input.exists_compareLocalizedOccurrenceThroughRule5At?_of_frame
      target view frame derived left right
  refine ⟨result, computed, ?_⟩
  obtain ⟨leftKey, rightKey, keysDerived, resultEq⟩ :=
    input.compareLocalizedOccurrenceThroughRule5At?_sound
      target view frame left right result computed
  obtain ⟨leftKeyDerived, rightKeyDerived, _comparison⟩ := keysDerived
  have leftMajor : input.DeclarativeLocalizedRerootRuleMajorKey
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt left) leftKey.prior.rule4aKey.constitutional :=
    input.DeclarativeLocalizedRerootCumulativeRule45Key_constitutional_derived
      .rule4a target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt left) leftKey.prior.rule4aKey leftKeyDerived.1.1
  have rightMajor : input.DeclarativeLocalizedRerootRuleMajorKey
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt right) rightKey.prior.rule4aKey.constitutional :=
    input.DeclarativeLocalizedRerootCumulativeRule45Key_constitutional_derived
      .rule4a target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt right) rightKey.prior.rule4aKey rightKeyDerived.1.1
  have rootStrict : input.compareLocalizedRerootCursorConstitutionalRoot
      (frame.cursorAt left) (frame.cursorAt right) = Ordering.lt := by
    simpa [compareLocalizedRerootCursorConstitutionalRoot,
      LocalizedOccurrenceFourLigandFrame.rootAtomicNumberAt] using
      (compare_lt_iff_lt.mpr lower)
  have constitutionalStrict : OfficialRuleMajorKey.compare
      leftKey.prior.rule4aKey.constitutional
      rightKey.prior.rule4aKey.constitutional = Ordering.lt :=
    input.declarative_ruleMajor_compare_lt_of_root_lt
      leftMajor rightMajor rootStrict
  have cumulativeStrict : input.compareLocalizedRerootCumulativeRule45Keys
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey = Ordering.lt := by
    simp [compareLocalizedRerootCumulativeRule45Keys, compareLex,
      Ordering.byKey, constitutionalStrict]
  have compoundStrict : input.compareLocalizedRerootCompoundRule4bcKeys
      leftKey.prior rightKey.prior = Ordering.lt := by
    rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
      leftKey.prior rightKey.prior (by rw [cumulativeStrict]; decide)]
    exact cumulativeStrict
  have throughEq : input.compareLocalizedRerootCompoundThroughRule5
      leftKey rightKey = { ordering := Ordering.lt, pseudo := false } := by
    unfold compareLocalizedRerootCompoundThroughRule5
    rw [compoundStrict]
    rfl
  rw [resultEq]
  simp [localizedOccurrenceRule45ComparisonRecord, throughEq]

/-- The symmetric strict case: a larger left root atomic number decides the actual comparison
strictly, with `pseudo = false`. -/
theorem localizedConstitutionalFrame_compare_eq_gt_of_rootAtomicNumber_gt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (left right : Fin 4)
    (higher : frame.rootAtomicNumberAt input right < frame.rootAtomicNumberAt input left) :
    ∃ result,
      input.compareLocalizedOccurrenceThroughRule5At? target view frame left right =
        some result ∧
      result = { ordering := Ordering.gt, pseudo := false } := by
  obtain ⟨result, computed⟩ :=
    input.exists_compareLocalizedOccurrenceThroughRule5At?_of_frame
      target view frame derived left right
  refine ⟨result, computed, ?_⟩
  obtain ⟨leftKey, rightKey, keysDerived, resultEq⟩ :=
    input.compareLocalizedOccurrenceThroughRule5At?_sound
      target view frame left right result computed
  obtain ⟨leftKeyDerived, rightKeyDerived, _comparison⟩ := keysDerived
  have leftMajor : input.DeclarativeLocalizedRerootRuleMajorKey
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt left) leftKey.prior.rule4aKey.constitutional :=
    input.DeclarativeLocalizedRerootCumulativeRule45Key_constitutional_derived
      .rule4a target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt left) leftKey.prior.rule4aKey leftKeyDerived.1.1
  have rightMajor : input.DeclarativeLocalizedRerootRuleMajorKey
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt right) rightKey.prior.rule4aKey.constitutional :=
    input.DeclarativeLocalizedRerootCumulativeRule45Key_constitutional_derived
      .rule4a target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt right) rightKey.prior.rule4aKey rightKeyDerived.1.1
  have rootStrict : input.compareLocalizedRerootCursorConstitutionalRoot
      (frame.cursorAt left) (frame.cursorAt right) = Ordering.gt := by
    simpa [compareLocalizedRerootCursorConstitutionalRoot,
      LocalizedOccurrenceFourLigandFrame.rootAtomicNumberAt] using
      (compare_gt_iff_gt.mpr higher)
  have constitutionalStrict : OfficialRuleMajorKey.compare
      leftKey.prior.rule4aKey.constitutional
      rightKey.prior.rule4aKey.constitutional = Ordering.gt :=
    input.declarative_ruleMajor_compare_gt_of_root_gt
      leftMajor rightMajor rootStrict
  have cumulativeStrict : input.compareLocalizedRerootCumulativeRule45Keys
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey = Ordering.gt := by
    simp [compareLocalizedRerootCumulativeRule45Keys, compareLex,
      Ordering.byKey, constitutionalStrict]
  have compoundStrict : input.compareLocalizedRerootCompoundRule4bcKeys
      leftKey.prior rightKey.prior = Ordering.gt := by
    rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
      leftKey.prior rightKey.prior (by rw [cumulativeStrict]; decide)]
    exact cumulativeStrict
  have throughEq : input.compareLocalizedRerootCompoundThroughRule5
      leftKey rightKey = { ordering := Ordering.gt, pseudo := false } := by
    unfold compareLocalizedRerootCompoundThroughRule5
    rw [compoundStrict]
    rfl
  rw [resultEq]
  simp [localizedOccurrenceRule45ComparisonRecord, throughEq]

/-- Pairwise distinct neighbouring atomic numbers force the actual occurrence comparison to be
strict at every pair of distinct slots, with zero pseudo comparisons. -/
theorem localizedConstitutionalFrame_compare_strict_of_separated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (separated : input.ConstitutionallyAtomicNumberSeparatedFrame frame)
    (left right : Fin 4) (different : left ≠ right) :
    ∃ result,
      input.compareLocalizedOccurrenceThroughRule5At? target view frame left right =
        some result ∧
      result.ordering ≠ Ordering.eq ∧ result.pseudo = false := by
  rcases Nat.lt_or_gt_of_ne (separated left right different) with lower | higher
  · obtain ⟨result, computed, resultEq⟩ :=
      input.localizedConstitutionalFrame_compare_eq_lt_of_rootAtomicNumber_lt
        target view frame derived left right lower
    exact ⟨result, computed, by rw [resultEq]; decide, by rw [resultEq]⟩
  · obtain ⟨result, computed, resultEq⟩ :=
      input.localizedConstitutionalFrame_compare_eq_gt_of_rootAtomicNumber_gt
        target view frame derived left right higher
    exact ⟨result, computed, by rw [resultEq]; decide, by rw [resultEq]⟩

/-- The actual pair comparison is literally independent of the dependency view: both views return
the same optional result when the frame is atomically separated. -/
theorem localizedConstitutionalFrame_compare_state_independent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (leftView rightView : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (separated : input.ConstitutionallyAtomicNumberSeparatedFrame frame)
    (left right : Fin 4) (different : left ≠ right) :
    input.compareLocalizedOccurrenceThroughRule5At? target leftView frame left right =
      input.compareLocalizedOccurrenceThroughRule5At? target rightView frame left right := by
  rcases Nat.lt_or_gt_of_ne (separated left right different) with lower | higher
  · obtain ⟨leftResult, leftComputed, leftEq⟩ :=
      input.localizedConstitutionalFrame_compare_eq_lt_of_rootAtomicNumber_lt
        target leftView frame derived left right lower
    obtain ⟨rightResult, rightComputed, rightEq⟩ :=
      input.localizedConstitutionalFrame_compare_eq_lt_of_rootAtomicNumber_lt
        target rightView frame derived left right lower
    rw [leftComputed, rightComputed, leftEq, rightEq]
  · obtain ⟨leftResult, leftComputed, leftEq⟩ :=
      input.localizedConstitutionalFrame_compare_eq_gt_of_rootAtomicNumber_gt
        target leftView frame derived left right higher
    obtain ⟨rightResult, rightComputed, rightEq⟩ :=
      input.localizedConstitutionalFrame_compare_eq_gt_of_rootAtomicNumber_gt
        target rightView frame derived left right higher
    rw [leftComputed, rightComputed, leftEq, rightEq]

/-! ## Strict-rank callback and production sort -/

/-- Off the diagonal, the actual occurrence comparator is exactly the strict atomic-number rank
comparator. -/
theorem localizedConstitutionalFrame_compare_eq_strictRankComparison
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (separated : input.ConstitutionallyAtomicNumberSeparatedFrame frame)
    (left right : Fin 4) (different : left ≠ right) :
    input.compareLocalizedOccurrenceThroughRule5At? target view frame left right =
      strictRankComparison
        (fun index : Fin 4 => frame.rootAtomicNumberAt input index) left right := by
  rcases Nat.lt_or_gt_of_ne (separated left right different) with lower | higher
  · obtain ⟨result, computed, resultEq⟩ :=
      input.localizedConstitutionalFrame_compare_eq_lt_of_rootAtomicNumber_lt
        target view frame derived left right lower
    have compared : compare (frame.rootAtomicNumberAt input left)
        (frame.rootAtomicNumberAt input right) = Ordering.lt :=
      compare_lt_iff_lt.mpr lower
    rw [computed]
    simp [strictRankComparison, resultEq, compared]
  · obtain ⟨result, computed, resultEq⟩ :=
      input.localizedConstitutionalFrame_compare_eq_gt_of_rootAtomicNumber_gt
        target view frame derived left right higher
    have compared : compare (frame.rootAtomicNumberAt input left)
        (frame.rootAtomicNumberAt input right) = Ordering.gt :=
      compare_gt_iff_gt.mpr higher
    rw [computed]
    simp [strictRankComparison, resultEq, compared]

/-- Atomic-number separation makes the production tracked four-ligand sort total, with exact slot
preservation, strict descending atomic-number order, and zero pseudo comparisons. -/
theorem exists_localizedConstitutionalFrame_trackedOrder
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (separated : input.ConstitutionallyAtomicNumberSeparatedFrame frame) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      tracked.highestFirst.Pairwise (fun left right =>
        frame.rootAtomicNumberAt input right < frame.rootAtomicNumberAt input left) ∧
      tracked.pseudoComparisons = 0 := by
  have injective : Function.Injective
      (fun index : Fin 4 => frame.rootAtomicNumberAt input index) := by
    intro left right equal
    by_contra different
    exact separated left right different equal
  have total := sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne
    (fun index : Fin 4 => frame.rootAtomicNumberAt input index) injective
    (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
    (fun left right different =>
      input.localizedConstitutionalFrame_compare_eq_strictRankComparison
        target view frame derived separated left right different)
  simpa [localizedOccurrenceRule45TrackedOrder?] using total

/-- Atomic-number separation also makes the all-pairs coherence gate accept, so the safe order is
the same tracked order, with every earlier/later actual comparison strictly decreasing. -/
theorem exists_localizedConstitutionalFrame_safeTrackedOrder
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (separated : input.ConstitutionallyAtomicNumberSeparatedFrame frame) :
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
    input.exists_localizedConstitutionalFrame_trackedOrder
      target view frame derived separated
  have canonicalSort : input.CanonicalLocalizedOccurrenceRule45Sort
      target view frame (List.finRange 4) [] 0 tracked :=
    (input.localizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
      target view frame tracked).mp trackedComputed
  have canonicalStrict : tracked.highestFirst.Pairwise (fun left right =>
      ∃ result,
        input.CanonicalLocalizedOccurrenceThroughRule5At
          target view frame left right result ∧
        result.ordering = Ordering.gt) :=
    List.Pairwise.imp (by
      intro left right higher
      have different : left ≠ right := by
        rintro rfl
        exact Nat.lt_irrefl _ higher
      obtain ⟨result, computed, resultEq⟩ :=
        input.localizedConstitutionalFrame_compare_eq_gt_of_rootAtomicNumber_gt
          target view frame derived left right higher
      exact ⟨result,
        (input.compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
          target view frame left right result).mp computed,
        by rw [resultEq]⟩) strict
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
  have safeComputed :
      input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame = some tracked := by
    simp [safeLocalizedOccurrenceRule45TrackedOrder?, trackedComputed, coherent]
  exact ⟨tracked, safeComputed, canonicalSort, permutation,
    canonicalStrict.imp (by
      intro left right canonical
      obtain ⟨result, canonicalCompared, higher⟩ := canonical
      exact ⟨result,
        (input.compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
          target view frame left right result).mpr canonicalCompared,
        higher⟩),
    pseudo⟩

/-- The tracked order hidden behind a successful safe order. -/
theorem localizedConstitutionalFrame_trackedOrder_of_safe
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder)
    (computed : input.safeLocalizedOccurrenceRule45TrackedOrder?
      target view frame = some tracked) :
    input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked := by
  unfold safeLocalizedOccurrenceRule45TrackedOrder? at computed
  cases trackedComputed : input.localizedOccurrenceRule45TrackedOrder?
      target view frame with
  | none => simp [trackedComputed] at computed
  | some observed =>
      by_cases coherent : input.localizedOccurrenceRule45OrderCoherent?
          target view frame observed.highestFirst
      · have observedEq : observed = tracked := by
          simpa [trackedComputed, coherent] using computed
        exact congrArg some observedEq
      · simp [trackedComputed, coherent] at computed

/-! ## Descriptor normalization from physical geometry -/

/-- At an atomically separated centre whose actual priority-ordered coordinates have rational
orientation `normalizedRS`, the production Rules-4a--5 descriptor is the uppercase
`.chiral normalizedRS` label, and every comparison in its tracked history had zero pseudo weight.

The geometry hypothesis is stated for the actual tracked order produced by the executable sorter;
it therefore cannot presuppose the label it explains. -/
theorem localizedConstitutionalFrame_descriptor_eq_chiral_of_geometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (separated : input.ConstitutionallyAtomicNumberSeparatedFrame frame)
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
  obtain ⟨tracked, safeComputed, canonicalSort, permutation, canonicalStrict, pseudo⟩ :=
    input.exists_localizedConstitutionalFrame_safeTrackedOrder
      target view frame derived separated
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

/-! ## The physical-frame join: actual coordinates, actual permutation -/

/-- The `map` of a list is the `ofFn` of the same function read through `List.getElem`. -/
private theorem map_eq_ofFn_getElem {α β : Type} (list : List α) (function : α → β) :
    list.map function =
      List.ofFn (fun index : Fin list.length => function (list[index])) :=
  (List.ofFn_getElem_eq_map list function).symm

/-- **Physical frame join.**  Suppose the four actual neighbour slots of the frame have exact
physical coordinates in the original slot order (`pointsAt`), and the written-order configuration
has parity `parity` with nonzero determinant (`writtenParity`).  Then the executable tracked sort
exposes the actual priority permutation `tracked.highestFirst.map Fin.val`, and the production
Rules-4a--5 descriptor is the uppercase chiral label whose `RS` sign is the written parity adjusted
by the inversion parity of exactly that permutation.

No positions list, no sorted-point equality, and no label is supplied: the permutation is read off
the actual sort and the sorted coordinates are the actual `mapM` image of the four frame points. -/
theorem localizedConstitutionalFrame_descriptor_eq_chiral_of_physicalFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (separated : input.ConstitutionallyAtomicNumberSeparatedFrame frame)
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
    input.exists_localizedConstitutionalFrame_trackedOrder
      target view frame derived separated
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
  refine input.localizedConstitutionalFrame_descriptor_eq_chiral_of_geometry
    target view frame derived separated center centerReal
    (RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven positions)) ?_
  intro observed computed
  have observedEq : observed = tracked := by
    rw [computed] at trackedComputed
    exact Option.some.inj trackedComputed
  subst observedEq
  exact ⟨observed.highestFirst.map pointsAt,
    pointsDeclared observed.highestFirst, rational⟩

/-! ## Unique fixed-point model readback

The unique localized CIP model is indexed by occurrences and stores an optional label at each one.
Reading it at a target yields the bare Rules-4a--5 descriptor exactly when the concrete extended
evaluator agrees with that descriptor at the target.  The agreement is the explicit
single-bond/no-Rule-3 bridge; the descriptor value itself is the theorem proved above. -/

/-- A concrete localized model state reads the normalized chiral descriptor at a target, provided
the concrete evaluator is explicitly bridged to the bare Rules-4a--5 occurrence descriptor there.

`model` is any model of the occurrence system; by
`existsUnique_localizedAuxiliaryCIPModel` it is the unique complete model.  The bridge is a
hypothesis and is reported as the remaining extended-pipeline integration obligation. -/
theorem localizedCIPModel_reader_eq_chiral_of_rule45_descriptor
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem semantics).CIPModel state)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (normalizedRS : RS)
    (bridge : semantics.executableRule target
        (input.localizedDependencyView state target) =
      input.localizedOccurrenceRule45Descriptor? target view)
    (descriptorEq : input.localizedOccurrenceRule45Descriptor? target view =
      some (.chiral normalizedRS)) :
    state target = some (.chiral normalizedRS) := by
  have executableEq : state target =
      semantics.executableRule target
        (input.localizedDependencyView state target) :=
    ((semantics.derivation_executable_iff state target (state target)).1
      (model target)).symm
  rw [executableEq, bridge, descriptorEq]











theorem localizedCIPModel_reader_eq_chiral_of_physicalFrame
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem semantics).CIPModel state)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (separated : input.ConstitutionallyAtomicNumberSeparatedFrame frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity)
    (bridge : semantics.executableRule target
        (input.localizedDependencyView state target) =
      input.localizedOccurrenceRule45Descriptor? target view) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      state target = some (.chiral (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) := by
  obtain ⟨tracked, trackedComputed, pseudo, descriptorEq⟩ :=
    input.localizedConstitutionalFrame_descriptor_eq_chiral_of_physicalFrame
      target view frame derived separated center centerReal pointsAt spatial parity writtenParity
  refine ⟨tracked, trackedComputed, pseudo, ?_⟩
  exact input.localizedCIPModel_reader_eq_chiral_of_rule45_descriptor
    semantics state model target view
    (RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))
    bridge descriptorEq

/-! ## Public kernel guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedOccurrenceFourLigandFrame.rootAtomicNumberAt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ConstitutionallyAtomicNumberSeparatedFrame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarative_compoundRule45Key_constitutional_rule1a_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalFrame_compare_eq_lt_of_rootAtomicNumber_lt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalFrame_compare_eq_gt_of_rootAtomicNumber_gt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalFrame_compare_strict_of_separated
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalFrame_compare_state_independent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalFrame_compare_eq_strictRankComparison
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedConstitutionalFrame_trackedOrder
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedConstitutionalFrame_safeTrackedOrder
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalFrame_trackedOrder_of_safe
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalFrame_descriptor_eq_chiral_of_geometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalFrame_descriptor_eq_chiral_of_physicalFrame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCIPModel_reader_eq_chiral_of_rule45_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCIPModel_reader_eq_chiral_of_physicalFrame

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
