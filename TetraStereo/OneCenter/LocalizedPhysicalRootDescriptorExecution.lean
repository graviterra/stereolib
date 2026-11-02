import TetraStereo.OneCenter.LocalizedConstitutionallyRigidFrameNormalization
import TetraStereo.OneCenter.LocalizedAcyclicFourLigandFrameCompleteness
import TetraStereo.OneCenter.LocalizedTetrahedralPermutationExistence
import TetraStereo.KernelOnly

set_option autoImplicit false

noncomputable section

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput














































/-! ## The actual callback is the compound callback of the actual slot keys -/





theorem compareLocalizedOccurrenceThroughRule5At?_eq_compoundActualCompareAt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index)) :
    input.compareLocalizedOccurrenceThroughRule5At? target view frame =
      compoundActualCompareAt input keys := by
  funext left right
  exact input.compareLocalizedOccurrenceThroughRule5At?_eq_some_record
    target view frame keys built left right

/-! ## All-pairs strict coherence from the actual descending rank -/

/-- At a strictly higher computed rank, the actual occurrence callback returns an actual record
whose ordering is `gt`.  No pseudo assumption is made: only the ordering component is read, and
the equality of the two keys is off the diagonal because the strict rank inequality forbids it. -/
theorem compareLocalizedOccurrenceThroughRule5At?_exists_ordering_gt_of_rank_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index))
    (separated : input.CompoundKeyOffDiagonalStrict keys)
    {left right : Fin 4}
    (higher : input.compoundKeyRank keys right < input.compoundKeyRank keys left) :
    ∃ result,
      input.compareLocalizedOccurrenceThroughRule5At? target view frame left right = some result ∧
      result.ordering = Ordering.gt := by
  have different : left ≠ right := by
    rintro rfl
    exact Nat.lt_irrefl _ higher
  have comparisonEq : input.compareLocalizedRerootCompoundRule45Keys (keys left) (keys right) =
      compare (input.compoundKeyRank keys left) (input.compoundKeyRank keys right) := by
    have h := input.compoundKeyComparison_eq_compare_rank keys separated left right
    simpa [compoundKeyComparison, Ordering.byKey] using h
  refine ⟨localizedOccurrenceRule45ComparisonRecord
    (input.compareLocalizedRerootCompoundThroughRule5 (keys left) (keys right)), ?_, ?_⟩
  · exact input.compareLocalizedOccurrenceThroughRule5At?_eq_some_record
      target view frame keys built left right
  · show (input.compareLocalizedRerootCompoundThroughRule5 (keys left) (keys right)).ordering =
      Ordering.gt
    rw [input.compareLocalizedRerootCompoundThroughRule5_ordering, comparisonEq]
    exact compare_gt_iff_gt.mpr higher

/-- **Derived all-pairs coherence.**  If the actual tracked result exposes a list whose reverse is
sorted by the computed compound rank, then every earlier/later pair of the list is an actual
comparison with ordering `gt`, so the production coherence gate accepts.  The proof uses the actual
rank comparison and the actual compound callback equality; it never assumes `pseudo = false`. -/
theorem localizedOccurrenceRule45OrderCoherent?_eq_true_of_sortedByRank
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index))
    (separated : input.CompoundKeyOffDiagonalStrict keys)
    (tracked : TrackedLocalizedLigandOrder)
    (sorted : SortedByRank (input.compoundKeyRank keys) tracked.highestFirst.reverse) :
    input.localizedOccurrenceRule45OrderCoherent?
      target view frame tracked.highestFirst = true := by
  have pairwise : tracked.highestFirst.Pairwise (fun left right =>
      ∃ result,
        input.compareLocalizedOccurrenceThroughRule5At? target view frame left right = some result ∧
        result.ordering = Ordering.gt) :=
    List.Pairwise.imp
      (by
        intro left right higher
        exact input.compareLocalizedOccurrenceThroughRule5At?_exists_ordering_gt_of_rank_lt
          target view frame keys built separated higher)
      (List.pairwise_reverse.mp sorted)
  exact (input.localizedOccurrenceRule45OrderCoherent?_eq_true_iff
    target view frame tracked.highestFirst).mpr pairwise

/-! ## Actual tracked and safe order with the exact prior-tie pair count -/

/-- **Actual tracked sort.**  Under the three data-core comparison hypotheses, the production
tracked sort succeeds on the actual slot keys, returns a permutation of the four positions strictly
descending in the computed compound rank, and records exactly the number of distinct prior-tied
pairs.  The pseudo flags are the actual ones (they may be `true`). -/
theorem exists_actualTrackedOrder_of_actualCompound_data
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index))
    (separated : input.CompoundKeyOffDiagonalStrict keys)
    (maxTwo : input.PriorTieClassAtMostTwo keys)
    (mirror : input.PriorTieMirrorReadings keys) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      SortedByRank (input.compoundKeyRank keys) tracked.highestFirst.reverse ∧
      tracked.pseudoComparisons =
        sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys) := by
  have callbackEq :=
    input.compareLocalizedOccurrenceThroughRule5At?_eq_compoundActualCompareAt
      target view frame keys built
  obtain ⟨result, computed, permutation, sorted, pseudo⟩ :=
    sortFourLocalizedLigandsTracked_actualCompound_sourcePairFidelity
      input keys separated maxTwo mirror
  have trackedComputed : input.localizedOccurrenceRule45TrackedOrder? target view frame =
      some result := by
    rw [show input.localizedOccurrenceRule45TrackedOrder? target view frame =
        sortFourLocalizedLigandsTracked (compoundActualCompareAt input keys) from by
      simp [localizedOccurrenceRule45TrackedOrder?, callbackEq]]
    exact computed
  exact ⟨result, trackedComputed, by simpa using permutation, sorted, pseudo⟩

/-- **Actual safe sort.**  The derived all-pairs coherence makes the production safe order return
the *same* tracked result as the actual tracked sort, with every earlier/later pair an actual
comparison of ordering `gt`, and with the exact prior-tie pair count. -/
theorem exists_safeTrackedOrder_of_actualCompound_data
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index))
    (separated : input.CompoundKeyOffDiagonalStrict keys)
    (maxTwo : input.PriorTieClassAtMostTwo keys)
    (mirror : input.PriorTieMirrorReadings keys) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      tracked.highestFirst.Pairwise (fun left right =>
        ∃ result,
          input.compareLocalizedOccurrenceThroughRule5At?
            target view frame left right = some result ∧
          result.ordering = Ordering.gt) ∧
      tracked.pseudoComparisons =
        sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys) := by
  obtain ⟨tracked, trackedComputed, permutation, sorted, pseudo⟩ :=
    input.exists_actualTrackedOrder_of_actualCompound_data
      target view frame keys built separated maxTwo mirror
  have coherent :=
    input.localizedOccurrenceRule45OrderCoherent?_eq_true_of_sortedByRank
      target view frame keys built separated tracked sorted
  have pairwise : tracked.highestFirst.Pairwise (fun left right =>
      ∃ result,
        input.compareLocalizedOccurrenceThroughRule5At? target view frame left right = some result ∧
        result.ordering = Ordering.gt) :=
    List.Pairwise.imp
      (by
        intro left right higher
        exact input.compareLocalizedOccurrenceThroughRule5At?_exists_ordering_gt_of_rank_lt
          target view frame keys built separated higher)
      (List.pairwise_reverse.mp sorted)
  have safeComputed : input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame =
      some tracked := by
    simp [safeLocalizedOccurrenceRule45TrackedOrder?, trackedComputed, coherent]
  exact ⟨tracked, safeComputed, permutation, pairwise, pseudo⟩

/-- The safe result is the canonical safe order, and it carries the exact prior-tie pair count. -/
theorem exists_canonicalSafeTrackedOrder_of_actualCompound_data
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some (keys index))
    (separated : input.CompoundKeyOffDiagonalStrict keys)
    (maxTwo : input.PriorTieClassAtMostTwo keys)
    (mirror : input.PriorTieMirrorReadings keys) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      input.CanonicalSafeLocalizedOccurrenceRule45TrackedOrder target view frame tracked ∧
      tracked.pseudoComparisons =
        sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys) := by
  obtain ⟨tracked, safeComputed, _permutation, _pairwise, pseudo⟩ :=
    input.exists_safeTrackedOrder_of_actualCompound_data
      target view frame keys built separated maxTwo mirror
  exact ⟨tracked, safeComputed,
    (input.safeLocalizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
      target view frame tracked).mp safeComputed,
    pseudo⟩

/-! ## Descriptor from the actual unsorted physical coordinates -/

/-- The actual priority-ordered coordinates are declared by the actual per-slot spatial lookup. -/
theorem forall₂_spatialPoint_of_spatial
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (order : List (Fin 4)) :
    List.Forall₂
      (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
        (frame.cursorAt index) point)
      order (order.map pointsAt) := by
  induction order with
  | nil => exact List.Forall₂.nil
  | cons head tail inductionHypothesis =>
      exact List.Forall₂.cons
        ((input.localizedRerootCursorSpatialPoint?_eq_some_iff
          (frame.cursorAt head) (pointsAt head)).mp (spatial head))
        inductionHypothesis

/-- Actual real-node spatial lookup at a frame slot: when the slot's current atom is known and the
physical `spatialPointAt?` lookup succeeds at that atom, the cursor's spatial read is that point.
This is the bridge from the physical per-atom coordinate input to the cursor-level reads consumed by
the descriptor stage. -/
theorem localizedRerootCursorSpatialPoint?_eq_of_spatialPointAt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (atomAt : Fin 4 → input.Atom)
    (pointsAt : Fin 4 → CartesianPoint3)
    (current : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? = some (atomAt index))
    (physical : ∀ index : Fin 4,
      input.spatialPointAt? (atomAt index) = some (pointsAt index)) :
    ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index) := by
  intro index
  simp [localizedRerootCursorSpatialPoint?, current index, physical index]

/-- **Actual descriptor execution.**  With actual slot keys and actual nondegenerate coordinates at
the frame slots, the production descriptor returns the pseudo-aware classification
`classifyTetrahedralRSPseudo normalizedRS tracked.pseudoComparisons`, where the raw `RS` sign is a
rational descriptor of the actual priority-ordered point list and `normalizedRS` is obtained from
the actual sort permutation plus nonzero oriented volume.  The tracked pseudo count is exactly the
prior-tie pair count. -/
theorem localizedOccurrenceRule45Descriptor?_eq_classify_of_actualGeometry
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
    (separated : input.CompoundKeyOffDiagonalStrict keys)
    (maxTwo : input.PriorTieClassAtMostTwo keys)
    (mirror : input.PriorTieMirrorReadings keys)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0) :
    ∃ (tracked : TrackedLocalizedLigandOrder) (normalizedRS : RS),
      input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      input.localizedOccurrenceRule45Descriptor? target view =
        some (classifyTetrahedralRSPseudo normalizedRS tracked.pseudoComparisons) ∧
      RationalTetrahedralDescriptor (tracked.highestFirst.map pointsAt) normalizedRS ∧
      tracked.pseudoComparisons =
        sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys) := by
  obtain ⟨tracked, safeComputed, canonicalSafe, pseudo⟩ :=
    input.exists_canonicalSafeTrackedOrder_of_actualCompound_data
      target view frame keys built separated maxTwo mirror
  obtain ⟨normalizedRS, rational⟩ :=
    rationalTetrahedralDescriptor_exists_of_permutation pointsAt tracked.highestFirst
      canonicalSafe.2.1 nonzero
  have pointsDeclared : List.Forall₂
      (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
        (frame.cursorAt index) point)
      tracked.highestFirst (tracked.highestFirst.map pointsAt) :=
    input.forall₂_spatialPoint_of_spatial frame pointsAt spatial tracked.highestFirst
  let evidence : input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel :=
    { center := center, frame := frame, tracked := tracked,
      points := tracked.highestFirst.map pointsAt }
  have canonicalEvidence :
      input.CanonicalLocalizedOccurrenceRule45SpatialEvidence target view evidence :=
    ⟨centerReal, derived, canonicalSafe, pointsDeclared⟩
  have canonicalDescriptor :
      input.CanonicalLocalizedOccurrenceRule45Descriptor target view
        (classifyTetrahedralRSPseudo normalizedRS tracked.pseudoComparisons) :=
    ⟨evidence, normalizedRS, canonicalEvidence, rational, rfl⟩
  have descriptorEq : input.localizedOccurrenceRule45Descriptor? target view =
      some (classifyTetrahedralRSPseudo normalizedRS tracked.pseudoComparisons) :=
    (input.localizedOccurrenceRule45Descriptor?_eq_some_iff_canonical
      target view _).mpr canonicalDescriptor
  exact ⟨tracked, normalizedRS, safeComputed, descriptorEq, rational, pseudo⟩

/-- **Lowercase equivalence.**  The executed pseudo-aware classification is lowercase exactly when
the exact distinct-prior-tie pair count is one.  This is the general pseudo (`pseudo = true`) form of
the P-92.1.1 condition; the ordinary chiral branch is count zero. -/
theorem localizedOccurrenceRule45Descriptor?_eq_classify_and_isLowercase_iff
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
    (separated : input.CompoundKeyOffDiagonalStrict keys)
    (maxTwo : input.PriorTieClassAtMostTwo keys)
    (mirror : input.PriorTieMirrorReadings keys)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0) :
    ∃ (tracked : TrackedLocalizedLigandOrder) (normalizedRS : RS),
      input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      input.localizedOccurrenceRule45Descriptor? target view =
        some (classifyTetrahedralRSPseudo normalizedRS
          (sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys))) ∧
      (LocalizedTetrahedralRSPseudoDescriptor.IsLowercase
        (classifyTetrahedralRSPseudo normalizedRS
          (sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys))) ↔
        sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys) = 1) ∧
      RationalTetrahedralDescriptor (tracked.highestFirst.map pointsAt) normalizedRS := by
  obtain ⟨tracked, normalizedRS, safeComputed, descriptorEq, rational, pseudo⟩ :=
    input.localizedOccurrenceRule45Descriptor?_eq_classify_of_actualGeometry
      target view frame derived keys built separated maxTwo mirror
      center centerReal pointsAt spatial nonzero
  have descriptorCount : input.localizedOccurrenceRule45Descriptor? target view =
      some (classifyTetrahedralRSPseudo normalizedRS
        (sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys))) := by
    rw [descriptorEq, pseudo]
  exact ⟨tracked, normalizedRS, safeComputed, descriptorCount,
    isLowercase_classify_iff normalizedRS
      (sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys)),
    rational⟩






theorem referenceState_eq_classify_of_actualGeometry
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (keys : Fin 4 → input.certified.LocalizedRerootCompoundRule45Key)
    (built : ∀ index : Fin 4,
      input.certified.buildLocalizedRerootCompoundRule45Key? target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt index) = some (keys index))
    (separated : input.certified.CompoundKeyOffDiagonalStrict keys)
    (maxTwo : input.certified.PriorTieClassAtMostTwo keys)
    (mirror : input.certified.PriorTieMirrorReadings keys)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint?
        (frame.cursorAt index) = some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0) :
    ∃ (tracked : TrackedLocalizedLigandOrder) (normalizedRS : RS),
      input.certified.safeLocalizedOccurrenceRule45TrackedOrder? target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) frame = some tracked ∧
      LocalizedUniversalReference.referenceState input target =
        some (classifyTetrahedralRSPseudo normalizedRS tracked.pseudoComparisons) ∧
      RationalTetrahedralDescriptor (tracked.highestFirst.map pointsAt) normalizedRS ∧
      tracked.pseudoComparisons =
        sourceEnantiomorphicPairCount (compoundPriorTieRelation input.certified keys) := by
  obtain ⟨tracked, normalizedRS, safeComputed, descriptorEq, rational, pseudo⟩ :=
    input.certified.localizedOccurrenceRule45Descriptor?_eq_classify_of_actualGeometry
      target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target)
      frame derived keys built separated maxTwo mirror center centerReal pointsAt spatial nonzero
  refine ⟨tracked, normalizedRS, safeComputed, ?_, rational, pseudo⟩
  rw [LocalizedUniversalReference.referenceState_eq_bareRule45Descriptor_of_noDoubleRecords
    input noDouble target]
  exact descriptorEq

/-! ## Frame-invariant physical data for the detected-root endpoint -/






def ActualCompoundKeyData
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  ∀ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame),
    input.localizedOccurrenceFourLigandFrame? target = some frame →
      input.CompoundKeyOffDiagonalStrict
        (frame.compoundKeyAt input target view derived) ∧
      input.PriorTieClassAtMostTwo
        (frame.compoundKeyAt input target view derived) ∧
      input.PriorTieMirrorReadings
        (frame.compoundKeyAt input target view derived)

/-- Actual real-node coordinate availability at every actual successful frame: the four slot
lookups return concrete unsorted points, and the oriented volume of the written frame order is
nonzero.  This is the genuine physical geometry input; no sorted coordinate list or sorted volume
is mentioned. -/
def ActualFrameSpatialCoordinates
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) : Prop :=
  ∀ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel),
    input.localizedOccurrenceFourLigandFrame? target = some frame →
      ∃ pointsAt : Fin 4 → CartesianPoint3,
        (∀ index : Fin 4,
          input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
            some (pointsAt index)) ∧
        CartesianPoint3.orientedVolume (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0

/-- The physical real-node form of the geometry input: at every actual successful frame there are
actual current atoms and actual `spatialPointAt?` reads at those atoms, and the oriented volume of
the written frame order is nonzero.  This mentions only the physical per-atom coordinate lookup, not
cursor-level reads, sorted coordinates or a sorted volume. -/
def ActualFrameRealNodeCoordinates
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) : Prop :=
  ∀ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel),
    input.localizedOccurrenceFourLigandFrame? target = some frame →
      ∃ (atomAt : Fin 4 → input.Atom) (pointsAt : Fin 4 → CartesianPoint3),
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? = some (atomAt index)) ∧
        (∀ index : Fin 4,
          input.spatialPointAt? (atomAt index) = some (pointsAt index)) ∧
        CartesianPoint3.orientedVolume (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0

/-- The real-node physical coordinate input derives the cursor-level spatial reads used by the
descriptor stage, through the actual lookup equation at each frame slot. -/
theorem actualFrameSpatialCoordinates_of_realNode
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (realNode : input.ActualFrameRealNodeCoordinates target) :
    input.ActualFrameSpatialCoordinates target := by
  intro frame frameComputed
  obtain ⟨atomAt, pointsAt, current, physical, nonzero⟩ := realNode frame frameComputed
  exact ⟨pointsAt,
    input.localizedRerootCursorSpatialPoint?_eq_of_spatialPointAt
      frame atomAt pointsAt current physical,
    nonzero⟩





theorem actualCompoundKeyData_of_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (separated : input.CompoundKeyOffDiagonalStrict
      (frame.compoundKeyAt input target view derived))
    (maxTwo : input.PriorTieClassAtMostTwo
      (frame.compoundKeyAt input target view derived))
    (mirror : input.PriorTieMirrorReadings
      (frame.compoundKeyAt input target view derived)) :
    input.ActualCompoundKeyData target view := by
  intro other otherDerived otherComputed
  have frameEq : other = frame := Option.some.inj (otherComputed.symm.trans frameComputed)
  subst frameEq
  exact ⟨separated, maxTwo, mirror⟩

/-- Real-node coordinate data proved at one actual frame lift to the frame-invariant predicate, for
the same uniqueness reason. -/
theorem actualFrameRealNodeCoordinates_of_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (atomAt : Fin 4 → input.Atom)
    (pointsAt : Fin 4 → CartesianPoint3)
    (current : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? = some (atomAt index))
    (physical : ∀ index : Fin 4,
      input.spatialPointAt? (atomAt index) = some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0) :
    input.ActualFrameRealNodeCoordinates target := by
  intro other otherComputed
  have frameEq : other = frame := Option.some.inj (otherComputed.symm.trans frameComputed)
  subst frameEq
  exact ⟨atomAt, pointsAt, current, physical, nonzero⟩











theorem exists_descriptor_classify_of_detectedPhysicalRoot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {oAtom : input.Atom}
    (oObserved : target.1.node.current? = some oAtom)
    (center : input.detectedMultiCenterMolecule.Center)
    (centerEq : center.1 = oAtom)
    (centerReal : input.RealTetrahedralCenterNode target.1.node ⟨center.1, center.2⟩)
    (data : input.ActualCompoundKeyData target view)
    (realNode : input.ActualFrameRealNodeCoordinates target) :
    ∃ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
      (alpha : Equiv.Perm (Fin 4))
      (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
      (tracked : TrackedLocalizedLigandOrder) (normalizedRS : RS)
      (pointsAt : Fin 4 → CartesianPoint3),
      input.localizedOccurrenceFourLigandFrame? target = some frame ∧
      (∀ index : Fin 4,
        (frame.cursorAt index).occurrence.1.node.current? =
          some (input.detectedMultiCenterMolecule.ligandAtomAt center (alpha index))) ∧
      input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      input.localizedOccurrenceRule45Descriptor? target view =
        some (classifyTetrahedralRSPseudo normalizedRS
          (sourceEnantiomorphicPairCount
            (compoundPriorTieRelation input
              (frame.compoundKeyAt input target view derived)))) ∧
      (LocalizedTetrahedralRSPseudoDescriptor.IsLowercase
        (classifyTetrahedralRSPseudo normalizedRS
          (sourceEnantiomorphicPairCount
            (compoundPriorTieRelation input
              (frame.compoundKeyAt input target view derived)))) ↔
        sourceEnantiomorphicPairCount
          (compoundPriorTieRelation input
            (frame.compoundKeyAt input target view derived)) = 1) ∧
      RationalTetrahedralDescriptor (tracked.highestFirst.map pointsAt) normalizedRS ∧
      (∀ index : Fin 4,
        input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index)) ∧
      (∀ index : Fin 4,
        input.spatialPointAt?
          (input.detectedMultiCenterMolecule.ligandAtomAt center (alpha index)) =
            some (pointsAt index)) ∧
      CartesianPoint3.orientedVolume (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0 := by
  obtain ⟨frame, alpha, frameComputed, ligandLink⟩ :=
    input.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
      singleBonded acyclic enough target oObserved center centerEq
  let derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mp frameComputed
  obtain ⟨separated, maxTwo, mirror⟩ := data frame derived frameComputed
  obtain ⟨atomAt, pointsAt, current, physical, nonzero⟩ := realNode frame frameComputed
  have spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index) :=
    input.localizedRerootCursorSpatialPoint?_eq_of_spatialPointAt
      frame atomAt pointsAt current physical
  obtain ⟨tracked, normalizedRS, safeComputed, descriptorEq, rational, pseudo⟩ :=
    input.localizedOccurrenceRule45Descriptor?_eq_classify_of_actualGeometry
      target view frame derived
      (frame.compoundKeyAt input target view derived)
      (fun index => frame.compoundKeyAt_built input target view derived index)
      separated maxTwo mirror ⟨center.1, center.2⟩ centerReal pointsAt spatial nonzero
  have descriptorCount : input.localizedOccurrenceRule45Descriptor? target view =
      some (classifyTetrahedralRSPseudo normalizedRS
        (sourceEnantiomorphicPairCount
          (compoundPriorTieRelation input
            (frame.compoundKeyAt input target view derived)))) := by
    rw [descriptorEq, pseudo]
  exact ⟨frame, alpha, derived, tracked, normalizedRS, pointsAt, frameComputed, ligandLink,
    safeComputed, descriptorCount,
    isLowercase_classify_iff normalizedRS
      (sourceEnantiomorphicPairCount
        (compoundPriorTieRelation input
          (frame.compoundKeyAt input target view derived))),
    rational, spatial,
    (by
      intro index
      have atomEq : atomAt index =
          input.detectedMultiCenterMolecule.ligandAtomAt center (alpha index) :=
        Option.some.inj ((current index).symm.trans (ligandLink index))
      rw [← atomEq]
      exact physical index),
    nonzero⟩




theorem exists_referenceState_classify_of_detectedPhysicalRoot
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input)
    {oAtom : input.certified.Atom}
    (oObserved : target.1.node.current? = some oAtom)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (centerEq : center.1 = oAtom)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node
      ⟨center.1, center.2⟩)
    (data : input.certified.ActualCompoundKeyData target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target))
    (realNode : input.certified.ActualFrameRealNodeCoordinates target) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4))
      (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
      (tracked : TrackedLocalizedLigandOrder) (normalizedRS : RS)
      (pointsAt : Fin 4 → CartesianPoint3),
      input.certified.localizedOccurrenceFourLigandFrame? target = some frame ∧
      (∀ index : Fin 4,
        (frame.cursorAt index).occurrence.1.node.current? =
          some (input.certified.detectedMultiCenterMolecule.ligandAtomAt center (alpha index))) ∧
      input.certified.safeLocalizedOccurrenceRule45TrackedOrder? target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) frame = some tracked ∧
      LocalizedUniversalReference.referenceState input target =
        some (classifyTetrahedralRSPseudo normalizedRS
          (sourceEnantiomorphicPairCount
            (compoundPriorTieRelation input.certified
              (frame.compoundKeyAt input.certified target
                (input.certified.localizedDependencyView
                  (LocalizedUniversalReference.referenceState input) target) derived)))) ∧
      RationalTetrahedralDescriptor (tracked.highestFirst.map pointsAt) normalizedRS ∧
      (∀ index : Fin 4,
        input.certified.localizedRerootCursorSpatialPoint?
          (frame.cursorAt index) = some (pointsAt index)) ∧
      (∀ index : Fin 4,
        input.certified.spatialPointAt?
          (input.certified.detectedMultiCenterMolecule.ligandAtomAt center (alpha index)) =
            some (pointsAt index)) ∧
      CartesianPoint3.orientedVolume (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0 := by
  obtain ⟨frame, alpha, frameComputed, ligandLink⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
      singleBonded acyclic enough target oObserved center centerEq
  let derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame :=
    (input.certified.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mp frameComputed
  let referenceView :=
    input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target
  obtain ⟨separated, maxTwo, mirror⟩ := data frame derived frameComputed
  obtain ⟨atomAt, pointsAt, current, physical, nonzero⟩ := realNode frame frameComputed
  have spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint?
        (frame.cursorAt index) = some (pointsAt index) :=
    input.certified.localizedRerootCursorSpatialPoint?_eq_of_spatialPointAt
      frame atomAt pointsAt current physical
  obtain ⟨tracked, normalizedRS, safeComputed, descriptorEq, rational, pseudo⟩ :=
    input.certified.localizedOccurrenceRule45Descriptor?_eq_classify_of_actualGeometry
      target referenceView frame derived
      (frame.compoundKeyAt input.certified target referenceView derived)
      (fun index => frame.compoundKeyAt_built input.certified target referenceView derived index)
      separated maxTwo mirror ⟨center.1, center.2⟩ centerReal pointsAt spatial nonzero
  have readback :=
    LocalizedUniversalReference.referenceState_eq_bareRule45Descriptor_of_noDoubleRecords
      input noDouble target
  have descriptorCount : LocalizedUniversalReference.referenceState input target =
      some (classifyTetrahedralRSPseudo normalizedRS
        (sourceEnantiomorphicPairCount
          (compoundPriorTieRelation input.certified
            (frame.compoundKeyAt input.certified target referenceView derived)))) := by
    rw [readback, descriptorEq, pseudo]
  exact ⟨frame, alpha, derived, tracked, normalizedRS, pointsAt, frameComputed, ligandLink,
    safeComputed, descriptorCount, rational, spatial,
    (by
      intro index
      have atomEq : atomAt index =
          input.certified.detectedMultiCenterMolecule.ligandAtomAt center (alpha index) :=
        Option.some.inj ((current index).symm.trans (ligandLink index))
      rw [← atomEq]
      exact physical index),
    nonzero⟩

end CertifiedLocalizedCIPInput

/-! ## Public kernel guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceThroughRule5At?_eq_compoundActualCompareAt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceThroughRule5At?_exists_ordering_gt_of_rank_lt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45OrderCoherent?_eq_true_of_sortedByRank
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_actualTrackedOrder_of_actualCompound_data
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_safeTrackedOrder_of_actualCompound_data
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_canonicalSafeTrackedOrder_of_actualCompound_data
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.forall₂_spatialPoint_of_spatial
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorSpatialPoint?_eq_of_spatialPointAt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45Descriptor?_eq_classify_of_actualGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45Descriptor?_eq_classify_and_isLowercase_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.referenceState_eq_classify_of_actualGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualCompoundKeyData
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualFrameSpatialCoordinates
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualFrameRealNodeCoordinates
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrameSpatialCoordinates_of_realNode
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualCompoundKeyData_of_frame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrameRealNodeCoordinates_of_frame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_descriptor_classify_of_detectedPhysicalRoot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_referenceState_classify_of_detectedPhysicalRoot

end TetraStereo.OneCenter
