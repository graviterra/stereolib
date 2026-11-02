import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through5FixedPoint
import TetraStereo.OneCenter.PublicParametricCompoundRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput





























































/-! ## The frame builder with an arbitrary reader -/

/-- Public Rule-3--5 key frame under an arbitrary total label reader.  The Rule-3 pass is exactly
the shipped reader-free `buildAromaticCanonicalRule3CanonicalKeyFrame?`; only the direct compound
`List.mapM` is compiled by the existing parametric `...WithRead?` builder. -/
noncomputable def buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    Option (source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let rule3Frame ← source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel cursors
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← cursors.mapM
      (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead? read fuel)
    if rule45Length : rule45Keys.length = 4 then
      some { rule3Frame, rule3Length, rule45Keys, rule45Length }
    else none
  else none

private theorem mapM_compoundWithRead_eq_of_dependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ (fuel : Nat) (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)),
      cursors.mapM
          (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
            (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor) fuel) =
        cursors.mapM
          (source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel)
  | fuel, [] => rfl
  | fuel, cursor :: cursors => by
      rw [List.mapM_cons, List.mapM_cons,
        source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
          target view fuel cursor,
        mapM_compoundWithRead_eq_of_dependencyLabel source target view fuel cursors]

/-- **Unconditional exact restricted specialization.**  Substituting the shipped dependency
reader for the arbitrary callback reproduces the shipped public Rule-3--5 frame builder literally,
for every fuel and every cursor list. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_eq_rule3Through5KeyFrame?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ (fuel : Nat) (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)),
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
        fuel cursors =
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        target view fuel cursors := by
  intro fuel cursors
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
    buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
  rw [mapM_compoundWithRead_eq_of_dependencyLabel source target view fuel cursors]

/-- The Rule-3 component of a successful arbitrary-reader frame is exactly the shipped
reader-free canonical frame.  In particular the raw keys, the physical-topology resolution and
the common exclusion set are unchanged. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      read fuel cursors = some frame) :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel cursors =
      some frame.rule3Frame := by
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead? at computed
  cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      fuel cursors with
  | none => simp [rule3Computed] at computed
  | some rule3Frame =>
      by_cases rule3Length : rule3Frame.keys.length = 4
      · cases rule45Computed : cursors.mapM
            (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
              read fuel) with
        | none => simp [rule3Computed, rule3Length, rule45Computed] at computed
        | some rule45Keys =>
            by_cases rule45Length : rule45Keys.length = 4
            · simp [rule3Computed, rule3Length, rule45Computed,
                rule45Length] at computed
              subst frame
              simpa using rule3Computed
            · simp [rule3Computed, rule3Length, rule45Computed,
                rule45Length] at computed
      · simp [rule3Computed, rule3Length] at computed

/-- The Rule-3 component of an arbitrary-reader frame is declaratively the shipped
reader-free canonical frame. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      read fuel cursors = some frame) :
    source.DeclarativeAromaticCanonicalRule3CanonicalKeyFrame
      fuel cursors frame.rule3Frame :=
  source.buildAromaticCanonicalRule3CanonicalKeyFrame?_sound fuel cursors
    frame.rule3Frame
    (source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame
      read fuel cursors frame computed)

/-- Under the shipped restricted reader the arbitrary-reader frame satisfies the shipped
declarative frame predicate.  This is derived from the exact specialization above; no semantic
fact about an arbitrary reader is assumed. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_sound_of_dependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
      fuel cursors = some frame) :
    source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyFrame
      target view fuel cursors frame := by
  rw [source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_eq_rule3Through5KeyFrame?
    target view] at computed
  exact source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound
    target view fuel cursors frame computed

/-! ## Spatial evidence with an arbitrary reader -/

/-- Public Rule-3--5 spatial evidence under an arbitrary total label reader.  Center and base
perception, the tracked sorter, the pseudo-comparison count and the exact rational point read are
the shipped routines; only the frame builder inside is reader-parametric. -/
noncomputable def aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (ruleFuel : Nat) :
    Option (source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  let base ← source.aromaticCanonicalOccurrenceFourLigandFrame? target
  let keys ← source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
    read ruleFuel base.roots
  let tracked ← source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys
  let points ← tracked.highestFirst.mapM fun index =>
    source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }

/-- **Exact restricted specialization of spatial evidence**, for every rule fuel. -/
theorem aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?_eq_spatialEvidence?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ ruleFuel : Nat,
      source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
        target ruleFuel =
      source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
        target view ruleFuel := by
  intro ruleFuel
  unfold aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?
    aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
  simp only [source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_eq_rule3Through5KeyFrame?
    target view ruleFuel]

/-- Under the shipped restricted reader the arbitrary-reader evidence satisfies the shipped
declarative spatial-evidence predicate. -/
theorem aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?_sound_of_dependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat)
    (evidence : source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?
      (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
      target ruleFuel = some evidence) :
    source.DeclarativeAromaticCanonicalOccurrenceRule3Through5SpatialEvidence
      target view ruleFuel evidence := by
  rw [source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?_eq_spatialEvidence?
    target view ruleFuel] at computed
  exact source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?_sound
    target view ruleFuel evidence computed

/-! ## Descriptor with an arbitrary reader -/

/-- Public Rule-3--5 descriptor under an arbitrary total label reader.  The raw geometric
descriptor and the pseudoasymmetric classification are exactly the shipped routines. -/
noncomputable def aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (ruleFuel : Nat) : Option AromaticCanonicalAuxiliaryLabel := do
  let evidence ← source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?
    read target ruleFuel
  let raw ← CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- **Exact restricted specialization of the descriptor**, for every rule fuel. -/
theorem aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_eq_descriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ ruleFuel : Nat,
      source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
        target ruleFuel =
      source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        target view ruleFuel := by
  intro ruleFuel
  unfold aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
    aromaticCanonicalOccurrenceRule3Through5Descriptor?
  rw [source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?_eq_spatialEvidence?
    target view ruleFuel]

/-- Under the shipped restricted reader a successful arbitrary-reader descriptor is exactly one
canonical source occurrence descriptor. -/
theorem aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_eq_some_iff_canonical_of_dependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) (descriptor : AromaticCanonicalAuxiliaryLabel) :
    source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
        target ruleFuel = some descriptor ↔
      source.CanonicalAromaticCanonicalOccurrenceRule3Through5Descriptor
        target view ruleFuel descriptor := by
  rw [source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_eq_descriptor?
    target view ruleFuel]
  exact source.aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
    target view ruleFuel descriptor

/-! ## The sibling frame seam

The seam isolates exactly what a public outward/parent-insulation/whole-state comparison may
supply without proving equality of complete compound keys:

* the Rule-3 frame is literally shared, so the reader-free Rule-3 raw/rebuilt keys, topology
  resolution and exclusion set coincide;
* for every pair of ligand indices, the two frames' actual compound Rules-4a--5 keys have the
  same `ConstitutionalRule5Comparison` record, i.e. both the ordering and the pseudoasymmetry
  flag agree.

The compound keys themselves may differ arbitrarily in any field that does not change this
record: in particular the parent-side key is allowed to differ from the outward/whole-state key.
-/

/-- Sibling interface for two actual Rule-3--5 frames.  Both fields are genuine premises; no
comparison or descriptor equality is stored as a hypothesis. -/
structure AromaticCanonicalOccurrenceRule3Through5FrameSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    Prop where
  /-- The actual Rule-3 canonical frame is literally shared. -/
  sharedRule3Frame : left.rule3Frame = right.rule3Frame
  /-- Pairwise comparator results, retaining ordering and pseudoasymmetry, for the direct
  compound Rules-4a--5 keys at the same ligand indices. -/
  rule45PairComparisons : ∀ (leftIndex rightIndex : Fin 4),
    source.compareAromaticCanonicalRerootCompoundThroughRule5
        (left.keyAt leftIndex).rule45 (left.keyAt rightIndex).rule45 =
      source.compareAromaticCanonicalRerootCompoundThroughRule5
        (right.keyAt leftIndex).rule45 (right.keyAt rightIndex).rule45

/-- Constructor from the two observable comparison components.  Siblings that prove the ordering
and the pseudoasymmetry flag separately can build the record-level seam directly. -/
theorem AromaticCanonicalOccurrenceRule3Through5FrameSeam.of_ordering_pseudo
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (shared : left.rule3Frame = right.rule3Frame)
    (orderingEq : ∀ (leftIndex rightIndex : Fin 4),
      (source.compareAromaticCanonicalRerootCompoundThroughRule5
        (left.keyAt leftIndex).rule45 (left.keyAt rightIndex).rule45).ordering =
      (source.compareAromaticCanonicalRerootCompoundThroughRule5
        (right.keyAt leftIndex).rule45 (right.keyAt rightIndex).rule45).ordering)
    (pseudoEq : ∀ (leftIndex rightIndex : Fin 4),
      (source.compareAromaticCanonicalRerootCompoundThroughRule5
        (left.keyAt leftIndex).rule45 (left.keyAt rightIndex).rule45).pseudo =
      (source.compareAromaticCanonicalRerootCompoundThroughRule5
        (right.keyAt leftIndex).rule45 (right.keyAt rightIndex).rule45).pseudo) :
    source.AromaticCanonicalOccurrenceRule3Through5FrameSeam left right := by
  refine ⟨shared, fun leftIndex rightIndex => ?_⟩
  have hOrd := orderingEq leftIndex rightIndex
  have hPse := pseudoEq leftIndex rightIndex
  cases hLeft : source.compareAromaticCanonicalRerootCompoundThroughRule5
      (left.keyAt leftIndex).rule45 (left.keyAt rightIndex).rule45
  cases hRight : source.compareAromaticCanonicalRerootCompoundThroughRule5
      (right.keyAt leftIndex).rule45 (right.keyAt rightIndex).rule45
  simp_all only [ConstitutionalRule5Comparison.ordering,
    ConstitutionalRule5Comparison.pseudo]

/-- Equal shared Rule-3 frames give pointwise equal Rule-3 components of the four indexed
keys. -/
theorem AromaticCanonicalOccurrenceRule3Through5KeyFrame.keyAt_rule3_eq_of_rule3Frame_eq
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (shared : left.rule3Frame = right.rule3Frame) (index : Fin 4) :
    (left.keyAt index).rule3 = (right.keyAt index).rule3 := by
  simp [AromaticCanonicalOccurrenceRule3Through5KeyFrame.keyAt, shared]

/-- Actual frame comparison transport from the seam.  The result is the complete
`ConstitutionalRule5Comparison` record, so ordering and pseudoasymmetry transport together. -/
theorem compareAromaticCanonicalOccurrenceRule3Through5At_eq_of_frameSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameSeam left right)
    (leftIndex rightIndex : Fin 4) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At left leftIndex rightIndex =
      source.compareAromaticCanonicalOccurrenceRule3Through5At right
        leftIndex rightIndex := by
  unfold compareAromaticCanonicalOccurrenceRule3Through5At
  dsimp only
  rw [AromaticCanonicalOccurrenceRule3Through5KeyFrame.keyAt_rule3_eq_of_rule3Frame_eq
      seam.sharedRule3Frame leftIndex,
    AromaticCanonicalOccurrenceRule3Through5KeyFrame.keyAt_rule3_eq_of_rule3Frame_eq
      seam.sharedRule3Frame rightIndex]
  generalize rule3Comparison :
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (right.keyAt leftIndex).rule3 (right.keyAt rightIndex).rule3 = outcome
  cases outcome <;>
    simp [rule3Comparison, seam.rule45PairComparisons leftIndex rightIndex]

/-- Ordering component of actual frame comparison transport. -/
theorem compareAromaticCanonicalOccurrenceRule3Through5At_ordering_eq_of_frameSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameSeam left right)
    (leftIndex rightIndex : Fin 4) :
    (source.compareAromaticCanonicalOccurrenceRule3Through5At
        left leftIndex rightIndex).ordering =
      (source.compareAromaticCanonicalOccurrenceRule3Through5At
        right leftIndex rightIndex).ordering :=
  congrArg ConstitutionalRule5Comparison.ordering
    (source.compareAromaticCanonicalOccurrenceRule3Through5At_eq_of_frameSeam
      seam leftIndex rightIndex)

/-- Pseudoasymmetry component of actual frame comparison transport. -/
theorem compareAromaticCanonicalOccurrenceRule3Through5At_pseudo_eq_of_frameSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameSeam left right)
    (leftIndex rightIndex : Fin 4) :
    (source.compareAromaticCanonicalOccurrenceRule3Through5At
        left leftIndex rightIndex).pseudo =
      (source.compareAromaticCanonicalOccurrenceRule3Through5At
        right leftIndex rightIndex).pseudo :=
  congrArg ConstitutionalRule5Comparison.pseudo
    (source.compareAromaticCanonicalOccurrenceRule3Through5At_eq_of_frameSeam
      seam leftIndex rightIndex)

/-- Ordering transport for the complete key comparator at the same indexed keys.  This is the
form consumed when a sibling compares individual ligand keys rather than the whole frame. -/
theorem compareAromaticCanonicalOccurrenceRule3Through5Keys_eq_of_frameSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameSeam left right)
    (leftIndex rightIndex : Fin 4) :
    source.compareAromaticCanonicalOccurrenceRule3Through5Keys
        (left.keyAt leftIndex) (left.keyAt rightIndex) =
      source.compareAromaticCanonicalOccurrenceRule3Through5Keys
        (right.keyAt leftIndex) (right.keyAt rightIndex) := by
  rw [← source.compareAromaticCanonicalOccurrenceRule3Through5At_ordering
      left leftIndex rightIndex,
    ← source.compareAromaticCanonicalOccurrenceRule3Through5At_ordering
      right leftIndex rightIndex]
  exact source.compareAromaticCanonicalOccurrenceRule3Through5At_ordering_eq_of_frameSeam
    seam leftIndex rightIndex

/-- The actual safe tracked sorter transports along the seam.  Both the highest-first ligand
order and the exact pseudo-comparison count are therefore unchanged. -/
theorem safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_frameSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameSeam left right) :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? left =
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? right :=
  source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_compare
    right left
    (fun leftIndex rightIndex =>
      source.compareAromaticCanonicalOccurrenceRule3Through5At_eq_of_frameSeam
        seam leftIndex rightIndex)

/-- If both safe tracked sorts succeed, the seam forces the exact pseudo-comparison counts to
agree. -/
theorem safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_pseudoComparisons_eq_of_frameSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameSeam left right)
    {leftTracked rightTracked : TrackedLocalizedLigandOrder}
    (leftComputed :
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? left =
        some leftTracked)
    (rightComputed :
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? right =
        some rightTracked) :
    leftTracked.pseudoComparisons = rightTracked.pseudoComparisons := by
  have same :=
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_frameSeam seam
  rw [leftComputed, rightComputed, Option.some.injEq] at same
  rw [same]

/-! ## Descriptor seams -/

/-- The descriptor routine applied to one completed spatial-evidence record.  This is the exact
`descriptorOfPriorityOrderedPoints?` plus `classifyTetrahedralRSPseudo` composition used by the
shipped descriptor. -/
noncomputable def aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (evidence : source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel) :
    Option AromaticCanonicalAuxiliaryLabel := do
  let raw ← CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- The shipped descriptor is the evidence builder followed by the evidence descriptor. -/
theorem aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_evidenceDescriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) :
    source.aromaticCanonicalOccurrenceRule3Through5Descriptor? target view ruleFuel =
      (source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
        target view ruleFuel).bind
        (source.aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor
          (carrierFuel := carrierFuel)) :=
  rfl

/-- Descriptor transport from the two descriptor-visible data: exact point order and the
pseudo-comparison count. -/
theorem aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor_eq_of_points_pseudo
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel}
    (pointsEq : left.points = right.points)
    (pseudoEq : left.tracked.pseudoComparisons = right.tracked.pseudoComparisons) :
    source.aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor left =
      source.aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor right := by
  unfold aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor
  rw [pointsEq, pseudoEq]

/-- The descriptor produced directly by an actual frame and an actual four-ligand base.  This is
the same tracked-sort, priority-ordered point read and classification pipeline as
`aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?`, exposed at the frame seam. -/
noncomputable def aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) :
    Option AromaticCanonicalAuxiliaryLabel := do
  let tracked ← source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? frame
  let points ← tracked.highestFirst.mapM fun index =>
    source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt index)
  let raw ← CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? points
  some (classifyTetrahedralRSPseudo raw tracked.pseudoComparisons)

/-- **Actual frame descriptor transport.**  Sharing the Rule-3 frame and the pairwise compound
comparison records is enough to transport the complete descriptor on the same base: the tracked
order, its pseudo-comparison count and the priority-ordered coordinates are all literally equal. -/
theorem aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?_eq_of_frameSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameSeam left right)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) :
    source.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor? left base =
      source.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor? right base := by
  unfold aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?
  rw [source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_frameSeam seam]

/-- Actual frame descriptor transport when the two bases read pointwise the same coordinates.
The tracked priority order itself is transported by the seam. -/
theorem aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?_eq_of_frameSeam_pointsAgree
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameSeam left right)
    (leftBase rightBase : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (pointsAgree : ∀ order : List (Fin 4),
      order.mapM (fun index =>
        source.aromaticCanonicalRerootSpatialPoint? (leftBase.cursorAt index)) =
      order.mapM (fun index =>
        source.aromaticCanonicalRerootSpatialPoint? (rightBase.cursorAt index))) :
    source.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor? left leftBase =
      source.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor? right rightBase := by
  unfold aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?
  rw [source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_frameSeam seam]
  simp only [pointsAgree]

/-- A frame descriptor agrees with the evidence descriptor whenever the evidence record stores
exactly the outputs of the two preceding pipeline stages. -/
theorem aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?_eq_evidenceDescriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (evidence : source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (trackedComputed :
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? evidence.keys =
        some evidence.tracked)
    (pointsComputed :
      evidence.tracked.highestFirst.mapM (fun index =>
        source.aromaticCanonicalRerootSpatialPoint? (evidence.base.cursorAt index)) =
        some evidence.points) :
    source.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?
        evidence.keys evidence.base =
      source.aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor evidence := by
  unfold aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?
    aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor
  simp [trackedComputed, pointsComputed]

/-! ## Bundled interface for the sibling public outward, parent-insulation and whole-state
modules -/

/-- Descriptor-facing consequences of the frame seam, bundled for sibling consumption.  Every
field is a theorem derived from the seam, not an extra hypothesis. -/
structure AromaticCanonicalOccurrenceRule3Through5FrameSeamConsequences
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) : Prop where
  compareAt_eq : ∀ (leftIndex rightIndex : Fin 4),
    source.compareAromaticCanonicalOccurrenceRule3Through5At left leftIndex rightIndex =
      source.compareAromaticCanonicalOccurrenceRule3Through5At right
        leftIndex rightIndex
  trackedOrder_eq :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? left =
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? right
  descriptor_eq :
    source.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor? left base =
      source.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor? right base

/-- Build the sibling interface from a seam. -/
theorem aromaticCanonicalOccurrenceRule3Through5FrameSeam_consequences
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameSeam left right)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) :
    source.AromaticCanonicalOccurrenceRule3Through5FrameSeamConsequences left right base :=
  { compareAt_eq := fun leftIndex rightIndex =>
      source.compareAromaticCanonicalOccurrenceRule3Through5At_eq_of_frameSeam
        seam leftIndex rightIndex
    trackedOrder_eq :=
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_frameSeam seam
    descriptor_eq :=
      source.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?_eq_of_frameSeam
        seam base }

end AuthoritativeChemicalInput
end TetraStereo.OneCenter

/-! ## Kernel-authority guards

Every public declaration introduced by this module is guarded.  The guarded set covers the three
arbitrary-reader builders (frame, spatial evidence, descriptor), their unconditional restricted
specializations and soundness corollaries, the frame seam and its constructor, all comparison /
tracked-order / pseudo-count / descriptor transport theorems, and the bundled sibling interface.
`assert_kernel_only` permits exactly `propext`, `Classical.choice` and `Quot.sound`, and rejects
`sorryAx`, project axioms and native/compiler trust. -/

assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_eq_rule3Through5KeyFrame?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame_sound
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_sound_of_dependencyLabel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?_eq_spatialEvidence?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?_sound_of_dependencyLabel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_eq_descriptor?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_eq_some_iff_canonical_of_dependencyLabel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalOccurrenceRule3Through5FrameSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalOccurrenceRule3Through5FrameSeam.of_ordering_pseudo
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalOccurrenceRule3Through5KeyFrame.keyAt_rule3_eq_of_rule3Frame_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalOccurrenceRule3Through5At_eq_of_frameSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalOccurrenceRule3Through5At_ordering_eq_of_frameSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalOccurrenceRule3Through5At_pseudo_eq_of_frameSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalOccurrenceRule3Through5Keys_eq_of_frameSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_frameSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_pseudoComparisons_eq_of_frameSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_evidenceDescriptor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5EvidenceDescriptor_eq_of_points_pseudo
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?_eq_of_frameSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?_eq_of_frameSeam_pointsAgree
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?_eq_evidenceDescriptor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalOccurrenceRule3Through5FrameSeamConsequences
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5FrameSeam_consequences
