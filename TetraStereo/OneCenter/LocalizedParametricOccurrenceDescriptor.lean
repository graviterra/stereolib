import TetraStereo.OneCenter.LocalizedOccurrenceRule45Descriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Parametric comparison seam for the localized occurrence Rules-4a--5 descriptor

`LocalizedOccurrenceRule45Descriptor` fixes one comparison source:
`compareLocalizedOccurrenceThroughRule5At?`, which reads both ligands through the restricted
dependency view.  This module separates that comparison source from the surrounding occurrence
pipeline while leaving the production construction untouched.

`localizedOccurrenceRule45SpatialEvidenceWith?` and
`localizedOccurrenceRule45DescriptorWith?` take an arbitrary frame-dependent callback

`compareFrame : (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) →
  Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison`

and otherwise perform exactly the production construction: the actual occurrence center and
four-ligand frame are built by `localizedOccurrenceDescriptorCenter?` and
`localizedOccurrenceFourLigandFrame?`; the actual `sortFourLocalizedLigandsTracked` stable sort is
used; the actual all-pairs coherence check and `localizedRerootCursorSpatialPoint?` extraction are
used; and the final reading goes through `descriptorOfPriorityOrderedPoints?` and
`classifyTetrahedralRSPseudo`.  Only the pairwise comparison records are supplied by the callback.

## Main results

* `localizedOccurrenceRule45DescriptorWith?_restricted` — specializing the callback to the existing
  `compareLocalizedOccurrenceThroughRule5At?` reproduces the existing
  `localizedOccurrenceRule45Descriptor?` *exactly*, including the `none` case.  The same exact
  recovery is proved for the evidence layer and for the tracked safe order.
* `localizedOccurrenceRule45DescriptorWith?_eq_of_frame_comparisons` — extensional congruence: if
  two callbacks agree on every pair at one actual (constructed) four-ligand frame, then the final
  descriptors are equal.  The hypothesis is restricted to frames that the actual construction
  returns; no comparison values at unconstructed frames are inspected.
* `localizedOccurrenceRule45DescriptorWith?_eq_restricted_of_frame_comparisons` — the consumer
  bridge: a callback that agrees with `compareLocalizedOccurrenceThroughRule5At?` on every
  constructed frame yields the existing descriptor.  This is the exact seam for applying a derived
  whole-frame pair-comparison theorem to the occurrence descriptor.

## Scope

This is structural plumbing, not an independent chemical completion.  It introduces no second
sort, no second frame construction and no second geometry implementation, and it assumes no
desired descriptor value.  Supplying a comparison callback together with the frame-wise pair
equalities (for example from a future parametric Rule-4/5 key) remains the caller's obligation.
-/

/-- A comparison callback whose values may depend on the actual occurrence frame. -/
abbrev LocalizedOccurrenceRule45FrameComparator
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) : Type :=
  (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) →
    Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison

/-! ## Generic pair coherence

These are the production strict-pair and all-pairs coherence checks with only the comparison
source abstracted. -/

/-- Strict all-pairs check for one ordered pair, relative to an arbitrary comparison source. -/
def localizedOccurrenceRule45PairStrictWith?
    (compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison)
    (left right : Fin 4) : Bool :=
  match compareAt left right with
  | none => false
  | some result => result.ordering == Ordering.gt

/-- Strict all-pairs coherence relative to an arbitrary comparison source. -/
def localizedOccurrenceRule45OrderCoherentWith?
    (compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison) :
    List (Fin 4) → Bool
  | [] => true
  | left :: rest =>
      rest.all (fun right =>
        localizedOccurrenceRule45PairStrictWith? compareAt left right) &&
      localizedOccurrenceRule45OrderCoherentWith? compareAt rest

/-! ## Exact recovery of the restricted comparison pipeline -/

/-- The generic strict-pair check specialized to the restricted occurrence comparison is the
existing check. -/
theorem localizedOccurrenceRule45PairStrictWith?_restricted
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4) :
    localizedOccurrenceRule45PairStrictWith?
        (input.compareLocalizedOccurrenceThroughRule5At? target view frame) left right =
      input.localizedOccurrenceRule45OrderPairStrict? target view frame left right :=
  rfl

/-- The generic coherence check specialized to the restricted occurrence comparison is the
existing check, for every proposed order. -/
theorem localizedOccurrenceRule45OrderCoherentWith?_restricted
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    ∀ order,
      localizedOccurrenceRule45OrderCoherentWith?
          (input.compareLocalizedOccurrenceThroughRule5At? target view frame) order =
        input.localizedOccurrenceRule45OrderCoherent? target view frame order
  | [] => rfl
  | left :: rest => by
      simp [localizedOccurrenceRule45OrderCoherentWith?,
        localizedOccurrenceRule45OrderCoherent?,
        localizedOccurrenceRule45PairStrictWith?_restricted input target view frame left,
        localizedOccurrenceRule45OrderCoherentWith?_restricted
          input target view frame rest]

/-- The tracked safe order relative to an arbitrary comparison source: the actual four-position
tracked stable sort followed by the actual all-pairs coherence check. -/
noncomputable def localizedOccurrenceRule45SafeTrackedOrderWith?
    (compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison) :
    Option TrackedLocalizedLigandOrder := do
  let tracked ← sortFourLocalizedLigandsTracked compareAt
  if localizedOccurrenceRule45OrderCoherentWith? compareAt tracked.highestFirst then
    some tracked
  else none

/-- The parametric safe order specialized to the restricted occurrence comparison is the existing
safe order. -/
theorem localizedOccurrenceRule45SafeTrackedOrderWith?_restricted
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    localizedOccurrenceRule45SafeTrackedOrderWith?
        (input.compareLocalizedOccurrenceThroughRule5At? target view frame) =
      input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame := by
  unfold localizedOccurrenceRule45SafeTrackedOrderWith?
    safeLocalizedOccurrenceRule45TrackedOrder?
    localizedOccurrenceRule45TrackedOrder?
  simp only [localizedOccurrenceRule45OrderCoherentWith?_restricted
    input target view frame]

/-! ## Parametric occurrence evidence and descriptor -/

/-- Parametric spatial evidence.  The center, the four-ligand frame, the tracked safe order and
the ordered spatial points are obtained by exactly the production construction; only the pairwise
comparisons come from `compareFrame`. -/
noncomputable def localizedOccurrenceRule45SpatialEvidenceWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (_view : input.LocalizedDependencyView target)
    (compareFrame : LocalizedOccurrenceRule45FrameComparator input carrierFuel) :
    Option (input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let frame ← input.localizedOccurrenceFourLigandFrame? target
  let tracked ← localizedOccurrenceRule45SafeTrackedOrderWith? (compareFrame frame)
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (frame.cursorAt index)
  some { center := center, frame := frame, tracked := tracked, points := points }

/-- State-relative occurrence descriptor through Rules 4a--5 relative to an arbitrary
frame-dependent comparison source. -/
noncomputable def localizedOccurrenceRule45DescriptorWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (compareFrame : LocalizedOccurrenceRule45FrameComparator input carrierFuel) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ←
    input.localizedOccurrenceRule45SpatialEvidenceWith? target view compareFrame
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- The parametric evidence specialized to the restricted occurrence comparison is the existing
evidence. -/
theorem localizedOccurrenceRule45SpatialEvidenceWith?_restricted
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedOccurrenceRule45SpatialEvidenceWith? target view
        (input.compareLocalizedOccurrenceThroughRule5At? target view) =
      input.localizedOccurrenceRule45SpatialEvidence? target view := by
  unfold localizedOccurrenceRule45SpatialEvidenceWith?
    localizedOccurrenceRule45SpatialEvidence?
  simp only [localizedOccurrenceRule45SafeTrackedOrderWith?_restricted]

/-- The parametric descriptor specialized to the restricted occurrence comparison is the existing
descriptor, including the `none` case. -/
theorem localizedOccurrenceRule45DescriptorWith?_restricted
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedOccurrenceRule45DescriptorWith? target view
        (input.compareLocalizedOccurrenceThroughRule5At? target view) =
      input.localizedOccurrenceRule45Descriptor? target view := by
  unfold localizedOccurrenceRule45DescriptorWith?
    localizedOccurrenceRule45Descriptor?
  rw [localizedOccurrenceRule45SpatialEvidenceWith?_restricted]

/-! ## Extensional congruence over actual frames -/

/-- If the four-ligand frame construction fails, the parametric evidence fails. -/
theorem localizedOccurrenceRule45SpatialEvidenceWith?_eq_none_of_frame?_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (compareFrame : LocalizedOccurrenceRule45FrameComparator input carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = none) :
    input.localizedOccurrenceRule45SpatialEvidenceWith? target view compareFrame = none := by
  unfold localizedOccurrenceRule45SpatialEvidenceWith?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target <;>
    simp [frameComputed]

/-- If the four-ligand frame construction fails, the production evidence fails. -/
theorem localizedOccurrenceRule45SpatialEvidence?_eq_none_of_frame?_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = none) :
    input.localizedOccurrenceRule45SpatialEvidence? target view = none := by
  unfold localizedOccurrenceRule45SpatialEvidence?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target <;>
    simp [frameComputed]

/-- Extensional congruence of the evidence: callbacks that agree on every ordered pair at one
actual constructed frame produce the same evidence.  Nothing at other frames is inspected. -/
theorem localizedOccurrenceRule45SpatialEvidenceWith?_eq_of_frame_comparisons
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (first second : LocalizedOccurrenceRule45FrameComparator input carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (agrees : ∀ left right : Fin 4, first frame left right = second frame left right) :
    input.localizedOccurrenceRule45SpatialEvidenceWith? target view first =
      input.localizedOccurrenceRule45SpatialEvidenceWith? target view second := by
  have frameAgrees : first frame = second frame :=
    funext fun left => funext fun right => agrees left right
  unfold localizedOccurrenceRule45SpatialEvidenceWith?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target <;>
    simp [frameComputed, frameAgrees]

/-- Extensional congruence of the final descriptor: callbacks that agree on every ordered pair at
one actual constructed frame produce the same descriptor. -/
theorem localizedOccurrenceRule45DescriptorWith?_eq_of_frame_comparisons
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (first second : LocalizedOccurrenceRule45FrameComparator input carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (agrees : ∀ left right : Fin 4, first frame left right = second frame left right) :
    input.localizedOccurrenceRule45DescriptorWith? target view first =
      input.localizedOccurrenceRule45DescriptorWith? target view second := by
  unfold localizedOccurrenceRule45DescriptorWith?
  rw [localizedOccurrenceRule45SpatialEvidenceWith?_eq_of_frame_comparisons
    input target view first second frame frameComputed agrees]

/-- Consumer bridge: a callback that agrees with the existing restricted occurrence comparison on
every constructed frame yields exactly the existing occurrence descriptor, including the `none`
case.  This is the seam used to insert a derived whole-frame pair-comparison theorem without
assuming any desired descriptor value. -/
theorem localizedOccurrenceRule45DescriptorWith?_eq_restricted_of_frame_comparisons
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (compareFrame : LocalizedOccurrenceRule45FrameComparator input carrierFuel)
    (agrees : ∀ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel),
      input.localizedOccurrenceFourLigandFrame? target = some frame →
        ∀ left right : Fin 4,
          compareFrame frame left right =
            input.compareLocalizedOccurrenceThroughRule5At? target view frame left right) :
    input.localizedOccurrenceRule45DescriptorWith? target view compareFrame =
      input.localizedOccurrenceRule45Descriptor? target view := by
  cases frameComputed : input.localizedOccurrenceFourLigandFrame? target with
  | none =>
      unfold localizedOccurrenceRule45DescriptorWith?
        localizedOccurrenceRule45Descriptor?
      rw [localizedOccurrenceRule45SpatialEvidenceWith?_eq_none_of_frame?_eq_none
            input target view compareFrame frameComputed,
          localizedOccurrenceRule45SpatialEvidence?_eq_none_of_frame?_eq_none
            input target view frameComputed]
  | some frame =>
      exact (localizedOccurrenceRule45DescriptorWith?_eq_of_frame_comparisons
          input target view compareFrame
            (input.compareLocalizedOccurrenceThroughRule5At? target view)
            frame frameComputed (agrees frame frameComputed)).trans
        (localizedOccurrenceRule45DescriptorWith?_restricted input target view)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45PairStrictWith?_restricted
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45OrderCoherentWith?_restricted
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45SafeTrackedOrderWith?_restricted
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45SpatialEvidenceWith?_restricted
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45DescriptorWith?_restricted
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45SpatialEvidenceWith?_eq_none_of_frame?_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45SpatialEvidence?_eq_none_of_frame?_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45SpatialEvidenceWith?_eq_of_frame_comparisons
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45DescriptorWith?_eq_of_frame_comparisons
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45DescriptorWith?_eq_restricted_of_frame_comparisons
