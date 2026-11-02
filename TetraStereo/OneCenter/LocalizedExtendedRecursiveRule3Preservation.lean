import TetraStereo.OneCenter.LocalizedRule3ExtendedNodePreservation
import TetraStereo.OneCenter.LocalizedRerootExtendedShortCircuitRule3Key

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Simultaneous successful-result preservation for the entire recursive Rule3 construction.
It retains full keys, raw and rebuilt frames, topology and exclusion metadata at the same fuel.
No readiness certificate, chosen successful recursive answer, or equal-callback premise is required. -/
theorem localizedExtendedRule3_mutual_success_refinement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target) :
    ∀ fuel,
      (∀ excluded cursor, OptionSuccessRefines
        (input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel excluded cursor)
        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel excluded cursor)) ∧
      (∀ cursors, OptionSuccessRefines
        (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel cursors)
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro excluded cursor
        simp only [buildLocalizedRerootDescriptorBearingRule3Key?,
          buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
          ← executableLocalizedRerootChildren?_eq_localizedRerootChildren,
          localizedDescriptorBearingRule3StructuralNode?_eq_localizedRule3StructuralNodeExec]
        exact .refl _
      · intro cursors
        exact .refl _
  | succ fuel ih =>
      constructor
      · intro excluded cursor
        simp only [buildLocalizedRerootDescriptorBearingRule3Key?,
          buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
          ← executableLocalizedRerootChildren?_eq_localizedRerootChildren]
        apply OptionSuccessRefines.bind (.refl _)
        intro children
        apply OptionSuccessRefines.bind
          (input.extendedShortNode_preserves_original_with_refined_callback
            target cursor.occurrence view fuel _ ih.2 excluded)
        intro observation
        by_cases empty : children = []
        · simp only [if_pos empty]
          exact .refl _
        · simp only [if_neg empty]
          apply OptionSuccessRefines.bind
            (OptionSuccessRefines.mapM _ _ (ih.1 excluded) children)
          intro childKeys
          exact .refl _
      · intro cursors
        simp only [buildLocalizedDescriptorBearingRule3Frame?, buildLocalizedExtendedShortCircuitRule3FrameExec?]
        apply OptionSuccessRefines.bind
          (OptionSuccessRefines.mapM _ _ (ih.1 []) cursors)
        intro rawKeys
        simp only [localizedRule3CoupledTopologyResolutionExec?_eq_original]
        apply OptionSuccessRefines.bind (.refl _)
        intro topology
        apply OptionSuccessRefines.bind
          (OptionSuccessRefines.mapM _ _
            (ih.1 (input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology)) cursors)
        intro keys
        exact .refl _

/-- Every old successful full key survives, including its observation and provenance records. -/
theorem extendedShortCircuitRule3Key_preserves_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel) (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel excluded cursor = some key) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel excluded cursor = some key :=
  (input.localizedExtendedRule3_mutual_success_refinement target view fuel).1 excluded cursor key computed

/-- Both passes of every old successful frame survive with the identical complete frame. -/
theorem extendedShortCircuitRule3Frame_preserves_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedDescriptorBearingRule3Frame? target view fuel cursors = some frame) :
    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors = some frame :=
  (input.localizedExtendedRule3_mutual_success_refinement target view fuel).2 cursors frame computed

/-- Executable-to-executable form of complete frame preservation. -/
theorem extendedShortCircuitRule3Frame_preserves_originalExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedDescriptorBearingRule3FrameExec? target view fuel cursors = some frame) :
    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors = some frame :=
  input.extendedShortCircuitRule3Frame_preserves_original target view fuel cursors frame
    (by rwa [buildLocalizedDescriptorBearingRule3FrameExec?_eq_original] at computed)

/-- Optional node observations are also retained, including structural absence and excluded units. -/
theorem extendedShortCircuitRule3Node_preserves_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedDescriptorBearingRule3Node? target occurrence view fuel excluded)
      (input.localizedExtendedShortCircuitRule3NodeExec? target occurrence view fuel excluded) := by
  cases fuel with
  | zero =>
      simp only [localizedDescriptorBearingRule3Node?, localizedExtendedShortCircuitRule3NodeExec?,
        localizedDescriptorBearingRule3StructuralNode?_eq_localizedRule3StructuralNodeExec]
      exact .refl _
  | succ fuel =>
      exact input.extendedShortNode_preserves_original_with_refined_callback
        target occurrence view fuel _
        (input.localizedExtendedRule3_mutual_success_refinement target view fuel).2 excluded

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
