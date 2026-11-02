import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceAlignment

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileScheduledSource

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceOrdering
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceAlignment
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

theorem actual_written_descriptor (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    writtenFramePriorityDescriptor parity (alignmentSlots n parity)
      (viewTracked n parity view).highestFirst = descriptorOfParity parity false := by
  have odd : permutationIsEven [1, 2, 3, 0] = false := by decide +kernel
  rw [(view_tracked_properties n parity view).2.1]
  rw [FamilySourceBridge.written_descriptor_of_positions parity _ [1, 2, 3, 0] _
    (aligned_role_positions n parity), odd]

noncomputable def viewEvidence (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    ParserRichPriorityEvidence (nitrileSource parity n) 1 :=
  { slots := alignmentSlots n parity
    keys := nitrileViewKeys parity n 1 view
    tracked := viewTracked n parity view
    writtenParity := parity
    raw := writtenFramePriorityDescriptor parity (alignmentSlots n parity)
      (viewTracked n parity view).highestFirst }

/-- The actual rich source evidence builder consumes this nitrile family's own expanded annotation,
returned frame, finite alignment, derived source keys and coherent tracked order. -/
theorem actual_view_evidence (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    constitutionParserRichPriorityEvidence? (expanded parity n) (nitrileSource parity n)
      (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n)) view 4 =
        some (viewEvidence n parity view) := by
  have observed : (expanded parity n).atomAt? (nitrileCenter parity n).1.val =
      some (materializedAtomSpec (centerSpec parity)) :=
    expanded_original_atom parity n 0 _ (raw_center parity n)
  have tagged : (materializedAtomSpec (centerSpec parity)).tetrahedral? = some parity := rfl
  have aligned : findSlotAlignment? ((expanded parity n).writtenNeighbors (nitrileCenter parity n).1.val)
      (occurrenceRootIDs (nitrileSource parity n) (nitrileFrame parity n 1).roots) =
        some (alignmentSlots n parity) := slots_computed n parity
  have computed : (nitrileSource parity n).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))
      view 4 (nitrileFrame parity n 1).roots = some (nitrileViewKeys parity n 1 view) :=
    nitrile_view_keys_computed parity n 1 view
  exact FamilySourceBridge.rich_evidence_of_steps (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2
    ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n)) view 4
    (nitrileCenter parity n) (materializedAtomSpec (centerSpec parity)) parity (nitrileFrame parity n 1).roots
    (alignmentSlots n parity) (nitrileViewKeys parity n 1 view) (viewTracked n parity view)
    (occurrenceTetrahedralCenter?_final _ _ _) observed tagged
    (returned_frame n parity) aligned computed (view_tracked_properties n parity view).1

/-- Actual rich source descriptor under every dependency view. No scheduled output,
comparison, key or desired label is supplied as a premise. -/
theorem actual_view_descriptor (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    constitutionParserRichDescriptor? (expanded parity n) (nitrileSource parity n)
      (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n)) view 4 =
        some (.chiral (descriptorOfParity parity false)) := by
  have classified := FamilySourceBridge.rich_descriptor_of_evidence (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2
    ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n)) view 4
    (viewEvidence n parity view) (actual_view_evidence n parity view)
  simpa only [viewEvidence, actual_written_descriptor,
    (view_tracked_properties n parity view).2.2.1, classifyTetrahedralRSPseudo] using classified

/-- The genuine production source scheduler constructs the state internally. -/
noncomputable def scheduledState (n : Nat) (parity : TetrahedralInputParity) :
    (nitrileSource parity n).AromaticCanonicalAuxiliaryState 1 :=
  constitutionParserRichScheduledState (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2 1 4

noncomputable def scheduledView (n : Nat) (parity : TetrahedralInputParity) :
    (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n)) :=
  (nitrileSource parity n).aromaticCanonicalDependencyView (scheduledState n parity)
    ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))

theorem actual_scheduled_model (n : Nat) (parity : TetrahedralInputParity) :
    ((nitrileSource parity n).aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics (expanded parity n) (nitrileSource parity n)
        (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2 1 4)).CIPModel
          (scheduledState n parity) :=
  constitutionParserRichScheduledState_cipModel (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2 1 4

theorem actual_scheduled_evaluation (n : Nat) (parity : TetrahedralInputParity) :
    constitutionParserRichDescriptor? (expanded parity n) (nitrileSource parity n)
      (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))
      (scheduledView n parity) 4 =
        scheduledState n parity ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n)) :=
  FamilySourceBridge.scheduled_evaluation (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2 1 4
    ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))

theorem actual_scheduled_descriptor (n : Nat) (parity : TetrahedralInputParity) :
    scheduledState n parity ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n)) =
      some (.chiral (descriptorOfParity parity false)) :=
  FamilySourceBridge.scheduled_output_of_all_views (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2 1 4
    ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))
    (.chiral (descriptorOfParity parity false)) (actual_view_descriptor n parity)

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileScheduledSource
