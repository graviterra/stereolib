import TetraStereo.UniversalProof.NextFrontier.NativeRingSourceAlignment

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingScheduledSource

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingSourceInput
open TetraStereo.UniversalProof.NativeRingSourceOrdering
open TetraStereo.UniversalProof.NativeRingSourceAlignment
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

theorem actual_written_descriptor (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))) :
    writtenFramePriorityDescriptor parity (alignmentSlots n parity)
      (viewTracked n parity view).highestFirst = descriptorOfParity parity false := by
  have odd : permutationIsEven [1, 2, 3, 0] = false := by decide +kernel
  rw [(view_tracked_properties n parity view).2.1]
  rw [FamilySourceBridge.written_descriptor_of_positions parity _ [1, 2, 3, 0] _
    (aligned_role_positions n parity), odd]

noncomputable def viewEvidence (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))) :
    ParserRichPriorityEvidence (ringSource n parity) 1 :=
  { slots := alignmentSlots n parity
    keys := ringViewKeys n parity 1 view
    tracked := viewTracked n parity view
    writtenParity := parity
    raw := writtenFramePriorityDescriptor parity (alignmentSlots n parity)
      (viewTracked n parity view).highestFirst }

/-- The actual rich source evidence builder consumes this ring's own expanded annotation,
returned frame, finite alignment, derived source keys and coherent tracked order. -/
theorem actual_view_evidence (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))) :
    constitutionParserRichPriorityEvidence? (expanded n parity) (ringSource n parity)
      (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity)) view 4 =
        some (viewEvidence n parity view) := by
  have observed : (expanded n parity).atomAt? (ringCenter n parity).1.val =
      some (materializedAtomSpec (taggedCarbon parity)) :=
    expanded_original_atom n parity 0 _ (ringRaw_atomAt_zero n parity)
  have tagged : (materializedAtomSpec (taggedCarbon parity)).tetrahedral? = some parity := rfl
  have aligned : findSlotAlignment? ((expanded n parity).writtenNeighbors (ringCenter n parity).1.val)
      (occurrenceRootIDs (ringSource n parity) (ringFrame n parity 1).roots) =
        some (alignmentSlots n parity) := slots_computed n parity
  have computed : (ringSource n parity).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))
      view 4 (ringFrame n parity 1).roots = some (ringViewKeys n parity 1 view) :=
    ring_view_keys_computed n parity 1 view
  exact FamilySourceBridge.rich_evidence_of_steps (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2
    ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity)) view 4
    (ringCenter n parity) (materializedAtomSpec (taggedCarbon parity)) parity (ringFrame n parity 1).roots
    (alignmentSlots n parity) (ringViewKeys n parity 1 view) (viewTracked n parity view)
    (occurrenceTetrahedralCenter?_final _ _ _) observed tagged
    (returned_frame n parity) aligned computed (view_tracked_properties n parity view).1

/-- Actual rich source descriptor under every dependency view. No scheduled output,
comparison, key or desired label is supplied as a premise. -/
theorem actual_view_descriptor (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))) :
    constitutionParserRichDescriptor? (expanded n parity) (ringSource n parity)
      (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity)) view 4 =
        some (.chiral (descriptorOfParity parity false)) := by
  have classified := FamilySourceBridge.rich_descriptor_of_evidence (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2
    ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity)) view 4
    (viewEvidence n parity view) (actual_view_evidence n parity view)
  simpa only [viewEvidence, actual_written_descriptor,
    (view_tracked_properties n parity view).2.2.1, classifyTetrahedralRSPseudo] using classified

/-- The genuine production source scheduler constructs the state internally. -/
noncomputable def scheduledState (n : Nat) (parity : TetrahedralInputParity) :
    (ringSource n parity).AromaticCanonicalAuxiliaryState 1 :=
  constitutionParserRichScheduledState (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2 1 4

noncomputable def scheduledView (n : Nat) (parity : TetrahedralInputParity) :
    (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity)) :=
  (ringSource n parity).aromaticCanonicalDependencyView (scheduledState n parity)
    ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))

theorem actual_scheduled_model (n : Nat) (parity : TetrahedralInputParity) :
    ((ringSource n parity).aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics (expanded n parity) (ringSource n parity)
        (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2 1 4)).CIPModel
          (scheduledState n parity) :=
  constitutionParserRichScheduledState_cipModel (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2 1 4

theorem actual_scheduled_evaluation (n : Nat) (parity : TetrahedralInputParity) :
    constitutionParserRichDescriptor? (expanded n parity) (ringSource n parity)
      (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))
      (scheduledView n parity) 4 =
        scheduledState n parity ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity)) :=
  FamilySourceBridge.scheduled_evaluation (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2 1 4
    ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))

theorem actual_scheduled_descriptor (n : Nat) (parity : TetrahedralInputParity) :
    scheduledState n parity ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity)) =
      some (.chiral (descriptorOfParity parity false)) :=
  FamilySourceBridge.scheduled_output_of_all_views (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2 1 4
    ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))
    (.chiral (descriptorOfParity parity false)) (actual_view_descriptor n parity)

end TetraStereo.UniversalProof.NativeRingScheduledSource
