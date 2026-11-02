import TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralComparison
import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityFinishCompletion
import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityPublicReport
import TetraStereo.UniversalProof.FamilySourceBridge

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Proposed final actual-source join for the eight-member parsed family. Production source
keys, complete prior ties, actual Rule5 comparison, actual safe sorting and source-written
alignment independently produce the same descriptor as actual runtime discovery. The source
scheduler uses carrier/rule fuel1/4; runtime discovery keeps its own actual analysisFuel. No
identity of those fuel parameters, supplied descriptor, model, or callback is assumed. -/

namespace TetraStereo.UniversalProof.NextFrontier.ParsedParitySameSourceModel

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.ParsedParitySourceIntake
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmSource
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmDescriptor
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralSourceLeaves
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRoles
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRule45
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralComparison
open TetraStereo.UniversalProof.NextFrontier.ParsedParityRoleSort
open TetraStereo.UniversalProof.FramedParsedParityFamily (expectedPositions)
open TetraStereo.UniversalProof.FramedParsedParitySchedulerCenter
  (actualResult actualMol actualFuel centralCandidate)
open TetraStereo.UniversalProof.FramedParsedParitySchedulerLeaves (stateD stateD_center_lookup)
open TetraStereo.UniversalProof.FramedParsedParityPublicReport
  (analyzeNormalized_of_discovery reportFromState_eq_expected expectedReport center_outcome expectedCenterOutcome)

private theorem final_center_computed (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalOccurrenceTetrahedralCenter?
      (source.aromaticCanonicalFinalOccurrence fuel center) = some center := by
  classical
  have real : (source.aromaticCanonicalFinalOccurrence fuel center).1.node.provenance = .realAtom := rfl
  have current : (source.aromaticCanonicalFinalOccurrence fuel center).1.node.current? = some center.1 := rfl
  unfold aromaticCanonicalOccurrenceTetrahedralCenter?
  rw [dif_pos real, current]
  simp only
  rw [dif_pos center.2]

theorem central_center_computed (c l r : TetrahedralInputParity) :
    (ownSource (raw c l r)).aromaticCanonicalOccurrenceTetrahedralCenter? (centralTarget c l r) =
      some (sourceCenter c l r) :=
  final_center_computed (ownSource (raw c l r)) 1 (sourceCenter c l r)

private theorem central_frame_returned (c l r : TetrahedralInputParity) :
    (ownSource (raw c l r)).aromaticCanonicalOccurrenceLigandFrame? (centralTarget c l r) =
      some (sourceFrame c l r).roots := (source_returned_four_roots c l r).1

private theorem armReference_ne (l r : TetrahedralInputParity) (opposite : l ≠ r) :
    armReference l r true ≠ armReference l r false := by
  cases l <;> cases r <;> simp_all [armReference, armParity, descriptorOfParity]

private theorem physical_positions (l r : TetrahedralInputParity) :
    (expectedRoles (armReference l r true)).map Fin.val = expectedPositions l := by
  cases l <;> cases r <;> decide +kernel

/-- Actual sorting, physical written positions, and exactly one pseudo comparison. -/
theorem central_sorted_opposite (c l r : TetrahedralInputParity) (opposite : l ≠ r) :
    ∃ tracked,
      (ownSource (raw c l r)).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
        (centralKeys c l r) = some tracked ∧
      tracked.highestFirst.map (fun slot => (centralSlots c l r).getD slot.val 0) =
        expectedPositions l ∧ tracked.pseudoComparisons = 1 := by
  obtain ⟨tracked, computed, roles, pseudo⟩ := actual_safe_sort_opposite (ownSource (raw c l r))
    (centralKeys c l r) (centralRoles c l r) (centralRoles_injective c l r)
    (armReference l r true) (armReference l r false) (armReference_ne l r opposite)
    (central_callback_table c l r)
  refine ⟨tracked, computed, ?_, pseudo⟩
  exact (central_written_positions_of_roles c l r tracked.highestFirst
    (expectedRoles (armReference l r true)) roles).trans (physical_positions l r)

/-- Equal actual arm labels refuse the actual production safe sorter. -/
theorem central_sort_equal_none (c arm : TetrahedralInputParity) :
    (ownSource (raw c arm arm)).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
      (centralKeys c arm arm) = none := by
  apply actual_safe_sort_equal (ownSource (raw c arm arm)) (centralKeys c arm arm)
    (centralRoles c arm arm) (centralRoles_injective c arm arm) (armReference arm arm true)
  intro first second different
  simpa only [armReference, armParity, ite_true, ite_false] using
    central_callback_table c arm arm first second different

noncomputable def centralEvidence (c l r : TetrahedralInputParity)
    (tracked : TrackedLocalizedLigandOrder) : ParserRichPriorityEvidence (ownSource (raw c l r)) 1 :=
  { slots := centralSlots c l r
    keys := centralKeys c l r
    tracked := tracked
    writtenParity := c
    raw := writtenFramePriorityDescriptor c (centralSlots c l r) tracked.highestFirst }

theorem central_evidence_of_order (c l r : TetrahedralInputParity)
    (tracked : TrackedLocalizedLigandOrder)
    (computed : (ownSource (raw c l r)).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
      (centralKeys c l r) = some tracked) :
    constitutionParserRichPriorityEvidence? (raw c l r) (ownSource (raw c l r))
      (family_annotation_agreement c l r) (raw_written c l r) (centralTarget c l r)
      (centralView c l r) 4 = some (centralEvidence c l r tracked) := by
  exact TetraStereo.UniversalProof.FamilySourceBridge.rich_evidence_of_steps
    (raw c l r) (ownSource (raw c l r)) (family_annotation_agreement c l r)
    (raw_written c l r) (centralTarget c l r) (centralView c l r) 4
    (sourceCenter c l r) (centerSpec c l r) c (sourceFrame c l r).roots
    (centralSlots c l r) (centralKeys c l r) tracked
    (central_center_computed c l r)
    (by simpa only [sourceCenter_index] using centerSpec_observed c l r)
    (centerSpec_tetrahedral c l r) (central_frame_returned c l r)
    (by simpa only [sourceCenter_index] using central_slots_computed c l r)
    (central_keys_computed c l r) computed

def centralLabel (c l r : TetrahedralInputParity) : Option AromaticCanonicalAuxiliaryLabel :=
  if l = r then none else
    some (classifyTetrahedralRSPseudo (descriptorOfParity c (permutationIsEven (expectedPositions l))) 1)

/-- No supplied output or state: the actual same-model central descriptor for all eight members. -/
theorem central_descriptor (c l r : TetrahedralInputParity) :
    constitutionParserRichDescriptor? (raw c l r) (ownSource (raw c l r))
      (family_annotation_agreement c l r) (raw_written c l r) (centralTarget c l r)
      (centralView c l r) 4 = centralLabel c l r := by
  by_cases same : l = r
  · subst r
    have aligned : findSlotAlignment? ((raw c l l).writtenNeighbors 1)
        (occurrenceRootIDs (ownSource (raw c l l)) (sourceFrame c l l).roots) =
          some (centralSlots c l l) := central_slots_computed c l l
    simp only [constitutionParserRichDescriptor?, constitutionParserRichPriorityEvidence?,
      central_center_computed, Bind.bind, Option.bind, parserIndexViaConversion_val,
      rawWrittenLigandFrame, sourceCenter_index, centerSpec_observed, centerSpec_tetrahedral,
      central_frame_returned, aligned, central_keys_computed,
      central_sort_equal_none, centralLabel, ite_true]
  · obtain ⟨tracked, computed, positions, pseudo⟩ := central_sorted_opposite c l r same
    unfold constitutionParserRichDescriptor?
    rw [central_evidence_of_order c l r tracked computed]
    change some (classifyTetrahedralRSPseudo
      (writtenFramePriorityDescriptor c (centralSlots c l r) tracked.highestFirst)
      tracked.pseudoComparisons) = centralLabel c l r
    simp only [writtenFramePriorityDescriptor, positions, pseudo, centralLabel, if_neg same]

/-- The same internally constructed source scheduler holds both arm labels and this center. -/
theorem central_scheduled_descriptor (c l r : TetrahedralInputParity) :
    familyScheduledState c l r (centralTarget c l r) = centralLabel c l r := by
  have evaluates := TetraStereo.UniversalProof.FamilySourceBridge.scheduled_evaluation
    (raw c l r) (ownSource (raw c l r)) (family_annotation_agreement c l r)
    (raw_written c l r) 1 4 (centralTarget c l r)
  exact evaluates.symm.trans (central_descriptor c l r)

theorem central_opposite_meaning (c l r : TetrahedralInputParity) (opposite : l ≠ r) :
    ConstitutionParserRichDescriptorMeaning (raw c l r) (ownSource (raw c l r))
      (family_annotation_agreement c l r) (raw_written c l r) (centralTarget c l r)
      (centralView c l r) 4
      (classifyTetrahedralRSPseudo (descriptorOfParity c (permutationIsEven (expectedPositions l))) 1) := by
  apply constitutionParserRichDescriptor?_sound (raw c l r) (ownSource (raw c l r))
    (family_annotation_agreement c l r) (raw_written c l r) (centralTarget c l r) (centralView c l r) 4
  simpa only [centralLabel, if_neg opposite] using central_descriptor c l r

theorem central_equal_no_canonical (c arm : TetrahedralInputParity) :
    ¬ ∃ descriptor, CanonicalConstitutionParserRichDescriptor (raw c arm arm) (ownSource (raw c arm arm))
      (family_annotation_agreement c arm arm) (raw_written c arm arm) (centralTarget c arm arm)
      (centralView c arm arm) 4 descriptor := by
  apply (constitutionParserRichDescriptor?_eq_none_iff_no_canonical (raw c arm arm)
    (ownSource (raw c arm arm)) (family_annotation_agreement c arm arm) (raw_written c arm arm)
    (centralTarget c arm arm) (centralView c arm arm) 4).mp
  simpa only [centralLabel, ite_true] using central_descriptor c arm arm

theorem family_same_model (c l r : TetrahedralInputParity) :
    ((ownSource (raw c l r)).aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics (raw c l r) (ownSource (raw c l r))
        (family_annotation_agreement c l r) (raw_written c l r) 1 4)).CIPModel
        (familyScheduledState c l r) ∧
    familyScheduledState c l r (centralTarget c l r) = centralLabel c l r ∧
    (∀ left, familyScheduledState c l r (armTarget c l r left) =
      some (.chiral (descriptorOfParity (armParity l r left) false))) := by
  exact ⟨constitutionParserRichScheduledState_cipModel (raw c l r) (ownSource (raw c l r))
    (family_annotation_agreement c l r) (raw_written c l r) 1 4,
    central_scheduled_descriptor c l r, arm_scheduled_descriptor c l r⟩

/-- Every model of this exact source semantics is this internally constructed scheduled model. -/
theorem family_model_unique (c l r : TetrahedralInputParity)
    (state : (ownSource (raw c l r)).AromaticCanonicalAuxiliaryState 1)
    (model : ((ownSource (raw c l r)).aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics (raw c l r) (ownSource (raw c l r))
        (family_annotation_agreement c l r) (raw_written c l r) 1 4)).CIPModel state) :
    state = familyScheduledState c l r :=
  constitutionParserRichModel_unique (raw c l r) (ownSource (raw c l r))
    (family_annotation_agreement c l r) (raw_written c l r) 1 4 state model

/-- Explicit conversion from runtime R/S-plus-case metadata to the source label type. -/
def runtimeFactLabel (fact : RawDescriptorFact) : AromaticCanonicalAuxiliaryLabel :=
  if fact.uppercase then .chiral fact.descriptor else
    .pseudoasymmetric (match fact.descriptor with | .R => .r | .S => .s)

/-- Actual runtime discovery uses its actual analysisFuel. Independent source fuel1/4 produces
exactly the same assigned/refused central label, without asserting those fuel values are equal. -/
theorem actual_discovery_agreement (c l r : TetrahedralInputParity) :
    familyScheduledState c l r (centralTarget c l r) =
      ((discoverRawDescriptors (actualResult c l r) (actualMol c l r) (actualFuel c l r)).factAt? 1).map
        runtimeFactLabel := by
  rw [central_scheduled_descriptor,
    TetraStereo.UniversalProof.FramedParsedParityFinishCompletion.actual_descriptors,
    stateD_center_lookup]
  cases c <;> cases l <;> cases r <;> decide +kernel

def sourceOutcome : Option AromaticCanonicalAuxiliaryLabel → StereoOutcome
  | none => .refused .notStereogenic
  | some (.chiral sense) => .tetrahedral sense
  | some (.pseudoasymmetric sense) => .pseudoTetrahedral sense

/-- Exact public central refusal/lowercase outcome, joined to the actual complete discovery state. -/
theorem actual_public_center_agreement (c l r : TetrahedralInputParity) :
    annotatedTetrahedralOutcome? (actualResult c l r) (actualMol c l r)
      (discoverRawDescriptors (actualResult c l r) (actualMol c l r) (actualFuel c l r))
      (actualFuel c l r) 1 = some (sourceOutcome (familyScheduledState c l r (centralTarget c l r))) := by
  rw [TetraStereo.UniversalProof.FramedParsedParityFinishCompletion.actual_descriptors,
    center_outcome, central_scheduled_descriptor]
  cases c <;> cases l <;> cases r <;> decide +kernel

/-- All three public report rows agree with labels in ONE constructed source model. -/
theorem actual_public_report_agreement (c l r : TetrahedralInputParity) :
    analyzeNormalized (actualResult c l r) =
      [{ unit := .tetrahedral 1, outcome := sourceOutcome (familyScheduledState c l r (centralTarget c l r)) },
       { unit := .tetrahedral 2, outcome := sourceOutcome (familyScheduledState c l r (armTarget c l r true)) },
       { unit := .tetrahedral 7, outcome := sourceOutcome (familyScheduledState c l r (armTarget c l r false)) }] := by
  rw [analyzeNormalized_of_discovery (actualResult c l r) (stateD c l r)
    (TetraStereo.UniversalProof.FramedParsedParityFinishCompletion.actual_descriptors c l r),
    reportFromState_eq_expected, central_scheduled_descriptor, arm_scheduled_descriptor,
    arm_scheduled_descriptor]
  cases c <;> cases l <;> cases r <;> decide +kernel

end TetraStereo.UniversalProof.NextFrontier.ParsedParitySameSourceModel
