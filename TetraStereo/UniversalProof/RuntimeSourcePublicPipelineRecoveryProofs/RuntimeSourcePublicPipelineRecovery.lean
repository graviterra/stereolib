import TetraStereo.UniversalProof.RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery
import TetraStereo.UniversalProof.ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

set_option autoImplicit false

namespace TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
open TetraStereo.UniversalProof.RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge















/-- Independent actual atom-record intake: no other actual atom carries a tetrahedral annotation. -/
def OnlyCenterTagged (raw : RawMolecule) (center : Nat) : Prop :=
  ∀ index : Fin raw.atomCount, ∀ spec, raw.atomAt? index.val = some spec →
    spec.tetrahedral?.isSome = true → index.val = center

/-- The actual discovery filter rejects every node from independent input annotation absence. -/
theorem auxiliary_node_not_selected (raw : RawMolecule) (center : Nat)
    (only : OnlyCenterTagged raw center) (node : RawMolecule.CanonicalBranchNode) :
    (node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom && node.atom != center &&
      (raw.atomAt? node.atom).any (fun spec => spec.tetrahedral?.isSome)) = false := by
  by_cases atCenter : node.atom = center
  · simp [atCenter]
  · cases observed : raw.atomAt? node.atom with
    | none => simp
    | some spec =>
        have bound : node.atom < raw.atomCount :=
          listGet?_eq_some_implies_lt raw.atoms node.atom spec observed
        have noTag : spec.tetrahedral?.isSome = false := by
          apply Bool.eq_false_of_not_eq_true
          intro tagged
          exact atCenter (only ⟨node.atom, bound⟩ spec observed tagged)
        simp [noTag]

theorem auxiliary_filter_empty (raw : RawMolecule) (center : Nat)
    (only : OnlyCenterTagged raw center) (nodes : List RawMolecule.CanonicalBranchNode) :
    (nodes.filter fun node =>
      node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom && node.atom != center &&
        (raw.atomAt? node.atom).any (fun spec => spec.tetrahedral?.isSome)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro node _
  simpa only [Bool.not_eq_true] using auxiliary_node_not_selected raw center only node

/-- Honest intermediate collector binding; no supplied scheduler state or expected label. -/
theorem auxiliary_state_empty_of_actual_tree (raw : RawMolecule) (fuel center : Nat)
    (only : OnlyCenterTagged raw center) (nodes : List RawMolecule.CanonicalBranchNode)
    (collected : collectCanonicalTreeAuthoritative raw fuel [canonicalCenterRoot center] = some nodes) :
    buildOccurrenceAuxStateFullyAuthoritative? raw fuel center = some [] := by
  simp [buildOccurrenceAuxStateFullyAuthoritative?, collected,
    auxiliary_filter_empty raw center only nodes, sortDescBy, discoverOccurrenceAuxBatchesAuthoritative?]

/-- Actual public occurrence-fact output record, retaining positions and zero auxiliary evidence. -/
def recoveredPublicFact (center : Nat) (positions : List Nat) (descriptor : RS) : RawDescriptorFact where
  atom := center
  descriptor := descriptor
  uppercase := true
  evidenceSize := 1
  decisiveRule? := none
  descriptorDependentPairs := 0
  priorityPositions := positions

/-- The public occurrence entry point consumes its internally derived empty environment. -/
theorem public_fact_of_actual_local_fact (raw : RawMolecule) (fuel center : Nat)
    (only : OnlyCenterTagged raw center) (nodes : List RawMolecule.CanonicalBranchNode)
    (collected : collectCanonicalTreeAuthoritative raw fuel [canonicalCenterRoot center] = some nodes)
    (positions : List Nat) (descriptor : RS)
    (localComputed : occurrenceFactAuthoritative? raw fuel [] (canonicalCenterRoot center) =
      some (recoveredFact center positions descriptor)) :
    tetrahedralOccurrenceFact? raw fuel center = some (recoveredPublicFact center positions descriptor) := by
  have environment := auxiliary_state_empty_of_actual_tree raw fuel center only nodes collected
  simp [tetrahedralOccurrenceFact?, tetrahedralOccurrenceFactAuthoritative?, environment,
    localComputed, recoveredFact, recoveredPublicFact]

/-- General runtime public occurrence-fact success at an explicitly bound actual finite collector.
The closed witness below derives the collector; this library statement does not hide that premise. -/
theorem public_fact_exists_of_actual_tree (raw : RawMolecule) (fuel center : Nat)
    (domain : SingleLeafDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4)
    (only : OnlyCenterTagged raw center) (nodes : List RawMolecule.CanonicalBranchNode)
    (collected : collectCanonicalTreeAuthoritative raw fuel [canonicalCenterRoot center] = some nodes)
    (spec : AtomSpec) (atomObserved : raw.atomAt? center = some spec)
    (parity : TetrahedralInputParity) (parityObserved : spec.tetrahedral? = some parity) :
    ∃ positions,
      tetrahedralOccurrenceFact? raw fuel center =
        some (recoveredPublicFact center positions (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven positions))) := by
  obtain ⟨positions, localComputed⟩ := actual_runtime_fact_exists raw center domain written four
    spec atomObserved parity parityObserved [] fuel
  exact ⟨positions, public_fact_of_actual_local_fact raw fuel center only nodes collected positions _ localComputed⟩

theorem collected_empty (raw : RawMolecule) (fuel : Nat) :
    collectCanonicalTreeAuthoritative raw fuel [] = some [] := by
  cases fuel <;> rfl

namespace ClosedCF

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness

abbrev raw : RawMolecule := annotatedRawCF
abbrev source : AuthoritativeChemicalInput := parserSource
abbrev center : source.AromaticCanonicalTetrahedralCenter := parserCenter

def leaves : List RawMolecule.CanonicalBranchNode :=
  [canonicalRoot 0 1, canonicalRoot 0 2, canonicalRoot 0 3, canonicalRoot 0 4]

def actualTree : List RawMolecule.CanonicalBranchNode := canonicalCenterRoot 0 :: leaves

theorem actual_only_center_tagged : OnlyCenterTagged raw 0 := by
  intro index spec observed tagged
  change Fin 5 at index
  fin_cases index <;> simp [raw, annotatedRawCF, atomAt?, listGet?] at observed
  all_goals subst spec
  all_goals simp_all [AtomSpec.aliphatic]

theorem actual_first_frontier : raw.canonicalChildren (canonicalCenterRoot 0) = leaves := by
  decide +kernel

theorem actual_leaf_frontier : leaves.flatMap raw.canonicalChildren = [] := by
  decide +kernel

/-- Actual complete canonical collection, at every fuel at least two, without a caller tree. -/
theorem actual_collected_tree (extraFuel : Nat) :
    collectCanonicalTreeAuthoritative raw (extraFuel + 2) [canonicalCenterRoot 0] = some actualTree := by
  simp only [collectCanonicalTreeAuthoritative, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, actual_first_frontier]
  have leafCollected : collectCanonicalTreeAuthoritative raw (extraFuel + 1) leaves = some leaves := by
    change (do
      let tail ← collectCanonicalTreeAuthoritative raw extraFuel (leaves.flatMap raw.canonicalChildren)
      some (leaves ++ tail)) = some leaves
    rw [actual_leaf_frontier, collected_empty]
    rfl
  rw [leafCollected]
  rfl

theorem actual_auxiliary_state (extraFuel : Nat) :
    buildOccurrenceAuxStateFullyAuthoritative? raw (extraFuel + 2) 0 = some [] :=
  auxiliary_state_empty_of_actual_tree raw (extraFuel + 2) 0 actual_only_center_tagged actualTree
    (actual_collected_tree extraFuel)

/-- Actual public occurrence entry point succeeds after deriving its own whole auxiliary state. -/
theorem actual_public_fact (extraFuel : Nat) :
    ∃ positions,
      tetrahedralOccurrenceFact? raw (extraFuel + 2) 0 =
        some (recoveredPublicFact 0 positions (RawMolecule.descriptorOfParity TetrahedralInputParity.clockwise
          (RawMolecule.permutationIsEven positions))) :=
  public_fact_exists_of_actual_tree raw (extraFuel + 2) 0
    RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.ClosedCF.actual_domain
    NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_written_exact
    RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.ClosedCF.actual_four
    actual_only_center_tagged actualTree (actual_collected_tree extraFuel)
    { AtomSpec.aliphatic .C with tetrahedral? := some TetrahedralInputParity.clockwise }
    NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_input_parity
    TetrahedralInputParity.clockwise (by rfl)

/-- The actual public occurrence fact has the SAME-source parser label and independent meaning.
The environment is internally computed; no auxiliary state is supplied to this theorem. -/
theorem actual_public_formal_alignment (extraFuel : Nat)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center)) :
    ∃ positions descriptor,
      tetrahedralOccurrenceFact? raw (extraFuel + 2) 0 = some (recoveredPublicFact 0 positions descriptor) ∧
      constitutionParserRichDescriptor? raw source
        NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_annotation_agreement
        NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_written_exact
        (source.aromaticCanonicalFinalOccurrence 0 center) view 2 = some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning raw source
        NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_annotation_agreement
        NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_written_exact
        (source.aromaticCanonicalFinalOccurrence 0 center) view 2 (.chiral descriptor) := by
  obtain ⟨positions, descriptor, localComputed, parserComputed, parserMeaning, _⟩ :=
    RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery.ClosedCF.actual_runtime_fact_alignment view [] (extraFuel + 2)
  refine ⟨positions, descriptor, ?_, parserComputed, parserMeaning⟩
  exact public_fact_of_actual_local_fact raw (extraFuel + 2) 0 actual_only_center_tagged
    actualTree (actual_collected_tree extraFuel) positions descriptor localComputed

/-- Actual closed input label, derived by identifying the new public occurrence fact with the
checked SAME-source parser output. This is not a caller-provided expected label. -/
theorem actual_public_R (extraFuel : Nat)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center)) :
    ∃ positions, tetrahedralOccurrenceFact? raw (extraFuel + 2) 0 =
      some (recoveredPublicFact 0 positions RS.R) := by
  obtain ⟨positions, descriptor, publicComputed, parserComputed, _⟩ :=
    actual_public_formal_alignment extraFuel view
  have known : constitutionParserRichDescriptor? raw source
      NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_annotation_agreement
      NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_written_exact
      (source.aromaticCanonicalFinalOccurrence 0 center) view 2 = some (.chiral RS.R) :=
    SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel.ClosedConstitutionParserModel.parser_actual_constitution_descriptor_R view
  have equal : descriptor = RS.R := by
    have labels := Option.some.inj (parserComputed.symm.trans known)
    exact LocalizedTetrahedralRSPseudoDescriptor.chiral.inj labels
  exact ⟨positions, equal ▸ publicComputed⟩

/-- No new H is demanded here, but production still changes raw inline-count/table metadata. -/
theorem actual_zero_hydrogen_demand :
    ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.ZeroHydrogenDemand raw := by
  intro index bound
  change index < 5 at bound
  interval_cases index <;> decide +kernel

/-- Actual whole returned expansion record; no false raw-record identity is used. -/
theorem actual_expansion_record : raw.withExplicitHydrogens =
    ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materializedWrittenRecord raw :=
  ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.zero_demand_expansion_exact_record raw
    actual_zero_hydrogen_demand NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_written_exact

/-- Actual plain single bonds need no unspecified-bond rewrite. -/
theorem actual_unspecified_normalization : raw.normalizeUnspecifiedBonds = raw := by
  decide +kernel

/-- This is the actual higher public classifier on its ACTUAL hydrogen-materialized input.
The finite closed witness does not establish its unrestricted refinement to the occurrence API. -/
theorem actual_expanded_public_R : expandedTetrahedralDescriptorAt? raw.withExplicitHydrogens 0 = some RS.R := by
  rw [actual_expansion_record]
  decide +kernel

/-- The actual public parsed intake performs its real normalization/materialization before output. -/
theorem actual_parsed_public_R : parsedTetrahedralDescriptorAt? raw 0 = some RS.R := by
  unfold parsedTetrahedralDescriptorAt?
  rw [actual_unspecified_normalization]
  exact actual_expanded_public_R

end ClosedCF

end TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
