import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupport
import TetraStereo.UniversalProof.NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery
import TetraStereo.UniversalProof.PositiveHydrogenPublicPipelineRecoveryProofs.PositiveHydrogenPublicPipelineRecovery
import TetraStereo.OneCenter.CIPP93NoncarbonTetrahedralNormalization

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge




















/-- The exact input consumed by the actual higher parsed classifier. -/
def parsedInput (raw : RawMolecule) : RawMolecule :=
  raw.normalizeUnspecifiedBonds.withExplicitHydrogens

theorem parsed_classifier_input (raw : RawMolecule) (center : Nat) :
    parsedTetrahedralDescriptorAt? raw center =
      expandedTetrahedralDescriptorAt? (parsedInput raw) center := rfl


-- actual_legacy_root_rule1a is re-exported from NativeInitialSeedRuntimeSupport.


-- actual_legacy_strict_branch is re-exported from NativeInitialSeedRuntimeSupport.


theorem normalized_record_neighbors (raw : RawMolecule) (center : Nat) :
    recordNeighbors raw.normalizeUnspecifiedBonds center = recordNeighbors raw center := by
  unfold recordNeighbors normalizeUnspecifiedBonds
  rw [List.filterMap_map]
  apply congrArg (fun callback => raw.bonds.filterMap callback)
  funext bond
  simp only [Function.comp_apply, recordNeighbor?, normalizeUnspecifiedBond_source,
    normalizeUnspecifiedBond_target]

theorem normalized_incident_atoms (raw : RawMolecule) (center : Nat) :
    raw.normalizeUnspecifiedBonds.incidentAtoms center = raw.incidentAtoms center := by
  change (recordNeighbors raw.normalizeUnspecifiedBonds center).eraseDups =
    (recordNeighbors raw center).eraseDups
  rw [normalized_record_neighbors]

theorem normalized_atomic_number (raw : RawMolecule) (index : Nat) :
    raw.normalizeUnspecifiedBonds.atomZAt index = raw.atomZAt index := rfl

theorem normalized_hydrogen_demand (raw : RawMolecule) (index : Nat) :
    raw.normalizeUnspecifiedBonds.hydrogenCountAt index = raw.hydrogenCountAt index := by
  unfold hydrogenCountAt
  change (match raw.atomAt? index with
    | none => 0
    | some spec => match spec.explicitHydrogens? with
      | some count => count
      | none => match (defaultValences spec).find?
          (fun valence => raw.normalizeUnspecifiedBonds.incidentBondOrderSum index ≤ valence) with
        | some valence => valence - raw.normalizeUnspecifiedBonds.incidentBondOrderSum index
        | none => 0) = _
  simp only [BlueBookP93.NoncarbonTetrahedra.Production.normalizeUnspecifiedBonds_incidentBondOrderSum]
  rfl

theorem normalized_zero_demand (raw : RawMolecule)
    (zero : ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.ZeroHydrogenDemand raw) :
    ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.ZeroHydrogenDemand raw.normalizeUnspecifiedBonds := by
  intro index bound
  rw [normalized_hydrogen_demand]
  exact zero index bound

theorem normalized_single_leaf (raw : RawMolecule) (center : Nat)
    (domain : SingleLeafDomain raw center) : SingleLeafDomain raw.normalizeUnspecifiedBonds center := by
  refine ⟨⟨normalizeUnspecifiedBonds_wellFormed raw domain.leaf.wellFormed,
    domain.leaf.centerBound, ?_, ?_, ?_⟩, ?_⟩
  · rw [normalized_record_neighbors]
    apply List.all_eq_true.mpr
    intro atom member
    exact decide_eq_true (by
      rw [normalizeUnspecifiedBonds_bondOrder]
      exact domain.leaf.single member)
  · rw [normalized_record_neighbors]
    apply List.all_eq_true.mpr
    intro atom member
    exact decide_eq_true (by
      rw [normalized_incident_atoms]
      exact domain.leaf.leaf member)
  · simpa only [normalized_record_neighbors, normalized_atomic_number] using domain.leaf.distinctRanks
  · intro bond member incident
    obtain ⟨original, retained, rfl⟩ := List.mem_map.mp member
    have originalIncident : original.source = center ∨ original.target = center := by
      simpa only [normalizeUnspecifiedBond_source, normalizeUnspecifiedBond_target] using incident
    have kind := domain.incidentKinds original retained originalIncident
    simp only [normalizeUnspecifiedBond, kind]

theorem materialized_atom_lookup (raw : RawMolecule) (index : Nat) :
    (ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materializedWrittenRecord raw).atomAt? index =
      (raw.atomAt? index).map materializedAtomSpec :=
  listGet?_map materializedAtomSpec raw.atoms index

theorem materialized_atomic_number (raw : RawMolecule) (index : Nat) :
    (ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materializedWrittenRecord raw).atomZAt index =
      raw.atomZAt index := by
  unfold atomZAt
  rw [materialized_atom_lookup]
  cases raw.atomAt? index <;> rfl

theorem materialized_record_neighbors (raw : RawMolecule) (center : Nat) :
    recordNeighbors (ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materializedWrittenRecord raw) center =
      recordNeighbors raw center := rfl

theorem materialized_incident_atoms (raw : RawMolecule) (center : Nat) :
    (ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materializedWrittenRecord raw).incidentAtoms center =
      raw.incidentAtoms center := rfl

theorem materialized_well_formed (raw : RawMolecule) (well : raw.WellFormed) :
    (ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materializedWrittenRecord raw).WellFormed := by
  intro bond member
  have endpoints := well bond member
  change bond.source < _ ∧ bond.target < _ ∧ bond.source ≠ bond.target
  simpa only [ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materialized_record_atom_count] using endpoints

theorem materialized_single_leaf (raw : RawMolecule) (center : Nat)
    (domain : SingleLeafDomain raw center) :
    SingleLeafDomain (ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materializedWrittenRecord raw) center := by
  refine ⟨⟨materialized_well_formed raw domain.leaf.wellFormed, ?_, ?_, ?_, ?_⟩,
    domain.incidentKinds⟩
  · simpa only [ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materialized_record_atom_count]
      using domain.leaf.centerBound
  · exact domain.leaf.singleEdges
  · exact domain.leaf.leafNeighbors
  · have atomicNumbers :
        (ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materializedWrittenRecord raw).atomZAt =
          raw.atomZAt := by
      funext index
      exact materialized_atomic_number raw index
    simpa only [materialized_record_neighbors, atomicNumbers] using domain.leaf.distinctRanks

/-- Independent ORIGINAL graph and demand class; no preprocessed graph or output conclusion is
an input field. Zero demand still consumes inline metadata and constructs a total written table. -/
structure NormalizedLeafIntake (raw : RawMolecule) (center : Nat) : Prop where
  domain : SingleLeafDomain raw center
  zeroDemand : ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.ZeroHydrogenDemand raw
  writtenExact : raw.WrittenNeighborExact

theorem actual_parsed_record (raw : RawMolecule) (center : Nat)
    (intake : NormalizedLeafIntake raw center) :
    parsedInput raw = ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materializedWrittenRecord
      raw.normalizeUnspecifiedBonds :=
  ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.zero_demand_expansion_exact_record
    raw.normalizeUnspecifiedBonds (normalized_zero_demand raw intake.zeroDemand)
    (normalizeUnspecifiedBonds_writtenNeighborExact raw intake.writtenExact)

theorem actual_parsed_domain (raw : RawMolecule) (center : Nat)
    (intake : NormalizedLeafIntake raw center) : SingleLeafDomain (parsedInput raw) center := by
  rw [actual_parsed_record raw center intake]
  exact materialized_single_leaf raw.normalizeUnspecifiedBonds center
    (normalized_single_leaf raw center intake.domain)

theorem actual_parsed_atom_count (raw : RawMolecule) (center : Nat)
    (intake : NormalizedLeafIntake raw center) : (parsedInput raw).atomCount = raw.atomCount := by
  rw [actual_parsed_record raw center intake,
    ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materialized_record_atom_count]
  rfl

theorem actual_parsed_neighbors (raw : RawMolecule) (center : Nat)
    (intake : NormalizedLeafIntake raw center) (index : Nat) :
    recordNeighbors (parsedInput raw) index = recordNeighbors raw index := by
  rw [actual_parsed_record raw center intake, materialized_record_neighbors,
    normalized_record_neighbors]

theorem actual_parsed_atom_lookup (raw : RawMolecule) (center : Nat)
    (intake : NormalizedLeafIntake raw center) (index : Nat) :
    (parsedInput raw).atomAt? index = (raw.atomAt? index).map materializedAtomSpec := by
  rw [actual_parsed_record raw center intake, materialized_atom_lookup]
  rfl

theorem actual_parsed_atomic_number (raw : RawMolecule) (center : Nat)
    (intake : NormalizedLeafIntake raw center) (index : Nat) :
    (parsedInput raw).atomZAt index = raw.atomZAt index := by
  rw [actual_parsed_record raw center intake, materialized_atomic_number]
  rfl

theorem actual_parsed_legacy_strict_branch (raw : RawMolecule) (center : Nat)
    (intake : NormalizedLeafIntake raw center) (fuel left right : Nat)
    (different : raw.atomZAt left ≠ raw.atomZAt right) :
    (parsedInput raw).compareBranches? fuel center left right =
      some (compare (raw.atomZAt left) (raw.atomZAt right)) := by
  rw [actual_legacy_strict_branch (parsedInput raw) fuel center left right (by
    simpa only [actual_parsed_atomic_number raw center intake] using different),
    actual_parsed_atomic_number raw center intake, actual_parsed_atomic_number raw center intake]

theorem actual_parsed_written_order (raw : RawMolecule) (center : Nat)
    (intake : NormalizedLeafIntake raw center) (index : Nat) (bound : index < raw.atomCount) :
    (parsedInput raw).writtenNeighbors index = raw.writtenNeighbors index := by
  rw [actual_parsed_record raw center intake,
    ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.materialized_record_written_order
      raw.normalizeUnspecifiedBonds index bound,
    normalizeUnspecifiedBonds_writtenNeighbors]

theorem actual_parsed_written_exact (raw : RawMolecule) (center : Nat)
    (_intake : NormalizedLeafIntake raw center) : (parsedInput raw).WrittenNeighborExact :=
  withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds

theorem actual_parsed_only_center_tagged (raw : RawMolecule) (center : Nat)
    (intake : NormalizedLeafIntake raw center) (only : OnlyCenterTagged raw center) :
    OnlyCenterTagged (parsedInput raw) center := by
  intro index spec observed tagged
  rw [actual_parsed_atom_lookup raw center intake] at observed
  cases originalLookup : raw.atomAt? index.val with
  | none => simp only [originalLookup, Option.map_none] at observed; cases observed
  | some original =>
      have equal : materializedAtomSpec original = spec := by
        simpa only [originalLookup, Option.map_some, Option.some.injEq] using observed
      subst spec
      have bound : index.val < raw.atomCount := by
        simpa only [actual_parsed_atom_count raw center intake] using index.isLt
      exact only ⟨index.val, bound⟩ original originalLookup tagged

/-- This guard is transported for ALL actual hydrogen demands, not just the zero-demand class. -/
theorem actual_parsed_mass_guard (raw : RawMolecule) (known : raw.rule2MassesKnown? = true) :
    (parsedInput raw).rule2MassesKnown? = true :=
  withExplicitHydrogens_rule2MassesKnown?_eq_true raw.normalizeUnspecifiedBonds known

/-- Actual original-index embedding and tag preservation for ALL demands after normalization. -/
theorem actual_positive_or_zero_atom_transport (raw : RawMolecule) (well : raw.WellFormed)
    (index : Nat) (spec : AtomSpec) (observed : raw.atomAt? index = some spec) :
    (parsedInput raw).atomAt? index = some (materializedAtomSpec spec) :=
  PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.withExplicitHydrogens_originalAtom
    raw.normalizeUnspecifiedBonds (normalizeUnspecifiedBonds_wellFormed raw well) index spec observed

/-- Actual final written-row splicing for ALL demands; it is not guessed identical to input. -/
theorem actual_positive_or_zero_written_transport (raw : RawMolecule) (well : raw.WellFormed)
    (written : raw.WrittenNeighborExact) (center : Nat) (bound : center < raw.atomCount) :
    (parsedInput raw).writtenNeighbors center =
      HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.materializedWrittenRow raw.normalizeUnspecifiedBonds center :=
  HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.withExplicitHydrogens_writtenNeighbors
    raw.normalizeUnspecifiedBonds (normalizeUnspecifiedBonds_wellFormed raw well)
    (normalizeUnspecifiedBonds_writtenNeighborExact raw written) center bound

/-- GENERAL public occurrence success on the ACTUAL preprocessed input, with internally derived
collector and auxiliary state. This is not the distinct higher legacy classifier theorem. -/
theorem actual_parsed_public_occurrence (raw : RawMolecule) (center : Nat)
    (intake : NormalizedLeafIntake raw center)
    (four : (recordNeighbors raw center).length = 4) (only : OnlyCenterTagged raw center)
    (spec : AtomSpec) (observed : raw.atomAt? center = some spec)
    (parity : TetrahedralInputParity) (tag : spec.tetrahedral? = some parity) (extraFuel : Nat) :
    ∃ positions, tetrahedralOccurrenceFact? (parsedInput raw) (extraFuel + 2) center =
      some (recoveredPublicFact center positions
        (RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions))) := by
  apply RuntimeSourceGenericPublicPipelineRecoveryProofs.RuntimeSourceGenericPublicPipelineRecovery.actual_public_fact_exists
    (parsedInput raw) center (actual_parsed_domain raw center intake)
    (actual_parsed_written_exact raw center intake)
    (by simpa only [actual_parsed_neighbors raw center intake] using four)
    (actual_parsed_only_center_tagged raw center intake only)
    (materializedAtomSpec spec) (by
      rw [actual_parsed_atom_lookup raw center intake, observed]; rfl) parity tag extraFuel

/-- SAME ACTUAL parsed input/source, all carriers and own dependency views. Source agreement is
an independent intake condition for the actual materialized records, not a foreign-source cast. -/
theorem actual_parsed_source_assignment (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement (parsedInput raw) source) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (intake : NormalizedLeafIntake raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (spec : AtomSpec) (observed : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (tag : spec.tetrahedral? = some parity)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    ∃ descriptor,
      constitutionParserRichDescriptor? (parsedInput raw) source agreement
        (actual_parsed_written_exact raw center.1.val intake)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1)) =
          some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning (parsedInput raw) source agreement
        (actual_parsed_written_exact raw center.1.val intake)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1))
          (.chiral descriptor) := by
  obtain ⟨_, _, descriptor, _, _, _, _, computed, meaning, _⟩ :=
    NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.actual_local_descriptor_transport
      (parsedInput raw) source agreement (actual_parsed_written_exact raw center.1.val intake)
      carrierFuel center (actual_parsed_domain raw center.1.val intake)
      (by simpa only [actual_parsed_neighbors raw center.1.val intake] using four)
      (materializedAtomSpec spec) (by
        rw [actual_parsed_atom_lookup raw center.1.val intake, observed]; rfl)
      parity tag view [] 0
  exact ⟨descriptor, computed, meaning⟩

/-- The general zero-demand ORIGINAL intake class has a genuine annotated CF inhabitant. -/
theorem actual_CF_intake :
    NormalizedLeafIntake RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.ClosedCF.raw 0 :=
  ⟨RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.ClosedCF.actual_domain,
    RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.ClosedCF.actual_zero_hydrogen_demand,
    NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_written_exact⟩

theorem actual_CF_preprocessed_domain :
    SingleLeafDomain (parsedInput RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.ClosedCF.raw) 0 :=
  actual_parsed_domain _ 0 actual_CF_intake

/-- Closed physical-H input: preprocessing genuinely grows the graph and has nonidentity slots. -/
theorem actual_positive_hydrogen_input :
    parsedInput PositiveHydrogenPublicPipelineRecoveryProofs.PositiveHydrogenPublicPipelineRecovery.original =
      PositiveHydrogenPublicPipelineRecoveryProofs.PositiveHydrogenPublicPipelineRecovery.expanded := by
  unfold parsedInput
  rw [PositiveHydrogenPublicPipelineRecoveryProofs.PositiveHydrogenPublicPipelineRecovery.actual_unspecified_normalization]
  rfl

theorem actual_positive_hydrogen_nonidentity :
    PositiveHydrogenPublicPipelineRecoveryProofs.PositiveHydrogenPublicPipelineRecovery.original.hydrogenCountAt 0 = 1 ∧
    PositiveHydrogenPublicPipelineRecoveryProofs.PositiveHydrogenPublicPipelineRecovery.expanded.writtenNeighbors 0 = [4, 1, 2, 3] ∧
    findSlotAlignment? [4, 1, 2, 3] [some 1, some 2, some 3, some 4] = some [1, 2, 3, 0] :=
  ⟨PositiveHydrogenPublicPipelineRecoveryProofs.PositiveHydrogenPublicPipelineRecovery.actual_positive_demand,
    PositiveHydrogenPublicPipelineRecoveryProofs.PositiveHydrogenPublicPipelineRecovery.actual_written_hydrogen_first, by decide +kernel⟩

end TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery
