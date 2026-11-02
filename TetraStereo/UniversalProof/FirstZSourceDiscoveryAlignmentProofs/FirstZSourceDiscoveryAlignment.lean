import TetraStereo.UniversalProof.NonleafSourceParserAlignmentProofs.NonleafSourceParserAlignment
import TetraStereo.UniversalProof.RuntimeLegacyClassifierClosureProofs.RuntimeLegacyClassifierClosure
import TetraStereo.UniversalProof.FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

set_option autoImplicit false

namespace TetraStereo.UniversalProof.FirstZSourceDiscoveryAlignmentProofs.FirstZSourceDiscoveryAlignment

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.RuntimeLegacyClassifierClosureProofs.RuntimeLegacyClassifierClosure
open TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery
open TetraStereo.UniversalProof.NonleafSourceParserAlignmentProofs.NonleafSourceParserAlignment
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery
open TetraStereo.UniversalProof.FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery













/-- Actual runtime and legacy sorters agree through strict atomic ID permutation uniqueness,
without physical-leaf, cycle-free or OnlyCenterTagged hypotheses. -/
theorem runtime_positions_eq_legacy (raw : RawMolecule) (center : Nat)
    (domain : AtomicCenterDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4) (state : OccurrenceAuxState)
    (runtimeFuel legacyFuel : Nat) (result : List CanonicalRerootCursor × Nat)
    (computed : sortOccurrencesTrackedAuthoritative? raw state runtimeFuel
      (generatedRuntimeRoots raw center) = some result) :
    runtimePriorityPositions? raw center result.1 =
      some (legacyPositions raw legacyFuel center (raw.writtenNeighbors center)) := by
  obtain ⟨actual, actualComputed, permutation, strict, _⟩ :=
    actual_generated_sort raw center domain state runtimeFuel
  have sameResult : result = actual := Option.some.inj (computed.symm.trans actualComputed)
  subst result
  have writtenPerm := actual_written_permutation raw center domain written
  have writtenNodup := writtenPerm.nodup_iff.mpr domain.neighbors_nodup
  have distinct := (writtenPerm.map raw.atomZAt).nodup_iff.mpr domain.distinctRanks
  have runtimeIDsPerm : (actual.1.map (fun cursor => cursor.node.atom)).Perm (recordNeighbors raw center) := by
    have mapped := permutation.map (fun cursor => cursor.node.atom)
    rw [NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.generatedRuntimeRoots_eq raw center domain] at mapped
    simpa only [List.map_map, Function.comp_def, canonicalRoot, List.map_id'] using mapped
  have runtimeStrict : (actual.1.map (fun cursor => cursor.node.atom)).Pairwise
      (fun a b => raw.atomZAt b < raw.atomZAt a) := List.pairwise_map.mpr strict
  have legacyStrict : ((legacyPositions raw legacyFuel center (raw.writtenNeighbors center)).map
      (fun position => (raw.writtenNeighbors center).getD position 0)).Pairwise
        (fun a b => raw.atomZAt b < raw.atomZAt a) :=
    List.pairwise_map.mpr (legacy_positions_strict raw legacyFuel center _ distinct)
  have idsEqual := RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.atom_id_order_unique raw _ _
    runtimeStrict legacyStrict
    (runtimeIDsPerm.trans (legacy_sorted_atom_ids_perm raw legacyFuel center _ |>.trans writtenPerm).symm)
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    raw center (writtenPerm.length_eq.trans four)
  unfold runtimePriorityPositions?
  rw [ligands]
  change actual.1.mapM ((writtenSlot? (raw.writtenNeighbors center)) ∘ (fun cursor => cursor.node.atom)) = _
  rw [← List.mapM_map, idsEqual]
  apply written_positions_roundtrip _ writtenNodup
  intro position member
  exact List.mem_range.mp ((legacy_positions_perm raw legacyFuel center _).mem_iff.mp member)

/-- The SAME-source parser's derived label is the ACTUAL legacy first-Z parity formula.
The source old key-frame/sorter are constructed internally by171, not supplied as premises. -/
theorem actual_legacy_source_label (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement raw source) (written : raw.WrittenNeighborExact)
    (carrierFuel legacyFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SourceAtomicDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (spec : AtomSpec) (observed : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (tagged : spec.tetrahedral? = some parity)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    let label := descriptorOfParity parity (permutationIsEven
      (legacyPositions raw legacyFuel center.1.val (raw.writtenNeighbors center.1.val)))
    constitutionParserRichDescriptor? raw source agreement written
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) = some (.chiral label) ∧
    ConstitutionParserRichDescriptorMeaning raw source agreement written
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) (.chiral label) := by
  obtain ⟨result, positions, descriptor, _, runtimeComputed, positionsComputed, formula,
      parserComputed, meaning, _⟩ := actual_runtime_formal_descriptor_transport raw source
    agreement written carrierFuel center domain four noDouble spec observed parity tagged view [] 0
  have samePositions := Option.some.inj (positionsComputed.symm.trans
    (runtime_positions_eq_legacy raw center.1.val domain.atomic written four [] 0 legacyFuel
      result runtimeComputed))
  have labelEqual : descriptor = descriptorOfParity parity (permutationIsEven
      (legacyPositions raw legacyFuel center.1.val (raw.writtenNeighbors center.1.val))) := by
    rw [formula, samePositions]
  exact ⟨by simpa only [labelEqual] using parserComputed,
    by simpa only [labelEqual] using meaning⟩

theorem actual_materialized_written (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) : (materialized result).WrittenNeighborExact := by
  rw [materialized, zero_demand_expansion_exact_record result.parsed domain.zero domain.written]
  exact materialized_record_written_exact result.parsed domain.written

/-- Source incident-kind facts describe the original parsed bond records; materialization
preserves those records. No source identity/cursor cast is used. -/
theorem actual_materialized_source_domain (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (observed : result.parsed.atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some parity)
    (incidentKinds : ∀ bond ∈ result.parsed.bonds,
      bond.source = index ∨ bond.target = index → bond.kind = .single) :
    SourceAtomicDomain (materialized result) index := by
  have physical := (domain.tagged index spec parity observed tagged).1
  rw [materialized, zero_demand_expansion_exact_record result.parsed domain.zero domain.written]
  refine ⟨⟨materialized_well_formed result.parsed physical.wellFormed, ?_, ?_, ?_⟩,
    incidentKinds⟩
  · simpa only [materialized_record_atom_count] using physical.centerBound
  · intro atom member
    exact physical.single atom member
  · change ((recordNeighbors result.parsed index).map
      (materializedWrittenRecord result.parsed).atomZAt).Nodup
    have numbers : (materializedWrittenRecord result.parsed).atomZAt = result.parsed.atomZAt :=
      funext (materialized_atomic_number result.parsed)
    rw [numbers]
    exact physical.distinctRanks

theorem actual_materialized_four (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (observed : result.parsed.atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some parity) :
    (recordNeighbors (materialized result) index).length = 4 := by
  rw [materialized, zero_demand_expansion_exact_record result.parsed domain.zero domain.written]
  exact (domain.tagged index spec parity observed tagged).2.1

/-- ACTUAL whole discovered runtime tag and the SAME materialized source's parser agree at
every own-source dependency view. Source agreement is for the actual materialized input. -/
theorem actual_discovered_source_alignment (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement (materialized result) source)
    (carrierFuel fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (spec : AtomSpec) (observed : result.parsed.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (tagged : spec.tetrahedral? = some parity)
    (incidentKinds : ∀ bond ∈ result.parsed.bonds,
      bond.source = center.1.val ∨ bond.target = center.1.val → bond.kind = .single)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    (discoverRawDescriptors result (materialized result) fuel).factAt? center.1.val =
      some (seedFact result fuel center.1.val parity) ∧
    constitutionParserRichDescriptor? (materialized result) source agreement
      (actual_materialized_written result domain)
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) = some (.chiral (seedDescriptor result fuel center.1.val parity)) ∧
    ConstitutionParserRichDescriptorMeaning (materialized result) source agreement
      (actual_materialized_written result domain)
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) (.chiral (seedDescriptor result fuel center.1.val parity)) := by
  have intake := actual_materialized_legacy_intake result domain center.1.val spec parity observed tagged
  have sourceDomain := actual_materialized_source_domain result domain center.1.val spec parity
    observed tagged incidentKinds
  have four := actual_materialized_four result domain center.1.val spec parity observed tagged
  have parser := actual_legacy_source_label (materialized result) source agreement
    (actual_materialized_written result domain) carrierFuel fuel center sourceDomain four noDouble
    (materializedAtomSpec spec) intake.observed parity intake.tagged view
  exact ⟨actual_discovered_tag result domain fuel center.1.val spec parity observed tagged, parser⟩

/-- Internally scheduled source model, never a caller-provided state. -/
noncomputable def ownState (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement (materialized result) source) (carrierFuel : Nat) :
    source.AromaticCanonicalAuxiliaryState carrierFuel :=
  constitutionParserRichScheduledState (materialized result) source agreement
    (actual_materialized_written result domain) carrierFuel (2 * (carrierFuel + 1))

theorem ownState_cipModel (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement (materialized result) source) (carrierFuel : Nat) :
    (source.aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics (materialized result) source agreement
        (actual_materialized_written result domain) carrierFuel
        (2 * (carrierFuel + 1)))).CIPModel (ownState result domain source agreement carrierFuel) :=
  constitutionParserRichScheduledState_cipModel (materialized result) source agreement
    (actual_materialized_written result domain) carrierFuel (2 * (carrierFuel + 1))

/-- No supplied state/view/output premise: the final view is the actual dependency view of the
SAME source's internally scheduled model, and the runtime fact is the actual whole discovery. -/
theorem actual_discovered_own_model_alignment (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement (materialized result) source)
    (carrierFuel fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (spec : AtomSpec) (observed : result.parsed.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (tagged : spec.tetrahedral? = some parity)
    (incidentKinds : ∀ bond ∈ result.parsed.bonds,
      bond.source = center.1.val ∨ bond.target = center.1.val → bond.kind = .single)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond) :
    (discoverRawDescriptors result (materialized result) fuel).factAt? center.1.val =
      some (seedFact result fuel center.1.val parity) ∧
    ownState result domain source agreement carrierFuel
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) =
        some (.chiral (seedDescriptor result fuel center.1.val parity)) ∧
    ConstitutionParserRichDescriptorMeaning (materialized result) source agreement
      (actual_materialized_written result domain)
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)
      (source.aromaticCanonicalDependencyView (ownState result domain source agreement carrierFuel)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center))
      (2 * (carrierFuel + 1)) (.chiral (seedDescriptor result fuel center.1.val parity)) := by
  obtain ⟨discovered, parser, meaning⟩ := actual_discovered_source_alignment result domain source
    agreement carrierFuel fuel center spec observed parity tagged incidentKinds noDouble
    (source.aromaticCanonicalDependencyView (ownState result domain source agreement carrierFuel)
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
  have evaluated := constitutionParserRichModel_evaluates (materialized result) source agreement
    (actual_materialized_written result domain) (ownState result domain source agreement carrierFuel)
    (ownState_cipModel result domain source agreement carrierFuel)
    (source.aromaticCanonicalFinalOccurrence carrierFuel center)
  exact ⟨discovered, evaluated.symm.trans parser, meaning⟩

end TetraStereo.UniversalProof.FirstZSourceDiscoveryAlignmentProofs.FirstZSourceDiscoveryAlignment
