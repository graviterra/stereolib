import TetraStereo.UniversalProof.NonleafPositiveHydrogenPipelineRecoveryProofs.NonleafPositiveHydrogenPipelineRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ValenceCompleteCyclicHydrogenWitnessProofs.ValenceCompleteCyclicHydrogenWitness

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery
open TetraStereo.UniversalProof.RuntimeLegacyClassifierClosureProofs.RuntimeLegacyClassifierClosure
open TetraStereo.UniversalProof.RuntimePositiveHydrogenDomainRecoveryProofs.RuntimePositiveHydrogenDomainRecovery
open TetraStereo.UniversalProof.NonleafSourceParserAlignmentProofs.NonleafSourceParserAlignment
open TetraStereo.UniversalProof.NonleafPositiveHydrogenPipelineRecoveryProofs.NonleafPositiveHydrogenPipelineRecovery
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
















def smiles : String := "[C@@H](C1([H])C([H])([H])C1([H])[H])(F)Br"

def centerSpec : AtomSpec :=
  { AtomSpec.aliphatic .C with explicitHydrogens? := some 1, tetrahedral? := some .clockwise }

def physicalH : AtomSpec := { AtomSpec.aliphatic .H with explicitHydrogens? := some 0 }

/-- Explicitly exposed actual parser records, including the ring placeholder's resolved slot.
`actual_parse` binds this record to the production parser, rather than accepting it as input. -/
def raw : RawMolecule :=
  { atoms := [centerSpec, AtomSpec.aliphatic .C, physicalH, AtomSpec.aliphatic .C,
      physicalH, physicalH, AtomSpec.aliphatic .C, physicalH, physicalH,
      AtomSpec.aliphatic .F, AtomSpec.aliphatic .Br]
    bonds := [⟨0, 1, .single⟩, ⟨1, 6, .single⟩, ⟨1, 2, .single⟩,
      ⟨1, 3, .single⟩, ⟨3, 4, .single⟩, ⟨3, 5, .single⟩, ⟨3, 6, .single⟩,
      ⟨6, 7, .single⟩, ⟨6, 8, .single⟩, ⟨0, 9, .single⟩, ⟨0, 10, .single⟩]
    neighborOrder := [[1, 9, 10], [0, 6, 2, 3], [1], [1, 4, 5, 6],
      [3], [3], [3, 1, 7, 8], [6], [6], [0], [0]]
    introductionPredecessors :=
      [none, some 0, some 1, some 1, some 3, some 3, some 3, some 6, some 6, some 0, some 0] }

theorem actual_parse : parseOpenSMILES smiles = .ok raw := by rfl

theorem actual_original_count : raw.atomCount = 11 := rfl

theorem actual_admissible : raw.StereochemicalAdmissible := by
  apply (stereochemicalAdmissible?_eq_true_iff raw).mp
  decide +kernel

/-- Original center has three physical bonds and exactly one inline hydrogen. -/
theorem actual_center_valence : raw.incidentBondOrderSum 0 = 3 ∧
    raw.hydrogenCountAt 0 = 1 ∧ raw.usedValenceAt 0 = 4 := by decide +kernel

/-- All three ring carbons already have four actual single bonds, including written H atoms. -/
theorem actual_ring_valences :
    [1, 3, 6].map raw.incidentBondOrderSum = [4, 4, 4] ∧
    [1, 3, 6].map raw.hydrogenCountAt = [0, 0, 0] := by decide +kernel

/-- Each original physical H and each halogen has one physical bond and no additional H demand. -/
theorem actual_monovalent_valences :
    [2, 4, 5, 7, 8, 9, 10].map raw.incidentBondOrderSum = [1, 1, 1, 1, 1, 1, 1] ∧
    [2, 4, 5, 7, 8, 9, 10].map raw.hydrogenCountAt = [0, 0, 0, 0, 0, 0, 0] := by decide +kernel

theorem actual_only_one_demand : OneHydrogenDemand raw 0 := by
  refine ⟨by decide +kernel, actual_center_valence.2.1, ?_⟩
  intro index bound different
  change index < 11 at bound
  interval_cases index
  · contradiction
  all_goals decide +kernel

theorem actual_original_domain : SourceAtomicDomain raw 0 := by
  refine ⟨⟨actual_admissible.1.1, by decide +kernel, ?_, by decide +kernel⟩, ?_⟩
  · intro atom member
    change atom ∈ [1, 9, 10] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide +kernel
  · intro bond member _
    change bond ∈ [⟨0, 1, .single⟩, ⟨1, 6, .single⟩, ⟨1, 2, .single⟩,
      ⟨1, 3, .single⟩, ⟨3, 4, .single⟩, ⟨3, 5, .single⟩, ⟨3, 6, .single⟩,
      ⟨6, 7, .single⟩, ⟨6, 8, .single⟩, ⟨0, 9, .single⟩, ⟨0, 10, .single⟩] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem actual_intake : PositiveAtomicIntake raw 0 := by
  refine ⟨actual_original_domain, actual_admissible.1.2, actual_admissible.2,
    actual_only_one_demand, by decide +kernel, ?_⟩
  intro atom member
  change atom ∈ [1, 9, 10] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide +kernel

theorem actual_only_center : OnlyCenterTagged raw 0 := by
  intro index spec observed tagged
  change Fin 11 at index
  fin_cases index <;> simp [raw, atomAt?, listGet?] at observed
  all_goals subst spec
  all_goals simp_all [AtomSpec.aliphatic, physicalH, centerSpec]

theorem actual_cycle_nonleaf : raw.atomLiesInCycle 5 1 = true ∧
    (raw.incidentAtoms 1).length = 4 := by decide +kernel

theorem actual_one_fresh_H : raw.withExplicitHydrogens.atomCount = 12 ∧
    raw.withExplicitHydrogens.atomAt? 11 = some (AtomSpec.aliphatic .H) :=
  ⟨actual_atom_count raw 0 actual_only_one_demand,
    actual_fresh_hydrogen raw 0 actual_intake⟩

theorem actual_written_H_first : raw.withExplicitHydrogens.writtenNeighbors 0 = [11, 1, 9, 10] := by
  rw [actual_written_center raw 0 actual_intake]
  rfl

/-- Production valence sum at each of the four expanded carbon atoms is now exactly four. -/
theorem actual_expanded_carbon_valences :
    [0, 1, 3, 6].map raw.withExplicitHydrogens.incidentBondOrderSum = [4, 4, 4, 4] ∧
    [0, 1, 3, 6].map raw.withExplicitHydrogens.usedValenceAt = [4, 4, 4, 4] := by decide +kernel

theorem actual_expanded_monovalent_valences :
    [2, 4, 5, 7, 8, 9, 10, 11].map raw.withExplicitHydrogens.incidentBondOrderSum =
      [1, 1, 1, 1, 1, 1, 1, 1] := by decide +kernel

theorem actual_expanded_no_demand :
    ∀ index < raw.withExplicitHydrogens.atomCount,
      raw.withExplicitHydrogens.hydrogenCountAt index = 0 :=
  actual_expanded_zero_demand raw 0 actual_intake

theorem actual_expanded_nonleaf_domain : SourceAtomicDomain raw.withExplicitHydrogens 0 ∧
    (recordNeighbors raw.withExplicitHydrogens 0).length = 4 ∧
    raw.withExplicitHydrogens.atomLiesInCycle 5 1 = true ∧
    (raw.withExplicitHydrogens.incidentAtoms 1).length = 4 :=
  ⟨actual_expanded_domain raw 0 actual_intake, actual_four raw 0 actual_intake,
    by decide +kernel, by decide +kernel⟩

theorem actual_parsed_written_H_first : (parsedInput raw).writtenNeighbors 0 = [11, 1, 9, 10] := by
  have normalized : raw.normalizeUnspecifiedBonds = raw := by decide +kernel
  change raw.normalizeUnspecifiedBonds.withExplicitHydrogens.writtenNeighbors 0 = _
  rw [normalized]
  exact actual_written_H_first

/-- Actual higher classifier positions, with H first in the written row and last in priority. -/
theorem actual_legacy_positions : legacyPositions (parsedInput raw) (analysisFuel (parsedInput raw))
    0 ((parsedInput raw).writtenNeighbors 0) = [3, 2, 1, 0] := by decide +kernel

theorem actual_higher_R : parsedTetrahedralDescriptorAt? raw 0 = some .R := by
  have computed := actual_parsed_classifier raw 0 actual_intake centerSpec rfl .clockwise rfl
    (by decide +kernel) (by decide +kernel)
  simpa only [actual_legacy_positions] using computed

/-- This is the actual string entry point, not only a hand-assembled raw input. -/
theorem actual_smiles_higher_R : smilesTetrahedralDescriptorAt? smiles 0 = some .R := by
  rw [smilesTetrahedralDescriptorAt?, actual_parse]
  exact actual_higher_R

theorem actual_public_R (extraFuel : Nat) :
    tetrahedralOccurrenceFact? (parsedInput raw) ((parsedInput raw).atomCount + 1 + extraFuel) 0 =
      some (recoveredPublicFact 0 [3, 2, 1, 0] .R) := by
  have computed := actual_parsed_public_legacy_positions raw 0 actual_intake actual_only_center
    centerSpec rfl .clockwise rfl extraFuel
  simpa only [actual_legacy_positions] using computed

/-- OWN authoritative source converted from the actual normalized/materialized parser records. -/
def source : AuthoritativeChemicalInput :=
  (parsedInput raw).toAuthoritativeChemicalInput?.getD
    { molecule := { atoms := [], interactions := [] } }

def atom (index : Fin 12) : source.AromaticCanonicalAtom :=
  ⟨index.val, by change index.val < 12; exact index.isLt⟩

def center : source.AromaticCanonicalTetrahedralCenter :=
  ⟨atom 0, (mem_aromaticCanonicalTetrahedralCenterSet_iff _ _).mpr ⟨by
    unfold ConnectivityOnlyTetrahedralCenterAtom ConnectivityOnlyTetrahedralPeriodicElement
    decide +kernel, by
      have neighbors : source.aromaticCanonicalNeighborFinset (atom 0) =
          {atom 1, atom 9, atom 10, atom 11} := by
        ext neighbor
        rw [mem_aromaticCanonicalNeighborFinset_iff]
        change Fin 12 at neighbor
        fin_cases neighbor <;> unfold AromaticCanonicalAdjacent <;> decide +kernel
      rw [neighbors]
      decide +kernel⟩⟩

theorem actual_conversion : (parsedInput raw).toSemanticMolecule? = some source.molecule := by
  decide +kernel

theorem actual_annotation_agreement : RawAnnotationAgreement (parsedInput raw) source := by
  apply (rawAnnotationAgreement_iff (parsedInput raw) source).mpr
  exact ⟨actual_conversion, by decide +kernel⟩

theorem actual_no_double : source.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  have different : source.molecule.aromaticCanonicalBondOrder left.val right.val ≠ 2 := by
    change Fin 12 at left right
    fin_cases left <;> fin_cases right <;> decide +kernel
  exact different ordinary.2

/-- The same nominal source retains the physical ring and all five written ring hydrogens. -/
theorem actual_source_ring_and_hydrogens :
    source.AromaticCanonicalAdjacent (atom 1) (atom 3) ∧
    source.AromaticCanonicalAdjacent (atom 3) (atom 6) ∧
    source.AromaticCanonicalAdjacent (atom 6) (atom 1) ∧
    source.AromaticCanonicalAdjacent (atom 1) (atom 2) ∧
    source.AromaticCanonicalAdjacent (atom 3) (atom 4) ∧
    source.AromaticCanonicalAdjacent (atom 3) (atom 5) ∧
    source.AromaticCanonicalAdjacent (atom 6) (atom 7) ∧
    source.AromaticCanonicalAdjacent (atom 6) (atom 8) ∧
    source.AromaticCanonicalAdjacent (atom 0) (atom 11) := by
  unfold AromaticCanonicalAdjacent
  decide +kernel

/-- Closed all-carrier/view OWN source parser assignment with independent descriptor meaning.
R is obtained from the real public record, not passed to the source model as an input. -/
theorem actual_parser_R (carrierFuel : Nat)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    constitutionParserRichDescriptor? (parsedInput raw) source actual_annotation_agreement
      (withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds)
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) = some (.chiral .R) ∧
    ConstitutionParserRichDescriptorMeaning (parsedInput raw) source actual_annotation_agreement
      (withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds)
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
      (2 * (carrierFuel + 1)) (.chiral .R) := by
  obtain ⟨positions, descriptor, publicComputed, parserComputed, meaning, _⟩ :=
    actual_parsed_public_source_alignment raw source carrierFuel center actual_intake
      actual_annotation_agreement actual_no_double actual_only_center centerSpec rfl
      .clockwise rfl view 0
  have factsEqual := Option.some.inj (publicComputed.symm.trans (actual_public_R 0))
  have descriptorEqual : descriptor = .R := congrArg RawDescriptorFact.descriptor factsEqual
  simpa only [descriptorEqual] using And.intro parserComputed meaning

end TetraStereo.UniversalProof.ValenceCompleteCyclicHydrogenWitnessProofs.ValenceCompleteCyclicHydrogenWitness
