import TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace TetraStereo.UniversalProof.PlanarRuntimeAdjacentLigandWitnessProofs.PlanarRuntimeAdjacentLigandWitness

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery
















def bracket (element : Element) : AtomSpec :=
  { AtomSpec.aliphatic element with explicitHydrogens? := some 0 }

def centerSpec : AtomSpec :=
  { bracket .C with tetrahedral? := some .anticlockwise }

def raw : RawMolecule :=
  { atoms := [centerSpec, bracket .F, bracket .Br, bracket .C, bracket .C,
      bracket .Cl, bracket .H, bracket .H, bracket .C, bracket .C,
      bracket .Cl, bracket .H, bracket .H]
    bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .up⟩,
      ⟨3, 4, .double⟩, ⟨4, 5, .up⟩, ⟨3, 6, .single⟩, ⟨4, 7, .single⟩,
      ⟨0, 8, .up⟩, ⟨8, 9, .double⟩, ⟨9, 10, .down⟩,
      ⟨8, 11, .single⟩, ⟨9, 12, .single⟩]
    neighborOrder := [[1, 2, 3, 8], [0], [0], [0, 4, 6], [3, 5, 7], [4],
      [3], [4], [0, 9, 11], [8, 10, 12], [9], [8], [9]] }

def result : ChemistryNormalizationResult := normalizeRawMolecule raw

def fuel : Nat := analysisFuel raw

def rootCursor (atom : Nat) : CanonicalRerootCursor :=
  { node := canonicalRoot 0 atom, previous? := some (canonicalCenterRoot 0) }

def roots : List CanonicalRerootCursor :=
  [rootCursor 1, rootCursor 2, rootCursor 3, rootCursor 8]

def leftUnit : ChemistryNormalizationResult.Rule3GeometryOccurrence :=
  { left := 3, right := 4, near := 3, distance := 0, geometry := .seqtrans }

def rightUnit : ChemistryNormalizationResult.Rule3GeometryOccurrence :=
  { left := 8, right := 9, near := 8, distance := 0, geometry := .seqcis }

theorem actual_count : raw.atomCount = 13 ∧ fuel = 28 := ⟨rfl, rfl⟩

theorem actual_admissible : raw.StereochemicalAdmissible := by
  apply (stereochemicalAdmissible?_eq_true_iff raw).mp
  decide +kernel

theorem actual_valence_complete :
    [0, 3, 4, 8, 9].map raw.incidentBondOrderSum = [4, 4, 4, 4, 4] ∧
    [1, 2, 5, 6, 7, 10, 11, 12].map raw.incidentBondOrderSum =
      [1, 1, 1, 1, 1, 1, 1, 1] ∧
    (List.range raw.atomCount).map raw.hydrogenCountAt = List.replicate 13 0 := by
  decide +kernel

theorem actual_normalized_and_materialized :
    result.parsed = raw ∧ raw.withExplicitHydrogens = raw := by
  decide +kernel

theorem actual_real_four_frame :
    raw.ligandsWithLonePair 0 = [1, 2, 3, 8] ∧
    occurrenceLigandFrame? raw (canonicalCenterRoot 0) = some roots := by
  decide +kernel

theorem actual_only_center : OnlyCenterTagged raw 0 := by
  intro index spec observed tagged
  change Fin 13 at index
  fin_cases index <;> simp [raw, atomAt?, listGet?] at observed
  all_goals subst spec
  all_goals simp_all [bracket, centerSpec, AtomSpec.aliphatic]

/-- Successful complete collection internally gives the only-center empty auxiliary
state, without any supplied collected tree or successful-collector premise. -/
theorem actual_auxiliary_empty :
    buildOccurrenceAuxStateFullyAuthoritative? raw fuel 0 = some [] := by
  exact TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery.actual_auxiliary_empty
    raw 0 fuel actual_admissible.1.1
    (by decide +kernel) actual_only_center (by decide +kernel)

theorem actual_markers : result.stereobonds.directionalBonds =
    [⟨0, 3, .up⟩, ⟨4, 5, .up⟩, ⟨0, 8, .up⟩, ⟨9, 10, .down⟩] := by
  decide +kernel

/-- Center->near annotations reorient to down relative to the near endpoint;
near senior is center0 over physical H, and far senior is Cl over physical H. -/
theorem actual_absolute_geometry :
    result.perceivedDoubleBondStereo? 3 4 = some .E ∧
    result.perceivedDoubleBondStereo? 8 9 = some .Z := by
  decide +kernel

/-- The proper center frame has two actual constitutional ties, not arbitrary
nonneighbor indices. Directional spelling is not constitutional atom identity. -/
theorem actual_constitutional_tie :
    raw.compareBranchesAuthoritativeStatus 0 3 8 = .tied ∧
    raw.compareBranchesAuthoritativeStatus 0 8 3 = .tied := by
  decide +kernel

theorem actual_occurrence_only_tie :
    compareOccurrenceBranchesComplete? raw [] fuel (rootCursor 3) (rootCursor 8) =
      some { ordering := .eq, pseudo := false, rule4cCarrier? := none } ∧
    compareOccurrenceBranchesComplete? raw [] fuel (rootCursor 8) (rootCursor 3) =
      some { ordering := .eq, pseudo := false, rule4cCarrier? := none } := by
  decide +kernel

theorem actual_generated_geometry_units :
    result.rule3GeometryOccurrencesOnBranch raw 0 3 = [leftUnit] ∧
    result.rule3GeometryOccurrencesOnBranch raw 0 8 = [rightUnit] := by
  decide +kernel

theorem actual_generated_geometry_sequences :
    result.rule3GeometrySequenceOnBranch raw 0 3 = [.seqtrans] ∧
    result.rule3GeometrySequenceOnBranch raw 0 8 = [.seqcis] := by
  decide +kernel

theorem actual_geometry_keys :
    result.rule3CanonicalSignature raw fuel 0 3 = [1] ∧
    result.rule3CanonicalSignature raw fuel 0 8 = [2] := by
  decide +kernel

theorem actual_rule3_comparisons :
    result.compareRule3GeometryAtCenter raw fuel 0 3 8 = .lt ∧
    result.compareRule3GeometryAtCenter raw fuel 0 8 3 = .gt := by
  unfold ChemistryNormalizationResult.compareRule3GeometryAtCenter
    ChemistryNormalizationResult.compareRule3CanonicalSignatures
  rw [actual_geometry_keys.1, actual_geometry_keys.2]
  decide

/-- Geometry-aware constitutional fallthrough decides the two real center roots. -/
theorem actual_official_comparisons :
    compareBranchesThroughOfficialContext? result raw [] fuel 0 3 8 = some .lt ∧
    compareBranchesThroughOfficialContext? result raw [] fuel 0 8 3 = some .gt := by
  decide +kernel

theorem actual_decisive_rule3 :
    decisiveOfficialFamilyForBranches? result raw [] fuel 0 3 8 =
      some CIPRuleFamily.doubleBondGeometry := by decide +kernel

theorem actual_rule3_priority_positions :
    rankBranchPositionsThroughRule3? result raw fuel 0 [1, 2, 3, 8] =
      some [1, 0, 3, 2] := by decide +kernel

theorem actual_official_priority_positions :
    rankBranchPositionsThroughOfficialContext? result raw [] fuel 0 [1, 2, 3, 8] =
      some [1, 0, 3, 2] := by decide +kernel

theorem actual_written_parity :
    raw.writtenNeighbors 0 = [1, 2, 3, 8] ∧
    RawMolecule.permutationIsEven [1, 0, 3, 2] = true ∧
    RawMolecule.descriptorOfParity .anticlockwise true = RS.S := by decide +kernel

/-- The isotope/constitution-only higher helper refuses the actual tie; this is
not a chemical claim that the geometry-distinguished center is nonstereogenic. -/
theorem actual_legacy_parsed_refusal :
    parsedTetrahedralDescriptorAt? raw 0 = none := by decide +kernel

/-- The real Rule1--3 seed constructor assigns at the actual four-way center. -/
theorem actual_rule3_seed_outcome :
    tetrahedralOutcomeThroughRule3 result raw fuel 0 = .tetrahedral RS.S := by
  decide +kernel

def seedFact : RawDescriptorFact :=
  { atom := 0, descriptor := RS.S, uppercase := true, evidenceSize := 0,
    decisiveRule? := none, descriptorDependentPairs := 0,
    priorityPositions := [1, 0, 3, 2] }

/-- The state below is derived by the real constructor, not supplied by a caller. -/
theorem actual_initial_descriptor_state :
    initialRawDescriptorState result raw fuel = [seedFact] := by decide +kernel

/-- The complete public occurrence-only consumer keeps its genuine empty
auxiliary state, then refuses the central adjacent constitutional tie. -/
theorem actual_occurrence_public_refusal :
    tetrahedralOccurrenceFact? raw fuel 0 = none := by
  unfold tetrahedralOccurrenceFact? tetrahedralOccurrenceFactAuthoritative?
  rw [actual_auxiliary_empty]
  decide +kernel

/-- This separately exposed molecular-root constructor currently refuses an
empty descriptor-evidence population after a later-rule family was observed. -/
theorem actual_projected_empty_state_refusal :
    tetrahedralFactFromProjectedState? result raw [] 100 fuel 0 = none := by
  decide +kernel

/-- The actual geometry-aware public annotated branch directly uses strict
Rule3 positions even in the independently constructed empty-auxiliary situation. -/
theorem actual_annotated_empty_state_outcome :
    annotatedTetrahedralOutcome? result raw [] fuel 0 = some (.tetrahedral RS.S) := by
  decide +kernel

/-- The final source state must be constructed internally before any whole
analyzer statement. This finite assertion is deliberately separate from the
local outcome above and has not yet undergone the parent-protected gate. -/
theorem actual_discovered_descriptor_state :
    discoverRawDescriptors result raw fuel = [seedFact] := by decide +kernel

theorem actual_geometry_aware_assignment :
    tetrahedralAssignment? result raw (discoverRawDescriptors result raw fuel) fuel 0 =
      some { unit := .tetrahedral 0, outcome := .tetrahedral RS.S } := by
  rw [actual_discovered_descriptor_state]
  decide +kernel

/-- Actual public analyzer inclusion; the actual discovery state and source
admission are computed by production, not supplied expected-success hypotheses. -/
theorem actual_public_analyzer_emits_S :
    ({ unit := .tetrahedral 0, outcome := .tetrahedral RS.S } : StereoAssignment) ∈
      analyzeNormalized result := by decide +kernel

/-- The observed disagreement identifies two different actual consumers, not a
replacement backend or a transferred expected label. -/
theorem actual_consumer_separation :
    parsedTetrahedralDescriptorAt? raw 0 = none ∧
    tetrahedralOccurrenceFact? raw fuel 0 = none ∧
    ({ unit := .tetrahedral 0, outcome := .tetrahedral RS.S } : StereoAssignment) ∈
      analyzeNormalized result :=
  ⟨actual_legacy_parsed_refusal, actual_occurrence_public_refusal,
    actual_public_analyzer_emits_S⟩

end TetraStereo.UniversalProof.PlanarRuntimeAdjacentLigandWitnessProofs.PlanarRuntimeAdjacentLigandWitness
