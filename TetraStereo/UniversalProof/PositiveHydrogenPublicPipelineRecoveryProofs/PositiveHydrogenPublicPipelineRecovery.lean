import TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.PositiveHydrogenPublicPipelineRecoveryProofs.PositiveHydrogenPublicPipelineRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
open TetraStereo.UniversalProof.RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge

















abbrev original : RawMolecule := NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery.InlineHydrogenWitness.original
abbrev expanded : RawMolecule := NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery.InlineHydrogenWitness.expanded
abbrev source : AuthoritativeChemicalInput := RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment.InlineHydrogen.source

/-- The real original parity tag and positive inline demand already belong to the source input. -/
theorem actual_original_input : original.atomAt? 0 =
    some PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCenterSpec :=
  PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide_centerSpec_lookup

theorem actual_positive_demand : original.hydrogenCountAt 0 = 1 :=
  PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide_centerHydrogens

theorem actual_atom_count_growth : original.atomCount = 4 ∧ expanded.atomCount = 5 := by
  decide +kernel

def expandedCenterSpec : AtomSpec := materializedAtomSpec PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCenterSpec

theorem actual_expanded_atoms : expanded.atoms =
    [expandedCenterSpec,
      { AtomSpec.aliphatic .F with explicitHydrogens? := some 0 },
      { AtomSpec.aliphatic .Cl with explicitHydrogens? := some 0 },
      { AtomSpec.aliphatic .Br with explicitHydrogens? := some 0 },
      AtomSpec.aliphatic .H] := by
  decide +kernel

theorem actual_appended_hydrogen : expanded.atomAt? 4 = some (AtomSpec.aliphatic .H) :=
  PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide_expansion_boundary_hydrogen

theorem actual_materialized_center : expanded.atomAt? 0 = some expandedCenterSpec := by
  rw [atomAt?, actual_expanded_atoms]
  rfl

theorem actual_center_parity : expandedCenterSpec.tetrahedral? = some TetrahedralInputParity.clockwise :=
  PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide_expanded_center_tetrahedral

theorem actual_center_consumed_inline : expandedCenterSpec.explicitHydrogens? = some 0 :=
  PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide_expanded_center_inlineConsumed

theorem actual_expanded_conversion : expanded.toSemanticMolecule? = some source.molecule :=
  RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment.InlineHydrogen.actual_conversion

/-- Same ACTUAL expanded raw records and their ACTUAL converted source diagram. -/
theorem actual_annotation_agreement : RawAnnotationAgreement expanded source := by
  apply (rawAnnotationAgreement_iff expanded source).mpr
  exact ⟨actual_expanded_conversion, by decide +kernel⟩

theorem actual_written_exact : expanded.WrittenNeighborExact :=
  (expanded.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)

theorem actual_expanded_domain : SingleLeafDomain expanded 0 :=
  RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment.InlineHydrogen.actual_domain

theorem actual_four_roots : (recordNeighbors expanded 0).length = 4 := by
  rw [NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery.InlineHydrogenWitness.source_neighbor_records]
  rfl

theorem actual_written_hydrogen_first : expanded.writtenNeighbors 0 = [4, 1, 2, 3] := by
  decide +kernel

/-- The perceived center is recovered on the expanded source itself. -/
def center : source.AromaticCanonicalTetrahedralCenter :=
  ⟨RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment.InlineHydrogen.centerAtom,
    (mem_aromaticCanonicalTetrahedralCenterSet_iff _ _).mpr ⟨by
      unfold ConnectivityOnlyTetrahedralCenterAtom ConnectivityOnlyTetrahedralPeriodicElement
      decide +kernel, by
      have neighbors : source.aromaticCanonicalNeighborFinset
          RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment.InlineHydrogen.centerAtom =
          {⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩,
           ⟨3, by decide +kernel⟩, ⟨4, by decide +kernel⟩} := by
        ext neighbor
        rw [mem_aromaticCanonicalNeighborFinset_iff]
        fin_cases neighbor <;> unfold AromaticCanonicalAdjacent <;> decide +kernel
      rw [neighbors]
      decide +kernel⟩⟩

theorem actual_no_double : source.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  have different : source.molecule.aromaticCanonicalBondOrder left.val right.val ≠ 2 := by
    fin_cases left <;> fin_cases right <;> decide +kernel
  exact different ordinary.2

/-- An actual nonidentity written-to-official frame; this is not a caller permutation. -/
theorem actual_nonidentity_official_alignment :
    findSlotAlignment? (expanded.writtenNeighbors center.1.val) (officialRootIDs source center.1) =
      some [1, 2, 3, 0] :=
  RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment.InlineHydrogen.actual_nonidentity_alignment

theorem actual_nonidentity_meaning :
    ExactSlotAlignment (expanded.writtenNeighbors center.1.val) (officialRootIDs source center.1) [1, 2, 3, 0] :=
  RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment.InlineHydrogen.actual_alignment_meaning

theorem actual_identity_false :
    ¬ ExactSlotAlignment (expanded.writtenNeighbors center.1.val) (officialRootIDs source center.1) (List.range 4) :=
  RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment.InlineHydrogen.identity_alignment_false

/-- The parity consequence of this real nonidentity frame at the physical descending slot order.
This finite algebra check does not itself assert an actual source carrier order. -/
theorem actual_parity_distinction :
    SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence.writtenFramePriorityDescriptor TetrahedralInputParity.clockwise
      [1, 2, 3, 0] [(2 : Fin 4), 1, 0, 3] = RS.R ∧
    SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence.writtenFramePriorityDescriptor TetrahedralInputParity.clockwise
      [0, 1, 2, 3] [(2 : Fin 4), 1, 0, 3] = RS.S := by
  decide +kernel

/-- The actual runtime pipeline independently determines its literal positions and label. -/
theorem actual_local_runtime_R : occurrenceFactAuthoritative? expanded 2 [] (canonicalCenterRoot 0) =
    some (recoveredFact 0 [3, 2, 1, 0] RS.R) := by
  decide +kernel

/-- The SAME expanded source/formal view emits R, identified through the actual runtime program,
not by a desired label premise. Its returned carrier frame/alignment remains the actual one. -/
theorem actual_formal_R
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center)) :
    constitutionParserRichDescriptor? expanded source actual_annotation_agreement actual_written_exact
      (source.aromaticCanonicalFinalOccurrence 0 center) view 2 = some (.chiral RS.R) := by
  obtain ⟨positions, descriptor, localComputed, parserComputed, _, _⟩ :=
    actual_runtime_fact_formal_alignment expanded source actual_annotation_agreement actual_written_exact
      0 center actual_expanded_domain actual_four_roots actual_no_double expandedCenterSpec
      actual_materialized_center TetrahedralInputParity.clockwise actual_center_parity view [] 2
  have equalFacts := Option.some.inj (localComputed.symm.trans actual_local_runtime_R)
  have equal : descriptor = RS.R := congrArg OccurrenceAuxFact.descriptor equalFacts
  exact equal ▸ parserComputed

theorem actual_formal_R_meaning
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center)) :
    ConstitutionParserRichDescriptorMeaning expanded source actual_annotation_agreement actual_written_exact
      (source.aromaticCanonicalFinalOccurrence 0 center) view 2 (.chiral RS.R) :=
  constitutionParserRichDescriptor?_sound expanded source actual_annotation_agreement actual_written_exact
    (source.aromaticCanonicalFinalOccurrence 0 center) view 2 (.chiral RS.R) (actual_formal_R view)

/-- No actual noncenter expanded atom has a parity annotation. -/
theorem actual_only_center_tagged : OnlyCenterTagged expanded 0 := by
  intro index spec observed tagged
  change Fin 5 at index
  change listGet? expanded.atoms index.val = some spec at observed
  rw [actual_expanded_atoms] at observed
  fin_cases index <;> simp only [listGet?, Option.some.injEq] at observed
  all_goals subst spec
  all_goals simp_all [expandedCenterSpec, materializedAtomSpec, AtomSpec.aliphatic]

def leaves : List RawMolecule.CanonicalBranchNode :=
  [canonicalRoot 0 4, canonicalRoot 0 1, canonicalRoot 0 2, canonicalRoot 0 3]

def actualTree : List RawMolecule.CanonicalBranchNode := canonicalCenterRoot 0 :: leaves

theorem actual_first_frontier : expanded.canonicalChildren (canonicalCenterRoot 0) = leaves := by
  decide +kernel

theorem actual_leaf_frontier : leaves.flatMap expanded.canonicalChildren = [] := by
  decide +kernel

theorem actual_collected_tree (extraFuel : Nat) :
    collectCanonicalTreeAuthoritative expanded (extraFuel + 2) [canonicalCenterRoot 0] = some actualTree := by
  simp only [collectCanonicalTreeAuthoritative, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, actual_first_frontier]
  have leafCollected : collectCanonicalTreeAuthoritative expanded (extraFuel + 1) leaves = some leaves := by
    change (do
      let tail ← collectCanonicalTreeAuthoritative expanded extraFuel
        (leaves.flatMap expanded.canonicalChildren)
      some (leaves ++ tail)) = some leaves
    rw [actual_leaf_frontier, collected_empty]
    rfl
  rw [leafCollected]
  rfl

theorem actual_auxiliary_state (extraFuel : Nat) :
    buildOccurrenceAuxStateFullyAuthoritative? expanded (extraFuel + 2) 0 = some [] :=
  auxiliary_state_empty_of_actual_tree expanded (extraFuel + 2) 0 actual_only_center_tagged actualTree
    (actual_collected_tree extraFuel)

/-- The actual public occurrence API also consumes its own internally derived state. -/
theorem actual_public_occurrence_R (extraFuel : Nat)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center)) :
    ∃ positions, tetrahedralOccurrenceFact? expanded (extraFuel + 2) 0 =
      some (recoveredPublicFact 0 positions RS.R) := by
  obtain ⟨positions, descriptor, localComputed, parserComputed, _, _⟩ :=
    actual_runtime_fact_formal_alignment expanded source actual_annotation_agreement actual_written_exact
      0 center actual_expanded_domain actual_four_roots actual_no_double expandedCenterSpec
      actual_materialized_center TetrahedralInputParity.clockwise actual_center_parity view [] (extraFuel + 2)
  have equal : descriptor = RS.R := by
    exact LocalizedTetrahedralRSPseudoDescriptor.chiral.inj
      (Option.some.inj (parserComputed.symm.trans (actual_formal_R view)))
  refine ⟨positions, ?_⟩
  exact public_fact_of_actual_local_fact expanded (extraFuel + 2) 0 actual_only_center_tagged
    actualTree (actual_collected_tree extraFuel) positions RS.R (equal ▸ localComputed)

theorem actual_unspecified_normalization : original.normalizeUnspecifiedBonds = original := by
  decide +kernel

/-- Actual public classifier after positive hydrogen materialization, on its OWN converted graph. -/
theorem actual_expanded_public_R : expandedTetrahedralDescriptorAt? expanded 0 = some RS.R := by
  decide +kernel

/-- Actual parsed intake, not a renamed source evaluator: original → normalization → expansion. -/
theorem actual_parsed_public_R : parsedTetrahedralDescriptorAt? original 0 = some RS.R := by
  unfold parsedTetrahedralDescriptorAt?
  rw [actual_unspecified_normalization]
  exact actual_expanded_public_R

/-- Closed actual public/formal agreement on the SAME hydrogen-expanded constitution. -/
theorem actual_public_formal_agreement
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center)) :
    parsedTetrahedralDescriptorAt? original 0 = some RS.R ∧
      constitutionParserRichDescriptor? expanded source actual_annotation_agreement actual_written_exact
        (source.aromaticCanonicalFinalOccurrence 0 center) view 2 = some (.chiral RS.R) ∧
      ConstitutionParserRichDescriptorMeaning expanded source actual_annotation_agreement actual_written_exact
        (source.aromaticCanonicalFinalOccurrence 0 center) view 2 (.chiral RS.R) :=
  ⟨actual_parsed_public_R, actual_formal_R view, actual_formal_R_meaning view⟩

end TetraStereo.UniversalProof.PositiveHydrogenPublicPipelineRecoveryProofs.PositiveHydrogenPublicPipelineRecovery
