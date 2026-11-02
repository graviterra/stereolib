import TetraStereo.UniversalProof.SourceNativePlanarTetrahedralPriorityClosureProofs.SourceNativePlanarTetrahedralPriorityClosure
import TetraStereo.UniversalProof.SourceNativePlanarParserCausalModelProofs.SourceNativePlanarParserCausalModel

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativePlanarRule3UnitProofs.SourceNativePlanarRule3Unit
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence
open TetraStereo.UniversalProof.SourceNativePlanarParserCausalModelProofs.SourceNativePlanarParserCausalModel

























abbrev baseSource := TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.source

def annotatedRaw : RawMolecule :=
  { SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.raw with
    atoms := [{ AtomSpec.aliphatic .C with tetrahedral? := some .clockwise },
      AtomSpec.aliphatic .C, AtomSpec.aliphatic .F, AtomSpec.aliphatic .Br,
      AtomSpec.aliphatic .I, AtomSpec.aliphatic .C, AtomSpec.aliphatic .Cl,
      AtomSpec.aliphatic .F, AtomSpec.aliphatic .Cl] }

def diagram : DiagramConfiguration :=
  { SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.diagram with
    atomConfigurations := annotatedRaw.toDiagramConfiguration.atomConfigurations }

def source : AuthoritativeChemicalInput :=
  { baseSource with diagram? := some diagram }

local instance : NeZero source.molecule.atomCount := ⟨by change (9 : Nat) ≠ 0; decide⟩
local instance : NeZero annotatedRaw.atomCount := ⟨by change (9 : Nat) ≠ 0; decide⟩

theorem actual_constitution_and_positions :
    source.molecule = baseSource.molecule ∧ source.spatial? = none ∧
      diagram.atomPositions? = SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.diagram.atomPositions? ∧
      diagram.bonds = SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.diagram.bonds :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem actual_absolute_configuration :
    ({ atom := 0, parity := TetrahedralInputParity.clockwise,
       scope := DiagramConfigurationScope.absolute } : DiagramAtomConfiguration) ∈
      diagram.atomConfigurations := by decide +kernel

theorem actual_conversion : annotatedRaw.toSemanticMolecule? = some source.molecule := by
  decide +kernel

theorem actual_written_exact : annotatedRaw.WrittenNeighborExact :=
  (annotatedRaw.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)

theorem actual_record_audit_nil : rawAnnotationAgreementIssues annotatedRaw source = [] := by
  decide +kernel

theorem actual_annotation_agreement : RawAnnotationAgreement annotatedRaw source :=
  ⟨actual_conversion,
    (rawAnnotationAgreementIssues_eq_nil_iff annotatedRaw source).mp actual_record_audit_nil⟩

def normalized : ChemistryNormalizationResult := normalizeRawMolecule annotatedRaw

theorem actual_normalized_parsed : normalized.parsed = annotatedRaw := rfl

def certified : CertifiedChemistryNormalizationResult where
  result := normalized
  admissible := (normalized.parsed.admissible?_eq_true_iff).mp (by decide +kernel)
  writtenNeighborExact :=
    (normalized.parsed.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)
  valenceOK := (normalized.parsed.valenceOK?_eq_true_iff).mp (by decide +kernel)
  rule2MassesKnown := (normalized.parsed.rule2MassesKnown?_eq_true_iff).mp (by decide +kernel)

theorem actual_normalization_binding :
    certified.result = normalizeRawMolecule annotatedRaw ∧
      certified.result.parsed = annotatedRaw := ⟨rfl, actual_normalized_parsed⟩

noncomputable def center : source.AromaticCanonicalTetrahedralCenter :=
  SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.center

noncomputable def target : source.AromaticCanonicalOccurrence 1 :=
  source.aromaticCanonicalFinalOccurrence 1 center

abbrev Atom := source.AromaticCanonicalAtom

def rootNode : OfficialCIPNode Atom := OfficialCIPNode.root 0

theorem actual_root_children : source.molecule.aromaticCanonicalOfficialCIPChildrenAt 9 rootNode =
    [rootNode.extend 1 0, rootNode.extend 2 0, rootNode.extend 3 0, rootNode.extend 4 0] := by
  decide +kernel

def firstFrame (slot : Fin 4) : source.AromaticCanonicalOccurrenceFrame :=
  { root := 0, address := [slot.val]
    node := rootNode.extend ⟨slot.val + 1, by change slot.val + 1 < 9; omega⟩ 0, remaining := 1 }

noncomputable def firstOccurrence (slot : Fin 4) : source.AromaticCanonicalOccurrence 1 :=
  ⟨firstFrame slot, by
    apply (source.mem_aromaticCanonicalOccurrences_iff 1 _).mpr
    change source.DeclarativeAromaticCanonicalOccurrenceSubtree 0 [] 2 rootNode (firstFrame slot)
    refine .subtreeDescendant ?_ (.subtreeRoot [slot.val] 1 _)
    have children := actual_root_children
    change source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
      rootNode = _ at children
    rw [children]
    fin_cases slot <;> decide +kernel⟩

noncomputable def firstCursor (slot : Fin 4) : source.AromaticCanonicalRerootCursor 1 :=
  { occurrence := firstOccurrence slot, previous? := some target }

noncomputable def roots : List (source.AromaticCanonicalRerootCursor 1) := List.ofFn firstCursor

theorem actual_four_real_roots : roots.length = 4 ∧
    roots.map (fun cursor => cursor.occurrence.1.node.current?) = [some 1, some 2, some 3, some 4] ∧
    ∀ cursor ∈ roots, cursor.occurrence.1.node.provenance = .realAtom := by
  refine ⟨rfl, rfl, ?_⟩
  intro cursor present
  rcases List.mem_ofFn.mp present with ⟨slot, rfl⟩
  fin_cases slot <;> decide +kernel

theorem actual_returned_roots :
    source.aromaticCanonicalOccurrenceLigandFrame? target = some roots := by
  apply (source.aromaticCanonicalOccurrenceLigandFrame?_eq_some_iff target roots).mpr
  refine ⟨?_, ?_⟩
  · change (List.ofFn firstFrame) = source.intendedAromaticCanonicalRerootChildFrames
      { occurrence := target, previous? := none }
    decide +kernel
  · intro cursor present
    rcases List.mem_ofFn.mp present with ⟨slot, rfl⟩
    rfl

theorem actual_roots_valid :
    ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor :=
  source.aromaticCanonicalOccurrenceLigandFrame_cursor_valid target roots actual_returned_roots

theorem actual_recovered_center :
    source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center :=
  occurrenceTetrahedralCenter?_final source 1 center

theorem actual_raw_index :
    parserIndexViaConversion annotatedRaw source actual_annotation_agreement.1 center =
      (0 : Fin annotatedRaw.atomCount) := rfl

theorem actual_written_frame : rawWrittenLigandFrame annotatedRaw
    (parserIndexViaConversion annotatedRaw source actual_annotation_agreement.1 center) =
      [1, 2, 3, 4] := by
  rw [actual_raw_index]
  rfl

theorem actual_root_ids : occurrenceRootIDs source roots = [some 1, some 2, some 3, some 4] := rfl

theorem actual_slot_alignment : findSlotAlignment?
    (rawWrittenLigandFrame annotatedRaw
      (parserIndexViaConversion annotatedRaw source actual_annotation_agreement.1 center))
    (occurrenceRootIDs source roots) = some [0, 1, 2, 3] := by
  rw [actual_written_frame, actual_root_ids]
  decide +kernel

private theorem left_candidates : ∀ atom : Atom,
    atom ∈ source.aromaticCanonicalRule3Substituents 1 5 ↔ atom = 0 ∨ atom = 6 := by
  simp only [mem_aromaticCanonicalRule3Substituents_iff]
  unfold AromaticCanonicalAdjacent
  decide +kernel

private theorem right_candidates : ∀ atom : Atom,
    atom ∈ source.aromaticCanonicalRule3Substituents 5 1 ↔ atom = 7 ∨ atom = 8 := by
  simp only [mem_aromaticCanonicalRule3Substituents_iff]
  unfold AromaticCanonicalAdjacent
  decide +kernel

theorem own_left_senior :
    source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference 1 5 6 := by
  apply SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.canonical_senior_of_strict_atomic_heads source 1 5 6
  · exact (left_candidates 6).mpr (Or.inr rfl)
  · intro atom present different
    rcases (left_candidates atom).mp present with rfl | rfl
    · change 6 < 17; decide
    · exact (different rfl).elim

theorem own_right_senior :
    source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference 5 1 8 := by
  apply SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.canonical_senior_of_strict_atomic_heads source 5 1 8
  · exact (right_candidates 8).mpr (Or.inr rfl)
  · intro atom present different
    rcases (right_candidates atom).mp present with rfl | rfl
    · change 9 < 17; decide
    · exact (different rfl).elim

def cisUnit : source.AromaticCanonicalRule3SpatialUnitResult := ⟨6, 8, .seqcis⟩

theorem own_unit_canonical : CanonicalAromaticCanonicalPlanarRule3Unit source 1 5 cisUnit := by
  refine ⟨?_, own_left_senior, own_right_senior,
    SourceNativePlanarAlkeneWitnessProofs.SourceNativePlanarAlkeneWitness.pt 0 0,
    SourceNativePlanarAlkeneWitnessProofs.SourceNativePlanarAlkeneWitness.pt 2 0,
    SourceNativePlanarAlkeneWitnessProofs.SourceNativePlanarAlkeneWitness.pt (-1) 1,
    SourceNativePlanarAlkeneWitnessProofs.SourceNativePlanarAlkeneWitness.pt 3 1,
    ?_, ?_, ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
    decide +kernel
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 1 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 5 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 6 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 8 _).mp (by decide +kernel)
  · norm_num [PlanarRule3DoubleBondGeometryProofs.PlanarRule3DoubleBondGeometry.SameSide,
      PlanarRule3DoubleBondGeometryProofs.PlanarRule3DoubleBondGeometry.planarDirectedArea,
      SourceNativePlanarAlkeneWitnessProofs.SourceNativePlanarAlkeneWitness.pt]

theorem actual_planar_seqcis_unit : aromaticCanonicalPlanarRule3Unit? source 1 5 = some cisUnit :=
  (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical source 1 5 cisUnit).mpr own_unit_canonical

noncomputable def ownState : source.AromaticCanonicalAuxiliaryState 1 :=
  planarConstitutionParserRichScheduledState annotatedRaw source actual_annotation_agreement
    actual_written_exact 1 4

theorem ownState_cipModel :
    (source.aromaticCanonicalOccurrenceSystem
      (planarConstitutionParserRichAuxiliarySemantics annotatedRaw source actual_annotation_agreement
        actual_written_exact 1 4)).CIPModel ownState :=
  planarConstitutionParserRichScheduledState_cipModel annotatedRaw source actual_annotation_agreement
    actual_written_exact 1 4

/-- Genuine model evaluation does not assert a successful descriptor or any particular label. -/
theorem ownState_evaluates :
    planarConstitutionParserRichDescriptor? annotatedRaw source actual_annotation_agreement
      actual_written_exact target (source.aromaticCanonicalDependencyView ownState target) 4 =
        ownState target :=
  planarConstitutionParserRichModel_evaluates annotatedRaw source actual_annotation_agreement
    actual_written_exact ownState ownState_cipModel target

/-- TECHNICAL_PROOF_REQUIRED: the actual four-key two-pass compiler and strict sorter at THIS
source must be constructed before this intended clockwise/reverse-priority emission can be proved.
This is an explicitly UNPROVED obligation, not an input premise or a closed witness theorem. -/
def OwnPlanarParserAssignmentObligation : Prop :=
  (∀ view : source.AromaticCanonicalDependencyView target,
    planarConstitutionParserRichDescriptor? annotatedRaw source actual_annotation_agreement
      actual_written_exact target view 4 = some (.chiral RS.R)) ∧
    ownState target = some (.chiral RS.R)

end TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness
