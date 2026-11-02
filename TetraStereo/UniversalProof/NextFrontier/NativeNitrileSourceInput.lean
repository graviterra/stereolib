import TetraStereo.UniversalProof.NativeOrdinarySourceInput
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceInput

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery

/-! Nondirectional, resolved-bond source admission. Unlike `OrdinarySourceInput`, this interface
does not require every bond to be single. Every conclusion concerns `ownSource raw`, the actual
conversion of the same input. The generic premises are physical record properties, never successful
key construction, a desired descriptor, a supplied source model or a report result. -/

structure SupportedSourceInput (raw : RawMolecule) : Prop where
  well : raw.WellFormed
  written : raw.WrittenNeighborExact
  known : ∀ spec ∈ raw.atoms, spec.element ≠ .wildcard
  resolved : ∀ bond ∈ raw.bonds, bond.kind ≠ .unspecified
  nondirectional : ∀ bond ∈ raw.bonds, bond.kind.directional? = none

theorem actual_conversion (raw : RawMolecule)
    (known : ∀ spec ∈ raw.atoms, spec.element ≠ .wildcard) :
    raw.toAuthoritativeChemicalInput? = some (ownSource raw) := by
  have present := (raw.toAuthoritativeChemicalInput?_isSome).mpr known
  cases converted : raw.toAuthoritativeChemicalInput? with
  | none => simp [converted] at present
  | some source => simp [ownSource, converted]

theorem actual_structure (raw : RawMolecule)
    (known : ∀ spec ∈ raw.atoms, spec.element ≠ .wildcard) :
    raw.AuthoritativeStructureAgreement (ownSource raw) :=
  raw.authoritativeStructureAgreement_of_toAuthoritativeChemicalInput?
    (ownSource raw) (actual_conversion raw known)

theorem actual_raw_directions_empty (raw : RawMolecule)
    (nondirectional : ∀ bond ∈ raw.bonds, bond.kind.directional? = none) :
    rawBondDirections raw = [] := by
  unfold rawBondDirections
  apply List.filterMap_eq_nil_iff.mpr
  intro bond retained
  simp [nondirectional bond retained]

theorem actual_diagram_directions_empty (raw : RawMolecule)
    (nondirectional : ∀ bond ∈ raw.bonds, bond.kind.directional? = none) :
    raw.toDiagramConfiguration.bonds = [] := by
  change (raw.bonds.filterMap fun bond => match bond.kind with
    | .up => some ({ source := bond.source, target := bond.target, style := .directionalUp } : DiagramBond)
    | .down => some ({ source := bond.source, target := bond.target, style := .directionalDown } : DiagramBond)
    | _ => none) = []
  apply List.filterMap_eq_nil_iff.mpr
  intro bond retained
  have absent := nondirectional bond retained
  cases kind : bond.kind <;> simp [kind, ParsedBondKind.directional?] at absent ⊢

theorem actual_record_agreement (raw : RawMolecule)
    (input : SupportedSourceInput raw) : RawAnnotationRecordAgreement raw (ownSource raw) := by
  have structural := actual_structure raw input.known
  have atomRecords : sourceAtomConfigurations (ownSource raw) =
      raw.toDiagramConfiguration.atomConfigurations := by
    simp [sourceAtomConfigurations, structural.2]
  have directions : diagramDirectionalBonds (ownSource raw) = [] := by
    simp [diagramDirectionalBonds, structural.2,
      actual_diagram_directions_empty raw input.nondirectional]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro annotation retained
    simpa only [atomRecords] using raw_annotation_has_copied_diagram raw annotation retained
  · intro configuration retained
    rw [atomRecords] at retained
    exact copied_diagram_annotation_reflects raw configuration retained
  · intro direction retained
    rw [actual_raw_directions_empty raw input.nondirectional] at retained
    exact False.elim (List.not_mem_nil retained)
  · intro direction retained
    rw [directions] at retained
    exact False.elim (List.not_mem_nil retained)

theorem actual_annotation_agreement (raw : RawMolecule)
    (input : SupportedSourceInput raw) : RawAnnotationAgreement raw (ownSource raw) :=
  ⟨(actual_structure raw input.known).1, actual_record_agreement raw input⟩

theorem actual_annotation_audit_empty (raw : RawMolecule)
    (input : SupportedSourceInput raw) : rawAnnotationAgreementIssues raw (ownSource raw) = [] :=
  (rawAnnotationAgreement_iff raw (ownSource raw)).mp (actual_annotation_agreement raw input) |>.2

def actualCenter (raw : RawMolecule) (input : SupportedSourceInput raw)
    (atom : Fin raw.atomCount) (spec : AtomSpec) (observed : raw.atomAt? atom.val = some spec)
    (eligible : BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement spec.element)
    (four : (raw.writtenNeighbors atom.val).length = 4) :
    (ownSource raw).AromaticCanonicalTetrahedralCenter :=
  ⟨raw.convertedAtomIndex (ownSource raw) (actual_annotation_agreement raw input).1 atom,
    (raw.connectivityOnlyTetrahedralGraphFrameAt_iff_convertedCenter_mem
      (ownSource raw) (actual_annotation_agreement raw input).1 input.written
      input.resolved atom).mp ⟨spec, observed, eligible, four⟩⟩

@[simp] theorem actualCenter_index (raw : RawMolecule) (input : SupportedSourceInput raw)
    (atom : Fin raw.atomCount) (spec : AtomSpec) (observed : raw.atomAt? atom.val = some spec)
    (eligible : BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement spec.element)
    (four : (raw.writtenNeighbors atom.val).length = 4) :
    (actualCenter raw input atom spec observed eligible four).1.val = atom.val := rfl

private theorem lookup_ne_two (records : List ((Nat × Nat) × Nat)) (key : Nat × Nat)
    (noTwo : ∀ record ∈ records, record.2 ≠ 2) :
    SemanticMolecule.localizedBondOrderAtKey records key ≠ 2 := by
  induction records with
  | nil => simp [SemanticMolecule.localizedBondOrderAtKey]
  | cons head tail ih =>
      simp only [SemanticMolecule.localizedBondOrderAtKey]
      split
      · exact noTwo head List.mem_cons_self
      · exact ih (fun record retained => noTwo record (List.mem_cons_of_mem head retained))

/-- Triple bonds do not create ordinary-double stereogenic units. The original all-single
source restriction is therefore unnecessary for this independent readiness fact. -/
theorem actual_source_no_double (raw : RawMolecule)
    (known : ∀ spec ∈ raw.atoms, spec.element ≠ .wildcard)
    (kinds : ∀ bond ∈ raw.bonds, bond.kind = .single ∨ bond.kind = .triple) :
    (ownSource raw).NoAromaticCanonicalOrdinaryDoubleBond := by
  have converted := (actual_structure raw known).1
  have records : ∀ record ∈ (ownSource raw).molecule.localizedCovalentRecords,
      record.2 ≠ 2 := by
    intro record retained
    obtain ⟨interaction, member, selected⟩ := List.mem_filterMap.mp retained
    rw [raw.toSemanticMolecule?_interactions (ownSource raw).molecule converted] at member
    obtain ⟨bond, rawMember, rfl⟩ := List.mem_map.mp member
    rcases kinds bond rawMember with single | triple
    · have equal : (semanticEdgeKey bond.source bond.target, 1) = record := by
        simpa [RawBond.toSemanticInteraction, SemanticInteraction.localizedCovalentRecord?, single]
          using selected
      subst record
      simp
    · have equal : (semanticEdgeKey bond.source bond.target, 3) = record := by
        simpa [RawBond.toSemanticInteraction, SemanticInteraction.localizedCovalentRecord?, triple]
          using selected
      subst record
      simp
  intro left right ordinary
  have notTwo : (ownSource raw).molecule.aromaticCanonicalBondOrder left.val right.val ≠ 2 := by
    unfold SemanticMolecule.aromaticCanonicalBondOrder
    split
    · decide
    · unfold SemanticMolecule.localizedBondOrder
      split
      · decide
      · exact lookup_ne_two _ _ records
  exact notTwo ordinary.2

theorem nitrile_raw_source_no_double (parity : TetrahedralInputParity) (n : Nat) :
    (ownSource (NativeNitrileFamily.raw parity n)).NoAromaticCanonicalOrdinaryDoubleBond :=
  actual_source_no_double _ (NativeNitrileFamily.raw_known_elements parity n)
    (NativeNitrileFamily.raw_bond_kinds parity n)

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceInput
