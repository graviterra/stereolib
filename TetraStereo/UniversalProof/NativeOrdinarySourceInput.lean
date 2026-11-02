import TetraStereo.UniversalProof.NativeSourceSingleIncidence
import TetraStereo.OneCenter.AuthoritativeSemanticTetrahedralElementApplicability
import TetraStereo.OneCenter.AuthoritativeSemanticMancudePerceptionBoundary

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge

/-- Actual input-record conditions, independent of stereochemical outputs. -/
structure OrdinarySourceInput (raw : RawMolecule) : Prop where
  well : raw.WellFormed
  written : raw.WrittenNeighborExact
  known : ∀ spec ∈ raw.atoms, spec.element ≠ .wildcard
  single : ∀ bond ∈ raw.bonds, bond.kind = .single

/-- The existing parser-to-source conversion, never a separately chosen source molecule. -/
def ownSource (raw : RawMolecule) : AuthoritativeChemicalInput :=
  raw.toAuthoritativeChemicalInput?.getD { molecule := { atoms := [], interactions := [] } }

theorem actual_source_conversion (raw : RawMolecule) (input : OrdinarySourceInput raw) :
    raw.toAuthoritativeChemicalInput? = some (ownSource raw) := by
  have present := (raw.toAuthoritativeChemicalInput?_isSome).mpr input.known
  cases converted : raw.toAuthoritativeChemicalInput? with
  | none => simp [converted] at present
  | some source => simp [ownSource, converted]

theorem actual_structure_agreement (raw : RawMolecule) (input : OrdinarySourceInput raw) :
    raw.AuthoritativeStructureAgreement (ownSource raw) :=
  raw.authoritativeStructureAgreement_of_toAuthoritativeChemicalInput?
    (ownSource raw) (actual_source_conversion raw input)

/-- The parser-only converter creates no second spatial evidence channel. -/
theorem actual_source_no_spatial (raw : RawMolecule) : (ownSource raw).spatial? = none := by
  cases semanticObserved : raw.toSemanticMolecule? with
  | none => simp [ownSource, RawMolecule.toAuthoritativeChemicalInput?, semanticObserved]
  | some semantic => simp [ownSource, RawMolecule.toAuthoritativeChemicalInput?, semanticObserved]

private theorem filterMap_nil_of_none {Alpha Beta : Type*} (values : List Alpha)
    (f : Alpha → Option Beta) (absent : ∀ value ∈ values, f value = none) :
    values.filterMap f = [] := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      have head := absent first (by simp)
      have tail : ∀ value ∈ rest, f value = none := by
        intro value retained
        exact absent value (List.mem_cons_of_mem first retained)
      simp only [List.filterMap_cons, head]
      exact ih tail

private theorem enumerateFrom_member_lookup {Alpha : Type*} (values : List Alpha)
    (start : Nat) (indexed : Nat × Alpha) (retained : indexed ∈ enumerateFrom start values) :
    ∃ offset, indexed.1 = start + offset ∧ listGet? values offset = some indexed.2 := by
  induction values generalizing start with
  | nil => simp [enumerateFrom] at retained
  | cons first rest ih =>
      simp only [enumerateFrom, List.mem_cons] at retained
      rcases retained with equal | retained
      · subst indexed
        exact ⟨0, by simp, rfl⟩
      · obtain ⟨offset, indexEq, lookup⟩ := ih (start + 1) retained
        exact ⟨offset + 1, by omega, by simpa [listGet?] using lookup⟩

theorem enumerate_member_lookup {Alpha : Type*} (values : List Alpha)
    (indexed : Nat × Alpha) (retained : indexed ∈ enumerate values) :
    listGet? values indexed.1 = some indexed.2 := by
  obtain ⟨offset, indexEq, lookup⟩ := enumerateFrom_member_lookup values 0 indexed retained
  have equal : indexed.1 = offset := by omega
  simpa [equal] using lookup

/-- A copied diagram parity has a real raw annotation at the same index and absolute scope. -/
theorem copied_diagram_annotation_reflects (raw : RawMolecule)
    (configuration : DiagramAtomConfiguration)
    (retained : configuration ∈ raw.toDiagramConfiguration.atomConfigurations) :
    ∃ annotation ∈ rawAtomAnnotations raw,
      configuration.atom = annotation.index ∧ configuration.parity = annotation.parity ∧
        configuration.scope = .absolute := by
  change configuration ∈ ((enumerate raw.atoms).filterMap fun indexed =>
    indexed.2.tetrahedral?.map fun parity =>
      ({ atom := indexed.1, parity := parity } : DiagramAtomConfiguration)) at retained
  obtain ⟨indexed, indexMember, selected⟩ := List.mem_filterMap.mp retained
  have lookup := enumerate_member_lookup raw.atoms indexed indexMember
  have bound : indexed.1 < raw.atomCount :=
    listGet?_eq_some_implies_lt raw.atoms indexed.1 indexed.2 lookup
  cases parityObserved : indexed.2.tetrahedral? with
  | none => simp [parityObserved] at selected
  | some parity =>
      have equal : ({ atom := indexed.1, parity := parity } : DiagramAtomConfiguration) =
          configuration := by simpa [parityObserved] using selected
      subst configuration
      refine ⟨{ index := indexed.1, parity := parity }, ?_, rfl, rfl, rfl⟩
      exact rawAtomAnnotation_mem raw indexed.1 indexed.2 parity bound lookup parityObserved

/-- Every actual raw annotation is copied; all tags are handled together. -/
theorem raw_annotation_has_copied_diagram (raw : RawMolecule)
    (annotation : RawAtomAnnotation) (retained : annotation ∈ rawAtomAnnotations raw) :
    ∃ configuration ∈ raw.toDiagramConfiguration.atomConfigurations,
      configuration.atom = annotation.index ∧ configuration.parity = annotation.parity ∧
        configuration.scope = .absolute := by
  unfold rawAtomAnnotations at retained
  obtain ⟨index, _, selected⟩ := List.mem_filterMap.mp retained
  cases observed : raw.atomAt? index with
  | none => simp [observed] at selected
  | some spec =>
      cases tagged : spec.tetrahedral? with
      | none => simp [observed, tagged] at selected
      | some parity =>
          have equal : ({ index := index, parity := parity } : RawAtomAnnotation) =
              annotation := by simpa [observed, tagged] using selected
          subst annotation
          exact ⟨{ atom := index, parity := parity },
            raw.mem_toDiagramConfiguration_atomConfigurations_of_atomAt?
              index spec parity observed tagged, rfl, rfl, rfl⟩

theorem actual_raw_directions_nil (raw : RawMolecule) (input : OrdinarySourceInput raw) :
    rawBondDirections raw = [] := by
  unfold rawBondDirections
  apply filterMap_nil_of_none
  intro bond retained
  simp [input.single bond retained, ParsedBondKind.directional?]

theorem actual_copied_diagram_bonds_nil (raw : RawMolecule)
    (input : OrdinarySourceInput raw) : raw.toDiagramConfiguration.bonds = [] := by
  change (raw.bonds.filterMap fun bond => match bond.kind with
    | .up => some ({ source := bond.source, target := bond.target, style := .directionalUp } : DiagramBond)
    | .down => some ({ source := bond.source, target := bond.target, style := .directionalDown } : DiagramBond)
    | _ => none) = []
  apply filterMap_nil_of_none
  intro bond retained
  simp [input.single bond retained]

/-- Bidirectional record agreement is proved from the exact copied diagram, not assumed. -/
theorem structure_agreement_record_agreement (raw : RawMolecule)
    (input : OrdinarySourceInput raw) (source : AuthoritativeChemicalInput)
    (structural : raw.AuthoritativeStructureAgreement source) :
    RawAnnotationRecordAgreement raw source := by
  have atomRecords : sourceAtomConfigurations source =
      raw.toDiagramConfiguration.atomConfigurations := by
    simp [sourceAtomConfigurations, structural.2]
  have directions : diagramDirectionalBonds source = [] := by
    simp [diagramDirectionalBonds, structural.2, actual_copied_diagram_bonds_nil raw input]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro annotation retained
    simpa only [atomRecords] using raw_annotation_has_copied_diagram raw annotation retained
  · intro configuration retained
    rw [atomRecords] at retained
    exact copied_diagram_annotation_reflects raw configuration retained
  · intro direction retained
    rw [actual_raw_directions_nil raw input] at retained
    exact False.elim (List.not_mem_nil retained)
  · intro direction retained
    rw [directions] at retained
    exact False.elim (List.not_mem_nil retained)

theorem actual_annotation_agreement (raw : RawMolecule) (input : OrdinarySourceInput raw) :
    RawAnnotationAgreement raw (ownSource raw) :=
  ⟨(actual_structure_agreement raw input).1,
    structure_agreement_record_agreement raw input (ownSource raw)
      (actual_structure_agreement raw input)⟩

theorem actual_annotation_audit_nil (raw : RawMolecule) (input : OrdinarySourceInput raw) :
    rawAnnotationAgreementIssues raw (ownSource raw) = [] :=
  (rawAnnotationAgreement_iff raw (ownSource raw)).mp (actual_annotation_agreement raw input) |>.2

/-- The old parser's whole-source no-double restriction follows from all-single physical records. -/
theorem actual_source_no_double (raw : RawMolecule) (input : OrdinarySourceInput raw) :
    (ownSource raw).NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  let incidence : NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.SingleIncidentDomain raw left.val :=
    ⟨input.well, fun bond retained _ => input.single bond retained⟩
  have order := NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.Incidence.converted_canonical_bond_order
    raw (ownSource raw) (actual_annotation_agreement raw input).1 left incidence right.val
  have notTwo : (ownSource raw).molecule.aromaticCanonicalBondOrder left.val right.val ≠ 2 := by
    rw [order]
    split <;> omega
  exact notTwo ordinary.2

theorem actual_resolved_records (raw : RawMolecule) (input : OrdinarySourceInput raw) :
    ∀ bond ∈ raw.bonds, bond.kind ≠ .unspecified := by
  intro bond retained
  rw [input.single bond retained]
  decide

/-- Actual source center, constructed from physical written degree and element applicability. -/
def actualCenter (raw : RawMolecule) (input : OrdinarySourceInput raw)
    (atom : Fin raw.atomCount) (spec : AtomSpec) (observed : raw.atomAt? atom.val = some spec)
    (eligible : BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement spec.element)
    (four : (raw.writtenNeighbors atom.val).length = 4) :
    (ownSource raw).AromaticCanonicalTetrahedralCenter :=
  ⟨raw.convertedAtomIndex (ownSource raw) (actual_annotation_agreement raw input).1 atom,
    (raw.connectivityOnlyTetrahedralGraphFrameAt_iff_convertedCenter_mem
      (ownSource raw) (actual_annotation_agreement raw input).1 input.written
      (actual_resolved_records raw input) atom).mp ⟨spec, observed, eligible, four⟩⟩

@[simp] theorem actualCenter_index (raw : RawMolecule) (input : OrdinarySourceInput raw)
    (atom : Fin raw.atomCount) (spec : AtomSpec) (observed : raw.atomAt? atom.val = some spec)
    (eligible : BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement spec.element)
    (four : (raw.writtenNeighbors atom.val).length = 4) :
    (actualCenter raw input atom spec observed eligible four).1.val = atom.val := rfl

end TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
