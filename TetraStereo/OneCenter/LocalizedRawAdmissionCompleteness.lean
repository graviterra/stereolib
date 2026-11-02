import TetraStereo.OneCenter.LocalizedReferenceInput
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedRawAdmission





































































/-! ## Index bounds for the parser diagram materialization -/

/-- Zero-based enumeration is strictly bounded by the list length.  This is the missing generic
fact needed because `RawMolecule.toDiagramConfiguration` uses `enumerate` for atom configurations. -/
theorem mem_enumerateFrom_lt {α : Type*} (values : List α) (start : ℕ) (indexed : ℕ × α)
    (member : indexed ∈ enumerateFrom start values) :
    indexed.1 < start + values.length := by
  induction values generalizing start with
  | nil => simp [enumerateFrom] at member
  | cons head tail inductionHypothesis =>
      simp only [enumerateFrom, List.mem_cons] at member
      rcases member with equality | tailMember
      · subst indexed
        simp
      · have bounded := inductionHypothesis (start + 1) tailMember
        simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bounded

/-- Zero-based form of `mem_enumerateFrom_lt`. -/
theorem mem_enumerate_lt {α : Type*} (values : List α) (indexed : ℕ × α)
    (member : indexed ∈ enumerate values) :
    indexed.1 < values.length := by
  simpa [enumerate] using mem_enumerateFrom_lt values 0 indexed member

/-- Every diagram bond materialized from a well-formed raw molecule has real, distinct
endpoints.  Only `up`/`down` parser bond records are copied into the diagram; the remaining kinds
contribute no diagram bond and impose no obligation. -/
theorem toDiagramConfiguration_diagramBond_indices (molecule : RawMolecule)
    (wellFormed : molecule.WellFormed) (diagramBond : DiagramBond)
    (present : diagramBond ∈ molecule.toDiagramConfiguration.bonds) :
    diagramBond.source < molecule.atomCount ∧
      diagramBond.target < molecule.atomCount ∧
        diagramBond.source ≠ diagramBond.target := by
  simp only [RawMolecule.toDiagramConfiguration, List.mem_filterMap] at present
  obtain ⟨bond, bondPresent, selected⟩ := present
  have endpoints := wellFormed bond bondPresent
  cases kindObserved : bond.kind with
  | unspecified => simp [kindObserved] at selected
  | single => simp [kindObserved] at selected
  | double => simp [kindObserved] at selected
  | triple => simp [kindObserved] at selected
  | aromatic => simp [kindObserved] at selected
  | up =>
      simp [kindObserved] at selected
      subst diagramBond
      exact endpoints
  | down =>
      simp [kindObserved] at selected
      subst diagramBond
      exact endpoints

/-- Every atom-configuration entry materialized from the parser enumeration points at a real atom. -/
theorem toDiagramConfiguration_atomConfiguration_index (molecule : RawMolecule)
    (configuration : DiagramAtomConfiguration)
    (present : configuration ∈ molecule.toDiagramConfiguration.atomConfigurations) :
    configuration.atom < molecule.atomCount := by
  simp only [RawMolecule.toDiagramConfiguration, List.mem_filterMap] at present
  obtain ⟨indexed, indexedPresent, selected⟩ := present
  have indexBound := mem_enumerate_lt molecule.atoms indexed indexedPresent
  cases parityObserved : indexed.2.tetrahedral? with
  | none => simp [parityObserved] at selected
  | some parity =>
      simp [parityObserved] at selected
      subst configuration
      simpa [RawMolecule.atomCount] using indexBound

/-- The copied parser diagram satisfies the diagram-index side condition of authoritative
structural well-formedness as soon as the raw molecule is well formed.  The atom-count bridge
between the semantic and raw molecules is supplied explicitly. -/
theorem toDiagramConfiguration_diagramIndicesWellFormed
    (molecule : RawMolecule) (semantic : SemanticMolecule) (spatial : SpatialConfiguration)
    (semanticCount : semantic.atomCount = molecule.atomCount)
    (wellFormed : molecule.WellFormed) :
    ({ molecule := semantic
       spatial? := some spatial
       diagram? := some molecule.toDiagramConfiguration } :
        AuthoritativeChemicalInput).DiagramIndicesWellFormed := by
  simp only [AuthoritativeChemicalInput.DiagramIndicesWellFormed]
  refine ⟨trivial, ?_, ?_⟩
  · simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    intro diagramBond diagramBondPresent
    have endpoints :=
      toDiagramConfiguration_diagramBond_indices molecule wellFormed diagramBond
        diagramBondPresent
    exact ⟨⟨by simpa [semanticCount] using endpoints.1,
      by simpa [semanticCount] using endpoints.2.1⟩,
      endpoints.2.2⟩
  · simp only [List.all_eq_true, decide_eq_true_eq]
    intro configuration configurationPresent
    have bound :=
      toDiagramConfiguration_atomConfiguration_index molecule configuration configurationPresent
    simpa [semanticCount] using bound

/-! ## The premise supplied by graph readiness rather than assumed -/

/-- **The removed admission premise.**  Graph readiness of the converted semantic molecule already
implies the raw parser structural condition needed by the earlier `certify?` gate.  This is why the
constructive converse does not carry a separate `molecule.WellFormed` hypothesis: that clause of
`AuthoritativeChemicalInput.StructurallyWellFormed` is implied by the later
`LocalizedCIPGraphReady` gate through the checked parser bridge. -/
theorem wellFormed_of_localizedCIPGraphReady
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (ready : semantic.LocalizedCIPGraphReady) :
    molecule.WellFormed :=
  (RawMolecule.toSemanticMolecule?_structurallyWellFormed_iff molecule semantic converted).mp
    ready.1

/-- The source produced by `RawMolecule.toAuthoritativeChemicalInputWithSpatial?`, transported to
the semantic molecule of the readiness hypothesis, is structurally well formed as soon as the
semantic molecule is graph-ready and the spatial list is indexed by the atom list.

The diagram-index clauses are derived, not assumed: they follow from raw well-formedness, which is
itself derived from readiness by `wellFormed_of_localizedCIPGraphReady`. -/
theorem structurallyWellFormed_constructed
    (molecule : RawMolecule) (semantic : SemanticMolecule) (spatial : SpatialConfiguration)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (semanticReady : semantic.StructurallyWellFormed)
    (spatialLength : spatial.positions.length = semantic.atomCount)
    (wellFormed : molecule.WellFormed) :
    ({ molecule := semantic
       spatial? := some spatial
       diagram? := some molecule.toDiagramConfiguration } :
        AuthoritativeChemicalInput).StructurallyWellFormed := by
  have semanticCount : semantic.atomCount = molecule.atomCount :=
    RawMolecule.toSemanticMolecule?_atomCount molecule semantic converted
  have spatialReady :
      ({ molecule := semantic
         spatial? := some spatial
         diagram? := some molecule.toDiagramConfiguration } :
          AuthoritativeChemicalInput).SpatialIndicesWellFormed := by
    rw [AuthoritativeChemicalInput.SpatialIndicesWellFormed]
    simpa using spatialLength
  have diagramReady :
      ({ molecule := semantic
         spatial? := some spatial
         diagram? := some molecule.toDiagramConfiguration } :
          AuthoritativeChemicalInput).DiagramIndicesWellFormed :=
    toDiagramConfiguration_diagramIndicesWellFormed molecule semantic spatial semanticCount
      wellFormed
  exact ⟨semanticReady, spatialReady, diagramReady⟩

/-! ## Constructive raw admission -/

/-- **Constructive converse of `LocalizedReference.admitRawSpatial?_exact`.**

If the raw molecule converts to a graph-ready semantic molecule and the spatial configuration is
indexed by that molecule's atom list, then the actual executable
`LocalizedReference.admitRawSpatial?` returns some input.  The returned input preserves the
semantic molecule exactly, agrees with the raw parser structure (including the copied diagram), and
carries exactly the supplied spatial configuration.

The hypothesis `semantic.LocalizedCIPGraphReady` is the existing localized pair-bond domain.  It is
not narrowed to bond order one: double and triple bonds, and rings, are retained wherever that
predicate accepts them.  Semantic conversion success and graph readiness remain explicit. No
admission success or hand-built certificate is assumed; certification booleans are derived inside
the proof. -/
theorem admitRawSpatial?_complete
    (molecule : RawMolecule) (semantic : SemanticMolecule) (spatial : SpatialConfiguration)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (ready : semantic.LocalizedCIPGraphReady)
    (spatialLength : spatial.positions.length = semantic.atomCount) :
    ∃ input : LocalizedReference.Input,
      LocalizedReference.admitRawSpatial? molecule spatial = some input ∧
        input.certified.certified.input.molecule = semantic ∧
          molecule.AuthoritativeStructureAgreement input.certified.certified.input ∧
            input.certified.certified.input.spatial? = some spatial := by
  have wellFormed : molecule.WellFormed :=
    wellFormed_of_localizedCIPGraphReady molecule semantic converted ready
  let source : AuthoritativeChemicalInput :=
    { molecule := semantic
      spatial? := some spatial
      diagram? := some molecule.toDiagramConfiguration }
  have convertedSource :
      molecule.toAuthoritativeChemicalInputWithSpatial? spatial = some source := by
    unfold RawMolecule.toAuthoritativeChemicalInputWithSpatial?
    rw [converted]
    simp [source]
  have sourceStruct : source.StructurallyWellFormed := by
    simpa [source] using
      structurallyWellFormed_constructed molecule semantic spatial converted ready.1
        spatialLength wellFormed
  have structCheck : source.structurallyWellFormed? = true :=
    (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mpr sourceStruct
  have certifiedSome : source.certify?.isSome = true := by
    unfold AuthoritativeChemicalInput.certify?
    rw [dif_pos structCheck]
    rfl
  obtain ⟨certified, certifiedEq⟩ := Option.isSome_iff_exists.mp certifiedSome
  have certifiedInputEq : certified.input = source :=
    LocalizedNoDoubleReference.certify?_input_eq certifiedEq
  have sourceMolecule : source.molecule = semantic := rfl
  have certifiedReady : certified.input.molecule.LocalizedCIPGraphReady := by
    rw [certifiedInputEq, sourceMolecule]
    exact ready
  have localizedSome : certified.certifyLocalizedCIP?.isSome = true :=
    (CertifiedAuthoritativeChemicalInput.certifyLocalizedCIP?_isSome certified).mpr
      certifiedReady
  obtain ⟨localized, localizedEq⟩ := Option.isSome_iff_exists.mp localizedSome
  let input : LocalizedReference.Input := { certified := localized }
  have admitSourceEq : LocalizedReference.admitSource? source = some input := by
    simp [LocalizedReference.admitSource?, certifiedEq, localizedEq, input]
  have rawEq : LocalizedReference.admitRawSpatial? molecule spatial = some input := by
    simp [LocalizedReference.admitRawSpatial?, convertedSource, admitSourceEq]
  have exactFacts :=
    LocalizedReference.admitRawSpatial?_exact molecule spatial input rawEq
  refine ⟨input, rawEq, ?_, exactFacts.1, exactFacts.2⟩
  have agreement := exactFacts.1.1
  have equality : some semantic = some input.certified.certified.input.molecule := by
    rw [← converted]
    exact agreement
  exact (Option.some.inj equality).symm

/-- Convenience form of `admitRawSpatial?_complete` with the spatial index condition stated on the
raw atom list, which is how a parser-facing caller observes the coordinate convention. -/
theorem admitRawSpatial?_complete_of_rawCount
    (molecule : RawMolecule) (semantic : SemanticMolecule) (spatial : SpatialConfiguration)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (ready : semantic.LocalizedCIPGraphReady)
    (spatialLength : spatial.positions.length = molecule.atomCount) :
    ∃ input : LocalizedReference.Input,
      LocalizedReference.admitRawSpatial? molecule spatial = some input ∧
        input.certified.certified.input.molecule = semantic ∧
          molecule.AuthoritativeStructureAgreement input.certified.certified.input ∧
            input.certified.certified.input.spatial? = some spatial := by
  have semanticCount : semantic.atomCount = molecule.atomCount :=
    RawMolecule.toSemanticMolecule?_atomCount molecule semantic converted
  have spatialLength' : spatial.positions.length = semantic.atomCount := by
    rw [semanticCount]
    exact spatialLength
  exact admitRawSpatial?_complete molecule semantic spatial converted ready spatialLength'

/-- **Exact characterization of raw admission.**  The executable
`LocalizedReference.admitRawSpatial?` succeeds exactly when there is a semantic conversion whose
molecule lies in the localized CIP graph domain and whose spatial configuration has one coordinate
per atom.  The forward direction is the existing success-conditioned exactness theorem; the reverse
direction is the constructive result above.  No internal boolean appears in the statement. -/
theorem admitRawSpatial?_isSome_iff
    (molecule : RawMolecule) (spatial : SpatialConfiguration) :
    (LocalizedReference.admitRawSpatial? molecule spatial).isSome = true ↔
      ∃ semantic : SemanticMolecule,
        molecule.toSemanticMolecule? = some semantic ∧
          semantic.LocalizedCIPGraphReady ∧
            spatial.positions.length = semantic.atomCount := by
  constructor
  · intro accepted
    obtain ⟨input, inputEq⟩ := Option.isSome_iff_exists.mp accepted
    have facts := LocalizedReference.admitRawSpatial?_exact molecule spatial input inputEq
    refine ⟨input.certified.certified.input.molecule, facts.1.1,
      input.certified.graphReady, ?_⟩
    have spatialWellFormed := input.certified.certified.structurallyWellFormed.2.1
    simpa [AuthoritativeChemicalInput.SpatialIndicesWellFormed, facts.2] using spatialWellFormed
  · rintro ⟨semantic, converted, ready, spatialLength⟩
    obtain ⟨input, inputEq, _, _, _⟩ :=
      admitRawSpatial?_complete molecule semantic spatial converted ready spatialLength
    exact Option.isSome_iff_exists.mpr ⟨input, inputEq⟩

/-! ## The no-double source-record restriction

The pipeline of `LocalizedNoDoubleReferenceInput` adds one genuine source-record restriction: no
extracted localized covalent record may have order two.  It is stated below as a hypothesis and
transported through the executable test; it is not a bond-order-one restriction, since order three
is still permitted. -/

/-- Constructive raw admission for the no-double reference input.  The extra hypothesis
`semantic.NoLocalizedDoubleBondRecords` is the actual source-record restriction of
`LocalizedNoDoubleReferenceInput`; the executable `noLocalizedDoubleBondRecords?` test is derived
from it through the generic boolean reflection lemma. -/
theorem admitRawSpatial?_complete_noDouble
    (molecule : RawMolecule) (semantic : SemanticMolecule) (spatial : SpatialConfiguration)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (ready : semantic.LocalizedCIPGraphReady)
    (noDouble : semantic.NoLocalizedDoubleBondRecords)
    (spatialLength : spatial.positions.length = semantic.atomCount) :
    ∃ input : LocalizedNoDoubleReference.Input,
      LocalizedNoDoubleReference.admitRawSpatial? molecule spatial = some input ∧
        input.certified.certified.input.molecule = semantic ∧
          molecule.AuthoritativeStructureAgreement input.certified.certified.input ∧
            input.certified.certified.input.spatial? = some spatial ∧
              input.NoDoubleRecords := by
  have wellFormed : molecule.WellFormed :=
    wellFormed_of_localizedCIPGraphReady molecule semantic converted ready
  let source : AuthoritativeChemicalInput :=
    { molecule := semantic
      spatial? := some spatial
      diagram? := some molecule.toDiagramConfiguration }
  have convertedSource :
      molecule.toAuthoritativeChemicalInputWithSpatial? spatial = some source := by
    unfold RawMolecule.toAuthoritativeChemicalInputWithSpatial?
    rw [converted]
    simp [source]
  have sourceStruct : source.StructurallyWellFormed := by
    simpa [source] using
      structurallyWellFormed_constructed molecule semantic spatial converted ready.1
        spatialLength wellFormed
  have structCheck : source.structurallyWellFormed? = true :=
    (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mpr sourceStruct
  have certifiedSome : source.certify?.isSome = true := by
    unfold AuthoritativeChemicalInput.certify?
    rw [dif_pos structCheck]
    rfl
  obtain ⟨certified, certifiedEq⟩ := Option.isSome_iff_exists.mp certifiedSome
  have certifiedInputEq : certified.input = source :=
    LocalizedNoDoubleReference.certify?_input_eq certifiedEq
  have sourceMolecule : source.molecule = semantic := rfl
  have certifiedReady : certified.input.molecule.LocalizedCIPGraphReady := by
    rw [certifiedInputEq, sourceMolecule]
    exact ready
  have localizedSome : certified.certifyLocalizedCIP?.isSome = true :=
    (CertifiedAuthoritativeChemicalInput.certifyLocalizedCIP?_isSome certified).mpr
      certifiedReady
  obtain ⟨localized, localizedEq⟩ := Option.isSome_iff_exists.mp localizedSome
  have noDoubleCheck : semantic.noLocalizedDoubleBondRecords? = true :=
    (SemanticMolecule.noLocalizedDoubleBondRecords?_eq_true_iff semantic).mpr noDouble
  have localizedNoDouble :
      localized.certified.input.molecule.noLocalizedDoubleBondRecords? = true := by
    rw [LocalizedNoDoubleReference.certifyLocalizedCIP?_certified_eq localizedEq,
      LocalizedNoDoubleReference.certify?_input_eq certifiedEq, sourceMolecule]
    exact noDoubleCheck
  have admitSourceSome :
      (LocalizedNoDoubleReference.admitSource? source).isSome = true := by
    simp [LocalizedNoDoubleReference.admitSource?, certifiedEq, localizedEq, localizedNoDouble]
  have rawSome :
      (LocalizedNoDoubleReference.admitRawSpatial? molecule spatial).isSome = true := by
    simp [LocalizedNoDoubleReference.admitRawSpatial?, convertedSource, admitSourceSome]
  obtain ⟨input, rawEq⟩ := Option.isSome_iff_exists.mp rawSome
  have exactFacts :=
    LocalizedNoDoubleReference.admitRawSpatial?_exact molecule spatial input rawEq
  refine ⟨input, rawEq, ?_, exactFacts.1, exactFacts.2.1, exactFacts.2.2⟩
  have agreement := exactFacts.1.1
  have equality : some semantic = some input.certified.certified.input.molecule := by
    rw [← converted]
    exact agreement
  exact (Option.some.inj equality).symm

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.LocalizedRawAdmission.mem_enumerateFrom_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedRawAdmission.mem_enumerate_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedRawAdmission.toDiagramConfiguration_diagramBond_indices
assert_kernel_only TetraStereo.OneCenter.LocalizedRawAdmission.toDiagramConfiguration_atomConfiguration_index
assert_kernel_only TetraStereo.OneCenter.LocalizedRawAdmission.toDiagramConfiguration_diagramIndicesWellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedRawAdmission.wellFormed_of_localizedCIPGraphReady
assert_kernel_only TetraStereo.OneCenter.LocalizedRawAdmission.structurallyWellFormed_constructed
assert_kernel_only TetraStereo.OneCenter.LocalizedRawAdmission.admitRawSpatial?_complete
assert_kernel_only TetraStereo.OneCenter.LocalizedRawAdmission.admitRawSpatial?_complete_of_rawCount
assert_kernel_only TetraStereo.OneCenter.LocalizedRawAdmission.admitRawSpatial?_isSome_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRawAdmission.admitRawSpatial?_complete_noDouble

end TetraStereo.OneCenter.LocalizedRawAdmission
