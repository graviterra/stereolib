import TetraStereo.OneCenter.IUPACP93RelationalFullereneAuthorityCarrier

set_option autoImplicit false















namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic

noncomputable section

/-! ## Exact release-row index -/

/-- The five relationally instantiated P-93 fullerene release rows.  The separately reviewed
general-methodology provision has no molecule-specific source row and is intentionally absent. -/
inductive P93RelationalFullereneReleaseRow where
  | inherentParent
  | inherentSubstitution
  | noninherentSubstitution
  | chiralSubstituents
  | superimposed
  deriving DecidableEq, Repr

namespace P93RelationalFullereneReleaseRow

def all : List P93RelationalFullereneReleaseRow :=
  [ .inherentParent
  , .inherentSubstitution
  , .noninherentSubstitution
  , .chiralSubstituents
  , .superimposed
  ]

@[simp] theorem all_length : all.length = 5 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

theorem mem_all (row : P93RelationalFullereneReleaseRow) : row ∈ all := by
  cases row <;> decide

end P93RelationalFullereneReleaseRow

/-! ## Bibliographic and row data -/


structure IUPACP93RelationalFullereneBibliographicLocator where
  work : String
  part : String
  artifactSha256 : String
  pdfPage : Nat
  provision : String

/-- ASCII lowercase hexadecimal syntax used by the frozen SHA-256 artifact identifiers. -/
def IUPACP93RelationalFullereneSha256Char (character : Char) : Bool :=
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
    'a', 'b', 'c', 'd', 'e', 'f'].contains character

/-- Minimal integrity of a bibliographic source envelope.  Chemical claims are not validated by
this predicate. -/
structure IUPACP93RelationalFullereneBibliographicLocator.ValidFor
    (locator : IUPACP93RelationalFullereneBibliographicLocator) : Prop where
  workPresent : locator.work ≠ ""
  partPresent : locator.part ≠ ""
  artifactSha256Length : locator.artifactSha256.length = 64
  artifactSha256LowerHex :
    locator.artifactSha256.toList.all IUPACP93RelationalFullereneSha256Char = true
  pdfPagePositive : 0 < locator.pdfPage
  provisionPresent : locator.provision ≠ ""

/-- A printed local tetrahedral fact before conversion to whole-molecule atom numbers.  The
owner ordinal and external offset are source-audited data; neither is read back from executable
relational evidence. -/
structure IUPACP93RelationalFullereneLocalCenterAudit
    (owners : List MolecularFullereneAddend) where
  ownerIndex : Fin owners.length
  externalOffset : Nat
  localCenter : Nat
  citation : P93AuthorityCitationToken
  descriptor : BlueBookP92.CenterDescriptor

/-- Compile one local source fact into whole-addend ownership and the assembled atom index. -/
def IUPACP93RelationalFullereneLocalCenterAudit.compile
    {owners : List MolecularFullereneAddend}
    (audit : IUPACP93RelationalFullereneLocalCenterAudit owners) :
    P93RelationalFullereneSubstituentCIPAssignment where
  owner := owners.get audit.ownerIndex
  unit := .center (audit.externalOffset + audit.localCenter)
  citation := audit.citation
  descriptor := .center audit.descriptor



structure IUPACP93RelationalFullereneAuthorityAuditRow where
  releaseRow : P93RelationalFullereneReleaseRow
  bibliography : IUPACP93RelationalFullereneBibliographicLocator
  source : AuthoritativeChemicalInput
  molecule : RawMolecule
  spatial? : Option SpatialConfiguration
  sourceInputs :
    List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)
  selectedSourceInput? :
    Option (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)
  symmetryInput : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule
  isType4 : Bool
  exteriorSense? : Option FullereneExteriorFaceSense
  originalDerivativeChiral : Bool
  chiralAddends : Finset MolecularFullereneAddend
  printedCageHandedness? : Option (FullereneNumberingKind × FullereneHandedness)
  substituentAssignments : List P93RelationalFullereneSubstituentCIPAssignment

namespace IUPACP93RelationalFullereneAuthorityAuditRow

/-- The exact source and molecule pair owned by a row. -/
def MatchesSourceAndMolecule
    (row : IUPACP93RelationalFullereneAuthorityAuditRow)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule) : Prop :=
  source = row.source ∧ molecule = row.molecule

/-- Exact dependent equality with the row's symmetry input. -/
def MatchesSymmetryInput
    (row : IUPACP93RelationalFullereneAuthorityAuditRow)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule) : Prop :=
  row.MatchesSourceAndMolecule source molecule ∧ HEq input row.symmetryInput

/-- Membership in the exact source-oriented input family transcribed on the row. -/
def MatchesSourceInput
    (row : IUPACP93RelationalFullereneAuthorityAuditRow)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (input : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule) : Prop :=
  row.MatchesSourceAndMolecule source molecule ∧
    ∃ auditedInput ∈ row.sourceInputs, HEq input auditedInput






structure ValidFor
    (row : IUPACP93RelationalFullereneAuthorityAuditRow)
    (source : AuthoritativeChemicalInput) : Prop where
  sourceExact : row.source = source
  bibliographyValid : row.bibliography.ValidFor
  sourceStructurallyWellFormed : source.StructurallyWellFormed
  structureAgreement :
    row.molecule.MolecularFullereneTopologyRepresentationAgreement
      row.symmetryInput.topologyInput.carrier row.spatial? source
  type4IndexExact : (row.isType4 = true) ↔ row.releaseRow = .chiralSubstituents
  type4Shape : row.isType4 = true →
    row.sourceInputs = [] ∧ row.selectedSourceInput? = none ∧
      row.exteriorSense? = none ∧ row.printedCageHandedness? = none
  orientedShape : row.isType4 = false →
    row.sourceInputs ≠ [] ∧
      (∃ selected ∈ row.sourceInputs, row.selectedSourceInput? = some selected) ∧
      row.exteriorSense?.isSome = true ∧ row.printedCageHandedness?.isSome = true
  sourceInputsSymmetryExact : ∀ input ∈ row.sourceInputs,
    HEq input.symmetryInput row.symmetryInput
  substituentPairsNodup :
    (row.substituentAssignments.map fun assignment =>
      (assignment.owner, assignment.unit)).Nodup
  substituentAssignmentsSourceShaped : ∀ assignment ∈ row.substituentAssignments,
    assignment.owner ∈ row.chiralAddends ∧
      P93RelationalFullereneSubstituentAtomCarrier assignment.unit ⊆
        assignment.owner.externalAtoms ∧
      assignment.citation.Valid ∧
      P93FullereneSubstituentDescriptorMatchesUnit assignment.descriptor assignment.unit
  chiralOwnersCovered : ∀ owner ∈ row.chiralAddends,
    ∃ assignment ∈ row.substituentAssignments, assignment.owner = owner
  chiralAddendsPresent :
    (row.releaseRow = .chiralSubstituents ∨ row.releaseRow = .superimposed) →
      row.chiralAddends.Nonempty
  cipAssignmentsPresent :
    (row.releaseRow = .chiralSubstituents ∨ row.releaseRow = .superimposed) →
      row.substituentAssignments ≠ []

/-- One exact assignment claim found in a finite row table.  This is the single public inversion
predicate used both by the mechanically compiled policy and by concrete completeness proofs. -/
def AuditedAssignment
    (rows : List IUPACP93RelationalFullereneAuthorityAuditRow)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)
    (owner : MolecularFullereneAddend)
    (unit : P93FullereneSubstituentStereogenicUnit)
    (citation : P93AuthorityCitationToken)
    (descriptor : P93FullereneSubstituentCIPDescriptor) : Prop :=
  ∃ row ∈ rows, row.MatchesSymmetryInput source molecule input ∧
    ∃ assignment ∈ row.substituentAssignments,
      assignment.owner = owner ∧ assignment.unit = unit ∧
        assignment.citation = citation ∧ assignment.descriptor = descriptor

end IUPACP93RelationalFullereneAuthorityAuditRow

/-! ## Mechanical policy closure -/

namespace P93RelationalFullereneAuthorityPolicy




private def ofAuditRows
    (physicalObservation : P93AuthorityPhysicalObservationPolicy)
    (rows : List IUPACP93RelationalFullereneAuthorityAuditRow) :
    P93RelationalFullereneAuthorityPolicy where
  physicalObservation := physicalObservation
  RawMoleculeObserved source molecule :=
    ∃ row ∈ rows, row.MatchesSourceAndMolecule source molecule
  InputFamilyObserved source molecule spatial? inputs :=
    ∃ row ∈ rows, row.MatchesSourceAndMolecule source molecule ∧
      spatial? = row.spatial? ∧ HEq inputs row.sourceInputs
  InputObserved source molecule spatial? input :=
    ∃ row ∈ rows, row.MatchesSourceInput source molecule input ∧ spatial? = row.spatial?
  ExteriorFaceSenseObserved source molecule input sense :=
    ∃ row ∈ rows, row.MatchesSourceAndMolecule source molecule ∧
      row.exteriorSense? = some sense ∧
        ∃ selected, row.selectedSourceInput? = some selected ∧ HEq input selected
  OriginalDerivativeChiralityObserved source molecule input value :=
    ∃ row ∈ rows, row.MatchesSymmetryInput source molecule input ∧
      row.originalDerivativeChiral = value
  ChiralAddendsObserved source molecule input addends :=
    ∃ row ∈ rows, row.MatchesSymmetryInput source molecule input ∧
      row.chiralAddends = addends
  Type4InputObserved source molecule input :=
    ∃ row ∈ rows, row.MatchesSymmetryInput source molecule input ∧ row.isType4 = true
  PrintedCageHandednessObserved source molecule input kind handedness :=
    ∃ row ∈ rows, row.MatchesSourceAndMolecule source molecule ∧
      row.printedCageHandedness? = some (kind, handedness) ∧
        ∃ selected, row.selectedSourceInput? = some selected ∧ HEq input selected
  SubstituentUnitInAddendEligible source molecule input owner unit :=
    ∃ citation descriptor,
      IUPACP93RelationalFullereneAuthorityAuditRow.AuditedAssignment
        rows source molecule input owner unit citation descriptor
  SubstituentCitationAuthorized source molecule input owner citation unit :=
    ∃ descriptor,
      IUPACP93RelationalFullereneAuthorityAuditRow.AuditedAssignment
        rows source molecule input owner unit citation descriptor
  SubstituentDescriptorAuthorized source molecule input owner unit descriptor :=
    ∃ citation,
      IUPACP93RelationalFullereneAuthorityAuditRow.AuditedAssignment
        rows source molecule input owner unit citation descriptor

end P93RelationalFullereneAuthorityPolicy





structure P93RelationalFullereneSourceAudit where
  row : P93RelationalFullereneReleaseRow →
    IUPACP93RelationalFullereneAuthorityAuditRow
  releaseRowExact : ∀ releaseRow, (row releaseRow).releaseRow = releaseRow
  valid : ∀ releaseRow, (row releaseRow).ValidFor (row releaseRow).source
  sourcesNodup : (P93RelationalFullereneReleaseRow.all.map fun releaseRow =>
    (row releaseRow).source).Nodup
  physicalObservation : P93AuthorityPhysicalObservationPolicy

namespace P93RelationalFullereneSourceAudit

/-- The exact five rows, in frozen release-index order. -/
def rows (audit : P93RelationalFullereneSourceAudit) :
    List IUPACP93RelationalFullereneAuthorityAuditRow :=
  P93RelationalFullereneReleaseRow.all.map audit.row


def policy (audit : P93RelationalFullereneSourceAudit) :
    P93RelationalFullereneAuthorityPolicy :=
  P93RelationalFullereneAuthorityPolicy.ofAuditRows
    audit.physicalObservation audit.rows

@[simp] theorem rows_length (audit : P93RelationalFullereneSourceAudit) :
    audit.rows.length = 5 := by
  simp [rows]

theorem rows_releaseRows_exact (audit : P93RelationalFullereneSourceAudit) :
    audit.rows.map IUPACP93RelationalFullereneAuthorityAuditRow.releaseRow =
      P93RelationalFullereneReleaseRow.all := by
  rw [rows, List.map_map]
  have exactFunction :
      IUPACP93RelationalFullereneAuthorityAuditRow.releaseRow ∘ audit.row = id := by
    funext releaseRow
    exact audit.releaseRowExact releaseRow
  rw [exactFunction, List.map_id]

theorem rows_valid (audit : P93RelationalFullereneSourceAudit) :
    ∀ row ∈ audit.rows, row.ValidFor row.source := by
  intro row member
  simp only [rows, List.mem_map] at member
  obtain ⟨releaseRow, _member, rfl⟩ := member
  exact audit.valid releaseRow

theorem rows_sources_nodup (audit : P93RelationalFullereneSourceAudit) :
    (audit.rows.map IUPACP93RelationalFullereneAuthorityAuditRow.source).Nodup := by
  simpa [rows] using audit.sourcesNodup

end P93RelationalFullereneSourceAudit

end
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93RelationalFullereneAuthorityPolicy.ofAuditRows
assert_kernel_only TetraStereo.OneCenter.P93RelationalFullereneSourceAudit
assert_kernel_only TetraStereo.OneCenter.P93RelationalFullereneSourceAudit.policy
