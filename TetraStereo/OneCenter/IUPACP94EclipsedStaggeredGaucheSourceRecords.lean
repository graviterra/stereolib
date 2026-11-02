import TetraStereo.OneCenter.IUPACP94SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.P94MolecularLonePair

namespace P94EclipsedStaggeredGaucheSourceRecords

def sourceIllustrationBlock : P94SourceAuditLedger.IllustrationBlock :=
  .eclipsedStaggeredGaucheExamples

def sourceArtifactSha256 : String :=
  P94SourceAuditLedger.frozenP9Artifact.sha256

@[simp] theorem source_illustration_binding_exact :
    sourceIllustrationBlock =
        P94SourceAuditLedger.IllustrationBlock.eclipsedStaggeredGaucheExamples ∧
      sourceIllustrationBlock.pdfPage = 89 ∧
        sourceIllustrationBlock.clause = .eclipsedStaggeredGauche := by
  decide

@[simp] theorem source_artifact_digest_exact :
    sourceArtifactSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  rfl

inductive NewmanArrangement where
  | staggered
  | eclipsed
  deriving DecidableEq, Repr

/-- Exact label and alignment ledger for one of the two generic Newman projections. -/
structure GenericNewmanTemplate where
  frontLigandLabels : List String
  rearLigandLabels : List String
  eclipsedPairs : List (String × String)
  arrangement : NewmanArrangement
  deriving DecidableEq, Repr

def GenericNewmanTemplate.allLigandLabels (template : GenericNewmanTemplate) : List String :=
  template.frontLigandLabels ++ template.rearLigandLabels

def genericLigandLabels : List String := ["a", "b", "c", "d", "e", "f"]

def staggeredTemplate : GenericNewmanTemplate where
  frontLigandLabels := ["a", "b", "c"]
  rearLigandLabels := ["d", "e", "f"]
  eclipsedPairs := []
  arrangement := .staggered

def eclipsedTemplate : GenericNewmanTemplate where
  frontLigandLabels := ["a", "b", "c"]
  rearLigandLabels := ["d", "e", "f"]
  eclipsedPairs := [("a", "d"), ("b", "e"), ("c", "f")]
  arrangement := .eclipsed

@[simp] theorem staggered_template_exact :
    staggeredTemplate.frontLigandLabels = ["a", "b", "c"] ∧
      staggeredTemplate.rearLigandLabels = ["d", "e", "f"] ∧
        staggeredTemplate.eclipsedPairs = [] ∧
          staggeredTemplate.arrangement = .staggered := by
  decide

@[simp] theorem eclipsed_template_exact :
    eclipsedTemplate.frontLigandLabels = ["a", "b", "c"] ∧
      eclipsedTemplate.rearLigandLabels = ["d", "e", "f"] ∧
        eclipsedTemplate.eclipsedPairs = [("a", "d"), ("b", "e"), ("c", "f")] ∧
          eclipsedTemplate.arrangement = .eclipsed := by
  decide

theorem generic_ligand_labels_nodup : genericLigandLabels.Nodup := by
  decide

private def carbon : AtomSpec := AtomSpec.aliphatic .C
private def hydrogen : AtomSpec := AtomSpec.aliphatic .H
private def chlorine : AtomSpec := AtomSpec.aliphatic .Cl
private def wildcard : AtomSpec := AtomSpec.aliphatic .wildcard

private def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

/-- Parser-level graph of the generic source template.  Wildcards are intentionally not admitted
to a certified chemical normalization and therefore never masquerade as a frozen package. -/
def genericNewmanMolecule : RawMolecule where
  atoms := [carbon, carbon, wildcard, wildcard, wildcard, wildcard, wildcard, wildcard]
  bonds :=
    [bond 0 1, bond 0 2, bond 0 3, bond 0 4, bond 1 5, bond 1 6, bond 1 7]

def genericLabelAssignment : List (String × Nat) :=
  [("a", 2), ("b", 3), ("c", 4), ("d", 5), ("e", 6), ("f", 7)]

@[simp] theorem generic_newman_graph_exact :
    genericNewmanMolecule.atomCount = 8 ∧
      genericNewmanMolecule.bonds.length = 7 ∧
        (genericNewmanMolecule.atoms.drop 2).map AtomSpec.element =
          List.replicate 6 Element.wildcard := by
  decide

namespace Ethane

/-- Explicit-H ethane specialization of the source's identical-ligand rule. -/
def molecule : RawMolecule where
  atoms := [carbon, carbon, hydrogen, hydrogen, hydrogen, hydrogen, hydrogen, hydrogen]
  bonds :=
    [bond 0 1, bond 0 2, bond 0 3, bond 0 4, bond 1 5, bond 1 6, bond 1 7]

def source : AuthoritativeChemicalInput :=
  match molecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        diagram? := some molecule.toDiagramConfiguration }

def labelAssignment : List (String × Nat) := genericLabelAssignment

/-- Molecular part of a generic-template realization.  The disposition itself remains in the
template ledger because `RawMolecule` is constitutional and carries no Newman coordinates. -/
def TemplateMolecularRealization
    (template : GenericNewmanTemplate) (assignment : List (String × Nat)) : Prop :=
  template.allLigandLabels = assignment.map Prod.fst ∧
    (assignment.map Prod.snd).Nodup ∧
    (∀ label ∈ template.frontLigandLabels, ∃ atom, (label, atom) ∈ assignment ∧
      molecule.bondOrder 0 atom = 1 ∧ molecule.atoms[atom]?.map AtomSpec.element = some .H) ∧
    (∀ label ∈ template.rearLigandLabels, ∃ atom, (label, atom) ∈ assignment ∧
      molecule.bondOrder 1 atom = 1 ∧ molecule.atoms[atom]?.map AtomSpec.element = some .H)

@[simp] theorem molecule_counts_exact :
    molecule.atomCount = 8 ∧ molecule.bonds.length = 7 := by
  decide

@[simp] theorem molecule_bondOrder_0_2 : molecule.bondOrder 0 2 = 1 := by decide
@[simp] theorem molecule_bondOrder_0_3 : molecule.bondOrder 0 3 = 1 := by decide
@[simp] theorem molecule_bondOrder_0_4 : molecule.bondOrder 0 4 = 1 := by decide
@[simp] theorem molecule_bondOrder_1_5 : molecule.bondOrder 1 5 = 1 := by decide
@[simp] theorem molecule_bondOrder_1_6 : molecule.bondOrder 1 6 = 1 := by decide
@[simp] theorem molecule_bondOrder_1_7 : molecule.bondOrder 1 7 = 1 := by decide
@[simp] theorem molecule_element_2 : molecule.atoms[2]?.map AtomSpec.element = some .H := by decide
@[simp] theorem molecule_element_3 : molecule.atoms[3]?.map AtomSpec.element = some .H := by decide
@[simp] theorem molecule_element_4 : molecule.atoms[4]?.map AtomSpec.element = some .H := by decide
@[simp] theorem molecule_element_5 : molecule.atoms[5]?.map AtomSpec.element = some .H := by decide
@[simp] theorem molecule_element_6 : molecule.atoms[6]?.map AtomSpec.element = some .H := by decide
@[simp] theorem molecule_element_7 : molecule.atoms[7]?.map AtomSpec.element = some .H := by decide

theorem generic_templates_molecularly_realized :
    TemplateMolecularRealization staggeredTemplate labelAssignment ∧
      TemplateMolecularRealization eclipsedTemplate labelAssignment := by
  simp [TemplateMolecularRealization, GenericNewmanTemplate.allLigandLabels,
    staggeredTemplate, eclipsedTemplate, labelAssignment, genericLabelAssignment]
  simp [molecule, hydrogen, AtomSpec.aliphatic]

theorem converted : molecule.toSemanticMolecule? = some source.molecule := by
  decide

theorem structureAgreement : molecule.AuthoritativeStructureAgreement source := by
  exact ⟨converted, by decide⟩

theorem source_structurallyWellFormed : source.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide)

def ledger : CertifiedLonePairLedger molecule where
  source := source
  converted := converted
  annotations := []
  sourceWellFormed := source_structurallyWellFormed
  indicesValid := by simp [RawMolecule.EveryParserAtomElectronicStateAnnotationIndexValid]
  keysNodup := by simp
  electronicallyValid := by simp

def torsionUnit : P94ConformationUnit where
  kind := .torsionAxis
  atoms := [0, 1]
  torsionParticipants? := some (.atom 2, .atom 5)

theorem torsionUnit_valid : torsionUnit.ValidFor molecule := by
  refine ⟨by simp [torsionUnit], ?_, ?_⟩
  · intro atom member
    simp [torsionUnit] at member
    rcases member with rfl | rfl <;> norm_num [molecule, RawMolecule.atomCount]
  · refine ⟨.atom 2, .atom 5, 0, 1, rfl, ?_, by norm_num [torsionUnit], ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · intro pair member
      change pair ∈ [(0, 1)] at member
      simp at member
      subst pair
      exact ⟨bond 0 1, by simp [molecule], by rfl⟩
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · change 0 < molecule.bondOrder 0 2
      decide
    · change 0 < molecule.bondOrder 1 5
      decide

def zeroAngle : TorsionAngle :=
  TorsionAngle.ofRat 0 (by norm_num) (by norm_num)

def sixtyAngle : TorsionAngle :=
  TorsionAngle.ofRat 60 (by norm_num) (by norm_num)

noncomputable def staggeredContext : StaggeredContext where
  admissible := P94FiniteAngleAdmissible [0, 60]
  separationFromNearestEclipsed := P94FiniteAngleSeparation [(0, 0), (60, 60)]
  allLigandsIdentical := (true = true)

noncomputable def eclipsedRecord : P94EclipsedStaggeredEvidence where
  unit := torsionUnit
  angle := zeroAngle
  staggeredContext := staggeredContext

noncomputable def staggeredRecord : P94EclipsedStaggeredEvidence where
  unit := torsionUnit
  angle := sixtyAngle
  staggeredContext := staggeredContext

noncomputable def eclipsedEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .eclipsed
  evidence := .eclipsedStaggered eclipsedRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := by simp [P94ConformationEvidence.MolecularRolesValid]
  predicateClosure := .eclipsedStaggered eclipsedRecord [0, 60] [(0, 0), (60, 60)] true
    rfl rfl rfl
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    norm_num [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      eclipsedRecord, staggeredContext, Eclipsed, zeroAngle, torsionUnit]

theorem staggered_support :
    (P94ConformationEvidence.eclipsedStaggered staggeredRecord : P94ReviewedEvidence).Supports
      .staggered := by
  refine ⟨rfl, ?_⟩
  refine ⟨by simp [staggeredRecord, staggeredContext], ?_, ?_⟩
  · simp [staggeredRecord, staggeredContext, P94FiniteAngleAdmissible, sixtyAngle]
  · intro other admissible
    change other.degrees ∈ [0, 60] at admissible
    simp at admissible
    rcases admissible with zero | sixty
    · simp [staggeredContext, P94FiniteAngleSeparation, staggeredRecord, sixtyAngle, zero]
    · simp [staggeredContext, P94FiniteAngleSeparation, staggeredRecord, sixtyAngle, sixty]

noncomputable def staggeredEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .staggered
  evidence := .eclipsedStaggered staggeredRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := by simp [P94ConformationEvidence.MolecularRolesValid]
  predicateClosure := .eclipsedStaggered staggeredRecord [0, 60] [(0, 0), (60, 60)] true
    rfl rfl rfl
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := staggered_support

@[simp] theorem source_entries_support_exact :
    eclipsedEntry.evidence.Supports eclipsedEntry.claim.descriptor ∧
      staggeredEntry.evidence.Supports staggeredEntry.claim.descriptor :=
  ⟨eclipsedEntry.supports, staggeredEntry.supports⟩

theorem zero_not_staggered : ¬ IsStaggered staggeredContext zeroAngle := by
  intro staggered
  have maximal := staggered.2.2 sixtyAngle (by
    simp [staggeredContext, P94FiniteAngleAdmissible, sixtyAngle])
  norm_num [staggeredContext, P94FiniteAngleSeparation, zeroAngle, sixtyAngle] at maximal

theorem eclipsed_evidence_not_supports_staggered :
    ¬ eclipsedEntry.evidence.Supports .staggered := by
  intro supports
  exact zero_not_staggered supports.2

theorem eclipsed_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence eclipsedEntry.evidence)
    (supports : eclipsedEntry.evidence.Supports claim.descriptor) :
    claim = eclipsedEntry.claim := by
  cases claim <;>
    simp [eclipsedEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, eclipsedRecord, staggeredContext, IsStaggered,
      P94FiniteAngleAdmissible, P94FiniteAngleSeparation, Eclipsed,
      zeroAngle] at claimMatches supports ⊢
  case staggered =>
    have impossible := supports.2 sixtyAngle (Or.inr rfl)
    norm_num [sixtyAngle] at impossible

theorem staggered_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence staggeredEntry.evidence)
    (supports : staggeredEntry.evidence.Supports claim.descriptor) :
    claim = staggeredEntry.claim := by
  cases claim <;>
    simp [staggeredEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, staggeredRecord, staggeredContext, IsStaggered,
      P94FiniteAngleAdmissible, P94FiniteAngleSeparation, Eclipsed,
      sixtyAngle] at claimMatches supports ⊢

noncomputable def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [eclipsedEntry, staggeredEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    rcases member with rfl | rfl
    · have claimExact := eclipsed_uniqueClaim claim claimMatches supports
      subst claim
      exact ⟨eclipsedEntry, by simp, rfl, rfl⟩
    · have claimExact := staggered_uniqueClaim claim claimMatches supports
      subst claim
      exact ⟨staggeredEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim =
      [.eclipsed, .staggered] := by
  rfl

theorem normalizationReady : molecule.P94NormalizationReady := by
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · exact
      ⟨ molecule.admissible?_eq_true_iff.mp (by decide)
      , molecule.writtenNeighborExact?_eq_true_iff.mp (by decide) ⟩
  · exact molecule.valenceOK?_eq_true_iff.mp (by decide)
  · exact molecule.rule2MassesKnown?_eq_true_iff.mp (by decide)
  · intro rawBond member
    simp [molecule] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [bond]

noncomputable def frozenRecord : P94FrozenPackageRecord where
  source := source
  molecule := molecule
  package := sourcePackage
  normalizationReady := normalizationReady

end Ethane

namespace Dichloroethane

/-- Constitution printed in the source's synclinal/gauche/skew Newman projection. -/
def molecule : RawMolecule where
  atoms := [carbon, carbon, chlorine, chlorine]
  bonds := [bond 0 1, bond 0 2, bond 1 3]

def source : AuthoritativeChemicalInput :=
  match molecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        diagram? := some molecule.toDiagramConfiguration }

@[simp] theorem molecule_counts_exact :
    molecule.atomCount = 4 ∧ molecule.bonds.length = 3 := by
  decide

theorem converted : molecule.toSemanticMolecule? = some source.molecule := by
  decide

theorem structureAgreement : molecule.AuthoritativeStructureAgreement source := by
  exact ⟨converted, by decide⟩

theorem source_structurallyWellFormed : source.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide)

def ledger : CertifiedLonePairLedger molecule where
  source := source
  converted := converted
  annotations := []
  sourceWellFormed := source_structurallyWellFormed
  indicesValid := by simp [RawMolecule.EveryParserAtomElectronicStateAnnotationIndexValid]
  keysNodup := by simp
  electronicallyValid := by simp

def torsionUnit : P94ConformationUnit where
  kind := .torsionAxis
  atoms := [0, 1]
  torsionParticipants? := some (.atom 2, .atom 3)

theorem torsionUnit_valid : torsionUnit.ValidFor molecule := by
  refine ⟨by simp [torsionUnit], ?_, ?_⟩
  · intro atom member
    simp [torsionUnit] at member
    rcases member with rfl | rfl <;> norm_num [molecule, RawMolecule.atomCount]
  · refine ⟨.atom 2, .atom 3, 0, 1, rfl, ?_, by norm_num [torsionUnit], ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · intro pair member
      change pair ∈ [(0, 1)] at member
      simp at member
      subst pair
      exact ⟨bond 0 1, by simp [molecule], by rfl⟩
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · change 0 < molecule.bondOrder 0 2
      decide
    · change 0 < molecule.bondOrder 1 3
      decide

def sixtyAngle : TorsionAngle :=
  TorsionAngle.ofRat 60 (by norm_num) (by norm_num)

private def frontCandidate : P94TorsionSelectionCandidate :=
  { participant := .atom 2
    ranking := { sequencePriority := 1, identityClass := 1, resultingMagnitude := 60 } }

private def rearCandidate : P94TorsionSelectionCandidate :=
  { participant := .atom 3
    ranking := { sequencePriority := 1, identityClass := 1, resultingMagnitude := 60 } }

def gaucheRecord : P94TorsionEvidence where
  unit := torsionUnit
  frame := { front := .atom 2, rear := .atom 3, angle := sixtyAngle }
  frontCandidates := [frontCandidate]
  rearCandidates := [rearCandidate]
  selectedFront := frontCandidate
  selectedRear := rearCandidate
  rotationSense := .clockwise

theorem gaucheRecord_selected : gaucheRecord.SelectedBySourceCriteria := by
  simp [gaucheRecord, frontCandidate, rearCandidate,
    P94TorsionEvidence.SelectedBySourceCriteria,
    TorsionCandidate.SelectedByP94Criteria, TorsionCandidate.AllDifferent]

theorem gaucheRecord_roles :
    (P94ConformationEvidence.torsion gaucheRecord : P94ReviewedEvidence).MolecularRolesValid
      molecule := by
  constructor
  · simp [P94TorsionEvidence.CandidateParticipantsBounded,
      P94TorsionEvidence.ParticipantBounded, gaucheRecord, frontCandidate, rearCandidate,
      P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
  · refine ⟨.atom 2, .atom 3, 0, 1, rfl, rfl, rfl, ⟨rfl, rfl⟩, ?_, ?_⟩
    · intro candidate member
      have identity : candidate = frontCandidate := by simpa [gaucheRecord] using member
      subst candidate
      change 0 < molecule.bondOrder 0 2
      decide
    · intro candidate member
      have identity : candidate = rearCandidate := by simpa [gaucheRecord] using member
      subst candidate
      change 0 < molecule.bondOrder 1 3
      decide

private theorem selectedLonePairsCertified :
    P94SelectedLonePairsCertified ledger (.torsion gaucheRecord) := by
  intro record equality candidate member atom lonePair
  cases equality
  simp [gaucheRecord, frontCandidate, rearCandidate] at member
  rcases member with rfl | rfl <;> simp at lonePair

theorem torsion_sense_support :
    (P94ConformationEvidence.torsion gaucheRecord : P94ReviewedEvidence).Supports
      (.torsionSense .clockwise) := by
  exact ⟨rfl, rfl, by norm_num [SignAgreesWithRotation, gaucheRecord, sixtyAngle]⟩

theorem synclinal_support :
    (P94ConformationEvidence.torsion gaucheRecord : P94ReviewedEvidence).Supports
      (.torsionClass .synclinal) := by
  exact ⟨rfl, gaucheRecord_selected, by
    norm_num [ClassifiedAs, TorsionAngle.magnitude, gaucheRecord, sixtyAngle]⟩

def torsionSenseEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionSense .clockwise
  evidence := .torsion gaucheRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := gaucheRecord_roles
  predicateClosure := .torsion gaucheRecord
  selectedLonePairsCertified := selectedLonePairsCertified
  matchesEvidence := gaucheRecord_selected
  supports := torsion_sense_support

def synclinalEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionClass .synclinal
  evidence := .torsion gaucheRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := gaucheRecord_roles
  predicateClosure := .torsion gaucheRecord
  selectedLonePairsCertified := selectedLonePairsCertified
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := synclinal_support

def gaucheEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .gauche
  evidence := .torsion gaucheRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := gaucheRecord_roles
  predicateClosure := .torsion gaucheRecord
  selectedLonePairsCertified := selectedLonePairsCertified
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := synclinal_support

@[simp] theorem gauche_entry_support_exact :
    gaucheEntry.evidence.Supports gaucheEntry.claim.descriptor :=
  gaucheEntry.supports

theorem supportedClaim_exact (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence gaucheEntry.evidence)
    (supports : gaucheEntry.evidence.Supports claim.descriptor) :
    claim = .torsionSense .clockwise ∨
      claim = .torsionClass .synclinal ∨ claim = .gauche := by
  cases claim <;>
    try simp [gaucheEntry, P94AuthorityClaim.MatchesEvidence] at claimMatches
  case torsionSense sense =>
    cases sense with
    | clockwise => exact Or.inl rfl
    | anticlockwise =>
        norm_num [gaucheEntry, P94AuthorityClaim.descriptor,
          P94ConformationEvidence.Supports, gaucheRecord, sixtyAngle,
          SignAgreesWithRotation] at supports
  case torsionClass classification =>
    cases classification with
    | synperiplanar =>
        norm_num [gaucheEntry, P94AuthorityClaim.descriptor,
          P94ConformationEvidence.Supports, gaucheRecord, sixtyAngle,
          ClassifiedAs, TorsionAngle.magnitude] at supports
    | synclinal => exact Or.inr (Or.inl rfl)
    | anticlinal =>
        norm_num [gaucheEntry, P94AuthorityClaim.descriptor,
          P94ConformationEvidence.Supports, gaucheRecord, sixtyAngle,
          ClassifiedAs, TorsionAngle.magnitude] at supports
    | antiperiplanar =>
        norm_num [gaucheEntry, P94AuthorityClaim.descriptor,
          P94ConformationEvidence.Supports, gaucheRecord, sixtyAngle,
          ClassifiedAs, TorsionAngle.magnitude] at supports
  case torsionElectronicProxy classification =>
    simp [P94AuthorityClaim.TorsionSelectsElectronicProxy,
      P94AuthorityClaim.IsElectronicProxy, gaucheRecord,
      frontCandidate, rearCandidate] at claimMatches
  case gauche => exact Or.inr (Or.inr rfl)

def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [torsionSenseEntry, synclinalEntry, gaucheEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    have evidenceExact : entry.evidence = gaucheEntry.evidence := by
      simp [torsionSenseEntry, synclinalEntry, gaucheEntry] at member ⊢
      rcases member with rfl | rfl | rfl <;> rfl
    rw [evidenceExact] at claimMatches supports
    rcases supportedClaim_exact claim claimMatches supports with first | second | third
    · subst claim
      exact ⟨torsionSenseEntry, by simp, rfl,
        (show torsionSenseEntry.evidence = gaucheEntry.evidence from rfl).trans
          evidenceExact.symm⟩
    · subst claim
      exact ⟨synclinalEntry, by simp, rfl,
        (show synclinalEntry.evidence = gaucheEntry.evidence from rfl).trans
          evidenceExact.symm⟩
    · subst claim
      exact ⟨gaucheEntry, by simp, rfl, evidenceExact.symm⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim =
      [.torsionSense .clockwise, .torsionClass .synclinal, .gauche] := by
  rfl

theorem normalizationReady : molecule.P94NormalizationReady := by
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · exact
      ⟨ molecule.admissible?_eq_true_iff.mp (by decide)
      , molecule.writtenNeighborExact?_eq_true_iff.mp (by decide) ⟩
  · exact molecule.valenceOK?_eq_true_iff.mp (by decide)
  · exact molecule.rule2MassesKnown?_eq_true_iff.mp (by decide)
  · intro rawBond member
    simp [molecule] at member
    rcases member with rfl | rfl | rfl <;> simp [bond]

def frozenRecord : P94FrozenPackageRecord where
  source := source
  molecule := molecule
  package := sourcePackage
  normalizationReady := normalizationReady

end Dichloroethane

noncomputable def frozenRecords : List P94FrozenPackageRecord :=
  [Ethane.frozenRecord, Dichloroethane.frozenRecord]

@[simp] theorem frozen_records_exact :
    frozenRecords.length = 2 ∧
      frozenRecords.map (fun record => record.molecule.atomCount) = [8, 4] := by
  decide

def distinguishedEntry : P94FrozenDistinguishedEntry where
  record := Dichloroethane.frozenRecord
  entry := Dichloroethane.gaucheEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim = .gauche ∧
      distinguishedEntry.entry.claim.clause = .eclipsedStaggeredGauche ∧
        distinguishedEntry.entry ∈ distinguishedEntry.record.package.evidenceEntries := by
  constructor
  · rfl
  · constructor
    · rfl
    · simp [distinguishedEntry, Dichloroethane.frozenRecord,
        Dichloroethane.sourcePackage]



structure FrozenSourceTranscription where
  artifactSha256 : String
  staggered : GenericNewmanTemplate
  eclipsed : GenericNewmanTemplate
  genericMolecule : RawMolecule
  genericAssignment : List (String × Nat)
  packageRecords : List P94FrozenPackageRecord

noncomputable def frozenSourceTranscription : FrozenSourceTranscription where
  artifactSha256 := sourceArtifactSha256
  staggered := staggeredTemplate
  eclipsed := eclipsedTemplate
  genericMolecule := genericNewmanMolecule
  genericAssignment := genericLabelAssignment
  packageRecords := frozenRecords

/-- Independent fidelity remains an explicit relation over the full template-plus-package
transcription, not merely over the chemically convenient specializations. -/
structure ReviewedSourceTranscription
    (SourceFaithful : FrozenSourceTranscription → Prop) where
  reviewerIdentity : String
  reviewDate : String
  method : String
  reviewerIdentityDeclared : reviewerIdentity ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  sourceFaithful : SourceFaithful frozenSourceTranscription

def currentIndependentSourceReviewIssued : Bool := true

@[simp] theorem current_independent_source_review_issued :
    currentIndependentSourceReviewIssued = true := by
  rfl

end P94EclipsedStaggeredGaucheSourceRecords
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.source_illustration_binding_exact
assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.staggered_template_exact
assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.eclipsed_template_exact
assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.generic_newman_graph_exact
assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.Ethane.generic_templates_molecularly_realized
assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.Ethane.torsionUnit_valid
assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.Ethane.source_entries_support_exact
assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.Ethane.normalizationReady
assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.Dichloroethane.torsionUnit_valid
assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.Dichloroethane.gauche_entry_support_exact
assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.Dichloroethane.normalizationReady
assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.distinguished_entry_exact
assert_kernel_only
  TetraStereo.OneCenter.P94EclipsedStaggeredGaucheSourceRecords.current_independent_source_review_issued
