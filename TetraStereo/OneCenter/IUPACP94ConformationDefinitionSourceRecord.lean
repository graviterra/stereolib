import TetraStereo.OneCenter.IUPACP94SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.P94MolecularLonePair

namespace P94ConformationDefinitionSourceRecord

def sourceIllustrationBlock : P94SourceAuditLedger.IllustrationBlock :=
  .fig93ConformerRepresentations

def sourceArtifactSha256 : String :=
  P94SourceAuditLedger.frozenP9Artifact.sha256

@[simp] theorem source_illustration_binding_exact :
    sourceIllustrationBlock = P94SourceAuditLedger.IllustrationBlock.fig93ConformerRepresentations ∧
      sourceIllustrationBlock.pdfPage = 87 ∧
        sourceIllustrationBlock.clause = .conformationDefinition := by
  decide

@[simp] theorem source_artifact_digest_exact :
    sourceArtifactSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  rfl

inductive FigureConformer where
  | conformerA
  | conformerB
  deriving DecidableEq, Repr

namespace FigureConformer

def all : List FigureConformer := [.conformerA, .conformerB]

theorem all_nodup : all.Nodup := by decide

end FigureConformer

inductive ProjectionKind where
  | sawhorse
  | newman
  | zigZag
  deriving DecidableEq, Repr

namespace ProjectionKind

def all : List ProjectionKind := [.sawhorse, .newman, .zigZag]

theorem all_nodup : all.Nodup := by decide

end ProjectionKind

structure FigureRepresentation where
  conformer : FigureConformer
  projection : ProjectionKind
  deriving DecidableEq, Repr

def representationInventory : List FigureRepresentation :=
  [ ⟨.conformerA, .sawhorse⟩, ⟨.conformerA, .newman⟩, ⟨.conformerA, .zigZag⟩
  , ⟨.conformerB, .sawhorse⟩, ⟨.conformerB, .newman⟩, ⟨.conformerB, .zigZag⟩ ]

@[simp] theorem representation_inventory_exact :
    representationInventory =
      [ ⟨.conformerA, .sawhorse⟩, ⟨.conformerA, .newman⟩, ⟨.conformerA, .zigZag⟩
      , ⟨.conformerB, .sawhorse⟩, ⟨.conformerB, .newman⟩, ⟨.conformerB, .zigZag⟩ ] := by
  rfl

@[simp] theorem representation_inventory_complete :
    representationInventory.length = 6 ∧ representationInventory.Nodup := by
  decide

theorem every_conformer_has_every_representation :
    ∀ conformer ∈ FigureConformer.all, ∀ representation ∈ ProjectionKind.all,
      ⟨conformer, representation⟩ ∈ representationInventory := by
  intro conformer conformerMember representation representationMember
  cases conformer <;> cases representation <;> simp [representationInventory]

def genericLigandLabels : List String := ["a", "b", "c", "d", "e", "f"]

@[simp] theorem generic_ligand_labels_exact :
    genericLigandLabels = ["a", "b", "c", "d", "e", "f"] ∧
      genericLigandLabels.Nodup := by
  decide

private def carbon : AtomSpec := AtomSpec.aliphatic .C
private def hydrogen : AtomSpec := AtomSpec.aliphatic .H
private def fluorine : AtomSpec := AtomSpec.aliphatic .F
private def chlorine : AtomSpec := AtomSpec.aliphatic .Cl
private def bromine : AtomSpec := AtomSpec.aliphatic .Br
private def iodine : AtomSpec := AtomSpec.aliphatic .I
private def wildcard : AtomSpec := AtomSpec.aliphatic .wildcard

private def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

/-- Constitutional skeleton of the generic Fig. 9.3 framework.  Wildcard atoms preserve the
source's abstract ligand labels and intentionally prevent certified chemical normalization. -/
def genericFigureMolecule : RawMolecule where
  atoms := [carbon, carbon, wildcard, wildcard, wildcard, wildcard, wildcard, wildcard]
  bonds :=
    [bond 0 1, bond 0 2, bond 0 3, bond 0 4, bond 1 5, bond 1 6, bond 1 7]

def genericLabelAssignment : List (String × Nat) :=
  [("a", 2), ("b", 3), ("c", 4), ("d", 5), ("e", 6), ("f", 7)]

@[simp] theorem generic_figure_graph_exact :
    genericFigureMolecule.atomCount = 8 ∧
      genericFigureMolecule.bonds.length = 7 ∧
        (genericFigureMolecule.atoms.drop 2).map AtomSpec.element =
          List.replicate 6 Element.wildcard := by
  decide

namespace Specialization

/-- A normalization-ready instantiation of the generic two-carbon framework.  The six distinct
written ligand atoms keep the A/B state carrier nondegenerate without claiming that Fig. 9.3
assigns chemical identities to `a`--`f`. -/
def molecule : RawMolecule where
  atoms := [carbon, carbon, hydrogen, fluorine, chlorine, hydrogen, bromine, iodine]
  bonds :=
    [bond 0 1, bond 0 2, bond 0 3, bond 0 4, bond 1 5, bond 1 6, bond 1 7]

def source : AuthoritativeChemicalInput :=
  match molecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        diagram? := some molecule.toDiagramConfiguration }

@[simp] theorem molecule_counts_exact :
    molecule.atomCount = 8 ∧ molecule.bonds.length = 7 := by
  decide

def ligand_elements_exact : List Element :=
  (molecule.atoms.drop 2).map AtomSpec.element

@[simp] theorem ligand_elements_value :
    ligand_elements_exact = [.H, .F, .Cl, .H, .Br, .I] := by
  rfl

/-- Exact constitutional realization of the generic source framework.  Conformer geometry is
recorded separately by the two finite state identifiers and their single-bond transition. -/
def generic_framework_molecularly_realized : Prop :=
  genericLabelAssignment.map Prod.snd = [2, 3, 4, 5, 6, 7] ∧
    molecule.bondOrder 0 1 = 1 ∧
      molecule.bondOrder 0 2 = 1 ∧ molecule.bondOrder 0 3 = 1 ∧
        molecule.bondOrder 0 4 = 1 ∧ molecule.bondOrder 1 5 = 1 ∧
          molecule.bondOrder 1 6 = 1 ∧ molecule.bondOrder 1 7 = 1

@[simp] theorem molecule_bondOrder_0_1 : molecule.bondOrder 0 1 = 1 := by decide
@[simp] theorem molecule_bondOrder_0_2 : molecule.bondOrder 0 2 = 1 := by decide
@[simp] theorem molecule_bondOrder_0_3 : molecule.bondOrder 0 3 = 1 := by decide
@[simp] theorem molecule_bondOrder_0_4 : molecule.bondOrder 0 4 = 1 := by decide
@[simp] theorem molecule_bondOrder_1_5 : molecule.bondOrder 1 5 = 1 := by decide
@[simp] theorem molecule_bondOrder_1_6 : molecule.bondOrder 1 6 = 1 := by decide
@[simp] theorem molecule_bondOrder_1_7 : molecule.bondOrder 1 7 = 1 := by decide

theorem generic_framework_realization_exact : generic_framework_molecularly_realized := by
  simp [generic_framework_molecularly_realized, genericLabelAssignment]

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

def wholeUnit : P94ConformationUnit where
  kind := .wholeMoleculeConformation
  atoms := List.range molecule.atomCount

theorem wholeUnit_valid : wholeUnit.ValidFor molecule := by
  simp [P94ConformationUnit.ValidFor, wholeUnit, molecule, RawMolecule.atomCount,
    List.nodup_range]

def conformerRecord : P94ConformerEvidence Nat where
  unit := wholeUnit
  singleBondRotation := P94FiniteNatRelation [(0, 1)]
  first := 0
  second := 1

@[simp] theorem conformer_transition_exact :
    conformerRecord.first = 0 ∧ conformerRecord.second = 1 ∧
      P94FiniteNatRelation [(0, 1)] 0 1 := by
  simp [conformerRecord, P94FiniteNatRelation]

theorem conformer_support :
    (P94ConformationEvidence.conformer conformerRecord : P94ReviewedEvidence).Supports
      .conformerPair := by
  refine ⟨rfl, by decide, ?_⟩
  exact InterconvertibleBySingleBondRotations.step
    (show P94FiniteNatRelation [(0, 1)] 0 1 from List.mem_cons_self)

def conformerEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .conformationDefinition
  evidence := .conformer conformerRecord
  unitValid := wholeUnit_valid
  molecularRolesValid := by simp [P94ConformationEvidence.MolecularRolesValid]
  predicateClosure := .conformer conformerRecord [(0, 1)] rfl
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := conformer_support

@[simp] theorem source_entry_support_exact :
    conformerEntry.evidence.Supports conformerEntry.claim.descriptor :=
  conformerEntry.supports

theorem conformer_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence conformerEntry.evidence)
    (supports : conformerEntry.evidence.Supports claim.descriptor) :
    claim = conformerEntry.claim := by
  cases claim <;> simp [conformerEntry, P94AuthorityClaim.MatchesEvidence,
    P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports] at claimMatches supports ⊢

def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [conformerEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    have entryExact : entry = conformerEntry := by simpa using member
    subst entry
    have claimExact := conformer_uniqueClaim claim claimMatches supports
    subst claim
    exact ⟨conformerEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim =
      [.conformationDefinition] := by
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

end Specialization

def frozenRecord : P94FrozenPackageRecord where
  source := Specialization.source
  molecule := Specialization.molecule
  package := Specialization.sourcePackage
  normalizationReady := Specialization.normalizationReady

@[simp] theorem frozen_record_exact :
    frozenRecord.source = Specialization.source ∧
      frozenRecord.molecule = Specialization.molecule ∧
        frozenRecord.package = Specialization.sourcePackage := by
  exact ⟨rfl, rfl, rfl⟩

def distinguishedEntry : P94FrozenDistinguishedEntry where
  record := frozenRecord
  entry := Specialization.conformerEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim = .conformationDefinition ∧
      distinguishedEntry.entry.claim.clause = .conformationDefinition ∧
        distinguishedEntry.entry ∈ distinguishedEntry.record.package.evidenceEntries := by
  constructor
  · rfl
  · constructor
    · rfl
    · simp [distinguishedEntry, frozenRecord, Specialization.sourcePackage]



structure FrozenSourceTranscription where
  artifactSha256 : String
  ligandLabels : List String
  representations : List FigureRepresentation
  genericMolecule : RawMolecule
  genericAssignment : List (String × Nat)
  packageRecord : P94FrozenPackageRecord

def frozenSourceTranscription : FrozenSourceTranscription where
  artifactSha256 := sourceArtifactSha256
  ligandLabels := genericLigandLabels
  representations := representationInventory
  genericMolecule := genericFigureMolecule
  genericAssignment := genericLabelAssignment
  packageRecord := frozenRecord

/-- Independent fidelity remains an explicit relation over the full generic-figure-plus-package
transcription. -/
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

end P94ConformationDefinitionSourceRecord
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P94ConformationDefinitionSourceRecord.source_illustration_binding_exact
assert_kernel_only
  TetraStereo.OneCenter.P94ConformationDefinitionSourceRecord.representation_inventory_complete
assert_kernel_only
  TetraStereo.OneCenter.P94ConformationDefinitionSourceRecord.every_conformer_has_every_representation
assert_kernel_only
  TetraStereo.OneCenter.P94ConformationDefinitionSourceRecord.generic_figure_graph_exact
assert_kernel_only
  TetraStereo.OneCenter.P94ConformationDefinitionSourceRecord.Specialization.generic_framework_realization_exact
assert_kernel_only
  TetraStereo.OneCenter.P94ConformationDefinitionSourceRecord.Specialization.wholeUnit_valid
assert_kernel_only
  TetraStereo.OneCenter.P94ConformationDefinitionSourceRecord.Specialization.source_entry_support_exact
assert_kernel_only
  TetraStereo.OneCenter.P94ConformationDefinitionSourceRecord.Specialization.normalizationReady
assert_kernel_only
  TetraStereo.OneCenter.P94ConformationDefinitionSourceRecord.distinguished_entry_exact
assert_kernel_only
  TetraStereo.OneCenter.P94ConformationDefinitionSourceRecord.current_independent_source_review_issued
