import TetraStereo.OneCenter.P94MolecularBicyclicFrameworkPerception
import TetraStereo.OneCenter.AuthoritativeParserMainGroupLewisGeneralHybridEvidence

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularLonePair

open CoordinateTwistInOut
open P94MolecularBicyclicFramework
open AuthoritativeChemicalInput

/-!
# Molecule-linked electronic evidence for P-94 lone-pair participants

The generic atom-electronic certificate used by ordinary-double-bond analysis validates chemical
inventories only at retained double-bond endpoints.  A P-94 bridgehead need not be such an
endpoint.  This module therefore gives the finite parser-side annotation ledger a separate,
molecule-wide contract appropriate to the represented in/out family.

Every annotation is tied to the exact raw-to-semantic conversion, has a unique raw atom key,
copies the semantic unpaired-electron count, belongs to a structurally well-formed source, and
satisfies the independent main-group formal-charge electron equation.  The ledger does not infer
an absent annotation and does not manufacture a virtual lone-pair coordinate.  It replaces the
opaque `LonePairAt` proposition by an exact, executable finite lookup whose positive results carry
the checked electronic ledger behind them.
-/

/-! ## Whole-atom electronic validity -/

/-- Molecule-wide main-group electronic meaning of one parser-side annotation.  Unlike the older
Rule-3 endpoint relation, this condition does not require the atom to participate in a double
bond. -/
def AnnotationSatisfiesMainGroupElectronBalance
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotation : ParserAtomElectronicStateAnnotation) : Prop :=
  ∃ valid : annotation.atomIndex < molecule.atomCount,
    annotation.unpairedElectronPositions =
      (source.molecule.atoms.get
        (molecule.convertedAtomIndex source converted
          ⟨annotation.atomIndex, valid⟩)).unpairedElectrons ∧
    ∃ valenceElectrons,
      mainGroupValenceElectronCount?
          (source.molecule.atoms.get
            (molecule.convertedAtomIndex source converted
              ⟨annotation.atomIndex, valid⟩)).element = some valenceElectrons ∧
        source.MainGroupLewisElectronBalance
          (molecule.convertedAtomIndex source converted
            ⟨annotation.atomIndex, valid⟩)
          valenceElectrons annotation.inventory

/-- Proof-carrying finite P-94 electronic sidecar for one exact raw molecule. -/
structure CertifiedLonePairLedger (molecule : RawMolecule) where
  source : AuthoritativeChemicalInput
  converted : molecule.toSemanticMolecule? = some source.molecule
  annotations : List ParserAtomElectronicStateAnnotation
  sourceWellFormed : source.StructurallyWellFormed
  indicesValid : molecule.EveryParserAtomElectronicStateAnnotationIndexValid annotations
  keysNodup : (annotations.map ParserAtomElectronicStateAnnotation.key).Nodup
  electronicallyValid : ∀ annotation, annotation ∈ annotations →
    AnnotationSatisfiesMainGroupElectronBalance molecule source converted annotation

namespace CertifiedLonePairLedger

/-- Executable finite question used by the P-94 `LonePairAt` relation. -/
def lonePairAt? {molecule : RawMolecule}
    (ledger : CertifiedLonePairLedger molecule) (atom : ℕ) : Bool :=
  ledger.annotations.any fun annotation =>
    decide (annotation.atomIndex = atom ∧ 0 < annotation.lonePairs)

/-- Relational spelling of the executable finite lookup. -/
def HasLonePairAt {molecule : RawMolecule}
    (ledger : CertifiedLonePairLedger molecule) (atom : ℕ) : Prop :=
  ledger.lonePairAt? atom = true

@[simp] theorem lonePairAt?_eq_true_iff {molecule : RawMolecule}
    (ledger : CertifiedLonePairLedger molecule) (atom : ℕ) :
    ledger.lonePairAt? atom = true ↔
      ∃ annotation ∈ ledger.annotations,
        annotation.atomIndex = atom ∧ 0 < annotation.lonePairs := by
  simp only [lonePairAt?, List.any_eq_true, decide_eq_true_eq]

/-- A positive electronic lookup can name only a real raw-molecule atom. -/
theorem hasLonePairAt_atom_bounded {molecule : RawMolecule}
    (ledger : CertifiedLonePairLedger molecule) (atom : ℕ)
    (present : ledger.HasLonePairAt atom) :
    atom < molecule.atomCount := by
  rcases (ledger.lonePairAt?_eq_true_iff atom).mp present with
    ⟨annotation, annotationPresent, atomIdentity, _positive⟩
  rw [← atomIdentity]
  exact ledger.indicesValid annotation annotationPresent

/-- Every positive lone-pair claim recovers the literal unique-key sidecar record and its checked
molecule-wide main-group electron-balance proof. -/
theorem hasLonePairAt_mainGroupLewis {molecule : RawMolecule}
    (ledger : CertifiedLonePairLedger molecule) (atom : ℕ)
    (present : ledger.HasLonePairAt atom) :
    ∃ annotation ∈ ledger.annotations,
      annotation.atomIndex = atom ∧ 0 < annotation.lonePairs ∧
        AnnotationSatisfiesMainGroupElectronBalance
          molecule ledger.source ledger.converted annotation := by
  rcases (ledger.lonePairAt?_eq_true_iff atom).mp present with
    ⟨annotation, annotationPresent, atomIdentity, positive⟩
  exact ⟨annotation, annotationPresent, atomIdentity, positive,
    ledger.electronicallyValid annotation annotationPresent⟩

end CertifiedLonePairLedger

/-! Public theorem names kept at the family namespace for compact kernel certificates. -/

@[simp] theorem lonePairAt?_eq_true_iff {molecule : RawMolecule}
    (ledger : CertifiedLonePairLedger molecule) (atom : ℕ) :
    ledger.lonePairAt? atom = true ↔
      ∃ annotation ∈ ledger.annotations,
        annotation.atomIndex = atom ∧ 0 < annotation.lonePairs :=
  ledger.lonePairAt?_eq_true_iff atom

theorem hasLonePairAt_atom_bounded {molecule : RawMolecule}
    (ledger : CertifiedLonePairLedger molecule) (atom : ℕ)
    (present : ledger.HasLonePairAt atom) :
    atom < molecule.atomCount :=
  ledger.hasLonePairAt_atom_bounded atom present

theorem hasLonePairAt_mainGroupLewis {molecule : RawMolecule}
    (ledger : CertifiedLonePairLedger molecule) (atom : ℕ)
    (present : ledger.HasLonePairAt atom) :
    ∃ annotation ∈ ledger.annotations,
      annotation.atomIndex = atom ∧ 0 < annotation.lonePairs ∧
        AnnotationSatisfiesMainGroupElectronBalance
          molecule ledger.source ledger.converted annotation :=
  ledger.hasLonePairAt_mainGroupLewis atom present

/-! ## Composition with graph-derived theta frameworks -/

/-- The two genuinely geometric/source-sensitive premises retained after both graph and
electronic perception. -/
structure RetainedSpatialInOutPremises where
  BridgeLongEnough : RawMolecule → P94ConformationUnit → ThetaFramework → Prop
  InteriorWitness : RawMolecule → P94ConformationUnit → ThetaFramework →
    ℕ → SpatialConfiguration → CartesianPoint3 → Prop

/-- Compose exact theta-framework perception with a lone-pair ledger tied to one raw molecule.
The equality guard prevents the electronic sidecar from being reused for a different molecule. -/
def graphElectronicPremises (molecule : RawMolecule)
    (ledger : CertifiedLonePairLedger molecule)
    (retained : RetainedSpatialInOutPremises) :
    IndependentInOutPremises ThetaFramework :=
  graphDerivedPremises
    { BridgeLongEnough := retained.BridgeLongEnough
      InteriorWitness := retained.InteriorWitness
      LonePairAt := fun candidate atom =>
        candidate = molecule ∧ ledger.HasLonePairAt atom }

theorem graphElectronicPremises_bicyclicFramework_iff
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (retained : RetainedSpatialInOutPremises) (candidate : RawMolecule)
    (unit : P94ConformationUnit) (framework : ThetaFramework) :
    (graphElectronicPremises molecule ledger retained).BicyclicFramework
        candidate unit framework ↔
      framework.ValidFor candidate unit :=
  Iff.rfl

theorem graphElectronicPremises_atomInFramework_iff
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (retained : RetainedSpatialInOutPremises) (candidate : RawMolecule)
    (unit : P94ConformationUnit) (framework : ThetaFramework) (atom : ℕ) :
    (graphElectronicPremises molecule ledger retained).AtomInFramework
        candidate unit framework atom ↔
      ∃ path ∈ framework.bridges, atom ∈ path :=
  Iff.rfl

theorem graphElectronicPremises_lonePairAt_iff
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (retained : RetainedSpatialInOutPremises) (candidate : RawMolecule) (atom : ℕ) :
    (graphElectronicPremises molecule ledger retained).LonePairAt candidate atom ↔
      candidate = molecule ∧ ledger.HasLonePairAt atom :=
  Iff.rfl

/-- Any lone-pair participant admitted by the coordinate in/out judgment recovers both its exact
finite annotation and the checked whole-atom electron equation. -/
theorem valid_lonePairParticipant_has_certified_evidence
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (retained : RetainedSpatialInOutPremises) (unit : P94ConformationUnit)
    (framework : ThetaFramework) (bridgehead center : ℕ)
    (valid : InOutParticipantChemicallyValid
      (graphElectronicPremises molecule ledger retained)
      molecule unit framework bridgehead (.lonePair center)) :
    ledger.HasLonePairAt bridgehead ∧ bridgehead < molecule.atomCount ∧
      ∃ annotation ∈ ledger.annotations,
        annotation.atomIndex = bridgehead ∧ 0 < annotation.lonePairs ∧
          AnnotationSatisfiesMainGroupElectronBalance
            molecule ledger.source ledger.converted annotation := by
  rcases valid with
    ⟨_bridgeheadInUnit, _actualBridgehead, bridgeheadBounded,
      _centerIdentity, lonePair⟩
  have present : ledger.HasLonePairAt bridgehead :=
    ((graphElectronicPremises_lonePairAt_iff
      molecule ledger retained molecule bridgehead).mp lonePair).2
  exact ⟨present, bridgeheadBounded,
    ledger.hasLonePairAt_mainGroupLewis bridgehead present⟩

end BlueBookP94.P94MolecularLonePair
end TetraStereo.OneCenter
