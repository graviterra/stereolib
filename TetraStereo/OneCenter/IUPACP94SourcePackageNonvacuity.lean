import TetraStereo.OneCenter.IUPACP94CanonicalSourceProgram

set_option autoImplicit false

/-!
# Concrete nonvacuity of the proof-carrying P-94 source-package schema

This module supplies one explicit finite carbon constitution containing the small physical
carriers needed by all twelve P-94 clauses: a torsion chain, five- and six-membered rings, a
monounsaturated six-ring, an eight-ring, and a substituted theta framework.  Evidence entries
are admitted only with their independent molecular-unit, molecular-role, and descriptor proofs.
The in/out entry additionally uses two exact rational coordinate realizations with opposite
strict bridgehead-axis dot-product signs.

The theorem below establishes nonvacuity of the schema policy.  It does not claim that this one
finite package is the complete P-94 source authority or that every admitted molecule is covered.
-/

namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.CoordinateTorsion
open BlueBookP94.CoordinateTwistInOut
open BlueBookP94.P94MolecularBicyclicFramework
open BlueBookP94.P94MolecularBridgeSufficiency
open BlueBookP94.P94MolecularLonePair
open BlueBookP94.P94MolecularBridgeheadAxisInterior
open IUPACNormativeProvision

namespace P94SourcePackageNonvacuity

private def carbon : AtomSpec := AtomSpec.aliphatic .C

private def bond (source target : Nat) (kind : ParsedBondKind := .single) : RawBond :=
  { source := source, target := target, kind := kind }

/-- The components, in index order, are `C=C-C=C`, a five-ring, a saturated six-ring, a
monounsaturated six-ring, a saturated eight-ring, and a substituted theta graph. -/
def molecule : RawMolecule where
  atoms := List.replicate 35 carbon
  bonds :=
    [ bond 0 1 .double, bond 1 2, bond 2 3 .double
    , bond 4 5, bond 5 6, bond 6 7, bond 7 8, bond 8 4
    , bond 9 10, bond 10 11, bond 11 12, bond 12 13, bond 13 14, bond 14 9
    , bond 15 16 .double, bond 16 17, bond 17 18, bond 18 19, bond 19 20, bond 20 15
    , bond 21 22, bond 22 23, bond 23 24, bond 24 25
    , bond 25 26, bond 26 27, bond 27 28, bond 28 21
    , bond 29 30, bond 29 31, bond 31 30
    , bond 29 32, bond 32 33, bond 33 30, bond 29 34 ]

def source : AuthoritativeChemicalInput :=
  match molecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        diagram? := some molecule.toDiagramConfiguration }

theorem converted : molecule.toSemanticMolecule? = some source.molecule := by
  decide

theorem structureAgreement : molecule.AuthoritativeStructureAgreement source := by
  exact ⟨converted, by decide⟩

theorem source_structurallyWellFormed : source.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide)

/-- No clause below needs a physical lone pair: P-94.2.2 is witnessed by a graph-checked
multiple-bond duplicate participant, and P-94.3.2.6 by an ordinary exocyclic atom. -/
def ledger : CertifiedLonePairLedger molecule where
  source := source
  converted := converted
  annotations := []
  sourceWellFormed := source_structurallyWellFormed
  indicesValid := by simp [RawMolecule.EveryParserAtomElectronicStateAnnotationIndexValid]
  keysNodup := by simp
  electronicallyValid := by simp

@[simp] theorem ledger_source : ledger.source = source := rfl

def wholeUnit : P94ConformationUnit where
  kind := .wholeMoleculeConformation
  atoms := List.range molecule.atomCount

def torsionUnit : P94ConformationUnit where
  kind := .torsionAxis
  atoms := [1, 2]
  torsionParticipants? := some (.atom 0, .atom 3)

def electronicTorsionUnit : P94ConformationUnit where
  kind := .torsionAxis
  atoms := [1, 2]
  torsionParticipants? := some (.duplicateAtom 0, .atom 3)

def fiveRingUnit : P94ConformationUnit where
  kind := .fiveMemberedRing
  atoms := [4, 5, 6, 7, 8]

def sixRingUnit : P94ConformationUnit where
  kind := .sixMemberedRing
  atoms := [9, 10, 11, 12, 13, 14]

def halfChairUnit : P94ConformationUnit where
  kind := .sixMemberedRing
  atoms := [15, 16, 17, 18, 19, 20]

def crownUnit : P94ConformationUnit where
  kind := .crownRing
  atoms := [21, 22, 23, 24, 25, 26, 27, 28]

def tubUnit : P94ConformationUnit where
  kind := .eightMemberedTubRing
  atoms := [21, 22, 23, 24, 25, 26, 27, 28]

def thetaUnit : P94ConformationUnit where
  kind := .bicyclicBridge
  atoms := [29, 30]

theorem wholeUnit_valid : wholeUnit.ValidFor molecule := by
  simp [P94ConformationUnit.ValidFor, wholeUnit, molecule, RawMolecule.atomCount,
    carbon, List.nodup_range]

@[simp] theorem molecule_bondOrder_one_zero : molecule.bondOrder 1 0 = 2 := by rfl
@[simp] theorem molecule_bondOrder_zero_one : molecule.bondOrder 0 1 = 2 := by rfl
@[simp] theorem molecule_bondOrder_one_two : molecule.bondOrder 1 2 = 1 := by rfl
@[simp] theorem molecule_bondOrder_two_three : molecule.bondOrder 2 3 = 2 := by rfl
@[simp] theorem molecule_bondOrder_15_16 : molecule.bondOrder 15 16 = 2 := by rfl
@[simp] theorem molecule_bondOrder_16_17 : molecule.bondOrder 16 17 = 1 := by rfl
@[simp] theorem molecule_bondOrder_17_18 : molecule.bondOrder 17 18 = 1 := by rfl
@[simp] theorem molecule_bondOrder_18_19 : molecule.bondOrder 18 19 = 1 := by rfl
@[simp] theorem molecule_bondOrder_19_20 : molecule.bondOrder 19 20 = 1 := by rfl
@[simp] theorem molecule_bondOrder_20_15 : molecule.bondOrder 20 15 = 1 := by rfl
@[simp] theorem molecule_bondOrder_21_22 : molecule.bondOrder 21 22 = 1 := by rfl
@[simp] theorem molecule_bondOrder_22_23 : molecule.bondOrder 22 23 = 1 := by rfl
@[simp] theorem molecule_bondOrder_23_24 : molecule.bondOrder 23 24 = 1 := by rfl
@[simp] theorem molecule_bondOrder_24_25 : molecule.bondOrder 24 25 = 1 := by rfl
@[simp] theorem molecule_bondOrder_25_26 : molecule.bondOrder 25 26 = 1 := by rfl
@[simp] theorem molecule_bondOrder_26_27 : molecule.bondOrder 26 27 = 1 := by rfl
@[simp] theorem molecule_bondOrder_27_28 : molecule.bondOrder 27 28 = 1 := by rfl
@[simp] theorem molecule_bondOrder_28_21 : molecule.bondOrder 28 21 = 1 := by rfl
@[simp] theorem molecule_bondOrder_29_34 : molecule.bondOrder 29 34 = 1 := by rfl

theorem torsionUnit_valid : torsionUnit.ValidFor molecule := by
  refine ⟨by simp [torsionUnit], ?_, ?_⟩
  · intro atom member
    simp [torsionUnit] at member
    rcases member with rfl | rfl <;> norm_num [molecule, RawMolecule.atomCount]
  · refine ⟨.atom 0, .atom 3, 1, 2, rfl, ?_, by norm_num [torsionUnit], ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · intro pair member
      change pair ∈ [(1, 2)] at member
      simp at member
      subst pair
      exact ⟨bond 1 2, by simp [molecule], by rfl⟩
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · change 0 < molecule.bondOrder 1 0
      rw [molecule_bondOrder_one_zero]
      norm_num
    · change 0 < molecule.bondOrder 2 3
      rw [molecule_bondOrder_two_three]
      norm_num

theorem electronicTorsionUnit_valid : electronicTorsionUnit.ValidFor molecule := by
  refine ⟨by simp [electronicTorsionUnit], ?_, ?_⟩
  · intro atom member
    simp [electronicTorsionUnit] at member
    rcases member with rfl | rfl <;> norm_num [molecule, RawMolecule.atomCount]
  · refine ⟨.duplicateAtom 0, .atom 3, 1, 2, rfl, ?_,
      by norm_num [electronicTorsionUnit], ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · intro pair member
      change pair ∈ [(1, 2)] at member
      simp at member
      subst pair
      exact ⟨bond 1 2, by simp [molecule], by rfl⟩
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · change 1 < molecule.bondOrder 1 0
      rw [molecule_bondOrder_one_zero]
      norm_num
    · change 0 < molecule.bondOrder 2 3
      rw [molecule_bondOrder_two_three]
      norm_num

theorem fiveRingUnit_valid : fiveRingUnit.ValidFor molecule := by
  simp [P94ConformationUnit.ValidFor, P94ConformationUnit.CyclicallyBonded,
    P94ConformationUnit.ConsecutivelyBonded, P94ConformationUnit.Bonded,
    fiveRingUnit, molecule, RawMolecule.atomCount, RawBond.connects, bond, carbon]

theorem sixRingUnit_valid : sixRingUnit.ValidFor molecule := by
  simp [P94ConformationUnit.ValidFor, P94ConformationUnit.CyclicallyBonded,
    P94ConformationUnit.ConsecutivelyBonded, P94ConformationUnit.Bonded,
    sixRingUnit, molecule, RawMolecule.atomCount, RawBond.connects, bond, carbon]

theorem halfChairUnit_valid : halfChairUnit.ValidFor molecule := by
  simp [P94ConformationUnit.ValidFor, P94ConformationUnit.CyclicallyBonded,
    P94ConformationUnit.ConsecutivelyBonded, P94ConformationUnit.Bonded,
    halfChairUnit, molecule, RawMolecule.atomCount, RawBond.connects, bond, carbon]

theorem crownUnit_valid : crownUnit.ValidFor molecule := by
  simp [P94ConformationUnit.ValidFor, P94ConformationUnit.CyclicallyBonded,
    P94ConformationUnit.ConsecutivelyBonded, P94ConformationUnit.Bonded,
    crownUnit, molecule, RawMolecule.atomCount, RawBond.connects, bond, carbon,
    even_iff_two_dvd]

theorem tubUnit_valid : tubUnit.ValidFor molecule := by
  simp [P94ConformationUnit.ValidFor, P94ConformationUnit.CyclicallyBonded,
    P94ConformationUnit.ConsecutivelyBonded, P94ConformationUnit.Bonded,
    tubUnit, molecule, RawMolecule.atomCount, RawBond.connects, bond, carbon]

theorem thetaUnit_valid : thetaUnit.ValidFor molecule := by
  simp [P94ConformationUnit.ValidFor, P94ConformationUnit.ConsecutivelyBonded,
    P94ConformationUnit.Bonded, thetaUnit, molecule, RawMolecule.atomCount,
    RawBond.connects, bond, carbon]

def zeroAngle : TorsionAngle := TorsionAngle.ofRat 0 (by norm_num) (by norm_num)
def oneEightyAngle : TorsionAngle := TorsionAngle.ofRat 180 (by norm_num) (by norm_num)

private def ordinaryFront : P94TorsionSelectionCandidate :=
  { participant := .atom 0
    ranking := { sequencePriority := 1, identityClass := 1, resultingMagnitude := 0 } }

private def electronicFront : P94TorsionSelectionCandidate :=
  { participant := .duplicateAtom 0
    ranking := { sequencePriority := 1, identityClass := 1, resultingMagnitude := 0 } }

private def rear : P94TorsionSelectionCandidate :=
  { participant := .atom 3
    ranking := { sequencePriority := 1, identityClass := 1, resultingMagnitude := 0 } }

def ordinaryTorsion : P94TorsionEvidence where
  unit := torsionUnit
  frame := { front := .atom 0, rear := .atom 3, angle := zeroAngle }
  frontCandidates := [ordinaryFront]
  rearCandidates := [rear]
  selectedFront := ordinaryFront
  selectedRear := rear
  rotationSense := .clockwise

def electronicTorsion : P94TorsionEvidence where
  unit := electronicTorsionUnit
  frame := { front := .duplicateAtom 0, rear := .atom 3, angle := zeroAngle }
  frontCandidates := [electronicFront]
  rearCandidates := [rear]
  selectedFront := electronicFront
  selectedRear := rear
  rotationSense := .clockwise

theorem ordinaryTorsion_selected : ordinaryTorsion.SelectedBySourceCriteria := by
  simp [ordinaryTorsion, ordinaryFront, rear, P94TorsionEvidence.SelectedBySourceCriteria,
    TorsionCandidate.SelectedByP94Criteria, TorsionCandidate.AllDifferent]

theorem electronicTorsion_selected : electronicTorsion.SelectedBySourceCriteria := by
  simp [electronicTorsion, electronicFront, rear, P94TorsionEvidence.SelectedBySourceCriteria,
    TorsionCandidate.SelectedByP94Criteria, TorsionCandidate.AllDifferent]

/-! ## Reusable one-entry source packages -/

def singletonPackage
    (entry : P94SourcePackageEvidenceEntry molecule ledger)
    (coordinatePairs : List (P94SourcePackageInOutCoordinatePair molecule ledger) := [])
    (uniqueClaim : ∀ claim : P94AuthorityClaim,
      claim.MatchesEvidence entry.evidence →
      entry.evidence.Supports claim.descriptor → claim = entry.claim) :
    P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [entry]
  compatibleClaimsListed := by
    intro listed listedMember claim claimMatches supports
    have listedIdentity : listed = entry := by simpa using listedMember
    subst listed
    have claimIdentity := uniqueClaim claim claimMatches supports
    subst claim
    exact ⟨entry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := coordinatePairs

/-! ## P-94.1: conformer pair -/

def conformerRecord : P94ConformerEvidence Nat where
  unit := wholeUnit
  singleBondRotation := P94FiniteNatRelation [(0, 1)]
  first := 0
  second := 1

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

theorem conformer_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence conformerEntry.evidence)
    (supports : conformerEntry.evidence.Supports claim.descriptor) :
    claim = conformerEntry.claim := by
  cases claim <;> simp [conformerEntry, P94AuthorityClaim.MatchesEvidence,
    P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports] at claimMatches supports ⊢

def conformerPackage : P94SourcePackageSchema source molecule :=
  singletonPackage conformerEntry [] conformer_uniqueClaim

/-! ## P-94.2.1 and P-94.2.2: ordinary and electronic-proxy torsions -/

theorem ordinaryTorsion_roles :
    (P94ConformationEvidence.torsion ordinaryTorsion : P94ReviewedEvidence).MolecularRolesValid
      molecule := by
  constructor
  · simp [P94TorsionEvidence.CandidateParticipantsBounded,
      P94TorsionEvidence.ParticipantBounded, ordinaryTorsion, ordinaryFront, rear,
      P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
  · refine ⟨.atom 0, .atom 3, 1, 2, rfl, rfl, rfl, ⟨rfl, rfl⟩, ?_, ?_⟩
    · intro candidate member
      have identity : candidate = ordinaryFront := by simpa [ordinaryTorsion] using member
      subst candidate
      change 0 < molecule.bondOrder 1 0
      rw [molecule_bondOrder_one_zero]
      norm_num
    · intro candidate member
      have identity : candidate = rear := by simpa [ordinaryTorsion] using member
      subst candidate
      change 0 < molecule.bondOrder 2 3
      rw [molecule_bondOrder_two_three]
      norm_num

theorem electronicTorsion_roles :
    (P94ConformationEvidence.torsion electronicTorsion : P94ReviewedEvidence).MolecularRolesValid
      molecule := by
  constructor
  · simp [P94TorsionEvidence.CandidateParticipantsBounded,
      P94TorsionEvidence.ParticipantBounded, electronicTorsion, electronicFront, rear,
      P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
  · refine ⟨.duplicateAtom 0, .atom 3, 1, 2, rfl, rfl, rfl, ⟨rfl, rfl⟩, ?_, ?_⟩
    · intro candidate member
      have identity : candidate = electronicFront := by
        simpa [electronicTorsion] using member
      subst candidate
      change 1 < molecule.bondOrder 1 0
      rw [molecule_bondOrder_one_zero]
      norm_num
    · intro candidate member
      have identity : candidate = rear := by simpa [electronicTorsion] using member
      subst candidate
      change 0 < molecule.bondOrder 2 3
      rw [molecule_bondOrder_two_three]
      norm_num

theorem ordinaryTorsion_support :
    (P94ConformationEvidence.torsion ordinaryTorsion : P94ReviewedEvidence).Supports
      (.torsionClass .synperiplanar) := by
  exact ⟨rfl, ordinaryTorsion_selected, by norm_num [ClassifiedAs, TorsionAngle.magnitude,
    ordinaryTorsion, zeroAngle]⟩

theorem electronicTorsion_support :
    (P94ConformationEvidence.torsion electronicTorsion : P94ReviewedEvidence).Supports
      (.torsionClass .synperiplanar) := by
  exact ⟨rfl, electronicTorsion_selected, by norm_num [ClassifiedAs, TorsionAngle.magnitude,
    electronicTorsion, zeroAngle]⟩

private theorem torsion_selectedLonePairsCertified (record : P94TorsionEvidence)
    (ordinaryOrElectronic : record = ordinaryTorsion ∨ record = electronicTorsion) :
    P94SelectedLonePairsCertified ledger (.torsion record) := by
  intro actual equality candidate member atom lonePair
  cases equality
  rcases ordinaryOrElectronic with rfl | rfl <;>
    simp [ordinaryTorsion, electronicTorsion, ordinaryFront, electronicFront, rear] at member
  · rcases member with rfl | rfl <;> simp at lonePair
  · rcases member with rfl | rfl <;> simp at lonePair

def ordinaryTorsionEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionClass .synperiplanar
  evidence := .torsion ordinaryTorsion
  unitValid := torsionUnit_valid
  molecularRolesValid := ordinaryTorsion_roles
  predicateClosure := .torsion ordinaryTorsion
  selectedLonePairsCertified := torsion_selectedLonePairsCertified ordinaryTorsion (Or.inl rfl)
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := ordinaryTorsion_support

theorem ordinaryTorsion_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence ordinaryTorsionEntry.evidence)
    (supports : ordinaryTorsionEntry.evidence.Supports claim.descriptor) :
    claim = ordinaryTorsionEntry.claim := by
  cases claim <;>
    try simp [ordinaryTorsionEntry, P94AuthorityClaim.MatchesEvidence] at claimMatches
  case torsionSense sense =>
    cases sense <;> norm_num [ordinaryTorsionEntry, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, ordinaryTorsion, zeroAngle,
      SignAgreesWithRotation] at supports
  case torsionClass classification =>
    cases classification <;>
      norm_num [ordinaryTorsionEntry, P94AuthorityClaim.descriptor,
        P94ConformationEvidence.Supports, ordinaryTorsion, zeroAngle,
        ClassifiedAs, TorsionAngle.magnitude] at supports
    rfl
  case torsionElectronicProxy classification =>
    simp [P94AuthorityClaim.TorsionSelectsElectronicProxy,
      P94AuthorityClaim.IsElectronicProxy, ordinaryTorsion, ordinaryFront, rear] at claimMatches
  case gauche =>
    norm_num [ordinaryTorsionEntry, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, ordinaryTorsion, zeroAngle,
      ClassifiedAs, TorsionAngle.magnitude] at supports

def ordinaryTorsionPackage : P94SourcePackageSchema source molecule :=
  singletonPackage ordinaryTorsionEntry [] ordinaryTorsion_uniqueClaim

def electronicTorsionEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionElectronicProxy .synperiplanar
  evidence := .torsion electronicTorsion
  unitValid := electronicTorsionUnit_valid
  molecularRolesValid := electronicTorsion_roles
  predicateClosure := .torsion electronicTorsion
  selectedLonePairsCertified :=
    torsion_selectedLonePairsCertified electronicTorsion (Or.inr rfl)
  matchesEvidence := ⟨electronicTorsion_selected, by simp [P94AuthorityClaim.TorsionSelectsElectronicProxy,
    P94AuthorityClaim.IsElectronicProxy, electronicTorsion, electronicFront]⟩
  supports := electronicTorsion_support

theorem electronicTorsion_proxy_unique (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence electronicTorsionEntry.evidence)
    (supports : electronicTorsionEntry.evidence.Supports claim.descriptor)
    (notOrdinary : claim ≠ .torsionClass .synperiplanar) :
    claim = electronicTorsionEntry.claim := by
  cases claim <;>
    try simp [electronicTorsionEntry, P94AuthorityClaim.MatchesEvidence] at claimMatches
  case torsionSense sense =>
    cases sense <;> norm_num [electronicTorsionEntry, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, electronicTorsion, zeroAngle,
      SignAgreesWithRotation] at supports
  case torsionClass classification =>
    cases classification <;>
      norm_num [electronicTorsionEntry, P94AuthorityClaim.descriptor,
        P94ConformationEvidence.Supports, electronicTorsion, zeroAngle,
        ClassifiedAs, TorsionAngle.magnitude] at supports ; simp_all
  case torsionElectronicProxy classification =>
    cases classification <;>
      norm_num [electronicTorsionEntry, P94AuthorityClaim.descriptor,
        P94ConformationEvidence.Supports, electronicTorsion, zeroAngle,
        ClassifiedAs, TorsionAngle.magnitude] at supports
    rfl
  case gauche =>
    norm_num [electronicTorsionEntry, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, electronicTorsion, zeroAngle,
      ClassifiedAs, TorsionAngle.magnitude] at supports

def electronicOrdinaryEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionClass .synperiplanar
  evidence := .torsion electronicTorsion
  unitValid := electronicTorsionUnit_valid
  molecularRolesValid := electronicTorsion_roles
  predicateClosure := .torsion electronicTorsion
  selectedLonePairsCertified :=
    torsion_selectedLonePairsCertified electronicTorsion (Or.inr rfl)
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := electronicTorsion_support

def electronicTorsionPackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [electronicOrdinaryEntry, electronicTorsionEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    rcases member with first | second
    · subst entry
      by_cases ordinary : claim =
          P94AuthorityClaim.torsionClass ConformationalClass.synperiplanar
      · subst claim
        exact ⟨electronicOrdinaryEntry, by simp, rfl, rfl⟩
      · have claimIdentity := electronicTorsion_proxy_unique claim claimMatches supports ordinary
        subst claim
        exact ⟨electronicTorsionEntry, by simp, rfl, rfl⟩
    · subst entry
      by_cases ordinary : claim =
          P94AuthorityClaim.torsionClass ConformationalClass.synperiplanar
      · subst claim
        exact ⟨electronicOrdinaryEntry, by simp, rfl, rfl⟩
      · have claimIdentity := electronicTorsion_proxy_unique claim claimMatches supports ordinary
        subst claim
        exact ⟨electronicTorsionEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

/-! ## P-94.3.1: acyclic conformations -/

noncomputable def eclipsedRecord : P94EclipsedStaggeredEvidence where
  unit := torsionUnit
  angle := zeroAngle
  staggeredContext :=
    { admissible := P94FiniteAngleAdmissible []
      separationFromNearestEclipsed := P94FiniteAngleSeparation []
      allLigandsIdentical := (true = true) }

noncomputable def eclipsedEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .eclipsed
  evidence := .eclipsedStaggered eclipsedRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := by simp [P94ConformationEvidence.MolecularRolesValid]
  predicateClosure := .eclipsedStaggered eclipsedRecord [] [] true rfl rfl rfl
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    norm_num [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      eclipsedRecord, Eclipsed, zeroAngle, torsionUnit]

theorem eclipsed_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence eclipsedEntry.evidence)
    (supports : eclipsedEntry.evidence.Supports claim.descriptor) :
    claim = eclipsedEntry.claim := by
  cases claim <;>
    simp [eclipsedEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, eclipsedRecord, IsStaggered,
      P94FiniteAngleAdmissible, Eclipsed, zeroAngle] at claimMatches supports ⊢

noncomputable def eclipsedPackage : P94SourcePackageSchema source molecule :=
  singletonPackage eclipsedEntry [] eclipsed_uniqueClaim

def trigonalRecord : P94TrigonalConformationEvidence where
  unit := torsionUnit
  observation :=
    { isR3CCYXGrouping := (true = true)
      xToSomeR := oneEightyAngle
      doubleBondBisectsRCRAngle := (true = true) }

def trigonalEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .trigonalBisecting
  evidence := .trigonal trigonalRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := by simp [P94ConformationEvidence.MolecularRolesValid]
  predicateClosure := .trigonal trigonalRecord true true rfl rfl
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    norm_num [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      trigonalRecord, IsBisectingConformation,
      ClassifiedAs, TorsionAngle.magnitude, oneEightyAngle, torsionUnit]

theorem trigonal_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence trigonalEntry.evidence)
    (supports : trigonalEntry.evidence.Supports claim.descriptor) :
    claim = trigonalEntry.claim := by
  cases claim <;>
    simp [trigonalEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, trigonalRecord, IsBisectingConformation,
      IsEclipsingConformation, ClassifiedAs, TorsionAngle.magnitude,
      oneEightyAngle] at claimMatches supports ⊢
  all_goals norm_num at supports

def trigonalPackage : P94SourcePackageSchema source molecule :=
  singletonPackage trigonalEntry [] trigonal_uniqueClaim

def sCisRecord : P94ConjugatedSystemEvidence where
  unit := torsionUnit
  system := .twoDoubleBondsSeparatedBySingleBond
  angle := zeroAngle

/-- The enum carried by `P94ConjugatedSystemEvidence` is realized by the authoritative graph:
atoms 0--3 are the actual `C=C-C=C` diene named by the torsion unit. -/
theorem sCisRecord_source_diene :
    molecule.bondOrder 0 1 = 2 ∧ molecule.bondOrder 1 2 = 1 ∧
      molecule.bondOrder 2 3 = 2 := by
  exact ⟨molecule_bondOrder_zero_one, molecule_bondOrder_one_two,
    molecule_bondOrder_two_three⟩

theorem sCisRecord_molecular_and_source_roles :
    (P94ConformationEvidence.conjugated sCisRecord : P94ReviewedEvidence).MolecularRolesValid
        molecule ∧
      molecule.bondOrder 0 1 = 2 ∧ molecule.bondOrder 1 2 = 1 ∧
        molecule.bondOrder 2 3 = 2 := by
  exact ⟨by simp [P94ConformationEvidence.MolecularRolesValid], sCisRecord_source_diene⟩

def sCisEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .sCis
  evidence := .conjugated sCisRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := sCisRecord_molecular_and_source_roles.1
  predicateClosure := .conjugated sCisRecord
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    norm_num [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      sCisRecord, SCisTransApplies,
      ClassifiedAs, TorsionAngle.magnitude, zeroAngle, torsionUnit]

theorem sCis_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence sCisEntry.evidence)
    (supports : sCisEntry.evidence.Supports claim.descriptor) : claim = sCisEntry.claim := by
  cases claim <;>
    simp [sCisEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, sCisRecord, SCisTransApplies,
      ClassifiedAs, TorsionAngle.magnitude, zeroAngle] at claimMatches supports ⊢
  all_goals norm_num at supports

def sCisPackage : P94SourcePackageSchema source molecule :=
  singletonPackage sCisEntry [] sCis_uniqueClaim

/-! ## P-94.3.2.1--5: ring conformations -/

def envelopeRecord : P94RingPlaneEvidence where
  unit := fiveRingUnit
  sides := [.onPlane, .onPlane, .onPlane, .onPlane, .positive]
  saturatedCyclic := False
  symmetricallyEquivalent := False

def envelopeEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .envelope
  evidence := .ringPlane envelopeRecord
  unitValid := fiveRingUnit_valid
  molecularRolesValid := by
    simp [P94ConformationEvidence.MolecularRolesValid, envelopeRecord, fiveRingUnit]
  predicateClosure := .ringPlane envelopeRecord false false false
    (by simp [envelopeRecord]) (by simp [envelopeRecord]) (by simp [envelopeRecord])
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    simp [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      envelopeRecord, fiveRingUnit, IsEnvelope]

theorem envelope_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence envelopeEntry.evidence)
    (supports : envelopeEntry.evidence.Supports claim.descriptor) : claim = envelopeEntry.claim := by
  cases claim <;>
    simp [envelopeEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, envelopeRecord, fiveRingUnit,
      IsEnvelope] at claimMatches supports ⊢

def envelopePackage : P94SourcePackageSchema source molecule :=
  singletonPackage envelopeEntry [] envelope_uniqueClaim

def chairRecord : P94RingPlaneEvidence where
  unit := sixRingUnit
  sides := [.onPlane, .onPlane, .positive, .onPlane, .onPlane, .negative]
  saturatedCyclic := False
  symmetricallyEquivalent := False

def chairEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .chair
  evidence := .ringPlane chairRecord
  unitValid := sixRingUnit_valid
  molecularRolesValid := by
    simp [P94ConformationEvidence.MolecularRolesValid, chairRecord, sixRingUnit]
  predicateClosure := .ringPlane chairRecord false false false
    (by simp [chairRecord]) (by simp [chairRecord]) (by simp [chairRecord])
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    simp [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      chairRecord, sixRingUnit, IsChair, SixRingReferencePlane, OppositeSides]

theorem chair_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence chairEntry.evidence)
    (supports : chairEntry.evidence.Supports claim.descriptor) : claim = chairEntry.claim := by
  cases claim <;>
    simp [chairEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, chairRecord, sixRingUnit, IsChair, IsBoat,
      SixRingReferencePlane, OppositeSides, SameOffPlaneSide] at claimMatches supports ⊢

def chairPackage : P94SourcePackageSchema source molecule :=
  singletonPackage chairEntry [] chair_uniqueClaim

def halfChairObservation : HalfChairObservation where
  ringSize := 6
  doubleBondCount := 1
  firstRemoteSide := .positive
  secondRemoteSide := .negative

def halfChairRecord : P94HalfChairEvidence where
  unit := halfChairUnit
  observation := halfChairObservation

theorem halfChair_roles :
    (P94ConformationEvidence.halfChair halfChairRecord : P94ReviewedEvidence).MolecularRolesValid
      molecule := by
  change halfChairObservation.doubleBondCount = halfChairUnit.CycleDoubleBondCount molecule ∧
    halfChairUnit.MonounsaturatedCyclic molecule
  have count : halfChairUnit.CycleDoubleBondCount molecule = 1 := by
    simp [P94ConformationUnit.CycleDoubleBondCount,
      P94ConformationUnit.cycleBondOrders, P94ConformationUnit.cyclicSuccessors,
      halfChairUnit]
  refine ⟨by simpa [halfChairObservation] using count.symm, count, ?_⟩
  intro edge edgeMember rawBond rawBondMember _connects
  have allowed : rawBond.kind = .single ∨ rawBond.kind = .double := by
    simp [molecule, bond] at rawBondMember
    rcases rawBondMember with h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h <;> subst rawBond <;> simp
  rcases allowed with allowed | allowed <;> rw [allowed] <;>
    simp [P94ConformationUnit.MonounsaturatedCycleBondKind]

def halfChairEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .halfChair
  evidence := .halfChair halfChairRecord
  unitValid := halfChairUnit_valid
  molecularRolesValid := halfChair_roles
  predicateClosure := .halfChair halfChairRecord
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    simp [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      halfChairRecord, halfChairObservation, halfChairUnit, IsHalfChair, OppositeSides]

theorem halfChair_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence halfChairEntry.evidence)
    (supports : halfChairEntry.evidence.Supports claim.descriptor) :
    claim = halfChairEntry.claim := by
  cases claim <;> simp [halfChairEntry, P94AuthorityClaim.MatchesEvidence] at claimMatches ⊢

def halfChairPackage : P94SourcePackageSchema source molecule :=
  singletonPackage halfChairEntry [] halfChair_uniqueClaim

def crownRecord : P94RingPlaneEvidence where
  unit := crownUnit
  sides := [.positive, .negative, .positive, .negative, .positive, .negative, .positive, .negative]
  saturatedCyclic := True
  symmetricallyEquivalent := True

theorem crown_saturated : crownUnit.SaturatedCyclic molecule := by
  constructor
  · intro order member
    simp [P94ConformationUnit.cycleBondOrders, P94ConformationUnit.cyclicSuccessors,
      crownUnit] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  · intro edge edgeMember rawBond rawBondMember connects
    simp [crownUnit, P94ConformationUnit.cyclicSuccessors] at edgeMember
    rcases edgeMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [molecule, bond] at rawBondMember
      rcases rawBondMember with h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h <;> subst rawBond <;>
        simp_all [RawBond.connects, P94ConformationUnit.SaturatedSingleBondKind]

def crownEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .crown
  evidence := .ringPlane crownRecord
  unitValid := crownUnit_valid
  molecularRolesValid := by
    simpa [P94ConformationEvidence.MolecularRolesValid, crownRecord] using crown_saturated
  predicateClosure := .ringPlane crownRecord true true false
    (by simp [crownRecord]) (by simp [crownRecord]) (by simp [crownRecord])
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    simp [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor, crownRecord,
      crownUnit, IsCrown, AlternatingOffPlane, OppositeSides, even_iff_two_dvd]

theorem crown_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence crownEntry.evidence)
    (supports : crownEntry.evidence.Supports claim.descriptor) : claim = crownEntry.claim := by
  cases claim <;>
    simp [crownEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, crownRecord, crownUnit] at claimMatches supports ⊢

def crownPackage : P94SourcePackageSchema source molecule :=
  singletonPackage crownEntry [] crown_uniqueClaim

def tubRecord : P94RingPlaneEvidence where
  unit := tubUnit
  sides := [.onPlane, .onPlane, .positive, .positive, .onPlane, .onPlane, .positive, .positive]
  saturatedCyclic := False
  symmetricallyEquivalent := False

def tubEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .tub
  evidence := .ringPlane tubRecord
  unitValid := tubUnit_valid
  molecularRolesValid := by
    simp [P94ConformationEvidence.MolecularRolesValid, tubRecord, tubUnit]
  predicateClosure := .ringPlane tubRecord false false false
    (by simp [tubRecord]) (by simp [tubRecord]) (by simp [tubRecord])
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    refine ⟨rfl, rfl, ?_⟩
    refine ⟨0, ?_⟩
    change
      [PlaneSide.onPlane, .onPlane, .positive, .positive, .onPlane, .onPlane,
        .positive, .positive].length = 8 ∧
      [PlaneSide.onPlane, .onPlane, .positive, .positive, .onPlane, .onPlane,
        .positive, .positive][0]? = some .onPlane ∧
      [PlaneSide.onPlane, .onPlane, .positive, .positive, .onPlane, .onPlane,
        .positive, .positive][1]? = some .onPlane ∧
      [PlaneSide.onPlane, .onPlane, .positive, .positive, .onPlane, .onPlane,
        .positive, .positive][4]? = some .onPlane ∧
      [PlaneSide.onPlane, .onPlane, .positive, .positive, .onPlane, .onPlane,
        .positive, .positive][5]? = some .onPlane ∧
      ∃ offSide,
        (offSide = .positive ∨ offSide = .negative) ∧
        [PlaneSide.onPlane, .onPlane, .positive, .positive, .onPlane, .onPlane,
          .positive, .positive][2]? = some offSide ∧
        [PlaneSide.onPlane, .onPlane, .positive, .positive, .onPlane, .onPlane,
          .positive, .positive][3]? = some offSide ∧
        [PlaneSide.onPlane, .onPlane, .positive, .positive, .onPlane, .onPlane,
          .positive, .positive][6]? = some offSide ∧
        [PlaneSide.onPlane, .onPlane, .positive, .positive, .onPlane, .onPlane,
          .positive, .positive][7]? = some offSide
    simp

theorem tub_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence tubEntry.evidence)
    (supports : tubEntry.evidence.Supports claim.descriptor) : claim = tubEntry.claim := by
  cases claim <;>
    simp [tubEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, tubRecord, tubUnit] at claimMatches supports ⊢

def tubPackage : P94SourcePackageSchema source molecule :=
  singletonPackage tubEntry [] tub_uniqueClaim

/-! ## P-94.3.2.6: exact theta-core in/out pair -/

noncomputable def thetaFramework : ThetaFramework where
  firstBridgehead := 29
  secondBridgehead := 30
  bridges := { [29, 30], [29, 31, 30], [29, 32, 33, 30] }

theorem thetaFramework_valid : thetaFramework.ValidFor molecule thetaUnit := by
  constructor
  · refine ⟨by norm_num [thetaFramework],
      by norm_num [thetaFramework, molecule, RawMolecule.atomCount], by decide, ?_, ?_⟩
    · intro path member
      simp [thetaFramework] at member
      rcases member with rfl | rfl | rfl <;>
        simp [thetaFramework, BondedPathBetween, molecule, RawMolecule.atomCount,
          P94ConformationUnit.ConsecutivelyBonded, P94ConformationUnit.Bonded,
          RawBond.connects, bond, carbon]
    · intro first firstMember second secondMember distinct
      simp [thetaFramework] at firstMember secondMember
      rcases firstMember with rfl | rfl | rfl <;>
        rcases secondMember with rfl | rfl | rfl <;>
        simp [ThetaFramework.pathInterior] at distinct ⊢
  · simp [ThetaFramework.NamesBridge, ThetaFramework.bridgeUnits,
      ThetaFramework.bridgeUnit, thetaFramework, thetaUnit]

def inPoint (atom : Nat) : CartesianPoint3 :=
  if atom = 30 then { x := 1, y := 0, z := 0 }
  else if atom = 34 then { x := 1 / 2, y := 0, z := 0 }
  else { x := 0, y := 0, z := 0 }

def outPoint (atom : Nat) : CartesianPoint3 :=
  if atom = 30 then { x := 1, y := 0, z := 0 }
  else if atom = 34 then { x := -1, y := 0, z := 0 }
  else { x := 0, y := 0, z := 0 }

def inSpatial : SpatialConfiguration := { positions := (List.range 35).map inPoint }
def outSpatial : SpatialConfiguration := { positions := (List.range 35).map outPoint }
def interiorPoint : CartesianPoint3 := { x := 1, y := 0, z := 0 }

noncomputable def inwardCoordinate : P94InOutCoordinateObservation where
  framework := thetaFramework
  spatial := inSpatial
  virtualPoints := []
  bridgehead := 29
  directedParticipant := .atom 34
  interior := interiorPoint

noncomputable def outwardCoordinate : P94InOutCoordinateObservation where
  framework := thetaFramework
  spatial := outSpatial
  virtualPoints := []
  bridgehead := 29
  directedParticipant := .atom 34
  interior := interiorPoint

theorem inward_graph_judged :
    CoordinateInOutDirectionJudgment
      (graphElectronicAxisBridgePremises molecule ledger)
      molecule thetaUnit inwardCoordinate .inward := by
  refine ⟨by simp [inwardCoordinate, VirtualTorsionPointLedger.Valid,
      VirtualTorsionPointLedger.keys], ?_, ?_,
    { x := 0, y := 0, z := 0 }, { x := 1 / 2, y := 0, z := 0 }, ?_, ?_, ?_⟩
  · exact ⟨thetaFramework_valid, 30, Or.inl ⟨rfl, rfl⟩,
      by norm_num [inwardCoordinate, inSpatial, inPoint, interiorPoint,
        CoordinateRing.SpatialPointAt]⟩
  · refine ⟨by simp [inwardCoordinate, thetaUnit], ⟨thetaFramework_valid, ?_⟩,
      by norm_num [inwardCoordinate, molecule, RawMolecule.atomCount],
      by norm_num [molecule, RawMolecule.atomCount], by simp [thetaUnit], ?_, ?_⟩
    · change 29 = 29 ∨ 29 = 30
      exact Or.inl rfl
    · simp [graphElectronicAxisBridgePremises, bridgeDerivedPremises,
        graphElectronicAxisBasePremises, inwardCoordinate, ThetaFramework.ContainsAtom,
        thetaFramework]
    · change 0 < molecule.bondOrder 29 34
      rw [molecule_bondOrder_29_34]
      norm_num
  · norm_num [inwardCoordinate, inSpatial, inPoint, CoordinateRing.SpatialPointAt]
  · norm_num [inwardCoordinate, inSpatial, inPoint, CoordinateTorsion.ParticipantPointAt]
  · norm_num [inwardCoordinate, interiorPoint, CartesianPoint3.displacement,
      RationalVector3.dot]

theorem outward_graph_judged :
    CoordinateInOutDirectionJudgment
      (graphElectronicAxisBridgePremises molecule ledger)
      molecule thetaUnit outwardCoordinate .outward := by
  refine ⟨by simp [outwardCoordinate, VirtualTorsionPointLedger.Valid,
      VirtualTorsionPointLedger.keys], ?_, ?_,
    { x := 0, y := 0, z := 0 }, { x := -1, y := 0, z := 0 }, ?_, ?_, ?_⟩
  · exact ⟨thetaFramework_valid, 30, Or.inl ⟨rfl, rfl⟩,
      by norm_num [outwardCoordinate, outSpatial, outPoint, interiorPoint,
        CoordinateRing.SpatialPointAt]⟩
  · refine ⟨by simp [outwardCoordinate, thetaUnit], ⟨thetaFramework_valid, ?_⟩,
      by norm_num [outwardCoordinate, molecule, RawMolecule.atomCount],
      by norm_num [molecule, RawMolecule.atomCount], by simp [thetaUnit], ?_, ?_⟩
    · change 29 = 29 ∨ 29 = 30
      exact Or.inl rfl
    · simp [graphElectronicAxisBridgePremises, bridgeDerivedPremises,
        graphElectronicAxisBasePremises, outwardCoordinate, ThetaFramework.ContainsAtom,
        thetaFramework]
    · change 0 < molecule.bondOrder 29 34
      rw [molecule_bondOrder_29_34]
      norm_num
  · norm_num [outwardCoordinate, outSpatial, outPoint, CoordinateRing.SpatialPointAt]
  · norm_num [outwardCoordinate, outSpatial, outPoint,
      CoordinateTorsion.ParticipantPointAt]
  · norm_num [outwardCoordinate, interiorPoint, CartesianPoint3.displacement,
      RationalVector3.dot]

noncomputable def inOutCoordinatePair : P94SourcePackageInOutCoordinatePair molecule ledger where
  unit := thetaUnit
  unitValid := thetaUnit_valid
  first := inwardCoordinate
  second := outwardCoordinate
  firstDirection := .inward
  secondDirection := .outward
  directionsOpposite := by decide
  sameFramework := rfl
  sameBridgehead := rfl
  sameParticipant := rfl
  firstJudged := inward_graph_judged
  secondJudged := outward_graph_judged

theorem graph_judged_to_source_policy
    (observation : P94InOutCoordinateObservation) (direction : BridgeheadDirection)
    (participant : Nat) (participantExact : observation.directedParticipant = .atom participant)
    (judged : CoordinateInOutDirectionJudgment
      (graphElectronicAxisBridgePremises molecule ledger)
      molecule thetaUnit observation direction) :
    CoordinateInOutDirectionJudgment
      (bridgeDerivedPremises
        (p94SourcePackageSchemaPolicy.inOutBasePremises source molecule))
      molecule thetaUnit observation direction := by
  unfold CoordinateInOutDirectionJudgment at judged ⊢
  rw [participantExact] at judged ⊢
  rcases judged with
    ⟨ledgerValid, interiorValid, participantValid,
      bridgeheadPoint, participantPoint, bridgeheadAt, participantAt, sign⟩
  rcases participantValid with
    ⟨bridgeheadMember, ⟨frameworkValid, bridgeheadValid⟩,
      bridgeheadBounded, participantBounded, participantOutsideUnit,
      participantOutsideFramework, participantBonded⟩
  refine ⟨ledgerValid, ⟨rfl, interiorValid⟩,
    ⟨bridgeheadMember, ⟨rfl, frameworkValid, bridgeheadValid⟩,
      bridgeheadBounded, participantBounded, participantOutsideUnit, ?_, participantBonded⟩,
    bridgeheadPoint, participantPoint, bridgeheadAt, participantAt, sign⟩
  rintro ⟨_, participantInFramework⟩
  exact participantOutsideFramework participantInFramework

theorem inward_policy_judged :
    CoordinateInOutDirectionJudgment
      (bridgeDerivedPremises
        (p94SourcePackageSchemaPolicy.inOutBasePremises source molecule))
      molecule thetaUnit inwardCoordinate .inward :=
  graph_judged_to_source_policy inwardCoordinate .inward 34 rfl inward_graph_judged

theorem outward_policy_judged :
    CoordinateInOutDirectionJudgment
      (bridgeDerivedPremises
        (p94SourcePackageSchemaPolicy.inOutBasePremises source molecule))
      molecule thetaUnit outwardCoordinate .outward :=
  graph_judged_to_source_policy outwardCoordinate .outward 34 rfl outward_graph_judged

noncomputable def inOutRecord : P94InOutEvidence ThetaFramework where
  unit := thetaUnit
  first :=
    { framework := thetaFramework
      bridgehead := 29
      directedParticipant := .atom 34
      bridgeLongEnough := True
      direction := .inward }
  second :=
    { framework := thetaFramework
      bridgehead := 29
      directedParticipant := .atom 34
      bridgeLongEnough := True
      direction := .outward }
  bicyclicSystem := thetaFramework.ValidFor molecule thetaUnit

noncomputable def inOutEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .inOut
  evidence := .inOut inOutRecord
  unitValid := thetaUnit_valid
  molecularRolesValid := by simp [P94ConformationEvidence.MolecularRolesValid]
  predicateClosure := .inOut inOutRecord true true rfl
    (by change True = (true = true); simp)
    (by change True = (true = true); simp)
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    refine ⟨rfl, thetaFramework_valid, rfl, rfl, rfl, trivial, trivial, ?_⟩
    decide

theorem inOut_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence inOutEntry.evidence)
    (supports : inOutEntry.evidence.Supports claim.descriptor) : claim = inOutEntry.claim := by
  cases claim <;>
    simp [inOutEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, inOutRecord] at claimMatches supports ⊢

noncomputable def inOutPackage : P94SourcePackageSchema source molecule :=
  singletonPackage inOutEntry [inOutCoordinatePair] inOut_uniqueClaim

theorem inOut_bridge_allows_both :
    BridgeAllowsBothDirections
      (p94SourcePackageSchemaPolicy.inOutBasePremises source molecule)
      molecule thetaUnit thetaFramework := by
  exact ⟨inwardCoordinate, outwardCoordinate, rfl, rfl, rfl, rfl,
    inward_policy_judged, outward_policy_judged⟩

theorem inOut_certificate_valid :
    P94ConcreteInOutCertificateValid p94SourcePackageSchemaPolicy source molecule inOutRecord
      (some (inwardCoordinate, outwardCoordinate)) := by
  refine ⟨inwardCoordinate, outwardCoordinate, rfl, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, thetaFramework_valid, thetaFramework_valid,
    inward_policy_judged, outward_policy_judged, Iff.rfl, ?_, ?_⟩
  · exact ⟨inOutPackage, inOutCoordinatePair, by simp [inOutPackage, singletonPackage],
      rfl, rfl⟩
  · norm_num [inwardCoordinate, inSpatial, molecule, RawMolecule.atomCount]
  · norm_num [outwardCoordinate, outSpatial, molecule, RawMolecule.atomCount]
  · change True ↔ BridgeAllowsBothDirections
      (p94SourcePackageSchemaPolicy.inOutBasePremises source molecule)
      molecule thetaUnit thetaFramework
    exact (iff_true_intro inOut_bridge_allows_both).symm
  · change True ↔ BridgeAllowsBothDirections
      (p94SourcePackageSchemaPolicy.inOutBasePremises source molecule)
      molecule thetaUnit thetaFramework
    exact (iff_true_intro inOut_bridge_allows_both).symm

/-! ## The twelve-row schema-reference nonvacuity collapse -/

noncomputable def observationOf
    (entry : P94SourcePackageEvidenceEntry molecule ledger)
    (certificate : Option
      (P94InOutCoordinateObservation × P94InOutCoordinateObservation)) :
    P94AuthorityObservation p94SourcePackageSchemaPolicy where
  molecule := molecule
  evidence := entry.evidence
  claim := entry.claim
  inOutCertificate? := certificate

theorem observationOf_valid
    (entry : P94SourcePackageEvidenceEntry molecule ledger)
    (observed : p94SourcePackageSchemaPolicy.EvidenceObserved source molecule entry.evidence)
    (certificate : Option
      (P94InOutCoordinateObservation × P94InOutCoordinateObservation))
    (certificateValid : P94InOutCertificateMatches p94SourcePackageSchemaPolicy source molecule
      entry.evidence certificate) :
    (observationOf entry certificate).ValidFor p94SourcePackageSchemaPolicy source := by
  exact ⟨structureAgreement, observed,
    entry.unitValid, entry.molecularRolesValid, entry.matchesEvidence,
    entry.supports, certificateValid⟩

theorem row_nonvacuous_of_entry
    (row : Remaining71P94AuthorityRow)
    (entry : P94SourcePackageEvidenceEntry molecule ledger)
    (observed : p94SourcePackageSchemaPolicy.EvidenceObserved source molecule entry.evidence)
    (certificate : Option
      (P94InOutCoordinateObservation × P94InOutCoordinateObservation))
    (certificateValid : P94InOutCertificateMatches p94SourcePackageSchemaPolicy source molecule
      entry.evidence certificate)
    (provisionExact : entry.claim.provision = row.provision) :
    ∃ input, ∃ observation : (row.reference p94SourcePackageSchemaPolicy).Observation,
      input.StructurallyWellFormed ∧
        (row.reference p94SourcePackageSchemaPolicy).Applicable input ∧
        (row.reference p94SourcePackageSchemaPolicy).Judges input observation := by
  let observation := observationOf entry certificate
  have judged : (row.reference p94SourcePackageSchemaPolicy).Judges source observation := by
    exact ⟨observationOf_valid entry observed certificate certificateValid, provisionExact⟩
  exact ⟨source, observation, source_structurallyWellFormed, ⟨observation, judged⟩, judged⟩

theorem Remaining71P94AuthorityRow.schema_reference_nonvacuous
    (row : Remaining71P94AuthorityRow) :
    ∃ input, ∃ observation : (row.reference p94SourcePackageSchemaPolicy).Observation,
      input.StructurallyWellFormed ∧
        (row.reference p94SourcePackageSchemaPolicy).Applicable input ∧
        (row.reference p94SourcePackageSchemaPolicy).Judges input observation := by
  cases row
  · exact row_nonvacuous_of_entry .conformationDefinition conformerEntry
      ⟨conformerPackage, conformerEntry, by simp [conformerPackage, singletonPackage], rfl⟩
      none (by rfl) rfl
  · exact row_nonvacuous_of_entry .torsionAngle ordinaryTorsionEntry
      ⟨ordinaryTorsionPackage, ordinaryTorsionEntry,
        by simp [ordinaryTorsionPackage, singletonPackage], rfl⟩ none (by rfl) rfl
  · exact row_nonvacuous_of_entry .torsionLonePairs electronicTorsionEntry
      ⟨electronicTorsionPackage, electronicTorsionEntry,
        by simp [electronicTorsionPackage], rfl⟩ none (by rfl) rfl
  · exact row_nonvacuous_of_entry .eclipsedStaggeredGauche eclipsedEntry
      ⟨eclipsedPackage, eclipsedEntry, by simp [eclipsedPackage, singletonPackage], rfl⟩
      none (by rfl) rfl
  · exact row_nonvacuous_of_entry .trigonalConformations trigonalEntry
      ⟨trigonalPackage, trigonalEntry, by simp [trigonalPackage, singletonPackage], rfl⟩
      none (by rfl) rfl
  · exact row_nonvacuous_of_entry .sCisSTrans sCisEntry
      ⟨sCisPackage, sCisEntry, by simp [sCisPackage, singletonPackage], rfl⟩
      none (by rfl) rfl
  · exact row_nonvacuous_of_entry .envelope envelopeEntry
      ⟨envelopePackage, envelopeEntry, by simp [envelopePackage, singletonPackage], rfl⟩
      none (by rfl) rfl
  · exact row_nonvacuous_of_entry .chairBoatTwist chairEntry
      ⟨chairPackage, chairEntry, by simp [chairPackage, singletonPackage], rfl⟩
      none (by rfl) rfl
  · exact row_nonvacuous_of_entry .halfChair halfChairEntry
      ⟨halfChairPackage, halfChairEntry, by simp [halfChairPackage, singletonPackage], rfl⟩
      none (by rfl) rfl
  · exact row_nonvacuous_of_entry .crown crownEntry
      ⟨crownPackage, crownEntry, by simp [crownPackage, singletonPackage], rfl⟩
      none (by rfl) rfl
  · exact row_nonvacuous_of_entry .tub tubEntry
      ⟨tubPackage, tubEntry, by simp [tubPackage, singletonPackage], rfl⟩
      none (by rfl) rfl
  · exact row_nonvacuous_of_entry .inOut inOutEntry
      ⟨inOutPackage, inOutEntry, by simp [inOutPackage, singletonPackage], rfl⟩
      (some (inwardCoordinate, outwardCoordinate)) inOut_certificate_valid rfl

end P94SourcePackageNonvacuity
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P94SourcePackageNonvacuity.Remaining71P94AuthorityRow.schema_reference_nonvacuous
