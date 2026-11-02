import TetraStereo.OneCenter.IUPACRemaining71P94ReviewedSemantics
import TetraStereo.OneCenter.P94MolecularBridgeheadAxisInterior

set_option autoImplicit false























namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.CoordinateTwistInOut
open BlueBookP94.P94MolecularBicyclicFramework
open BlueBookP94.P94MolecularLonePair
open BlueBookP94.P94MolecularBridgeheadAxisInterior
open IUPACNormativeProvision

/-! ## Exact twelve-clause source partition -/

/-- The twelve manifest-level P-94 clauses.  Constructor order is source order. -/
inductive P94Clause where
  | conformationDefinition
  | torsionAngle
  | torsionLonePairs
  | eclipsedStaggeredGauche
  | trigonalConformations
  | sCisSTrans
  | envelope
  | chairBoatTwist
  | halfChair
  | crown
  | tub
  | inOut
  deriving DecidableEq, Repr

namespace P94Clause

def all : List P94Clause :=
  [ .conformationDefinition
  , .torsionAngle
  , .torsionLonePairs
  , .eclipsedStaggeredGauche
  , .trigonalConformations
  , .sCisSTrans
  , .envelope
  , .chairBoatTwist
  , .halfChair
  , .crown
  , .tub
  , .inOut
  ]

/-- Exact manifest provision named by each P-94 clause. -/
def provision : P94Clause → IUPACNormativeProvision
  | .conformationDefinition => .p94ConformationDefinition
  | .torsionAngle => .p94TorsionAngle
  | .torsionLonePairs => .p94TorsionLonePairs
  | .eclipsedStaggeredGauche => .p94EclipsedStaggeredGauche
  | .trigonalConformations => .p94TrigonalConformations
  | .sCisSTrans => .p94SCisSTrans
  | .envelope => .p94Envelope
  | .chairBoatTwist => .p94ChairBoatTwist
  | .halfChair => .p94HalfChair
  | .crown => .p94Crown
  | .tub => .p94Tub
  | .inOut => .p94InOut

@[simp] theorem all_length : all.length = 12 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact : all.map provision = p94SemanticsSlice := by
  rfl

end P94Clause

namespace P94AuthorityClaim

/-- Source-clause projection of every typed P-94 claim. -/
def clause : P94AuthorityClaim → P94Clause
  | .conformationDefinition => .conformationDefinition
  | .torsionSense _ | .torsionClass _ => .torsionAngle
  | .torsionElectronicProxy _ => .torsionLonePairs
  | .eclipsed | .staggered | .gauche => .eclipsedStaggeredGauche
  | .trigonalBisecting | .trigonalEclipsing => .trigonalConformations
  | .sCis | .sTrans => .sCisSTrans
  | .envelope => .envelope
  | .chair | .boat | .sixRingTwist | .carbohydrateFiveRingTwist => .chairBoatTwist
  | .halfChair => .halfChair
  | .crown => .crown
  | .tub => .tub
  | .inOut => .inOut

/-- Claim-level and clause-level manifest projections agree definitionally in every branch. -/
@[simp] theorem clause_provision (claim : P94AuthorityClaim) :
    claim.clause.provision = claim.provision := by
  cases claim <;> rfl

end P94AuthorityClaim

namespace IUPACNormativeProvision.Remaining71P94AuthorityRow

/-- Exact source clause owned by each of the twelve reviewed P-94 rows. -/
def clause : Remaining71P94AuthorityRow → P94Clause
  | .conformationDefinition => .conformationDefinition
  | .torsionAngle => .torsionAngle
  | .torsionLonePairs => .torsionLonePairs
  | .eclipsedStaggeredGauche => .eclipsedStaggeredGauche
  | .trigonalConformations => .trigonalConformations
  | .sCisSTrans => .sCisSTrans
  | .envelope => .envelope
  | .chairBoatTwist => .chairBoatTwist
  | .halfChair => .halfChair
  | .crown => .crown
  | .tub => .tub
  | .inOut => .inOut

@[simp] theorem clause_provision (row : Remaining71P94AuthorityRow) :
    row.clause.provision = row.provision := by
  cases row <;> rfl

@[simp] theorem all_clauses_exact : all.map clause = P94Clause.all := by
  rfl

end IUPACNormativeProvision.Remaining71P94AuthorityRow

/-! ## Proof-carrying finite package entries -/

/-- One source-listed evidence record.  The claim proves which of the exact twelve source clauses
the record instantiates, while the independent support relation proves the claimed descriptor.
Molecule-relative validity is stored here so membership is already meaningful before the record
is projected through `P94AuthorityObservation.ValidFor`. -/
def P94SelectedLonePairsCertified
    {molecule : RawMolecule} (ledger : CertifiedLonePairLedger molecule)
    (evidence : P94ReviewedEvidence) : Prop :=
  ∀ record : P94TorsionEvidence, evidence = .torsion record →
    ∀ candidate ∈ record.frontCandidates ++ record.rearCandidates,
      ∀ atom : Nat, candidate.participant = .lonePair atom →
        ledger.HasLonePairAt atom

/-- Closed finite spelling of a relation on coordinate-frame identifiers. -/
def P94FiniteNatRelation (pairs : List (Nat × Nat)) (first second : Nat) : Prop :=
  (first, second) ∈ pairs

/-- Closed finite spelling of a predicate on coordinate-frame identifiers. -/
def P94FiniteNatPredicate (values : List Nat) (value : Nat) : Prop :=
  value ∈ values

/-- Closed finite admissible-angle set for one source package. -/
noncomputable def P94FiniteAngleAdmissible (degrees : List ℝ) (angle : TorsionAngle) : Prop :=
  angle.degrees ∈ degrees

/-- Closed finite separation table.  Missing angles receive zero; the package proof must still
show that the resulting context satisfies the requested source judgment. -/
noncomputable def P94FiniteAngleSeparation : List (ℝ × ℝ) → TorsionAngle → ℝ
  | [], _angle => 0
  | (degrees, separation) :: rest, angle =>
      if angle.degrees = degrees then separation else P94FiniteAngleSeparation rest angle

/-- Certificate that every proposition-valued or function-valued component hidden inside an
existing `P94ReviewedEvidence` record was compiled from finite package data (or, for the in/out
flag, from exact theta-framework validity).  The nine constructors are exhaustive and contain no
fallback predicate case. -/
inductive P94CanonicalEvidencePredicateClosure (molecule : RawMolecule) :
    P94ReviewedEvidence → Prop where
  | conformer (record : P94ConformerEvidence Nat) (rotations : List (Nat × Nat))
      (rotationExact : record.singleBondRotation = P94FiniteNatRelation rotations) :
      P94CanonicalEvidencePredicateClosure molecule (.conformer record)
  | torsion (record : P94TorsionEvidence) :
      P94CanonicalEvidencePredicateClosure molecule (.torsion record)
  | eclipsedStaggered (record : P94EclipsedStaggeredEvidence)
      (admissibleDegrees : List ℝ) (separations : List (ℝ × ℝ))
      (allLigandsIdentical : Bool)
      (admissibleExact : record.staggeredContext.admissible =
        P94FiniteAngleAdmissible admissibleDegrees)
      (separationExact : record.staggeredContext.separationFromNearestEclipsed =
        P94FiniteAngleSeparation separations)
      (identicalExact : record.staggeredContext.allLigandsIdentical =
        (allLigandsIdentical = true)) :
      P94CanonicalEvidencePredicateClosure molecule (.eclipsedStaggered record)
  | trigonal (record : P94TrigonalConformationEvidence)
      (isR3CCYXGrouping doubleBondBisectsRCRAngle : Bool)
      (groupingExact : record.observation.isR3CCYXGrouping =
        (isR3CCYXGrouping = true))
      (bisectsExact : record.observation.doubleBondBisectsRCRAngle =
        (doubleBondBisectsRCRAngle = true)) :
      P94CanonicalEvidencePredicateClosure molecule (.trigonal record)
  | conjugated (record : P94ConjugatedSystemEvidence) :
      P94CanonicalEvidencePredicateClosure molecule (.conjugated record)
  | ringPlane (record : P94RingPlaneEvidence)
      (saturatedCyclic symmetricallyEquivalent carbohydrateFiveRing : Bool)
      (saturatedExact : record.saturatedCyclic = (saturatedCyclic = true))
      (symmetricExact : record.symmetricallyEquivalent =
        (symmetricallyEquivalent = true))
      (carbohydrateExact : record.carbohydrateFiveRing =
        (carbohydrateFiveRing = true)) :
      P94CanonicalEvidencePredicateClosure molecule (.ringPlane record)
  | twist (record : P94TwistEvidence Nat)
      (rotations distinctEndpoints : List (Nat × Nat))
      (boatStates chairStates : List Nat)
      (rotationExact : record.singleBondRotation = P94FiniteNatRelation rotations)
      (distinctExact : record.endpointConformationsDistinct =
        P94FiniteNatRelation distinctEndpoints)
      (boatExact : record.isBoatState = P94FiniteNatPredicate boatStates)
      (chairExact : record.isChairState = P94FiniteNatPredicate chairStates) :
      P94CanonicalEvidencePredicateClosure molecule (.twist record)
  | halfChair (record : P94HalfChairEvidence) :
      P94CanonicalEvidencePredicateClosure molecule (.halfChair record)
  | inOut (record : P94InOutEvidence ThetaFramework)
      (firstBridgeLongEnough secondBridgeLongEnough : Bool)
      (bicyclicExact : record.bicyclicSystem =
        record.first.framework.ValidFor molecule record.unit)
      (firstBridgeExact : record.first.bridgeLongEnough =
        (firstBridgeLongEnough = true))
      (secondBridgeExact : record.second.bridgeLongEnough =
        (secondBridgeLongEnough = true)) :
      P94CanonicalEvidencePredicateClosure molecule (.inOut record)

structure P94SourcePackageEvidenceEntry
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule) where
  claim : P94AuthorityClaim
  evidence : P94ReviewedEvidence
  unitValid : evidence.unit.ValidFor molecule
  molecularRolesValid : evidence.MolecularRolesValid molecule
  predicateClosure : P94CanonicalEvidencePredicateClosure molecule evidence
  /-- P-94.2.2 lone-pair participants are not admitted merely because the participant constructor
  says `lonePair`; each selected lone pair must be a positive lookup in the molecule-bound
  electronic ledger.  Duplicate participants remain validated by `molecularRolesValid`. -/
  selectedLonePairsCertified : P94SelectedLonePairsCertified ledger evidence
  matchesEvidence : claim.MatchesEvidence evidence
  supports : evidence.Supports claim.descriptor

/-- One finite source-listed pair of coordinate realizations for a single in/out site.  Directions
are not stored as claims: they are proved by the exact rational-coordinate judgments.  Requiring
opposite directions and the same framework/site/participant is precisely the operational
bridge-sufficiency content of P-94.3.2.6. -/
structure P94SourcePackageInOutCoordinatePair
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule) where
  unit : P94ConformationUnit
  unitValid : unit.ValidFor molecule
  first : P94InOutCoordinateObservation
  second : P94InOutCoordinateObservation
  firstDirection : BridgeheadDirection
  secondDirection : BridgeheadDirection
  directionsOpposite : firstDirection ≠ secondDirection
  sameFramework : first.framework = second.framework
  sameBridgehead : first.bridgehead = second.bridgehead
  sameParticipant : first.directedParticipant = second.directedParticipant
  firstJudged : CoordinateInOutDirectionJudgment
    (graphElectronicAxisBridgePremises molecule ledger)
    molecule unit first firstDirection
  secondJudged : CoordinateInOutDirectionJudgment
    (graphElectronicAxisBridgePremises molecule ledger)
    molecule unit second secondDirection

/-- A finite, proof-carrying source package for one exact authoritative input/raw-molecule pair.
The ledger is tied back to the same authoritative input; hence a positive lone-pair projection
recovers both parser conversion and the checked main-group electron equation. -/
structure P94SourcePackageSchema
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule) where
  authoritativeStructureAgreement : molecule.AuthoritativeStructureAgreement source
  lonePairLedger : CertifiedLonePairLedger molecule
  ledgerSource : lonePairLedger.source = source
  evidenceEntries : List (P94SourcePackageEvidenceEntry molecule lonePairLedger)
  /-- Operational closure prevents `EvidenceObserved` from erasing source-clause provenance:
  every other claim compatible with a listed evidence value must itself be listed explicitly. -/
  compatibleClaimsListed :
    ∀ entry ∈ evidenceEntries, ∀ claim : P94AuthorityClaim,
      claim.MatchesEvidence entry.evidence →
      entry.evidence.Supports claim.descriptor →
      ∃ listed ∈ evidenceEntries,
        listed.claim = claim ∧ listed.evidence = entry.evidence
  inOutCoordinatePairs : List
    (P94SourcePackageInOutCoordinatePair molecule lonePairLedger)

/-- The one closed source-package relation from which every canonical policy predicate is
projected.  It is inhabited exactly when finite, proof-carrying package data exists for the given
authoritative input and molecule. -/
def P94SourcePackageSchemaInhabited
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule) : Prop :=
  Nonempty (P94SourcePackageSchema source molecule)

/-! ## Four projections and the fixed policy -/

def P94SourcePackageEvidenceObserved
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (evidence : P94ReviewedEvidence) : Prop :=
  ∃ package : P94SourcePackageSchema source molecule,
    ∃ entry ∈ package.evidenceEntries, entry.evidence = evidence

def P94SourcePackageInOutCoordinatePairObserved
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (first second : P94InOutCoordinateObservation) : Prop :=
  ∃ package : P94SourcePackageSchema source molecule,
    ∃ pair ∈ package.inOutCoordinatePairs,
      pair.first = first ∧ pair.second = second

def P94SourcePackageInOutInteriorWitness
    (_source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : ThetaFramework) (bridgehead : Nat)
    (spatial : SpatialConfiguration) (interior : CartesianPoint3) : Prop :=
  BridgeheadAxisInteriorWitness molecule unit framework bridgehead spatial interior

def P94SourcePackageLonePairObserved
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule) (atom : Nat) : Prop :=
  ∃ package : P94SourcePackageSchema source molecule,
    package.lonePairLedger.HasLonePairAt atom

/-- Schema projection of the finite package language.  This is useful for closing the arbitrary
predicate fields while developing the frozen compiler, but is deliberately not named or exported
as the completed canonical P-94 authority: package witnesses are still supplied existentially. -/
def p94SourcePackageSchemaPolicy : P94AuthorityPolicy where
  EvidenceObserved := P94SourcePackageEvidenceObserved
  InOutCoordinatePairObserved := P94SourcePackageInOutCoordinatePairObserved
  InOutInteriorWitness := P94SourcePackageInOutInteriorWitness
  LonePairObserved := P94SourcePackageLonePairObserved

@[simp] theorem p94SourcePackageSchemaPolicy_evidenceObserved_iff
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (evidence : P94ReviewedEvidence) :
    p94SourcePackageSchemaPolicy.EvidenceObserved source molecule evidence ↔
      ∃ package : P94SourcePackageSchema source molecule,
        ∃ entry ∈ package.evidenceEntries, entry.evidence = evidence :=
  Iff.rfl

@[simp] theorem p94SourcePackageSchemaPolicy_coordinatePairObserved_iff
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (first second : P94InOutCoordinateObservation) :
    p94SourcePackageSchemaPolicy.InOutCoordinatePairObserved source molecule first second ↔
      ∃ package : P94SourcePackageSchema source molecule,
        ∃ pair ∈ package.inOutCoordinatePairs,
          pair.first = first ∧ pair.second = second :=
  Iff.rfl

@[simp] theorem p94SourcePackageSchemaPolicy_interiorWitness_iff
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : ThetaFramework) (bridgehead : Nat)
    (spatial : SpatialConfiguration) (interior : CartesianPoint3) :
    p94SourcePackageSchemaPolicy.InOutInteriorWitness source molecule unit framework
        bridgehead spatial interior ↔
      BridgeheadAxisInteriorWitness molecule unit framework bridgehead spatial interior :=
  Iff.rfl

@[simp] theorem p94SourcePackageSchemaPolicy_lonePairObserved_iff
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule) (atom : Nat) :
    p94SourcePackageSchemaPolicy.LonePairObserved source molecule atom ↔
      ∃ package : P94SourcePackageSchema source molecule,
        package.lonePairLedger.HasLonePairAt atom :=
  Iff.rfl

/-! ## Information recovered from canonical observations -/

/-- An observed evidence record always recovers its independently validated molecule-relative
unit/role proofs and a source-aligned typed claim. -/
theorem canonicalEvidenceObserved_valid
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    {evidence : P94ReviewedEvidence}
    (observed : p94SourcePackageSchemaPolicy.EvidenceObserved source molecule evidence) :
    ∃ claim : P94AuthorityClaim,
      evidence.unit.ValidFor molecule ∧
        evidence.MolecularRolesValid molecule ∧
        claim.MatchesEvidence evidence ∧
        evidence.Supports claim.descriptor := by
  rcases observed with ⟨package, entry, member, rfl⟩
  exact ⟨entry.claim, entry.unitValid, entry.molecularRolesValid,
    entry.matchesEvidence, entry.supports⟩

/-- Although the legacy policy interface cannot receive a claim, package closure prevents claim
erasure operationally.  Any claim later accepted by `P94AuthorityObservation.ValidFor` is itself
present as an exact package entry for that same evidence value.  Thus torsion-angle evidence
cannot silently cross into P-94.2.2 unless the electronic-proxy claim was explicitly listed. -/
theorem p94SourcePackageSchema_compatibleClaimListed
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    {evidence : P94ReviewedEvidence} {claim : P94AuthorityClaim}
    (observed : p94SourcePackageSchemaPolicy.EvidenceObserved source molecule evidence)
    (claimMatches : claim.MatchesEvidence evidence)
    (supports : evidence.Supports claim.descriptor) :
    ∃ package : P94SourcePackageSchema source molecule,
      ∃ listed ∈ package.evidenceEntries,
        listed.claim = claim ∧ listed.evidence = evidence := by
  rcases observed with ⟨package, entry, entryMember, evidenceIdentity⟩
  have matchesEntry : claim.MatchesEvidence entry.evidence := by
    simpa [evidenceIdentity] using claimMatches
  have supportsEntry : entry.evidence.Supports claim.descriptor := by
    simpa [evidenceIdentity] using supports
  rcases package.compatibleClaimsListed entry entryMember claim matchesEntry supportsEntry with
    ⟨listed, listedMember, claimIdentity, listedEvidenceIdentity⟩
  exact ⟨package, listed, listedMember, claimIdentity,
    listedEvidenceIdentity.trans evidenceIdentity⟩

/-- Operational clause alignment for the schema policy follows from the exact listed claim, not
merely from the evidence constructor. -/
theorem p94SourcePackageSchema_operationalClauseAlignment
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    {evidence : P94ReviewedEvidence} {claim : P94AuthorityClaim}
    (observed : p94SourcePackageSchemaPolicy.EvidenceObserved source molecule evidence)
    (claimMatches : claim.MatchesEvidence evidence)
    (supports : evidence.Supports claim.descriptor) :
    ∃ package : P94SourcePackageSchema source molecule,
      ∃ listed ∈ package.evidenceEntries,
        listed.claim.clause = claim.clause ∧
          listed.claim.provision = claim.provision ∧
          listed.evidence = evidence := by
  rcases p94SourcePackageSchema_compatibleClaimListed observed claimMatches supports with
    ⟨package, listed, member, claimIdentity, evidenceIdentity⟩
  exact ⟨package, listed, member, congrArg P94AuthorityClaim.clause claimIdentity,
    congrArg P94AuthorityClaim.provision claimIdentity, evidenceIdentity⟩

/-- In particular, an evidence package cannot use a P-94.2.2 lone-pair candidate constructor as
its own electronic authority.  Every front or rear candidate lone pair—including candidates that
affect selection without being selected—projects to the same package's certified finite ledger. -/
theorem canonicalTorsionEvidenceObserved_candidateLonePairs
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    {record : P94TorsionEvidence}
    (observed : p94SourcePackageSchemaPolicy.EvidenceObserved
      source molecule (.torsion record)) :
    ∀ candidate ∈ record.frontCandidates ++ record.rearCandidates,
      ∀ atom : Nat, candidate.participant = .lonePair atom →
        p94SourcePackageSchemaPolicy.LonePairObserved source molecule atom := by
  rcases observed with ⟨package, entry, member, evidenceIdentity⟩
  have certified := entry.selectedLonePairsCertified record evidenceIdentity
  intro candidate candidateMember atom lonePair
  exact ⟨package, certified candidate candidateMember atom lonePair⟩

/-- Because source selection names members of the two candidate lists, the candidate theorem
specializes immediately to both selected participants. -/
theorem canonicalTorsionEvidenceObserved_selectedLonePairs
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    {record : P94TorsionEvidence}
    (observed : p94SourcePackageSchemaPolicy.EvidenceObserved
      source molecule (.torsion record))
    (selected : record.SelectedBySourceCriteria) :
    (∀ atom : Nat, record.selectedFront.participant = .lonePair atom →
      p94SourcePackageSchemaPolicy.LonePairObserved source molecule atom) ∧
    (∀ atom : Nat, record.selectedRear.participant = .lonePair atom →
      p94SourcePackageSchemaPolicy.LonePairObserved source molecule atom) := by
  have allCandidates := canonicalTorsionEvidenceObserved_candidateLonePairs observed
  constructor
  · exact allCandidates record.selectedFront
      (by simp [selected.1])
  · exact allCandidates record.selectedRear
      (by simp [selected.2.1])

/-- A canonical positive lone-pair observation is an executable hit in a finite certified ledger
and therefore names a real atom with a checked main-group Lewis-electron witness. -/
theorem canonicalLonePairObserved_certified
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule} {atom : Nat}
    (observed : p94SourcePackageSchemaPolicy.LonePairObserved source molecule atom) :
    atom < molecule.atomCount ∧
      ∃ package : P94SourcePackageSchema source molecule,
        ∃ annotation ∈ package.lonePairLedger.annotations,
          annotation.atomIndex = atom ∧ 0 < annotation.lonePairs ∧
            AnnotationSatisfiesMainGroupElectronBalance molecule
              package.lonePairLedger.source package.lonePairLedger.converted annotation := by
  rcases observed with ⟨package, present⟩
  exact ⟨package.lonePairLedger.hasLonePairAt_atom_bounded atom present,
    package, package.lonePairLedger.hasLonePairAt_mainGroupLewis atom present⟩

/-- Every projected coordinate pair comes from a finite entry whose two directions were checked
by the exact graph/electronic/opposite-axis coordinate semantics. -/
theorem canonicalCoordinatePairObserved_valid
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    {first second : P94InOutCoordinateObservation}
    (observed : p94SourcePackageSchemaPolicy.InOutCoordinatePairObserved
      source molecule first second) :
    ∃ package : P94SourcePackageSchema source molecule,
      ∃ pair ∈ package.inOutCoordinatePairs,
        pair.first = first ∧ pair.second = second ∧
          pair.firstDirection ≠ pair.secondDirection ∧
          pair.first.framework = pair.second.framework ∧
          pair.first.bridgehead = pair.second.bridgehead ∧
          pair.first.directedParticipant = pair.second.directedParticipant ∧
          CoordinateInOutDirectionJudgment
            (graphElectronicAxisBridgePremises molecule package.lonePairLedger)
            molecule pair.unit pair.first pair.firstDirection ∧
          CoordinateInOutDirectionJudgment
            (graphElectronicAxisBridgePremises molecule package.lonePairLedger)
            molecule pair.unit pair.second pair.secondDirection := by
  rcases observed with ⟨package, pair, member, firstIdentity, secondIdentity⟩
  exact ⟨package, pair, member, firstIdentity, secondIdentity,
    pair.directionsOpposite, pair.sameFramework, pair.sameBridgehead,
    pair.sameParticipant, pair.firstJudged, pair.secondJudged⟩

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P94Clause.all_provisions_exact
assert_kernel_only TetraStereo.OneCenter.P94AuthorityClaim.clause_provision
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P94AuthorityRow.clause_provision
assert_kernel_only TetraStereo.OneCenter.p94SourcePackageSchemaPolicy_interiorWitness_iff
assert_kernel_only TetraStereo.OneCenter.canonicalTorsionEvidenceObserved_selectedLonePairs
assert_kernel_only TetraStereo.OneCenter.canonicalLonePairObserved_certified
assert_kernel_only TetraStereo.OneCenter.canonicalCoordinatePairObserved_valid
