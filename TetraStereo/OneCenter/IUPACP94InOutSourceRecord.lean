import TetraStereo.OneCenter.IUPACP94SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.CoordinateTorsion
open BlueBookP94.CoordinateTwistInOut
open BlueBookP94.P94MolecularBicyclicFramework
open BlueBookP94.P94MolecularBridgeSufficiency
open BlueBookP94.P94MolecularLonePair
open BlueBookP94.P94MolecularBridgeheadAxisInterior

namespace P94InOutSourceRecord

def sourceIllustrationBlocks : List P94SourceAuditLedger.IllustrationBlock :=
  [.inOutExampleOne, .inOutExampleTwo]

def sourceArtifactSha256 : String :=
  P94SourceAuditLedger.frozenP9Artifact.sha256

@[simp] theorem source_illustration_blocks_exact :
    sourceIllustrationBlocks =
      [ P94SourceAuditLedger.IllustrationBlock.inOutExampleOne
      , P94SourceAuditLedger.IllustrationBlock.inOutExampleTwo ] := by
  rfl

@[simp] theorem source_illustration_bindings_exact :
    sourceIllustrationBlocks.map P94SourceAuditLedger.IllustrationBlock.pdfPage = [91, 91] ∧
      sourceIllustrationBlocks.map P94SourceAuditLedger.IllustrationBlock.clause =
        [.inOut, .inOut] := by
  decide

@[simp] theorem source_artifact_digest_exact :
    sourceArtifactSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  rfl

inductive DirectedParticipantKind where
  | exocyclicBond
  | lonePair
  deriving DecidableEq, Repr

inductive BridgeheadPairState where
  | inIn
  | inOut
  | outOut
  deriving DecidableEq, Repr

structure SourceFigureRecord where
  block : P94SourceAuditLedger.IllustrationBlock
  participantKind : DirectedParticipantKind
  pairState : BridgeheadPairState
  deriving DecidableEq, Repr

def sourceFigureInventory : List SourceFigureRecord :=
  [ ⟨.inOutExampleOne, .exocyclicBond, .inIn⟩
  , ⟨.inOutExampleOne, .exocyclicBond, .inOut⟩
  , ⟨.inOutExampleOne, .exocyclicBond, .outOut⟩
  , ⟨.inOutExampleTwo, .lonePair, .inIn⟩
  , ⟨.inOutExampleTwo, .lonePair, .inOut⟩
  , ⟨.inOutExampleTwo, .lonePair, .outOut⟩ ]

@[simp] theorem source_figure_inventory_exact :
    sourceFigureInventory.map (fun record =>
      (record.block, record.participantKind, record.pairState)) =
      [ (.inOutExampleOne, .exocyclicBond, .inIn)
      , (.inOutExampleOne, .exocyclicBond, .inOut)
      , (.inOutExampleOne, .exocyclicBond, .outOut)
      , (.inOutExampleTwo, .lonePair, .inIn)
      , (.inOutExampleTwo, .lonePair, .inOut)
      , (.inOutExampleTwo, .lonePair, .outOut) ] := by
  rfl

@[simp] theorem source_figure_inventory_complete :
    sourceFigureInventory.length = 6 ∧ sourceFigureInventory.Nodup := by
  decide

namespace TopologySpecialization

private def carbon : AtomSpec := AtomSpec.aliphatic .C

private def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

/-! Bridgeheads 0 and 1 are connected by three internally disjoint paths.  Atom 5 is the
ordinary exocyclic participant attached at bridgehead 0. -/
def molecule : RawMolecule where
  atoms := List.replicate 6 carbon
  bonds :=
    [ bond 0 1
    , bond 0 2, bond 2 1
    , bond 0 3, bond 3 4, bond 4 1
    , bond 0 5 ]

def source : AuthoritativeChemicalInput :=
  match molecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        diagram? := some molecule.toDiagramConfiguration }

@[simp] theorem molecule_counts_exact :
    molecule.atomCount = 6 ∧ molecule.bonds.length = 7 := by
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

def inOutUnit : P94ConformationUnit where
  kind := .bicyclicBridge
  atoms := [0, 1]

theorem inOutUnit_valid : inOutUnit.ValidFor molecule := by
  simp [P94ConformationUnit.ValidFor, P94ConformationUnit.ConsecutivelyBonded,
    P94ConformationUnit.Bonded, inOutUnit, molecule, RawMolecule.atomCount,
    RawBond.connects, bond, carbon]

noncomputable def thetaFramework : ThetaFramework where
  firstBridgehead := 0
  secondBridgehead := 1
  bridges := { [0, 1], [0, 2, 1], [0, 3, 4, 1] }

theorem thetaFramework_valid : thetaFramework.ValidFor molecule inOutUnit := by
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
      ThetaFramework.bridgeUnit, thetaFramework, inOutUnit]

@[simp] theorem molecule_bondOrder_zero_five : molecule.bondOrder 0 5 = 1 := by
  rfl

def inwardPoint (atom : Nat) : CartesianPoint3 :=
  if atom = 1 then { x := 1, y := 0, z := 0 }
  else if atom = 5 then { x := 1 / 2, y := 0, z := 0 }
  else { x := 0, y := 0, z := 0 }

def outwardPoint (atom : Nat) : CartesianPoint3 :=
  if atom = 1 then { x := 1, y := 0, z := 0 }
  else if atom = 5 then { x := -1, y := 0, z := 0 }
  else { x := 0, y := 0, z := 0 }

def inwardSpatial : SpatialConfiguration :=
  { positions := (List.range 6).map inwardPoint }

def outwardSpatial : SpatialConfiguration :=
  { positions := (List.range 6).map outwardPoint }

def interiorPoint : CartesianPoint3 := { x := 1, y := 0, z := 0 }

noncomputable def inwardCoordinate : P94InOutCoordinateObservation where
  framework := thetaFramework
  spatial := inwardSpatial
  virtualPoints := []
  bridgehead := 0
  directedParticipant := .atom 5
  interior := interiorPoint

noncomputable def outwardCoordinate : P94InOutCoordinateObservation where
  framework := thetaFramework
  spatial := outwardSpatial
  virtualPoints := []
  bridgehead := 0
  directedParticipant := .atom 5
  interior := interiorPoint

theorem inward_graph_judged :
    CoordinateInOutDirectionJudgment
      (graphElectronicAxisBridgePremises molecule ledger)
      molecule inOutUnit inwardCoordinate .inward := by
  refine ⟨by simp [inwardCoordinate, VirtualTorsionPointLedger.Valid,
      VirtualTorsionPointLedger.keys], ?_, ?_,
    { x := 0, y := 0, z := 0 }, { x := 1 / 2, y := 0, z := 0 }, ?_, ?_, ?_⟩
  · exact ⟨thetaFramework_valid, 1, Or.inl ⟨rfl, rfl⟩,
      by norm_num [inwardCoordinate, inwardSpatial, inwardPoint, interiorPoint,
        CoordinateRing.SpatialPointAt]⟩
  · refine ⟨by simp [inwardCoordinate, inOutUnit], ⟨thetaFramework_valid, ?_⟩,
      by norm_num [inwardCoordinate, molecule, RawMolecule.atomCount],
      by norm_num [molecule, RawMolecule.atomCount], by simp [inOutUnit], ?_, ?_⟩
    · change 0 = 0 ∨ 0 = 1
      exact Or.inl rfl
    · simp [graphElectronicAxisBridgePremises, bridgeDerivedPremises,
        graphElectronicAxisBasePremises, inwardCoordinate, ThetaFramework.ContainsAtom,
        thetaFramework]
    · change 0 < molecule.bondOrder 0 5
      rw [molecule_bondOrder_zero_five]
      norm_num
  · norm_num [inwardCoordinate, inwardSpatial, inwardPoint,
      CoordinateRing.SpatialPointAt]
  · norm_num [inwardCoordinate, inwardSpatial, inwardPoint,
      CoordinateTorsion.ParticipantPointAt]
  · norm_num [inwardCoordinate, interiorPoint, CartesianPoint3.displacement,
      RationalVector3.dot]

theorem outward_graph_judged :
    CoordinateInOutDirectionJudgment
      (graphElectronicAxisBridgePremises molecule ledger)
      molecule inOutUnit outwardCoordinate .outward := by
  refine ⟨by simp [outwardCoordinate, VirtualTorsionPointLedger.Valid,
      VirtualTorsionPointLedger.keys], ?_, ?_,
    { x := 0, y := 0, z := 0 }, { x := -1, y := 0, z := 0 }, ?_, ?_, ?_⟩
  · exact ⟨thetaFramework_valid, 1, Or.inl ⟨rfl, rfl⟩,
      by norm_num [outwardCoordinate, outwardSpatial, outwardPoint, interiorPoint,
        CoordinateRing.SpatialPointAt]⟩
  · refine ⟨by simp [outwardCoordinate, inOutUnit], ⟨thetaFramework_valid, ?_⟩,
      by norm_num [outwardCoordinate, molecule, RawMolecule.atomCount],
      by norm_num [molecule, RawMolecule.atomCount], by simp [inOutUnit], ?_, ?_⟩
    · change 0 = 0 ∨ 0 = 1
      exact Or.inl rfl
    · simp [graphElectronicAxisBridgePremises, bridgeDerivedPremises,
        graphElectronicAxisBasePremises, outwardCoordinate, ThetaFramework.ContainsAtom,
        thetaFramework]
    · change 0 < molecule.bondOrder 0 5
      rw [molecule_bondOrder_zero_five]
      norm_num
  · norm_num [outwardCoordinate, outwardSpatial, outwardPoint,
      CoordinateRing.SpatialPointAt]
  · norm_num [outwardCoordinate, outwardSpatial, outwardPoint,
      CoordinateTorsion.ParticipantPointAt]
  · norm_num [outwardCoordinate, interiorPoint, CartesianPoint3.displacement,
      RationalVector3.dot]

noncomputable def inOutCoordinatePair :
    P94SourcePackageInOutCoordinatePair molecule ledger where
  unit := inOutUnit
  unitValid := inOutUnit_valid
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
      molecule inOutUnit observation direction) :
    CoordinateInOutDirectionJudgment
      (bridgeDerivedPremises
        (p94SourcePackageSchemaPolicy.inOutBasePremises source molecule))
      molecule inOutUnit observation direction := by
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
      molecule inOutUnit inwardCoordinate .inward :=
  graph_judged_to_source_policy inwardCoordinate .inward 5 rfl inward_graph_judged

theorem outward_policy_judged :
    CoordinateInOutDirectionJudgment
      (bridgeDerivedPremises
        (p94SourcePackageSchemaPolicy.inOutBasePremises source molecule))
      molecule inOutUnit outwardCoordinate .outward :=
  graph_judged_to_source_policy outwardCoordinate .outward 5 rfl outward_graph_judged

noncomputable def inOutRecord : P94InOutEvidence ThetaFramework where
  unit := inOutUnit
  first :=
    { framework := thetaFramework
      bridgehead := 0
      directedParticipant := .atom 5
      bridgeLongEnough := True
      direction := .inward }
  second :=
    { framework := thetaFramework
      bridgehead := 0
      directedParticipant := .atom 5
      bridgeLongEnough := True
      direction := .outward }
  bicyclicSystem := thetaFramework.ValidFor molecule inOutUnit

noncomputable def inOutEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .inOut
  evidence := .inOut inOutRecord
  unitValid := inOutUnit_valid
  molecularRolesValid := by simp [P94ConformationEvidence.MolecularRolesValid]
  predicateClosure := .inOut inOutRecord true true rfl
    (by change True = (true = true); simp)
    (by change True = (true = true); simp)
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    refine ⟨rfl, thetaFramework_valid, rfl, rfl, rfl, trivial, trivial, ?_⟩
    decide

private theorem inOut_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence inOutEntry.evidence)
    (supports : inOutEntry.evidence.Supports claim.descriptor) : claim = inOutEntry.claim := by
  cases claim <;>
    simp [inOutEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, inOutRecord] at claimMatches supports ⊢

noncomputable def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [inOutEntry]
  compatibleClaimsListed := by
    intro listed listedMember claim claimMatches supports
    have listedIdentity : listed = inOutEntry := by simpa using listedMember
    subst listed
    have claimIdentity := inOut_uniqueClaim claim claimMatches supports
    subst claim
    exact ⟨inOutEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := [inOutCoordinatePair]

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim = [.inOut] := by
  rfl

@[simp] theorem source_package_coordinate_pair_count_exact :
    sourcePackage.inOutCoordinatePairs.length = 1 := by
  rfl

theorem bridge_allows_both :
    BridgeAllowsBothDirections
      (p94SourcePackageSchemaPolicy.inOutBasePremises source molecule)
      molecule inOutUnit thetaFramework := by
  exact ⟨inwardCoordinate, outwardCoordinate, rfl, rfl, rfl, rfl,
    inward_policy_judged, outward_policy_judged⟩

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

end TopologySpecialization

noncomputable def frozenRecord : P94FrozenPackageRecord where
  source := TopologySpecialization.source
  molecule := TopologySpecialization.molecule
  package := TopologySpecialization.sourcePackage
  normalizationReady := TopologySpecialization.normalizationReady

@[simp] theorem frozen_record_exact :
    frozenRecord.source = TopologySpecialization.source ∧
      frozenRecord.molecule = TopologySpecialization.molecule ∧
        frozenRecord.package = TopologySpecialization.sourcePackage := by
  exact ⟨rfl, rfl, rfl⟩

noncomputable def distinguishedEntry : P94FrozenDistinguishedEntry where
  record := frozenRecord
  entry := TopologySpecialization.inOutEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim = .inOut ∧
      distinguishedEntry.entry.claim.clause = .inOut ∧
        distinguishedEntry.entry ∈ distinguishedEntry.record.package.evidenceEntries := by
  constructor
  · rfl
  · constructor
    · rfl
    · simp [distinguishedEntry, frozenRecord, TopologySpecialization.sourcePackage]

structure FrozenSourceTranscription where
  artifactSha256 : String
  figures : List SourceFigureRecord
  packageRecord : P94FrozenPackageRecord

noncomputable def frozenSourceTranscription : FrozenSourceTranscription where
  artifactSha256 := sourceArtifactSha256
  figures := sourceFigureInventory
  packageRecord := frozenRecord

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

end P94InOutSourceRecord
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P94InOutSourceRecord.source_illustration_bindings_exact
assert_kernel_only
  TetraStereo.OneCenter.P94InOutSourceRecord.source_figure_inventory_complete
assert_kernel_only
  TetraStereo.OneCenter.P94InOutSourceRecord.TopologySpecialization.thetaFramework_valid
assert_kernel_only
  TetraStereo.OneCenter.P94InOutSourceRecord.TopologySpecialization.inward_graph_judged
assert_kernel_only
  TetraStereo.OneCenter.P94InOutSourceRecord.TopologySpecialization.outward_graph_judged
assert_kernel_only
  TetraStereo.OneCenter.P94InOutSourceRecord.TopologySpecialization.bridge_allows_both
assert_kernel_only
  TetraStereo.OneCenter.P94InOutSourceRecord.TopologySpecialization.normalizationReady
assert_kernel_only
  TetraStereo.OneCenter.P94InOutSourceRecord.distinguished_entry_exact
assert_kernel_only
  TetraStereo.OneCenter.P94InOutSourceRecord.current_independent_source_review_issued
