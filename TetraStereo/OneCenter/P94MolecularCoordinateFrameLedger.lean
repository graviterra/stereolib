import TetraStereo.OneCenter.P94MolecularAuditedTwistOutcomeAuditTrace

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularCoordinateFrameLedger

open CoordinateTwistInOut
open P94MolecularRingCycleScheduler
open P94MolecularRequestScheduler
open P94CarbohydrateFiveRingTwist
open P94MolecularHybridRingSelection
open P94MolecularHybridOutcomeLedger
open P94MolecularDirectRotationEvidence
open P94MolecularDirectRotationAuditLedger
open P94MolecularAuditedHybridTransaction
open P94MolecularAuditedTwistOutcomeAuditTrace

















def emptySpatialConfiguration : SpatialConfiguration :=
  { positions := [] }

structure MolecularCoordinateFrameLedger where
  unit : P94ConformationUnit
  frames : List SpatialConfiguration
  assertions : List (MolecularDirectRotationAssertion Nat)

def MolecularCoordinateFrameLedger.toDirectRotationLedger
    (input : MolecularCoordinateFrameLedger) : MolecularDirectRotationLedger Nat :=
  { unit := input.unit
    states := List.range input.frames.length
    spatialAt := fun state => input.frames.getD state emptySpatialConfiguration
    assertions := input.assertions }

theorem coordinateFrameLedger_states_eq (input : MolecularCoordinateFrameLedger) :
    input.toDirectRotationLedger.states = List.range input.frames.length :=
  rfl

theorem mem_coordinateFrameLedger_states_iff
    (input : MolecularCoordinateFrameLedger) (state : Nat) :
    state ∈ input.toDirectRotationLedger.states ↔ state < input.frames.length := by
  simp [MolecularCoordinateFrameLedger.toDirectRotationLedger]

theorem coordinateFrameLedger_states_nodup (input : MolecularCoordinateFrameLedger) :
    input.toDirectRotationLedger.states.Nodup := by
  exact List.nodup_range

theorem coordinateFrameLedger_states_length (input : MolecularCoordinateFrameLedger) :
    input.toDirectRotationLedger.states.length = input.frames.length := by
  simp [MolecularCoordinateFrameLedger.toDirectRotationLedger]

theorem coordinateFrameLedger_spatialAt_eq
    (input : MolecularCoordinateFrameLedger) (state : Nat) :
    input.toDirectRotationLedger.spatialAt state =
      input.frames.getD state emptySpatialConfiguration :=
  rfl

theorem coordinateFrameLedger_assertions_eq (input : MolecularCoordinateFrameLedger) :
    input.toDirectRotationLedger.assertions = input.assertions :=
  rfl

def MolecularCoordinateFrameLedger.CoordinateFramesCompleteFor
    (input : MolecularCoordinateFrameLedger) (molecule : RawMolecule) : Prop :=
  ∀ state < input.frames.length,
    (input.frames.getD state emptySpatialConfiguration).positions.length = molecule.atomCount

theorem coordinateFramesCompleteFor_iff_all_states_complete
    (input : MolecularCoordinateFrameLedger) (molecule : RawMolecule) :
    input.CoordinateFramesCompleteFor molecule ↔
      ∀ state ∈ input.toDirectRotationLedger.states,
        (input.toDirectRotationLedger.spatialAt state).positions.length = molecule.atomCount := by
  simp [MolecularCoordinateFrameLedger.CoordinateFramesCompleteFor,
    MolecularCoordinateFrameLedger.toDirectRotationLedger]

theorem coordinateFrameAssertion_validFor_iff
    (input : MolecularCoordinateFrameLedger) (molecule : RawMolecule)
    (assertion : MolecularDirectRotationAssertion Nat) :
    assertion.ValidFor molecule input.toDirectRotationLedger ↔
      input.unit.kind = .sixMemberedRing ∧
        input.unit.ValidFor molecule ∧
        assertion.first < input.frames.length ∧
        assertion.second < input.frames.length ∧
        assertion.first ≠ assertion.second ∧
        input.frames.getD assertion.first emptySpatialConfiguration ≠
          input.frames.getD assertion.second emptySpatialConfiguration ∧
        assertion.bond ∈ molecule.bonds ∧
        P94ConformationUnit.SaturatedSingleBondKind assertion.bond.kind ∧
        IsNamedCycleEdge input.unit.atoms assertion.bond.source assertion.bond.target ∧
        (input.frames.getD assertion.first
          emptySpatialConfiguration).positions.length = molecule.atomCount ∧
        (input.frames.getD assertion.second
          emptySpatialConfiguration).positions.length = molecule.atomCount := by
  simp [MolecularDirectRotationAssertion.ValidFor,
    MolecularCoordinateFrameLedger.toDirectRotationLedger]

theorem coordinateFrameRotationOutcomes_map_request
    (input : MolecularCoordinateFrameLedger) (molecule : RawMolecule) :
    (molecularDirectRotationOutcomes molecule input.toDirectRotationLedger).map
        MolecularDirectRotationOutcome.request = input.assertions := by
  simpa [MolecularCoordinateFrameLedger.toDirectRotationLedger] using
    molecularDirectRotationOutcomes_map_request molecule input.toDirectRotationLedger

theorem coordinateFrameRotationOutcomes_all_correct
    (input : MolecularCoordinateFrameLedger) (molecule : RawMolecule) :
    ∀ outcome ∈ molecularDirectRotationOutcomes molecule input.toDirectRotationLedger,
      outcome.Correct molecule input.toDirectRotationLedger :=
  molecularDirectRotationOutcomes_all_correct molecule input.toDirectRotationLedger

/-! ## Composition with the final audited hybrid transaction -/

structure MolecularCoordinateFrameHybridPlan where
  spatial : SpatialConfiguration
  twistLedgers : List MolecularCoordinateFrameLedger
  atomSpatialStates : List SpatialConfiguration
  lonePairStates : List
    P94MolecularLonePairInOutObservationScheduler.LonePairGeometryState

def MolecularCoordinateFrameHybridPlan.toAuditedHybridLedgerPlan
    (plan : MolecularCoordinateFrameHybridPlan) : MolecularAuditedHybridLedgerPlan Nat :=
  { spatial := plan.spatial
    twistLedgers := plan.twistLedgers.map
      MolecularCoordinateFrameLedger.toDirectRotationLedger
    atomSpatialStates := plan.atomSpatialStates
    lonePairStates := plan.lonePairStates }

theorem coordinateFrameHybridPlan_twistLedgers_eq
    (plan : MolecularCoordinateFrameHybridPlan) :
    plan.toAuditedHybridLedgerPlan.twistLedgers =
      plan.twistLedgers.map MolecularCoordinateFrameLedger.toDirectRotationLedger :=
  rfl

noncomputable def scheduledCoordinateFrameTwistInputs
    (molecule : RawMolecule) (plan : MolecularCoordinateFrameHybridPlan) :
    List (CoordinateTwistInput Nat) :=
  scheduledAuditedMolecularTwistInputs molecule plan.toAuditedHybridLedgerPlan

theorem mem_scheduledCoordinateFrameTwistInputs_iff
    (molecule : RawMolecule) (plan : MolecularCoordinateFrameHybridPlan)
    (twistInput : CoordinateTwistInput Nat) :
    twistInput ∈ scheduledCoordinateFrameTwistInputs molecule plan ↔
      ∃ frameLedger ∈ plan.twistLedgers,
        twistInput ∈ scheduledCoordinateTwistInputs
          (auditedCoordinateTwistLedger molecule frameLedger.toDirectRotationLedger) := by
  rw [scheduledCoordinateFrameTwistInputs,
    mem_scheduledAuditedMolecularTwistInputs_iff]
  constructor
  · rintro ⟨ledger, ledgerPresent, inputPresent⟩
    rcases List.mem_map.mp ledgerPresent with ⟨frameLedger, frameLedgerPresent, rfl⟩
    exact ⟨frameLedger, frameLedgerPresent, inputPresent⟩
  · rintro ⟨frameLedger, frameLedgerPresent, inputPresent⟩
    exact ⟨frameLedger.toDirectRotationLedger,
      List.mem_map.mpr ⟨frameLedger, frameLedgerPresent, rfl⟩,
      inputPresent⟩

theorem coordinateFrameHybridTwistAccepted_paths_audited
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (input : CoordinateTwistInput Nat) (output : CoordinateTwistEvidence Nat)
    (outcomePresent : (.twistAccepted input output : HybridMolecularOutcome Nat) ∈
      auditedHybridMolecularOutcomes premises certified plan.toAuditedHybridLedgerPlan external
        carbohydrateAuthority) :
    ∃ frameLedger ∈ plan.twistLedgers,
      DirectedRotationPath
          (AcceptedMolecularDirectRotation certified.result.parsed
            frameLedger.toDirectRotationLedger)
          input.firstLeg ∧
        DirectedRotationPath
          (AcceptedMolecularDirectRotation certified.result.parsed
            frameLedger.toDirectRotationLedger)
          input.secondLeg := by
  rcases auditedHybridTwistAccepted_paths_audited premises certified
      plan.toAuditedHybridLedgerPlan external carbohydrateAuthority input output outcomePresent with
    ⟨ledger, ledgerPresent, firstPath, secondPath⟩
  rcases List.mem_map.mp ledgerPresent with ⟨frameLedger, frameLedgerPresent, ledgerEq⟩
  subst ledger
  exact ⟨frameLedger, frameLedgerPresent, firstPath, secondPath⟩

end BlueBookP94.P94MolecularCoordinateFrameLedger
end TetraStereo.OneCenter
