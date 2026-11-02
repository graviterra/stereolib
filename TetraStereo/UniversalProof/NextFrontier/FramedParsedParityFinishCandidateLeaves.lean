import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityFinishEqualSupport

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Sixteen staged exact-solver candidate refusals (unexecuted successor). Every temporary R/S sense and case
is evaluated against the maintained parser, normalization, expanded molecule and shared seed D.
The wrapper is proved from separate official-ranking, Rule-6 and circular-carrier
refusal stages; no full candidate, discovery or report is sent to decide. -/
namespace TetraStereo.UniversalProof.FramedParsedParityFinishCandidateLeaves
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.FramedParsedParitySchedulerCenter
open TetraStereo.UniversalProof.FramedParsedParitySchedulerLeaves
open TetraStereo.UniversalProof.FramedParsedParityFinishEqualSupport

/-- Ranking refusal followed by the maintained Rule-6 refusal suffices, regardless of
which atom/annotation/element/frame guard the projected caller encounters first. -/
private theorem projected_none_of_stages (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (maxEvidenceSize fuel center : Nat)
    (rankNone : rankBranchPositionsThroughOfficialContext? result mol state fuel center
      (mol.ligandsWithLonePair center) = none)
    (rule6None : tetrahedralFactThroughRule6? result mol state fuel center = none) :
    tetrahedralFactFromProjectedState? result mol state maxEvidenceSize fuel center = none := by
  unfold tetrahedralFactFromProjectedState?
  cases atom : mol.atomAt? center with
  | none => rfl
  | some spec =>
      dsimp only
      cases parityCase : spec.tetrahedral? with
      | none => rfl
      | some parityValue =>
          dsimp only
          split
          · rfl
          · split
            · rfl
            · rw [rankNone, rule6None]

/-- A missing actual circular carrier refuses geometry even when its preceding rank is opaque. -/
private theorem geometry_none_of_carrier (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : RawDescriptorState) (fuel center : Nat)
    (carrierNone : exactCircularSharedRule3CarrierSense? result mol state fuel center = none) :
    tetrahedralExactCircularGeometryFact? result mol state fuel center = none := by
  unfold tetrahedralExactCircularGeometryFact?
  dsimp only [Bind.bind]
  simp [carrierNone]

/-- Both primitive recomputation branches refuse; the real singleton filterMap is then empty.
The candidate equation is a consequence, rather than a whole-candidate premise or reduction. -/
private theorem candidate_none_of_recomputation (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (maxEvidenceSize fuel center : Nat) (seed : RawDescriptorState)
    (sense : RS) (uppercase : Bool)
    (projectedNone : tetrahedralFactFromProjectedState? result mol
      (exactAuxiliaryAssumedState mol fuel seed [center] [(sense, uppercase)])
      maxEvidenceSize fuel center = none)
    (geometryNone : tetrahedralExactCircularGeometryFact? result mol
      (exactAuxiliaryAssumedState mol fuel seed [center] [(sense, uppercase)])
      fuel center = none) :
    exactAuxiliaryDescriptorCandidate? result mol maxEvidenceSize fuel seed
      [center] [(sense, uppercase)] = none := by
  have recomputed : exactAuxiliaryRecomputedState result mol maxEvidenceSize fuel [center]
      (exactAuxiliaryAssumedState mol fuel seed [center] [(sense, uppercase)]) = [] := by
    simp [exactAuxiliaryRecomputedState, projectedNone, geometryNone]
  unfold exactAuxiliaryDescriptorCandidate?
  dsimp only
  rw [recomputed]
  rfl

theorem candidate_aa_R_true :
    exactAuxiliaryDescriptorCandidate? (actualResult .anticlockwise .anticlockwise .anticlockwise)
      (actualMol .anticlockwise .anticlockwise .anticlockwise) 100 (actualFuel .anticlockwise .anticlockwise .anticlockwise)
      (stateD .anticlockwise .anticlockwise .anticlockwise) [1] [(RS.R, true)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_aa_R_false :
    exactAuxiliaryDescriptorCandidate? (actualResult .anticlockwise .anticlockwise .anticlockwise)
      (actualMol .anticlockwise .anticlockwise .anticlockwise) 100 (actualFuel .anticlockwise .anticlockwise .anticlockwise)
      (stateD .anticlockwise .anticlockwise .anticlockwise) [1] [(RS.R, false)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_aa_S_true :
    exactAuxiliaryDescriptorCandidate? (actualResult .anticlockwise .anticlockwise .anticlockwise)
      (actualMol .anticlockwise .anticlockwise .anticlockwise) 100 (actualFuel .anticlockwise .anticlockwise .anticlockwise)
      (stateD .anticlockwise .anticlockwise .anticlockwise) [1] [(RS.S, true)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_aa_S_false :
    exactAuxiliaryDescriptorCandidate? (actualResult .anticlockwise .anticlockwise .anticlockwise)
      (actualMol .anticlockwise .anticlockwise .anticlockwise) 100 (actualFuel .anticlockwise .anticlockwise .anticlockwise)
      (stateD .anticlockwise .anticlockwise .anticlockwise) [1] [(RS.S, false)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_ac_R_true :
    exactAuxiliaryDescriptorCandidate? (actualResult .anticlockwise .clockwise .clockwise)
      (actualMol .anticlockwise .clockwise .clockwise) 100 (actualFuel .anticlockwise .clockwise .clockwise)
      (stateD .anticlockwise .clockwise .clockwise) [1] [(RS.R, true)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_ac_R_false :
    exactAuxiliaryDescriptorCandidate? (actualResult .anticlockwise .clockwise .clockwise)
      (actualMol .anticlockwise .clockwise .clockwise) 100 (actualFuel .anticlockwise .clockwise .clockwise)
      (stateD .anticlockwise .clockwise .clockwise) [1] [(RS.R, false)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_ac_S_true :
    exactAuxiliaryDescriptorCandidate? (actualResult .anticlockwise .clockwise .clockwise)
      (actualMol .anticlockwise .clockwise .clockwise) 100 (actualFuel .anticlockwise .clockwise .clockwise)
      (stateD .anticlockwise .clockwise .clockwise) [1] [(RS.S, true)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_ac_S_false :
    exactAuxiliaryDescriptorCandidate? (actualResult .anticlockwise .clockwise .clockwise)
      (actualMol .anticlockwise .clockwise .clockwise) 100 (actualFuel .anticlockwise .clockwise .clockwise)
      (stateD .anticlockwise .clockwise .clockwise) [1] [(RS.S, false)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_ca_R_true :
    exactAuxiliaryDescriptorCandidate? (actualResult .clockwise .anticlockwise .anticlockwise)
      (actualMol .clockwise .anticlockwise .anticlockwise) 100 (actualFuel .clockwise .anticlockwise .anticlockwise)
      (stateD .clockwise .anticlockwise .anticlockwise) [1] [(RS.R, true)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_ca_R_false :
    exactAuxiliaryDescriptorCandidate? (actualResult .clockwise .anticlockwise .anticlockwise)
      (actualMol .clockwise .anticlockwise .anticlockwise) 100 (actualFuel .clockwise .anticlockwise .anticlockwise)
      (stateD .clockwise .anticlockwise .anticlockwise) [1] [(RS.R, false)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_ca_S_true :
    exactAuxiliaryDescriptorCandidate? (actualResult .clockwise .anticlockwise .anticlockwise)
      (actualMol .clockwise .anticlockwise .anticlockwise) 100 (actualFuel .clockwise .anticlockwise .anticlockwise)
      (stateD .clockwise .anticlockwise .anticlockwise) [1] [(RS.S, true)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_ca_S_false :
    exactAuxiliaryDescriptorCandidate? (actualResult .clockwise .anticlockwise .anticlockwise)
      (actualMol .clockwise .anticlockwise .anticlockwise) 100 (actualFuel .clockwise .anticlockwise .anticlockwise)
      (stateD .clockwise .anticlockwise .anticlockwise) [1] [(RS.S, false)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_cc_R_true :
    exactAuxiliaryDescriptorCandidate? (actualResult .clockwise .clockwise .clockwise)
      (actualMol .clockwise .clockwise .clockwise) 100 (actualFuel .clockwise .clockwise .clockwise)
      (stateD .clockwise .clockwise .clockwise) [1] [(RS.R, true)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_cc_R_false :
    exactAuxiliaryDescriptorCandidate? (actualResult .clockwise .clockwise .clockwise)
      (actualMol .clockwise .clockwise .clockwise) 100 (actualFuel .clockwise .clockwise .clockwise)
      (stateD .clockwise .clockwise .clockwise) [1] [(RS.R, false)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_cc_S_true :
    exactAuxiliaryDescriptorCandidate? (actualResult .clockwise .clockwise .clockwise)
      (actualMol .clockwise .clockwise .clockwise) 100 (actualFuel .clockwise .clockwise .clockwise)
      (stateD .clockwise .clockwise .clockwise) [1] [(RS.S, true)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem candidate_cc_S_false :
    exactAuxiliaryDescriptorCandidate? (actualResult .clockwise .clockwise .clockwise)
      (actualMol .clockwise .clockwise .clockwise) 100 (actualFuel .clockwise .clockwise .clockwise)
      (stateD .clockwise .clockwise .clockwise) [1] [(RS.S, false)] = none := by
  apply candidate_none_of_recomputation
  · apply projected_none_of_stages
    · -- Primitive strict-ranking refusal; explicitly open only this ranking definition.
      unfold rankBranchPositionsThroughOfficialContext?
      decide +kernel
    · -- Independent actual Rule-6 refusal in the identical provisional environment.
      unfold tetrahedralFactThroughRule6?
      decide +kernel
  · apply geometry_none_of_carrier
    -- No Rule-3 unit exists in this parsed molecule; the carrier gate precedes its search.
    unfold exactCircularSharedRule3CarrierSense? exactCircularSharedRule3CarrierSenseCapFree?
    decide +kernel

theorem equal_candidate_none (center arm : TetrahedralInputParity) (sense : RS)
    (uppercase : Bool) :
    exactAuxiliaryDescriptorCandidate? (actualResult center arm arm) (actualMol center arm arm)
      100 (actualFuel center arm arm) (stateD center arm arm) [1] [(sense, uppercase)] = none := by
  cases center with
  | clockwise =>
      cases arm with
      | clockwise =>
          cases sense with
          | R =>
              cases uppercase with
              | false => exact candidate_cc_R_false
              | true => exact candidate_cc_R_true
          | S =>
              cases uppercase with
              | false => exact candidate_cc_S_false
              | true => exact candidate_cc_S_true
      | anticlockwise =>
          cases sense with
          | R =>
              cases uppercase with
              | false => exact candidate_ca_R_false
              | true => exact candidate_ca_R_true
          | S =>
              cases uppercase with
              | false => exact candidate_ca_S_false
              | true => exact candidate_ca_S_true
  | anticlockwise =>
      cases arm with
      | clockwise =>
          cases sense with
          | R =>
              cases uppercase with
              | false => exact candidate_ac_R_false
              | true => exact candidate_ac_R_true
          | S =>
              cases uppercase with
              | false => exact candidate_ac_S_false
              | true => exact candidate_ac_S_true
      | anticlockwise =>
          cases sense with
          | R =>
              cases uppercase with
              | false => exact candidate_aa_R_false
              | true => exact candidate_aa_R_true
          | S =>
              cases uppercase with
              | false => exact candidate_aa_S_false
              | true => exact candidate_aa_S_true

end TetraStereo.UniversalProof.FramedParsedParityFinishCandidateLeaves
