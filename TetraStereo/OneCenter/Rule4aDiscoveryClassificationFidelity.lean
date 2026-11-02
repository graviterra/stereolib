import TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid
import TetraStereo.OneCenter.OfficialBranchPerception
import TetraStereo.OneCenter.OfficialDescriptorEnvironment
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section






















namespace DescriptorDiscoveryState

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : MultiCenterMolecule V} {cfg : m.Configuration}

/-- The shared Rule 4a class projection agrees with official branch perception for every discovery
state and every center.  Both sides choose lowercase pseudoasymmetry before uppercase chirality. -/
theorem rule4aKindAt?_eq_perceivedDescriptorAt?_rule4aKind
    (state : DescriptorDiscoveryState m cfg) (center : m.Center) :
    state.rule4aKindAt? center =
      (state.perceivedDescriptorAt? center).bind PerceivedDescriptor.rule4aKind? := by
  cases hpseudo : state.pseudo center with
  | none =>
      cases hrs : state.rs center with
      | none =>
          simp [rule4aKindAt?, perceivedDescriptorAt?, hpseudo, hrs]
      | some descriptor =>
          simp [rule4aKindAt?, perceivedDescriptorAt?, hpseudo, hrs,
            PerceivedDescriptor.rule4aKind?]
  | some descriptor =>
      simp [rule4aKindAt?, perceivedDescriptorAt?, hpseudo,
        PerceivedDescriptor.rule4aKind?]

/-- The official environment class projection is exactly the perceived class projection.  This is
the general agreement statement between the two public Rule 4a consumers. -/
theorem toOfficialDescriptorEnvironment_rule4aKind_eq_perceived
    (state : DescriptorDiscoveryState m cfg) (center : m.Center) :
    state.toOfficialDescriptorEnvironment.rule4aKind center =
      (state.perceivedDescriptorAt? center).bind PerceivedDescriptor.rule4aKind? := by
  rw [toOfficialDescriptorEnvironment_rule4aKind_eq_rule4aKindAt?,
    rule4aKindAt?_eq_perceivedDescriptorAt?_rule4aKind]

/-- A pseudoasymmetric descriptor fixes the environment class as pseudoasymmetric, for an
arbitrary `R/S` seed.  The explicit unused seed argument records that the conclusion is independent
of `state.rs`. -/
theorem toOfficialDescriptorEnvironment_rule4aKind_eq_pseudoasymmetric_of_pseudo_eq_some_of_rs
    (state : DescriptorDiscoveryState m cfg) {center : m.Center} {descriptor : PseudoRS}
    (h : state.pseudo center = some descriptor) (rsDescriptor : Option RS)
    (_hrs : state.rs center = rsDescriptor) :
    state.toOfficialDescriptorEnvironment.rule4aKind center =
      some OfficialStereogenicUnitKind.pseudoasymmetric :=
  toOfficialDescriptorEnvironment_rule4aKind_eq_some_of_pseudo_eq_some state h

/-- Both consumers map the same perceived descriptor to the same Rule 4a class. -/
theorem toOfficialDescriptorEnvironment_rule4aKind_eq_perceived_descriptor_kind
    (state : DescriptorDiscoveryState m cfg) {center : m.Center} {descriptor : PseudoRS}
    (h : state.pseudo center = some descriptor) :
    state.toOfficialDescriptorEnvironment.rule4aKind center =
      (PerceivedDescriptor.pseudoTetrahedral descriptor).rule4aKind? := by
  rw [toOfficialDescriptorEnvironment_rule4aKind_eq_perceived,
    perceivedDescriptorAt?_eq_some_of_pseudo_eq_some state center descriptor h]
  rfl

end DescriptorDiscoveryState

end

end OneCenter

namespace Examples
namespace PseudoasymmetricTrihydroxyglutaricAcid

open OneCenter

/-! ## The existing molecule-backed fixture -/

/-- On the existing `afterMiddleDiscoveryState`, the official environment classifies the middle
center as pseudoasymmetric.  The state simultaneously retains its middle `R/S` seed, so this is not
a replacement of the uppercase descriptor. -/
theorem afterMiddleDiscoveryEnvironment_rule4aKind_middle :
    afterMiddleDiscoveryState.toOfficialDescriptorEnvironment.rule4aKind middleCenter =
      some OfficialStereogenicUnitKind.pseudoasymmetric :=
  DescriptorDiscoveryState.toOfficialDescriptorEnvironment_rule4aKind_eq_some_of_pseudo_eq_some
    (state := afterMiddleDiscoveryState) (center := middleCenter) (descriptor := PseudoRS.r)
    afterMiddleDiscoveryState_middle_pseudo_eq_some_r

/-- Perception reports the middle center as a lowercase pseudo-tetrahedral descriptor. -/
theorem afterMiddleDiscovery_perceivedDescriptorAt?_middle :
    afterMiddleDiscoveryState.perceivedDescriptorAt? middleCenter =
      some (PerceivedDescriptor.pseudoTetrahedral PseudoRS.r) :=
  DescriptorDiscoveryState.perceivedDescriptorAt?_eq_some_of_pseudo_eq_some
    (state := afterMiddleDiscoveryState) (center := middleCenter) (descriptor := PseudoRS.r)
    afterMiddleDiscoveryState_middle_pseudo_eq_some_r

/-- The perceived descriptor binds to the pseudoasymmetric class. -/
theorem afterMiddleDiscovery_perceived_rule4aKind_middle :
    (afterMiddleDiscoveryState.perceivedDescriptorAt? middleCenter).bind
        PerceivedDescriptor.rule4aKind? =
      some OfficialStereogenicUnitKind.pseudoasymmetric := by
  rw [afterMiddleDiscovery_perceivedDescriptorAt?_middle]
  rfl

/-- The two public consumers agree on the actual fixture. -/
theorem afterMiddleDiscoveryEnvironment_rule4aKind_eq_perceived :
    afterMiddleDiscoveryState.toOfficialDescriptorEnvironment.rule4aKind middleCenter =
      (afterMiddleDiscoveryState.perceivedDescriptorAt? middleCenter).bind
        PerceivedDescriptor.rule4aKind? :=
  DescriptorDiscoveryState.toOfficialDescriptorEnvironment_rule4aKind_eq_perceived
    afterMiddleDiscoveryState middleCenter

/-- Both consumers classify the middle center as pseudoasymmetric on the actual fixture. -/
theorem afterMiddleDiscovery_both_consumers_classify_middle_pseudoasymmetric :
    afterMiddleDiscoveryState.toOfficialDescriptorEnvironment.rule4aKind middleCenter =
        some OfficialStereogenicUnitKind.pseudoasymmetric ∧
      (afterMiddleDiscoveryState.perceivedDescriptorAt? middleCenter).bind
          PerceivedDescriptor.rule4aKind? =
        some OfficialStereogenicUnitKind.pseudoasymmetric :=
  ⟨afterMiddleDiscoveryEnvironment_rule4aKind_middle,
    afterMiddleDiscovery_perceived_rule4aKind_middle⟩

/-- A Rule-5 assignment preserves the whole `R/S` map. -/
theorem afterMiddleDiscoveryState_rs_eq_initial :
    afterMiddleDiscoveryState.rs = initialDescriptorState.rs :=
  DescriptorDiscoveryState.applyRule5Task_rs initialDescriptorState middleRule5DiscoveryTask

/-- The middle `R/S` slot is unchanged by the Rule-5 step. -/
theorem afterMiddleDiscoveryState_rs_middle_eq_initial :
    afterMiddleDiscoveryState.rs middleCenter = initialDescriptorState.rs middleCenter := by
  rw [afterMiddleDiscoveryState_rs_eq_initial]

/-- The seeded middle `R/S` descriptor is the configuration descriptor. -/
theorem initialDescriptorState_rs_middle :
    initialDescriptorState.rs middleCenter = some (multi.configurationRS cfg middleCenter) := by
  simp [initialDescriptorState, DescriptorDiscoveryState.seedConfigurationRS]

/-- The middle center keeps its uppercase `R/S` seed while also carrying lowercase `r`.  These two
slots are independent; the pseudo descriptor does not overwrite the Rule-5 sense. -/
theorem afterMiddleDiscoveryState_rs_middle :
    afterMiddleDiscoveryState.rs middleCenter = some (multi.configurationRS cfg middleCenter) := by
  rw [afterMiddleDiscoveryState_rs_middle_eq_initial, initialDescriptorState_rs_middle]

/-- The official Rule 5 slot at the middle center remains the seeded uppercase descriptor. -/
theorem afterMiddleDiscoveryEnvironment_rule5_middle :
    afterMiddleDiscoveryState.toOfficialDescriptorEnvironment.rule5Descriptor middleCenter =
      some (OfficialRule5Descriptor.ofRS (multi.configurationRS cfg middleCenter)) :=
  DescriptorDiscoveryState.toOfficialDescriptorEnvironment_rule5_of_rs_eq_some
    (state := afterMiddleDiscoveryState) (center := middleCenter)
    (descriptor := multi.configurationRS cfg middleCenter)
    afterMiddleDiscoveryState_rs_middle

/-- The Rule 5 slot is literally the same before and after the middle discovery step. -/
theorem afterMiddleDiscoveryEnvironment_rule5_middle_eq_initial :
    afterMiddleDiscoveryState.toOfficialDescriptorEnvironment.rule5Descriptor middleCenter =
      initialDescriptorState.toOfficialDescriptorEnvironment.rule5Descriptor middleCenter := by
  rw [afterMiddleDiscoveryEnvironment_rule5_middle,
    DescriptorDiscoveryState.toOfficialDescriptorEnvironment_rule5_of_rs_eq_some
      (state := initialDescriptorState) (center := middleCenter)
      (descriptor := multi.configurationRS cfg middleCenter) initialDescriptorState_rs_middle]

/-- The fixture preserves the `R/S` seed and the Rule 5 descriptor separately from the lowercase
Rule 4a classification. -/
theorem afterMiddleDiscovery_rs_and_rule5_preserved :
    afterMiddleDiscoveryState.rs middleCenter = some (multi.configurationRS cfg middleCenter) ∧
      afterMiddleDiscoveryState.toOfficialDescriptorEnvironment.rule5Descriptor middleCenter =
        some (OfficialRule5Descriptor.ofRS (multi.configurationRS cfg middleCenter)) :=
  ⟨afterMiddleDiscoveryState_rs_middle, afterMiddleDiscoveryEnvironment_rule5_middle⟩



/-- The fixture's left source seed is exactly the left field of `middleDiscoveryResult`.  Stating
this through the result's own fields keeps the lemma independent of which literal `R/S` labels the
terminal calibration assigns: the example defines `middleDiscoveryResult` from exactly these two
seeds. -/
theorem initialDescriptorState_rs_left_eq_result :
    initialDescriptorState.rs middleRule5DiscoveryTask.leftSource =
      some middleDiscoveryResult.leftDescriptor := by
  simp [middleDiscoveryResult, middleRule5DiscoveryTask, Rule5DiscoveryTask.resolve]

/-- The fixture's right source seed is exactly the right field of `middleDiscoveryResult`. -/
theorem initialDescriptorState_rs_right_eq_result :
    initialDescriptorState.rs middleRule5DiscoveryTask.rightSource =
      some middleDiscoveryResult.rightDescriptor := by
  simp [middleDiscoveryResult, middleRule5DiscoveryTask, Rule5DiscoveryTask.resolve]

/-- The two source descriptors used by the fixture are genuinely distinct, extracted from the
existing fixture resolution through the guarded resolver's soundness theorem.  This is the
non-degeneracy fact the guard needs; it is not assumed. -/
theorem middleDiscoveryResult_descriptors_ne :
    middleDiscoveryResult.leftDescriptor ≠ middleDiscoveryResult.rightDescriptor :=
  Rule5DiscoveryTask.resolveFromState?_some_leftDescriptor_ne_rightDescriptor
    middleRule5DiscoveryTask initialDescriptorState middleDiscoveryResult
    middleRule5DiscoveryTask_resolveFromInitial

/-- The legacy distinct-source resolution is retained under the guard: the actual initial fixture
resolves to the actual legacy result.  This proof uses the guarded distinct-source lemma rather
than unfolding the resolver. -/
theorem middleRule5DiscoveryTask_resolveFromInitial_fidelity :
    middleRule5DiscoveryTask.resolveFromState? initialDescriptorState =
      some middleDiscoveryResult := by
  have h :=
    Rule5DiscoveryTask.resolveFromState?_eq_some_of_rs_sources_ne
      (task := middleRule5DiscoveryTask) (state := initialDescriptorState)
      (leftDescriptor := middleDiscoveryResult.leftDescriptor)
      (rightDescriptor := middleDiscoveryResult.rightDescriptor)
      initialDescriptorState_rs_left_eq_result initialDescriptorState_rs_right_eq_result
      middleDiscoveryResult_descriptors_ne
  simpa [middleDiscoveryResult, Rule5DiscoveryTask.resolve] using h

/-- The Rule-5 pseudo descriptor computed from the fixture's own source pair is lowercase `r`.
`sound` relates the descriptor to exactly this result's `leftDescriptor`/`rightDescriptor`, so the
statement does not depend on which literal `R/S` labels the terminal calibration assigns.  Under
the current source labels the pair is `R,S`; under the calibrated labels it is `S,R`. -/
theorem pseudoDescriptor_middleDiscoveryResult_eq_r :
    pseudoDescriptor (multi.configurationSign cfg middleCenter)
        middleDiscoveryResult.leftDescriptor middleDiscoveryResult.rightDescriptor =
      PseudoRS.r := by
  have h := middleDiscoveryResult.sound
  rw [middleDiscoveryResult_descriptor_eq_r] at h
  simpa [middleRule5DiscoveryTask] using h.symm





theorem initialDescriptorState_official_resolves :
    middleRule5DiscoveryTask.toOfficialDescriptorTask.resolve?
        initialDescriptorState.toOfficialDescriptorEnvironment =
      some
        (OfficialDescriptorValue.rule4cDescriptor
          (OfficialPseudoasymmetricDescriptor.ofPseudoRS PseudoRS.r)) := by
  have hPseudo :
      pseudoDescriptor 1 middleDiscoveryResult.leftDescriptor
          middleDiscoveryResult.rightDescriptor =
        PseudoRS.r := by
    simpa using pseudoDescriptor_middleDiscoveryResult_eq_r
  have h :=
    Rule5DiscoveryTask.toOfficialDescriptorTask_resolve?_eq_some_of_rs_sources_ne
      (task := middleRule5DiscoveryTask) (state := initialDescriptorState)
      (leftDescriptor := middleDiscoveryResult.leftDescriptor)
      (rightDescriptor := middleDiscoveryResult.rightDescriptor)
      initialDescriptorState_rs_left_eq_result initialDescriptorState_rs_right_eq_result
      middleDiscoveryResult_descriptors_ne
  simpa [middleRule5DiscoveryTask, hPseudo] using h

/-- The state after the middle discovery step still has the fixture's source pair: `applyRule5Task`
writes only the pseudo slot. -/
theorem afterMiddleDiscoveryState_rs_left_eq_result :
    afterMiddleDiscoveryState.rs middleRule5DiscoveryTask.leftSource =
      some middleDiscoveryResult.leftDescriptor := by
  rw [afterMiddleDiscoveryState_rs_eq_initial]
  exact initialDescriptorState_rs_left_eq_result

/-- The state after the middle discovery step still has the fixture's right source. -/
theorem afterMiddleDiscoveryState_rs_right_eq_result :
    afterMiddleDiscoveryState.rs middleRule5DiscoveryTask.rightSource =
      some middleDiscoveryResult.rightDescriptor := by
  rw [afterMiddleDiscoveryState_rs_eq_initial]
  exact initialDescriptorState_rs_right_eq_result

/-- The official adapter also resolves the state after the middle discovery step: the Rule-5 step
writes only the pseudo slot, so the terminal source descriptors are unchanged. -/
theorem afterMiddleDiscoveryState_official_task_resolves :
    middleRule5DiscoveryTask.toOfficialDescriptorTask.resolve?
        afterMiddleDiscoveryState.toOfficialDescriptorEnvironment =
      some
        (OfficialDescriptorValue.rule4cDescriptor
          (OfficialPseudoasymmetricDescriptor.ofPseudoRS PseudoRS.r)) := by
  have hPseudo :
      pseudoDescriptor 1 middleDiscoveryResult.leftDescriptor
          middleDiscoveryResult.rightDescriptor =
        PseudoRS.r := by
    simpa using pseudoDescriptor_middleDiscoveryResult_eq_r
  have h :=
    Rule5DiscoveryTask.toOfficialDescriptorTask_resolve?_eq_some_of_rs_sources_ne
      (task := middleRule5DiscoveryTask) (state := afterMiddleDiscoveryState)
      (leftDescriptor := middleDiscoveryResult.leftDescriptor)
      (rightDescriptor := middleDiscoveryResult.rightDescriptor)
      afterMiddleDiscoveryState_rs_left_eq_result afterMiddleDiscoveryState_rs_right_eq_result
      middleDiscoveryResult_descriptors_ne
  simpa [middleRule5DiscoveryTask, hPseudo] using h



/-- A discovery state on the actual molecule's centers with a chosen terminal `R/S` pair and no
lowercase descriptors.  The middle center is unseeded; only the two Rule-5 sources matter here. -/
def terminalSeedStateWith (leftDescriptor rightDescriptor : RS) :
    DescriptorDiscoveryState multi cfg where
  rs := fun c =>
    match c.1 with
    | Atom.c2 => some leftDescriptor
    | Atom.c4 => some rightDescriptor
    | _ => none
  pseudo := fun _ => none

@[simp] theorem terminalSeedStateWith_rs_left (leftDescriptor rightDescriptor : RS) :
    (terminalSeedStateWith leftDescriptor rightDescriptor).rs leftCenter = some leftDescriptor :=
  rfl

@[simp] theorem terminalSeedStateWith_rs_right (leftDescriptor rightDescriptor : RS) :
    (terminalSeedStateWith leftDescriptor rightDescriptor).rs rightCenter = some rightDescriptor :=
  rfl

@[simp] theorem terminalSeedStateWith_rs_middle (leftDescriptor rightDescriptor : RS) :
    (terminalSeedStateWith leftDescriptor rightDescriptor).rs middleCenter = none :=
  rfl

/-- Distinct available sources resolve exactly as the legacy `resolve` function. -/
theorem terminalSeedStateWith_resolve_of_ne (leftDescriptor rightDescriptor : RS)
    (hne : leftDescriptor ≠ rightDescriptor) :
    middleRule5DiscoveryTask.resolveFromState? (terminalSeedStateWith leftDescriptor rightDescriptor) =
      some (middleRule5DiscoveryTask.resolve leftDescriptor rightDescriptor) := by
  have hleft :
      (terminalSeedStateWith leftDescriptor rightDescriptor).rs
          middleRule5DiscoveryTask.leftSource = some leftDescriptor := by
    simp [middleRule5DiscoveryTask]
  have hright :
      (terminalSeedStateWith leftDescriptor rightDescriptor).rs
          middleRule5DiscoveryTask.rightSource = some rightDescriptor := by
    simp [middleRule5DiscoveryTask]
  exact Rule5DiscoveryTask.resolveFromState?_eq_some_of_rs_sources_ne
    (task := middleRule5DiscoveryTask)
    (state := terminalSeedStateWith leftDescriptor rightDescriptor)
    (leftDescriptor := leftDescriptor) (rightDescriptor := rightDescriptor)
    hleft hright hne

/-- Equal sources are refused by the actual resolver, for either repeated descriptor. -/
theorem terminalSeedStateWith_sameSign_refuses (descriptor : RS) :
    middleRule5DiscoveryTask.resolveFromState? (terminalSeedStateWith descriptor descriptor) = none := by
  have hleft :
      (terminalSeedStateWith descriptor descriptor).rs
          middleRule5DiscoveryTask.leftSource = some descriptor := by
    simp [middleRule5DiscoveryTask]
  have hright :
      (terminalSeedStateWith descriptor descriptor).rs
          middleRule5DiscoveryTask.rightSource = some descriptor := by
    simp [middleRule5DiscoveryTask]
  exact Rule5DiscoveryTask.resolveFromState?_eq_none_of_rs_sources_eq
    (task := middleRule5DiscoveryTask)
    (state := terminalSeedStateWith descriptor descriptor)
    (descriptor := descriptor) hleft hright

/-- `R,R` is refused: it is not an enantiomorphic pair. -/
theorem terminalSeedState_R_R_refuses :
    middleRule5DiscoveryTask.resolveFromState? (terminalSeedStateWith RS.R RS.R) = none :=
  terminalSeedStateWith_sameSign_refuses RS.R

/-- `S,S` is refused: it is not an enantiomorphic pair. -/
theorem terminalSeedState_S_S_refuses :
    middleRule5DiscoveryTask.resolveFromState? (terminalSeedStateWith RS.S RS.S) = none :=
  terminalSeedStateWith_sameSign_refuses RS.S

/-- `R,S` still resolves to the legacy distinct-pair computation. -/
theorem terminalSeedState_R_S_resolves :
    middleRule5DiscoveryTask.resolveFromState? (terminalSeedStateWith RS.R RS.S) =
      some (middleRule5DiscoveryTask.resolve RS.R RS.S) :=
  terminalSeedStateWith_resolve_of_ne RS.R RS.S (by intro h; cases h)

/-- Seeding the fixture's own two source descriptors (whatever their literal calibration) retains
exactly the existing fixture's `middleDiscoveryResult`. -/
theorem terminalSeedState_resolves_to_middleDiscoveryResult :
    middleRule5DiscoveryTask.resolveFromState?
        (terminalSeedStateWith middleDiscoveryResult.leftDescriptor
          middleDiscoveryResult.rightDescriptor) =
      some middleDiscoveryResult := by
  have h :=
    terminalSeedStateWith_resolve_of_ne middleDiscoveryResult.leftDescriptor
      middleDiscoveryResult.rightDescriptor middleDiscoveryResult_descriptors_ne
  simpa [middleDiscoveryResult, Rule5DiscoveryTask.resolve] using h

/-- `S,R` also still resolves; it is a different legacy input, not a degenerate one. -/
theorem terminalSeedState_S_R_resolves :
    middleRule5DiscoveryTask.resolveFromState? (terminalSeedStateWith RS.S RS.R) =
      some (middleRule5DiscoveryTask.resolve RS.S RS.R) :=
  terminalSeedStateWith_resolve_of_ne RS.S RS.R (by intro h; cases h)

/-- The actual official adapter refuses equal `R,R` sources. -/
theorem terminalSeedState_R_R_official_refuses :
    middleRule5DiscoveryTask.toOfficialDescriptorTask.resolve?
        (terminalSeedStateWith RS.R RS.R).toOfficialDescriptorEnvironment = none := by
  have hleft :
      (terminalSeedStateWith RS.R RS.R).rs middleRule5DiscoveryTask.leftSource = some RS.R := by
    simp [middleRule5DiscoveryTask]
  have hright :
      (terminalSeedStateWith RS.R RS.R).rs middleRule5DiscoveryTask.rightSource = some RS.R := by
    simp [middleRule5DiscoveryTask]
  exact Rule5DiscoveryTask.toOfficialDescriptorTask_resolve?_eq_none_of_rs_sources_eq
    (task := middleRule5DiscoveryTask)
    (state := terminalSeedStateWith RS.R RS.R) (descriptor := RS.R) hleft hright

/-- The actual official adapter refuses equal `S,S` sources. -/
theorem terminalSeedState_S_S_official_refuses :
    middleRule5DiscoveryTask.toOfficialDescriptorTask.resolve?
        (terminalSeedStateWith RS.S RS.S).toOfficialDescriptorEnvironment = none := by
  have hleft :
      (terminalSeedStateWith RS.S RS.S).rs middleRule5DiscoveryTask.leftSource = some RS.S := by
    simp [middleRule5DiscoveryTask]
  have hright :
      (terminalSeedStateWith RS.S RS.S).rs middleRule5DiscoveryTask.rightSource = some RS.S := by
    simp [middleRule5DiscoveryTask]
  exact Rule5DiscoveryTask.toOfficialDescriptorTask_resolve?_eq_none_of_rs_sources_eq
    (task := middleRule5DiscoveryTask)
    (state := terminalSeedStateWith RS.S RS.S) (descriptor := RS.S) hleft hright

/-- The actual official adapter still computes on the distinct `R,S` input.  The value is stated
through the same `pseudoDescriptor` expression that the legacy computation produced; its concrete
lowercase letter depends on the library-wide `PseudoRS.ofSign` calibration, which this leaf does
not assume. -/
theorem terminalSeedState_R_S_official_resolves :
    middleRule5DiscoveryTask.toOfficialDescriptorTask.resolve?
        (terminalSeedStateWith RS.R RS.S).toOfficialDescriptorEnvironment =
      some
        (OfficialDescriptorValue.rule4cDescriptor
          (OfficialPseudoasymmetricDescriptor.ofPseudoRS
            (pseudoDescriptor (multi.configurationSign cfg middleCenter) RS.R RS.S))) := by
  have hleft :
      (terminalSeedStateWith RS.R RS.S).rs middleRule5DiscoveryTask.leftSource = some RS.R := by
    simp [middleRule5DiscoveryTask]
  have hright :
      (terminalSeedStateWith RS.R RS.S).rs middleRule5DiscoveryTask.rightSource = some RS.S := by
    simp [middleRule5DiscoveryTask]
  have hne : (RS.R : RS) ≠ RS.S := by
    intro h
    cases h
  have h :=
    Rule5DiscoveryTask.toOfficialDescriptorTask_resolve?_eq_some_of_rs_sources_ne
      (task := middleRule5DiscoveryTask) (state := terminalSeedStateWith RS.R RS.S)
      (leftDescriptor := RS.R) (rightDescriptor := RS.S) hleft hright hne
  simpa [middleRule5DiscoveryTask] using h

/-- The actual official adapter still computes on the distinct `S,R` input.  The value is stated
through the same `pseudoDescriptor` expression that the legacy computation produced; no claim is
made that it is the single chemically correct label for the whole ligand pair. -/
theorem terminalSeedState_S_R_official_resolves :
    middleRule5DiscoveryTask.toOfficialDescriptorTask.resolve?
        (terminalSeedStateWith RS.S RS.R).toOfficialDescriptorEnvironment =
      some
        (OfficialDescriptorValue.rule4cDescriptor
          (OfficialPseudoasymmetricDescriptor.ofPseudoRS
            (pseudoDescriptor (multi.configurationSign cfg middleCenter) RS.S RS.R))) := by
  have hleft :
      (terminalSeedStateWith RS.S RS.R).rs middleRule5DiscoveryTask.leftSource = some RS.S := by
    simp [middleRule5DiscoveryTask]
  have hright :
      (terminalSeedStateWith RS.S RS.R).rs middleRule5DiscoveryTask.rightSource = some RS.R := by
    simp [middleRule5DiscoveryTask]
  have hne : (RS.S : RS) ≠ RS.R := by
    intro h
    cases h
  have h :=
    Rule5DiscoveryTask.toOfficialDescriptorTask_resolve?_eq_some_of_rs_sources_ne
      (task := middleRule5DiscoveryTask) (state := terminalSeedStateWith RS.S RS.R)
      (leftDescriptor := RS.S) (rightDescriptor := RS.R) hleft hright hne
  simpa [middleRule5DiscoveryTask] using h

end PseudoasymmetricTrihydroxyglutaricAcid
end Examples
end TetraStereo

/-! Kernel-authority checks for the complete discovery/environment fidelity surface. -/
assert_kernel_only TetraStereo.OneCenter.DescriptorDiscoveryState.rule4aKindAt?_eq_perceivedDescriptorAt?_rule4aKind
assert_kernel_only TetraStereo.OneCenter.DescriptorDiscoveryState.toOfficialDescriptorEnvironment_rule4aKind_eq_perceived
assert_kernel_only TetraStereo.OneCenter.DescriptorDiscoveryState.toOfficialDescriptorEnvironment_rule4aKind_eq_pseudoasymmetric_of_pseudo_eq_some_of_rs
assert_kernel_only TetraStereo.OneCenter.DescriptorDiscoveryState.toOfficialDescriptorEnvironment_rule4aKind_eq_perceived_descriptor_kind
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscoveryEnvironment_rule4aKind_middle
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscovery_perceivedDescriptorAt?_middle
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscovery_perceived_rule4aKind_middle
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscoveryEnvironment_rule4aKind_eq_perceived
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscovery_both_consumers_classify_middle_pseudoasymmetric
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscoveryState_rs_eq_initial
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscoveryState_rs_middle_eq_initial
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.initialDescriptorState_rs_middle
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscoveryState_rs_middle
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscoveryEnvironment_rule5_middle
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscoveryEnvironment_rule5_middle_eq_initial
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscovery_rs_and_rule5_preserved
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.initialDescriptorState_rs_left_eq_result
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.initialDescriptorState_rs_right_eq_result
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.middleDiscoveryResult_descriptors_ne
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.middleRule5DiscoveryTask_resolveFromInitial_fidelity
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.pseudoDescriptor_middleDiscoveryResult_eq_r
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.initialDescriptorState_official_resolves
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscoveryState_rs_left_eq_result
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscoveryState_rs_right_eq_result
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleDiscoveryState_official_task_resolves
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedStateWith_rs_left
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedStateWith_rs_right
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedStateWith_rs_middle
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedStateWith_resolve_of_ne
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedStateWith_sameSign_refuses
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedState_R_R_refuses
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedState_S_S_refuses
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedState_R_S_resolves
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedState_resolves_to_middleDiscoveryResult
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedState_S_R_resolves
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedState_R_R_official_refuses
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedState_S_S_official_refuses
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedState_R_S_official_resolves
assert_kernel_only TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.terminalSeedState_S_R_official_resolves
