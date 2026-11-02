import TetraStereo.OneCenter.LocalizedCyclicCumuleneOccurrenceBridge
import TetraStereo.OneCenter.LocalizedMonocyclicDoubleBondPerception

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Complete authority routing after an occurrence-level cyclic double-bond closure

This layer joins local occurrence topology to the two molecule-level cyclic classifiers:

* a fully all-double component is the separate P-31 cyclic-cumulene parent topology;
* an ordinary component with exactly one simple cycle is eligible for P-91/P-93 monocycle policy;
* a monocycle outside the currently transcribed ring-size/count policy remains an explicit gap; and
* every other ordinary closure is retained as a nonmonocyclic cyclic topology for its own P-93
  family (spiro, fused, bridged, etc.).

The route is total after a computed local ring closure and never guesses which cyclic rule applies.
-/

namespace CertifiedLocalizedCIPInput

/-- Exhaustive authority-facing outcome for a computed cyclic order-two occurrence. -/
inductive LocalizedRule3CyclicAuthorityRoute
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  | fullyCyclicCumulene
      (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (closure : input.LocalizedRerootCursor carrierFuel)
      (component : input.LocalizedCyclicCumuleneComponent)
  | ordinaryMonocyclicPolicy
      (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (closure : input.LocalizedRerootCursor carrierFuel)
      (result : input.LocalizedMonocyclicDoubleBondPolicyResult)
  | ordinaryMonocyclicPolicyGap
      (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (closure : input.LocalizedRerootCursor carrierFuel)
      (carrier : input.LocalizedMonocyclicDoubleBond)
      (doubleBondCount : Nat)
  | ordinaryNonmonocyclic
      (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (closure : input.LocalizedRerootCursor carrierFuel)

/-- Refine every local cyclic closure through complete molecule topology and independent P-93
policy selection. -/
noncomputable def localizedRule3CyclicAuthorityRoute?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3CyclicAuthorityRoute carrierFuel) := do
  let moleculeRoute ← input.localizedRule3RingClosureMoleculeRoute? occurrence
  match moleculeRoute with
  | .fullyCyclicCumulene initial closure component =>
      some (.fullyCyclicCumulene initial closure component)
  | .ordinaryCyclicDoubleBondSystem initial closure =>
      match input.localizedMonocyclicDoubleBondAt? initial.left initial.right with
      | none => some (.ordinaryNonmonocyclic initial closure)
      | some carrier =>
          let doubleBondCount := input.localizedDoubleBondCountIn carrier.ring
          match BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy
              carrier.ring.card doubleBondCount with
          | none =>
              some (.ordinaryMonocyclicPolicyGap
                initial closure carrier doubleBondCount)
          | some policy =>
              some (.ordinaryMonocyclicPolicy initial closure
                { carrier, doubleBondCount, policy })

/-- Independent exact meaning of every cyclic authority route. -/
inductive DeclarativeLocalizedRule3CyclicAuthorityRoute
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.LocalizedRule3CyclicAuthorityRoute carrierFuel → Prop
  | fullyCyclicCumulene {initial closure component}
      (moleculeRoute :
        input.DeclarativeLocalizedRule3RingClosureMoleculeRoute occurrence
          (.fullyCyclicCumulene initial closure component)) :
      input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
        (.fullyCyclicCumulene initial closure component)
  | ordinaryMonocyclicPolicy {initial closure result}
      (moleculeRoute :
        input.DeclarativeLocalizedRule3RingClosureMoleculeRoute occurrence
          (.ordinaryCyclicDoubleBondSystem initial closure))
      (policy : input.DeclarativeLocalizedMonocyclicDoubleBondPolicyResult
        initial.left initial.right result) :
      input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
        (.ordinaryMonocyclicPolicy initial closure result)
  | ordinaryMonocyclicPolicyGap {initial closure carrier doubleBondCount}
      (moleculeRoute :
        input.DeclarativeLocalizedRule3RingClosureMoleculeRoute occurrence
          (.ordinaryCyclicDoubleBondSystem initial closure))
      (monocycle : input.DeclarativeLocalizedMonocyclicDoubleBond
        initial.left initial.right carrier)
      (count : doubleBondCount = input.localizedDoubleBondCountIn carrier.ring)
      (outsidePolicy : BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy
        carrier.ring.card doubleBondCount = none) :
      input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
        (.ordinaryMonocyclicPolicyGap initial closure carrier doubleBondCount)
  | ordinaryNonmonocyclic {initial closure}
      (moleculeRoute :
        input.DeclarativeLocalizedRule3RingClosureMoleculeRoute occurrence
          (.ordinaryCyclicDoubleBondSystem initial closure))
      (notMonocyclic : ∀ carrier,
        ¬input.DeclarativeLocalizedMonocyclicDoubleBond
          initial.left initial.right carrier) :
      input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
        (.ordinaryNonmonocyclic initial closure)

/-- Every returned authority route has the complete molecule-level topology and policy meaning. -/
theorem localizedRule3CyclicAuthorityRoute?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (route : input.LocalizedRule3CyclicAuthorityRoute carrierFuel)
    (computed : input.localizedRule3CyclicAuthorityRoute? occurrence = some route) :
    input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence route := by
  unfold localizedRule3CyclicAuthorityRoute? at computed
  cases moleculeComputed :
      input.localizedRule3RingClosureMoleculeRoute? occurrence with
  | none => simp [moleculeComputed] at computed
  | some moleculeRoute =>
      have moleculeDerived := input.localizedRule3RingClosureMoleculeRoute?_sound
        occurrence moleculeRoute moleculeComputed
      cases moleculeRoute with
      | fullyCyclicCumulene initial closure component =>
          simp [moleculeComputed] at computed
          subst route
          exact DeclarativeLocalizedRule3CyclicAuthorityRoute.fullyCyclicCumulene
            moleculeDerived
      | ordinaryCyclicDoubleBondSystem initial closure =>
          cases monocycleComputed :
              input.localizedMonocyclicDoubleBondAt? initial.left initial.right with
          | none =>
              simp [moleculeComputed, monocycleComputed] at computed
              subst route
              exact DeclarativeLocalizedRule3CyclicAuthorityRoute.ordinaryNonmonocyclic
                moleculeDerived
                ((input.localizedMonocyclicDoubleBondAt?_eq_none_iff
                  initial.left initial.right).mp monocycleComputed)
          | some carrier =>
              have monocycleDerived :=
                (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
                  initial.left initial.right carrier).mp monocycleComputed
              cases policyComputed : BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy
                  carrier.ring.card
                    (input.localizedDoubleBondCountIn carrier.ring) with
              | none =>
                  simp [moleculeComputed, monocycleComputed, policyComputed] at computed
                  subst route
                  exact DeclarativeLocalizedRule3CyclicAuthorityRoute.ordinaryMonocyclicPolicyGap
                    moleculeDerived monocycleDerived rfl
                      policyComputed
              | some policy =>
                  simp [moleculeComputed, monocycleComputed, policyComputed] at computed
                  subst route
                  exact DeclarativeLocalizedRule3CyclicAuthorityRoute.ordinaryMonocyclicPolicy
                    moleculeDerived
                      ⟨monocycleDerived, rfl, policyComputed⟩

/-- Authority routing adds no failure after occurrence topology has produced a ring closure. -/
theorem exists_localizedRule3CyclicAuthorityRoute_of_ringClosure
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.ringClosure initial closure)) :
    ∃ route, input.localizedRule3CyclicAuthorityRoute? occurrence = some route := by
  obtain ⟨moleculeRoute, moleculeComputed⟩ :=
    input.exists_localizedRule3RingClosureMoleculeRoute_of_ringClosure
      occurrence initial closure entryComputed
  cases moleculeRoute with
  | fullyCyclicCumulene routeInitial routeClosure component =>
      exact ⟨.fullyCyclicCumulene routeInitial routeClosure component,
        by simp [localizedRule3CyclicAuthorityRoute?, moleculeComputed]⟩
  | ordinaryCyclicDoubleBondSystem routeInitial routeClosure =>
      cases monocycleComputed : input.localizedMonocyclicDoubleBondAt?
          routeInitial.left routeInitial.right with
      | none =>
          exact ⟨.ordinaryNonmonocyclic routeInitial routeClosure,
            by simp [localizedRule3CyclicAuthorityRoute?, moleculeComputed,
              monocycleComputed]⟩
      | some carrier =>
          cases policyComputed : BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy
              carrier.ring.card (input.localizedDoubleBondCountIn carrier.ring) with
          | none =>
              exact ⟨.ordinaryMonocyclicPolicyGap routeInitial routeClosure carrier
                  (input.localizedDoubleBondCountIn carrier.ring),
                by simp [localizedRule3CyclicAuthorityRoute?, moleculeComputed,
                  monocycleComputed, policyComputed]⟩
          | some policy =>
              exact ⟨.ordinaryMonocyclicPolicy routeInitial routeClosure
                  { carrier
                    doubleBondCount := input.localizedDoubleBondCountIn carrier.ring
                    policy },
                by simp [localizedRule3CyclicAuthorityRoute?, moleculeComputed,
                  monocycleComputed, policyComputed]⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
