import TetraStereo.OneCenter.LocalizedCyclicCumulenePerception
import TetraStereo.OneCenter.LocalizedRule3CumulatedChain

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# From a local ring closure to molecule-level cyclic-cumulene topology

An occurrence-tree `ringClosure` proves that one physical order-two edge returns to an atom
already on that branch.  It does not prove that every edge of the molecular ring is a double
bond.  This module makes the missing whole-molecule test explicit: the left endpoint is looked up
in the exact connected-component classifier for the physical order-two graph.

The result is constitution topology only.  A fully cyclic cumulene is deliberately not passed to
the open terminal-pair descriptor analyzers.
-/

namespace CertifiedLocalizedCIPInput

/-- Molecule-level route for an occurrence classified locally as a ring-closing order-two edge. -/
inductive LocalizedRule3RingClosureMoleculeRoute
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  | ordinaryCyclicDoubleBondSystem
      (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (closure : input.LocalizedRerootCursor carrierFuel)
  | fullyCyclicCumulene
      (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (closure : input.LocalizedRerootCursor carrierFuel)
      (component : input.LocalizedCyclicCumuleneComponent)

/-- Refine a local ring-closure result using the complete physical order-two component. -/
noncomputable def localizedRule3RingClosureMoleculeRoute?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3RingClosureMoleculeRoute carrierFuel) := do
  let entry ← input.localizedRule3CumulatedAxisEntry? occurrence
  match entry with
  | .ringClosure initial closure =>
      match input.localizedCyclicCumuleneComponentContaining? initial.left with
      | none => some (.ordinaryCyclicDoubleBondSystem initial closure)
      | some component => some (.fullyCyclicCumulene initial closure component)
  | .terminalStart _ | .internal _ _ | .branched _ _ _ _ => none

/-- Independent exact meaning of the occurrence-to-molecule cyclic route. -/
inductive DeclarativeLocalizedRule3RingClosureMoleculeRoute
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.LocalizedRule3RingClosureMoleculeRoute carrierFuel → Prop
  | ordinaryCyclicDoubleBondSystem {initial closure}
      (entry : input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
        (.ringClosure initial closure))
      (notFullyCyclic : ∀ component,
        ¬input.DeclarativeLocalizedCyclicCumuleneComponentContains
          component initial.left) :
      input.DeclarativeLocalizedRule3RingClosureMoleculeRoute occurrence
        (.ordinaryCyclicDoubleBondSystem initial closure)
  | fullyCyclicCumulene {initial closure component}
      (entry : input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
        (.ringClosure initial closure))
      (fullyCyclic : input.DeclarativeLocalizedCyclicCumuleneComponentContains
        component initial.left) :
      input.DeclarativeLocalizedRule3RingClosureMoleculeRoute occurrence
        (.fullyCyclicCumulene initial closure component)

/-- Every emitted route is justified by both the exact occurrence topology and the exact
whole-molecule component classification. -/
theorem localizedRule3RingClosureMoleculeRoute?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (route : input.LocalizedRule3RingClosureMoleculeRoute carrierFuel)
    (computed : input.localizedRule3RingClosureMoleculeRoute? occurrence = some route) :
    input.DeclarativeLocalizedRule3RingClosureMoleculeRoute occurrence route := by
  unfold localizedRule3RingClosureMoleculeRoute? at computed
  cases entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence with
  | none => simp [entryComputed] at computed
  | some entry =>
      cases entry with
      | terminalStart initial => simp [entryComputed] at computed
      | internal initial previous => simp [entryComputed] at computed
      | branched initial first second rest => simp [entryComputed] at computed
      | ringClosure initial closure =>
          have entryDerived := input.localizedRule3CumulatedAxisEntry?_sound occurrence
            (.ringClosure initial closure) entryComputed
          cases componentComputed :
              input.localizedCyclicCumuleneComponentContaining? initial.left with
          | none =>
              simp [entryComputed, componentComputed] at computed
              subst route
              exact DeclarativeLocalizedRule3RingClosureMoleculeRoute.ordinaryCyclicDoubleBondSystem
                entryDerived
                  ((input.localizedCyclicCumuleneComponentContaining?_eq_none_iff
                    initial.left).mp componentComputed)
          | some component =>
              simp [entryComputed, componentComputed] at computed
              subst route
              exact DeclarativeLocalizedRule3RingClosureMoleculeRoute.fullyCyclicCumulene
                entryDerived
                  ((input.localizedCyclicCumuleneComponentContaining?_eq_some_iff
                    initial.left component).mp componentComputed)

/-- A computed local ring closure whose endpoint lies in a fully cyclic component is routed to
that exact component. -/
theorem localizedRule3RingClosureMoleculeRoute?_eq_fullyCyclic_of_contains
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (component : input.LocalizedCyclicCumuleneComponent)
    (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.ringClosure initial closure))
    (contains : input.DeclarativeLocalizedCyclicCumuleneComponentContains
      component initial.left) :
    input.localizedRule3RingClosureMoleculeRoute? occurrence =
      some (.fullyCyclicCumulene initial closure component) := by
  have componentComputed :
      input.localizedCyclicCumuleneComponentContaining? initial.left = some component :=
    (input.localizedCyclicCumuleneComponentContaining?_eq_some_iff
      initial.left component).mpr contains
  simp [localizedRule3RingClosureMoleculeRoute?, entryComputed, componentComputed]

/-- A computed local ring closure whose endpoint lies in no fully cyclic component is routed to
the ordinary cyclic-double-bond-system case. -/
theorem localizedRule3RingClosureMoleculeRoute?_eq_ordinary_of_not_contains
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.ringClosure initial closure))
    (notFullyCyclic : ∀ component,
      ¬input.DeclarativeLocalizedCyclicCumuleneComponentContains
        component initial.left) :
    input.localizedRule3RingClosureMoleculeRoute? occurrence =
      some (.ordinaryCyclicDoubleBondSystem initial closure) := by
  have componentComputed :
      input.localizedCyclicCumuleneComponentContaining? initial.left = none :=
    (input.localizedCyclicCumuleneComponentContaining?_eq_none_iff
      initial.left).mpr notFullyCyclic
  simp [localizedRule3RingClosureMoleculeRoute?, entryComputed, componentComputed]

/-- Whole-molecule refinement is total after the local occurrence classifier has produced a ring
closure.  Thus cyclic perception adds no new failure state; it only selects one of the two exact
molecule-level topologies. -/
theorem exists_localizedRule3RingClosureMoleculeRoute_of_ringClosure
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.ringClosure initial closure)) :
    ∃ route, input.localizedRule3RingClosureMoleculeRoute? occurrence = some route := by
  cases componentComputed :
      input.localizedCyclicCumuleneComponentContaining? initial.left with
  | none =>
      exact ⟨.ordinaryCyclicDoubleBondSystem initial closure,
        by simp [localizedRule3RingClosureMoleculeRoute?, entryComputed, componentComputed]⟩
  | some component =>
      exact ⟨.fullyCyclicCumulene initial closure component,
        by simp [localizedRule3RingClosureMoleculeRoute?, entryComputed, componentComputed]⟩

/-- A fully cyclic result refines the P-31 parent topology and is disjoint from the open
terminal-pair cumulene descriptor schema. -/
theorem DeclarativeLocalizedRule3RingClosureMoleculeRoute.fullyCyclic_authority
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {initial closure component}
    (derived : input.DeclarativeLocalizedRule3RingClosureMoleculeRoute occurrence
      (.fullyCyclicCumulene initial closure component)) :
    BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
      ¬BlueBookP93.Cyclic.OpenTerminalCumuleneSchemaApplies .fullyCyclicCumulene := by
  cases derived with
  | fullyCyclicCumulene _entry fullyCyclic =>
      exact fullyCyclic.1.authority_topology

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
