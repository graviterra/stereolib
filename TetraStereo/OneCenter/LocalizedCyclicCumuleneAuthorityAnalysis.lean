import TetraStereo.OneCenter.LocalizedCyclicCumulenePerception

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecule-wide authority boundary for fully cyclic cumulenes

P-31.1.3.3 classifies a ring composed entirely of doubly linked atoms as a cyclic cumulene.
P-93.4.2.2, P-93.4.2.3, and their reuse by P-93.5.2.3 assign configuration from two terminal
ligand pairs, which this closed topology does not possess.

This module makes that negative applicability result visible at whole-molecule level.  It does
not strengthen the source into a claim that every possible stereodescriptor is permanently
omitted.  Each result says exactly that the component is a P-31 fully cyclic parent and that no
descriptor from the transcribed P-93 open-terminal cumulene families applies to it.
-/

namespace CertifiedLocalizedCIPInput

/-- One explicitly reported fully cyclic component at the P-31/P-93 configuration boundary. -/
structure LocalizedFullyCyclicCumuleneAuthorityBoundary
    (input : CertifiedLocalizedCIPInput) where
  component : input.LocalizedCyclicCumuleneComponent
  deriving DecidableEq, Repr

/-- Independent meaning of a reported fully cyclic cumulene boundary. -/
def DeclarativeLocalizedFullyCyclicCumuleneAuthorityBoundary
    (input : CertifiedLocalizedCIPInput)
    (boundary : input.LocalizedFullyCyclicCumuleneAuthorityBoundary) : Prop :=
  input.DeclarativeLocalizedCyclicCumuleneComponent boundary.component ∧
    BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
    ∀ parity descriptor,
      ¬BlueBookP93.Cyclic.OpenTerminalCumuleneDescriptorApplies
        .fullyCyclicCumulene parity descriptor

/-- Every independently perceived component has the exact P-31 parent classification and lies
outside both parity branches of the P-93 open-terminal cumulene descriptor schema. -/
theorem declarativeLocalizedFullyCyclicCumuleneAuthorityBoundary_of_component
    (input : CertifiedLocalizedCIPInput)
    (component : input.LocalizedCyclicCumuleneComponent)
    (derived : input.DeclarativeLocalizedCyclicCumuleneComponent component) :
    input.DeclarativeLocalizedFullyCyclicCumuleneAuthorityBoundary { component } := by
  exact ⟨derived,
    BlueBookP93.Cyclic.fully_cyclic_cumulene_is_P31_parent_topology,
    fun parity descriptor =>
      BlueBookP93.Cyclic.fully_cyclic_cumulene_has_no_open_terminal_descriptor
        parity descriptor⟩

/-- Report every perceived fully cyclic cumulene component exactly once.  Unlike a descriptor
analyzer, this list does not silently erase a recognized topology merely because the applicable
terminal-descriptor family is absent. -/
noncomputable def analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries
    (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedFullyCyclicCumuleneAuthorityBoundary :=
  input.localizedCyclicCumuleneComponents.map fun component => { component }

/-- Exact whole-molecule membership: a boundary is reported precisely when its retained component
satisfies the independent all-double closed-component predicate. -/
theorem mem_analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries_iff
    (input : CertifiedLocalizedCIPInput)
    (boundary : input.LocalizedFullyCyclicCumuleneAuthorityBoundary) :
    boundary ∈ input.analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries ↔
      input.DeclarativeLocalizedFullyCyclicCumuleneAuthorityBoundary boundary := by
  classical
  constructor
  · intro present
    rw [analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries, List.mem_map] at present
    rcases present with ⟨component, componentPresent, identity⟩
    subst boundary
    exact input.declarativeLocalizedFullyCyclicCumuleneAuthorityBoundary_of_component
      component
      ((input.mem_localizedCyclicCumuleneComponents_iff component).mp componentPresent)
  · intro derived
    rw [analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries, List.mem_map]
    exact ⟨boundary.component,
      (input.mem_localizedCyclicCumuleneComponents_iff boundary.component).mpr derived.1,
      by cases boundary; rfl⟩

/-- Canonical component representatives make the authority-boundary report duplicate-free. -/
theorem analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries_nodup
    (input : CertifiedLocalizedCIPInput) :
    input.analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries.Nodup := by
  classical
  unfold analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries
  exact List.Nodup.map (by
    intro left right identity
    cases left
    cases right
    simpa using identity) input.localizedCyclicCumuleneComponents_nodup

/-- Every public boundary result has the complete independent molecule-topology and P-93
non-applicability meaning. -/
theorem analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries_member_conforms
    (input : CertifiedLocalizedCIPInput)
    (boundary : input.LocalizedFullyCyclicCumuleneAuthorityBoundary)
    (present : boundary ∈
      input.analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries) :
    input.DeclarativeLocalizedFullyCyclicCumuleneAuthorityBoundary boundary :=
  (input.mem_analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries_iff boundary).mp present

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
