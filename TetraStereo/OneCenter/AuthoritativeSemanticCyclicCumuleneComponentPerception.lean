import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondTopologyPartition
import TetraStereo.OneCenter.P93CyclicConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Source-canonical perception of fully cyclic cumulative components

P-31.1.3.3 treats a ring composed entirely of doubly linked atoms as a parent-hydride topology,
not as an open terminal-pair cumulene.  The predicate here classifies the complete connected
component of the aromatic-safe ordinary-double-bond graph.  Requiring at least three atoms and
degree exactly two at every component vertex is an orientation-free finite graph definition of a
simple closed all-double component.
-/

/-- The simple graph containing precisely aromatic-safe source ordinary double bonds. -/
def aromaticCanonicalOrdinaryDoubleSimpleGraph
    (source : AuthoritativeChemicalInput) : SimpleGraph source.AromaticCanonicalAtom where
  Adj := source.AromaticCanonicalOrdinaryDoubleBond
  symm := by
    intro left right ordinary
    have valuesDifferent : left.val ≠ right.val := by
      intro equal
      exact ordinary.1.1 (Fin.ext equal)
    have reverseValuesDifferent : right.val ≠ left.val := valuesDifferent.symm
    exact ⟨⟨ordinary.1.1.symm, by
        simpa [semanticEdgeKey_comm] using ordinary.1.2⟩, by
      simpa [SemanticMolecule.aromaticCanonicalBondOrder,
        SemanticMolecule.localizedBondOrder, semanticEdgeKey_comm,
        valuesDifferent, reverseValuesDifferent] using ordinary.2⟩
  loopless := by
    constructor
    intro atom ordinary
    exact ordinary.1.1 rfl

@[simp] theorem aromaticCanonicalOrdinaryDoubleSimpleGraph_adj
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) :
    source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Adj left right ↔
      source.AromaticCanonicalOrdinaryDoubleBond left right :=
  Iff.rfl

/-- Exact finite vertex set of the source ordinary-double component at `representative`. -/
noncomputable def aromaticCanonicalOrdinaryDoubleComponentAtoms
    (source : AuthoritativeChemicalInput)
    (representative : source.AromaticCanonicalAtom) :
    Finset source.AromaticCanonicalAtom := by
  classical
  exact Finset.univ.filter fun atom =>
    source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Reachable representative atom

@[simp] theorem mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff
    (source : AuthoritativeChemicalInput)
    (representative atom : source.AromaticCanonicalAtom) :
    atom ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms representative ↔
      source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Reachable representative atom := by
  classical
  simp [aromaticCanonicalOrdinaryDoubleComponentAtoms]

@[simp] theorem representative_mem_aromaticCanonicalOrdinaryDoubleComponentAtoms
    (source : AuthoritativeChemicalInput)
    (representative : source.AromaticCanonicalAtom) :
    representative ∈
      source.aromaticCanonicalOrdinaryDoubleComponentAtoms representative := by
  rw [source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff]

/-- Independent P-31 source topology: a complete ordinary-double component with at least three
vertices, degree two everywhere, and the least vertex chosen as canonical representative. -/
def DeclarativeAromaticCanonicalCyclicCumuleneComponentAt
    (source : AuthoritativeChemicalInput)
    (representative : source.AromaticCanonicalAtom) : Prop :=
  3 ≤ (source.aromaticCanonicalOrdinaryDoubleComponentAtoms representative).card ∧
    (∀ atom,
      atom ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms representative →
        (source.aromaticCanonicalOrdinaryDoubleNeighbors atom).length = 2) ∧
    ∀ atom,
      atom ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms representative →
        representative ≤ atom

/-- Public carrier for one source-canonical fully cyclic cumulative component. -/
structure AromaticCanonicalCyclicCumuleneComponent
    (source : AuthoritativeChemicalInput) where
  representative : source.AromaticCanonicalAtom
  deriving DecidableEq, Repr

/-- Exact independent meaning of the public source carrier. -/
def DeclarativeAromaticCanonicalCyclicCumuleneComponent
    (source : AuthoritativeChemicalInput)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) : Prop :=
  source.DeclarativeAromaticCanonicalCyclicCumuleneComponentAt
    component.representative

/-- Decide whether one atom is the canonical representative of a fully cyclic component. -/
noncomputable def aromaticCanonicalCyclicCumuleneComponentAt?
    (source : AuthoritativeChemicalInput)
    (representative : source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalCyclicCumuleneComponent := by
  classical
  exact if source.DeclarativeAromaticCanonicalCyclicCumuleneComponentAt representative then
    some { representative }
  else none

/-- Per-atom source perception is exactly the independent component predicate. -/
theorem aromaticCanonicalCyclicCumuleneComponentAt?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (representative : source.AromaticCanonicalAtom)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) :
    source.aromaticCanonicalCyclicCumuleneComponentAt? representative = some component ↔
      component.representative = representative ∧
        source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component := by
  classical
  unfold aromaticCanonicalCyclicCumuleneComponentAt?
  by_cases derived :
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponentAt representative
  · rw [if_pos derived]
    constructor
    · intro identity
      have componentIdentity : ({ representative } :
          source.AromaticCanonicalCyclicCumuleneComponent) = component :=
        Option.some.inj identity
      subst component
      exact ⟨rfl, derived⟩
    · rintro ⟨identity, _componentDerived⟩
      cases component with
      | mk componentRepresentative =>
          simp only at identity
          subst componentRepresentative
          rfl
  · rw [if_neg derived]
    constructor
    · simp
    · rintro ⟨identity, componentDerived⟩
      apply (derived ?_).elim
      change source.DeclarativeAromaticCanonicalCyclicCumuleneComponentAt
        component.representative at componentDerived
      simpa [identity] using componentDerived

/-- All fully cyclic cumulative source components, once each. -/
noncomputable def aromaticCanonicalCyclicCumuleneComponents
    (source : AuthoritativeChemicalInput) :
    List source.AromaticCanonicalCyclicCumuleneComponent := by
  classical
  exact source.aromaticCanonicalAtomUniverse.filterMap
    source.aromaticCanonicalCyclicCumuleneComponentAt?

/-- Exact whole-source component coverage. -/
theorem mem_aromaticCanonicalCyclicCumuleneComponents_iff
    (source : AuthoritativeChemicalInput)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) :
    component ∈ source.aromaticCanonicalCyclicCumuleneComponents ↔
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component := by
  classical
  rw [aromaticCanonicalCyclicCumuleneComponents, List.mem_filterMap]
  constructor
  · rintro ⟨representative, _present, computed⟩
    exact (source.aromaticCanonicalCyclicCumuleneComponentAt?_eq_some_iff
      representative component).mp computed |>.2
  · intro derived
    exact ⟨component.representative,
      source.mem_aromaticCanonicalAtomUniverse component.representative,
      (source.aromaticCanonicalCyclicCumuleneComponentAt?_eq_some_iff
        component.representative component).mpr ⟨rfl, derived⟩⟩

/-- Least-representative selection prevents duplicate source component carriers. -/
theorem aromaticCanonicalCyclicCumuleneComponents_nodup
    (source : AuthoritativeChemicalInput) :
    source.aromaticCanonicalCyclicCumuleneComponents.Nodup := by
  classical
  unfold aromaticCanonicalCyclicCumuleneComponents
  apply List.Nodup.filterMap
  · intro left right component leftComputed rightComputed
    have leftIdentity :=
      (source.aromaticCanonicalCyclicCumuleneComponentAt?_eq_some_iff
        left component).mp leftComputed |>.1
    have rightIdentity :=
      (source.aromaticCanonicalCyclicCumuleneComponentAt?_eq_some_iff
        right component).mp rightComputed |>.1
    exact leftIdentity.symm.trans rightIdentity
  · exact source.aromaticCanonicalAtomUniverse_nodup

/-- Independent statement that an atom belongs to one classified source component. -/
def DeclarativeAromaticCanonicalCyclicCumuleneComponentContains
    (source : AuthoritativeChemicalInput)
    (component : source.AromaticCanonicalCyclicCumuleneComponent)
    (atom : source.AromaticCanonicalAtom) : Prop :=
  source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component ∧
    atom ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms
      component.representative

/-- An atom belongs to at most one canonical fully cyclic source component. -/
theorem declarativeAromaticCanonicalCyclicCumuleneComponentContains_unique
    (source : AuthoritativeChemicalInput) (atom : source.AromaticCanonicalAtom)
    {left right : source.AromaticCanonicalCyclicCumuleneComponent}
    (leftContains :
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponentContains left atom)
    (rightContains :
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponentContains right atom) :
    left = right := by
  have leftToAtom :=
    (source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff
      left.representative atom).mp leftContains.2
  have rightToAtom :=
    (source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff
      right.representative atom).mp rightContains.2
  have rightInLeft : right.representative ∈
      source.aromaticCanonicalOrdinaryDoubleComponentAtoms left.representative :=
    (source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff
      left.representative right.representative).mpr
      (leftToAtom.trans rightToAtom.symm)
  have leftInRight : left.representative ∈
      source.aromaticCanonicalOrdinaryDoubleComponentAtoms right.representative :=
    (source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff
      right.representative left.representative).mpr
      (rightToAtom.trans leftToAtom.symm)
  have leftLeRight : left.representative ≤ right.representative :=
    leftContains.1.2.2 right.representative rightInLeft
  have rightLeLeft : right.representative ≤ left.representative :=
    rightContains.1.2.2 left.representative leftInRight
  have representativesEqual : left.representative = right.representative :=
    le_antisymm leftLeRight rightLeLeft
  cases left
  cases right
  simp only at representativesEqual
  subst representativesEqual
  rfl

/-- Every classified source component is exactly the P-31 fully cyclic parent topology and is
outside the open-terminal descriptor schema. -/
theorem DeclarativeAromaticCanonicalCyclicCumuleneComponent.authority_topology
    (source : AuthoritativeChemicalInput)
    {component : source.AromaticCanonicalCyclicCumuleneComponent}
    (_derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component) :
    BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
      ¬BlueBookP93.Cyclic.OpenTerminalCumuleneSchemaApplies .fullyCyclicCumulene :=
  ⟨BlueBookP93.Cyclic.fully_cyclic_cumulene_is_P31_parent_topology,
    BlueBookP93.Cyclic.fully_cyclic_cumulene_has_no_open_terminal_schema⟩

/-- Consequently no descriptor from either P-93 open-terminal cumulene parity branch applies to
a classified fully cyclic source component. -/
theorem DeclarativeAromaticCanonicalCyclicCumuleneComponent.no_open_terminal_descriptor
    (source : AuthoritativeChemicalInput)
    {component : source.AromaticCanonicalCyclicCumuleneComponent}
    (_derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component)
    (parity : BlueBookP93.Cyclic.OpenCumuleneParity)
    (descriptor : BlueBookP93.Acyclic.Descriptor) :
    ¬BlueBookP93.Cyclic.OpenTerminalCumuleneDescriptorApplies
      .fullyCyclicCumulene parity descriptor :=
  BlueBookP93.Cyclic.fully_cyclic_cumulene_has_no_open_terminal_descriptor
    parity descriptor

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
