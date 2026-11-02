import TetraStereo.OneCenter.LocalizedAxialRootPerception
import TetraStereo.OneCenter.P93CyclicConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecule-level perception of fully cyclic cumulative components

P-31.1.3.3 defines a cyclic cumulene as a ring composed entirely of atoms linked by double
bonds.  A local occurrence-tree `ringClosure` is weaker: it can be produced by one double bond in
an otherwise ordinary ring.  This module therefore classifies the complete connected component of
the semantic graph's order-two subgraph.

A finite connected component with at least three vertices and degree exactly two at every vertex
is precisely the simple closed topology required here.  The least atom is retained as the unique
component representative.  This layer performs constitution perception only; it deliberately does
not invent an `E/Z` or `M/P` rule for a topology with no terminal ligand pairs.
-/

namespace CertifiedLocalizedCIPInput

/-- The simple graph containing exactly the physical order-two bonds. -/
def localizedOrderTwoSimpleGraph (input : CertifiedLocalizedCIPInput) :
    SimpleGraph input.Atom where
  Adj left right := input.moleculeGraph.bond left right = 2
  symm := by
    intro left right doubleBond
    simpa [input.moleculeGraph.bond_symm left right] using doubleBond
  loopless := by
    constructor
    intro atom doubleBond
    rw [input.moleculeGraph.bond_self] at doubleBond
    exact Nat.noConfusion doubleBond

@[simp] theorem localizedOrderTwoSimpleGraph_adj
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    input.localizedOrderTwoSimpleGraph.Adj left right ↔
      input.moleculeGraph.bond left right = 2 :=
  Iff.rfl

/-- Exact finite vertex set of the order-two connected component containing `representative`. -/
noncomputable def localizedOrderTwoComponentAtoms
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) :
    Finset input.Atom := by
  classical
  exact Finset.univ.filter fun atom =>
    input.localizedOrderTwoSimpleGraph.Reachable representative atom

@[simp] theorem mem_localizedOrderTwoComponentAtoms_iff
    (input : CertifiedLocalizedCIPInput) (representative atom : input.Atom) :
    atom ∈ input.localizedOrderTwoComponentAtoms representative ↔
      input.localizedOrderTwoSimpleGraph.Reachable representative atom := by
  classical
  simp [localizedOrderTwoComponentAtoms]

@[simp] theorem representative_mem_localizedOrderTwoComponentAtoms
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) :
    representative ∈ input.localizedOrderTwoComponentAtoms representative := by
  rw [input.mem_localizedOrderTwoComponentAtoms_iff]

/-- Independent graph meaning of one canonical fully cyclic cumulative component:

* the complete order-two connected component has at least three atoms;
* every atom in it has exactly two physical order-two neighbors; and
* `representative` is the least atom, making the component carrier unique.
-/
def DeclarativeLocalizedCyclicCumuleneComponentAt
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) : Prop :=
  3 ≤ (input.localizedOrderTwoComponentAtoms representative).card ∧
    (∀ atom, atom ∈ input.localizedOrderTwoComponentAtoms representative →
      (input.localizedOrderTwoNeighbors atom).length = 2) ∧
    ∀ atom, atom ∈ input.localizedOrderTwoComponentAtoms representative →
      representative ≤ atom

/-- Public carrier for one canonical all-double closed component. -/
structure LocalizedCyclicCumuleneComponent
    (input : CertifiedLocalizedCIPInput) where
  representative : input.Atom
  deriving DecidableEq, Repr

/-- Exact independent meaning of the public carrier. -/
def DeclarativeLocalizedCyclicCumuleneComponent
    (input : CertifiedLocalizedCIPInput)
    (component : input.LocalizedCyclicCumuleneComponent) : Prop :=
  input.DeclarativeLocalizedCyclicCumuleneComponentAt component.representative

/-- Decide whether an atom is the canonical representative of a fully cyclic cumulative
component. -/
noncomputable def localizedCyclicCumuleneComponentAt?
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) :
    Option input.LocalizedCyclicCumuleneComponent := by
  classical
  exact if input.DeclarativeLocalizedCyclicCumuleneComponentAt representative then
    some { representative }
  else none

/-- Successful single-atom perception is exactly the independent component predicate. -/
theorem localizedCyclicCumuleneComponentAt?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom)
    (component : input.LocalizedCyclicCumuleneComponent) :
    input.localizedCyclicCumuleneComponentAt? representative = some component ↔
      component.representative = representative ∧
        input.DeclarativeLocalizedCyclicCumuleneComponent component := by
  classical
  unfold localizedCyclicCumuleneComponentAt?
  by_cases derived : input.DeclarativeLocalizedCyclicCumuleneComponentAt representative
  · rw [if_pos derived]
    constructor
    · intro identity
      have componentIdentity : ({ representative } :
          input.LocalizedCyclicCumuleneComponent) = component :=
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
    · intro impossible
      simp at impossible
    · rintro ⟨identity, componentDerived⟩
      apply (derived ?_).elim
      change input.DeclarativeLocalizedCyclicCumuleneComponentAt
        component.representative at componentDerived
      simpa [identity] using componentDerived

/-- All fully cyclic cumulative components, one per order-two connected component. -/
noncomputable def localizedCyclicCumuleneComponents
    (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedCyclicCumuleneComponent := by
  classical
  exact ((Finset.univ : Finset input.Atom).sort (· ≤ ·)).filterMap
    input.localizedCyclicCumuleneComponentAt?

/-- Exact whole-molecule component coverage. -/
theorem mem_localizedCyclicCumuleneComponents_iff
    (input : CertifiedLocalizedCIPInput)
    (component : input.LocalizedCyclicCumuleneComponent) :
    component ∈ input.localizedCyclicCumuleneComponents ↔
      input.DeclarativeLocalizedCyclicCumuleneComponent component := by
  classical
  rw [localizedCyclicCumuleneComponents, List.mem_filterMap]
  constructor
  · rintro ⟨representative, _present, computed⟩
    exact (input.localizedCyclicCumuleneComponentAt?_eq_some_iff
      representative component).mp computed |>.2
  · intro derived
    exact ⟨component.representative, by simp,
      (input.localizedCyclicCumuleneComponentAt?_eq_some_iff
        component.representative component).mpr ⟨rfl, derived⟩⟩

/-- Canonical-minimum selection prevents duplicate component carriers. -/
theorem localizedCyclicCumuleneComponents_nodup
    (input : CertifiedLocalizedCIPInput) :
    input.localizedCyclicCumuleneComponents.Nodup := by
  classical
  unfold localizedCyclicCumuleneComponents
  apply List.Nodup.filterMap
  · intro left right component leftComputed rightComputed
    have leftIdentity := (input.localizedCyclicCumuleneComponentAt?_eq_some_iff
      left component).mp leftComputed |>.1
    have rightIdentity := (input.localizedCyclicCumuleneComponentAt?_eq_some_iff
      right component).mp rightComputed |>.1
    exact leftIdentity.symm.trans rightIdentity
  · exact Finset.sort_nodup _ _

/-- Independent statement that `atom` lies in a classified fully cyclic cumulative component.
This relation deliberately contains both the component certificate and component membership, so
an occurrence-level caller cannot infer fully cyclic topology merely from a local ring duplicate. -/
def DeclarativeLocalizedCyclicCumuleneComponentContains
    (input : CertifiedLocalizedCIPInput)
    (component : input.LocalizedCyclicCumuleneComponent)
    (atom : input.Atom) : Prop :=
  input.DeclarativeLocalizedCyclicCumuleneComponent component ∧
    atom ∈ input.localizedOrderTwoComponentAtoms component.representative

/-- A molecule atom belongs to at most one canonical fully cyclic cumulative component.  The
proof uses connectedness of the complete order-two components plus their least representatives;
it does not depend on enumeration order. -/
theorem declarativeLocalizedCyclicCumuleneComponentContains_unique
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {left right : input.LocalizedCyclicCumuleneComponent}
    (leftContains :
      input.DeclarativeLocalizedCyclicCumuleneComponentContains left atom)
    (rightContains :
      input.DeclarativeLocalizedCyclicCumuleneComponentContains right atom) :
    left = right := by
  have leftToAtom : input.localizedOrderTwoSimpleGraph.Reachable
      left.representative atom :=
    (input.mem_localizedOrderTwoComponentAtoms_iff left.representative atom).mp
      leftContains.2
  have rightToAtom : input.localizedOrderTwoSimpleGraph.Reachable
      right.representative atom :=
    (input.mem_localizedOrderTwoComponentAtoms_iff right.representative atom).mp
      rightContains.2
  have rightInLeft : right.representative ∈
      input.localizedOrderTwoComponentAtoms left.representative :=
    (input.mem_localizedOrderTwoComponentAtoms_iff
      left.representative right.representative).mpr
      (leftToAtom.trans rightToAtom.symm)
  have leftInRight : left.representative ∈
      input.localizedOrderTwoComponentAtoms right.representative :=
    (input.mem_localizedOrderTwoComponentAtoms_iff
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

/-- The unique fully cyclic cumulative component containing `atom`, when one exists.  This is a
proof-oriented exact lookup: constitution perception above is finite, while the returned choice
is characterized independently below and does not rely on a privileged list traversal order. -/
noncomputable def localizedCyclicCumuleneComponentContaining?
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    Option input.LocalizedCyclicCumuleneComponent := by
  classical
  exact if existsContaining : ∃ component,
      input.DeclarativeLocalizedCyclicCumuleneComponentContains component atom then
    some (Classical.choose existsContaining)
  else none

/-- Exact soundness and completeness of component containment lookup. -/
theorem localizedCyclicCumuleneComponentContaining?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    (component : input.LocalizedCyclicCumuleneComponent) :
    input.localizedCyclicCumuleneComponentContaining? atom = some component ↔
      input.DeclarativeLocalizedCyclicCumuleneComponentContains component atom := by
  classical
  unfold localizedCyclicCumuleneComponentContaining?
  by_cases existsContaining : ∃ candidate,
      input.DeclarativeLocalizedCyclicCumuleneComponentContains candidate atom
  · rw [dif_pos existsContaining]
    have chosenContains : input.DeclarativeLocalizedCyclicCumuleneComponentContains
        (Classical.choose existsContaining) atom :=
      Classical.choose_spec existsContaining
    constructor
    · intro computed
      have chosenIdentity : Classical.choose existsContaining = component :=
        Option.some.inj computed
      simpa [chosenIdentity] using chosenContains
    · intro componentContains
      have chosenIdentity : Classical.choose existsContaining = component :=
        input.declarativeLocalizedCyclicCumuleneComponentContains_unique atom
          chosenContains componentContains
      simp [chosenIdentity]
  · rw [dif_neg existsContaining]
    constructor
    · intro impossible
      simp at impossible
    · intro componentContains
      exact (existsContaining ⟨component, componentContains⟩).elim

/-- Lookup returns `none` exactly when the atom lies in no fully cyclic cumulative component. -/
theorem localizedCyclicCumuleneComponentContaining?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    input.localizedCyclicCumuleneComponentContaining? atom = none ↔
      ∀ component, ¬input.DeclarativeLocalizedCyclicCumuleneComponentContains
        component atom := by
  classical
  unfold localizedCyclicCumuleneComponentContaining?
  by_cases existsContaining : ∃ component,
      input.DeclarativeLocalizedCyclicCumuleneComponentContains component atom
  · rw [dif_pos existsContaining]
    simp only [Option.some_ne_none, false_iff]
    simpa using existsContaining
  · rw [dif_neg existsContaining]
    simp only [true_iff]
    simpa using existsContaining

/-- The classifier refines the independent P-31 fully cyclic cumulene topology and is disjoint
from the open terminal-pair cumulene schema used by the existing axial/planar analyzers. -/
theorem DeclarativeLocalizedCyclicCumuleneComponent.authority_topology
    (input : CertifiedLocalizedCIPInput)
    {component : input.LocalizedCyclicCumuleneComponent}
    (_derived : input.DeclarativeLocalizedCyclicCumuleneComponent component) :
    BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
      ¬BlueBookP93.Cyclic.OpenTerminalCumuleneSchemaApplies .fullyCyclicCumulene :=
  ⟨BlueBookP93.Cyclic.fully_cyclic_cumulene_is_P31_parent_topology,
    BlueBookP93.Cyclic.fully_cyclic_cumulene_has_no_open_terminal_schema⟩

/-- No atom of a classified fully cyclic component can be a terminal root of the open-chain
perceiver: degree two and degree one are kept disjoint. -/
theorem DeclarativeLocalizedCyclicCumuleneComponent.no_open_axial_root
    (input : CertifiedLocalizedCIPInput)
    {component : input.LocalizedCyclicCumuleneComponent}
    (derived : input.DeclarativeLocalizedCyclicCumuleneComponent component)
    (atom : input.Atom)
    (member : atom ∈ input.localizedOrderTwoComponentAtoms component.representative) :
    input.localizedAxialRootCandidateAt? atom = none := by
  have twoNeighbors := derived.2.1 atom member
  unfold localizedAxialRootCandidateAt?
  generalize neighborsIdentity : input.localizedOrderTwoNeighbors atom = neighbors
  rw [neighborsIdentity] at twoNeighbors
  cases neighbors with
  | nil => simp at twoNeighbors
  | cons first rest =>
      cases rest with
      | nil => simp at twoNeighbors
      | cons second more =>
          cases more with
          | nil => simp
          | cons third tail => simp at twoNeighbors

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
