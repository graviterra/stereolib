import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Lemmas
import TetraStereo.OneCenter.DeclarativeCIPConstitutional

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

universe u

/-!
# Independent exact Rule-1a observations

This module defines the positive-rational atomic-number observations required by revised CIP
Rule 1a.  It imports no production hierarchy, parser, comparison, or mancude search code.

For a localized mancude component, the observation is the mean atomic number of the partner of the
attached atom over *all* maximum matchings.  The definition is finite but declarative: it has no
enumeration order, fuel, or implementation edge cap.  A localized edge is a non-bridge single or
double edge between constitutionally eligible vertices.  Eligibility includes negatively charged
unmatched vertices, which is why `MoleculeGraph.formalCharge` is semantic rather than parser-only
data.
-/

/-- A nonnegative rational represented with a structurally positive denominator.

The representation is intentionally not reduced: Rule 1a compares rational values, so `1/2` and
`2/4` are observationally tied without requiring a normalization algorithm. -/
structure ExactAtomicNumber where
  numerator : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator
  deriving DecidableEq, Repr

namespace ExactAtomicNumber

@[ext] theorem ext {first second : ExactAtomicNumber}
    (hnumerator : first.numerator = second.numerator)
    (hdenominator : first.denominator = second.denominator) :
    first = second := by
  cases first
  cases second
  simp_all

def ofNat (value : ℕ) : ExactAtomicNumber :=
  ⟨value, 1, Nat.zero_lt_one⟩

def zero : ExactAtomicNumber := ofNat 0

def value (label : ExactAtomicNumber) : ℚ :=
  label.numerator / label.denominator

/-- Larger exact atomic numbers have higher Rule-1a priority. -/
def WeakPriority (left right : ExactAtomicNumber) : Prop :=
  right.value ≤ left.value

theorem weakPriority_refl (label : ExactAtomicNumber) : label.WeakPriority label :=
  by
    show label.value ≤ label.value
    exact le_rfl

theorem weakPriority_trans {first second third : ExactAtomicNumber}
    (hfirst : first.WeakPriority second) (hsecond : second.WeakPriority third) :
    first.WeakPriority third := by
  show third.value ≤ first.value
  exact hsecond.trans hfirst

theorem weakPriority_total (left right : ExactAtomicNumber) :
    left.WeakPriority right ∨ right.WeakPriority left :=
  by
    exact le_total right.value left.value

/-- Exact Rule-1a comparator graph. -/
def Outcome (left right : ExactAtomicNumber) (outcome : Ordering) : Prop :=
  compare left.value right.value = outcome

namespace Outcome

theorem functional {left right : ExactAtomicNumber} {first second : Ordering}
    (hfirst : Outcome left right first) (hsecond : Outcome left right second) :
    first = second :=
  hfirst.symm.trans hsecond

theorem total (left right : ExactAtomicNumber) : ∃ outcome, Outcome left right outcome :=
  ⟨compare left.value right.value, rfl⟩

end Outcome
end ExactAtomicNumber

end
end DeclarativeCIP

namespace MoleculeGraph

noncomputable section

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Number of written double bonds incident to an atom. -/
def incidentDoubleBondCount (molecule : MoleculeGraph Atom) (atom : Atom) : ℕ :=
  ((Finset.univ : Finset Atom).filter fun other => molecule.bond atom other = 2).card

/-- Vertices admitted to the localized mancude graph.

A matched vertex has exactly one incident written double bond.  A negatively charged vertex with
none is the unmatched electron-pair position in an odd mancude system. -/
def LocalizedMancudeVertex (molecule : MoleculeGraph Atom) (atom : Atom) : Prop :=
  molecule.incidentDoubleBondCount atom = 1 ∨
    (molecule.incidentDoubleBondCount atom = 0 ∧ molecule.formalCharge atom < 0)

/-- Single or double constitution edge between eligible mancude vertices, before bridges are
removed. -/
def MancudeCandidateEdge (molecule : MoleculeGraph Atom) (left right : Atom) : Prop :=
  (molecule.bond left right = 1 ∨ molecule.bond left right = 2) ∧
    molecule.LocalizedMancudeVertex left ∧ molecule.LocalizedMancudeVertex right

theorem mancudeCandidateEdge_symm (molecule : MoleculeGraph Atom) {left right : Atom} :
    molecule.MancudeCandidateEdge left right ↔ molecule.MancudeCandidateEdge right left := by
  simp only [MancudeCandidateEdge, molecule.bond_symm left right, and_congr_right_iff]
  tauto

/-- Candidate reachability while omitting one undirected edge. -/
def MancudeStepWithout (molecule : MoleculeGraph Atom) (blockedLeft blockedRight : Atom)
    (left right : Atom) : Prop :=
  molecule.MancudeCandidateEdge left right ∧
    ¬ ((left = blockedLeft ∧ right = blockedRight) ∨
       (left = blockedRight ∧ right = blockedLeft))

/-- Localized mancude edges are precisely candidate edges lying on a cycle, equivalently the
non-bridges of the candidate conjugated graph. -/
def LocalizedMancudeEdge (molecule : MoleculeGraph Atom) (left right : Atom) : Prop :=
  molecule.MancudeCandidateEdge left right ∧
    Relation.ReflTransGen (molecule.MancudeStepWithout left right) left right

/-- Membership in the localized component containing `attached`. -/
def InMancudeComponent (molecule : MoleculeGraph Atom) (attached atom : Atom) : Prop :=
  Relation.ReflTransGen molecule.LocalizedMancudeEdge attached atom

/-- A partner assignment represents an undirected matching of the localized component containing
`attached`.  Atoms outside that component are explicitly unmatched. -/
def IsMancudeMatching (molecule : MoleculeGraph Atom) (attached : Atom)
    (partner : Atom → Option Atom) : Prop :=
  (∀ atom, ¬ molecule.InMancudeComponent attached atom → partner atom = none) ∧
    ∀ left right, partner left = some right ↔
      partner right = some left ∧ molecule.LocalizedMancudeEdge left right

/-- Number of vertices saturated by a partner assignment.  Maximizing this is equivalent to
maximizing matching cardinality and avoids division by two. -/
def mancudeSaturation (partner : Atom → Option Atom) : ℕ :=
  ((Finset.univ : Finset Atom).filter fun atom => (partner atom).isSome).card

/-- A matching is maximum when no matching of the same localized component saturates more
vertices. -/
def IsMaximumMancudeMatching (molecule : MoleculeGraph Atom) (attached : Atom)
    (partner : Atom → Option Atom) : Prop :=
  molecule.IsMancudeMatching attached partner ∧
    ∀ other, molecule.IsMancudeMatching attached other →
      mancudeSaturation other ≤ mancudeSaturation partner

/-- Finite family of every maximum matching. -/
def maximumMancudeMatchings (molecule : MoleculeGraph Atom) (attached : Atom) :
    Finset (Atom → Option Atom) := by
  classical
  exact Finset.univ.filter (molecule.IsMaximumMancudeMatching attached)

private theorem empty_isMancudeMatching (molecule : MoleculeGraph Atom) (attached : Atom) :
    molecule.IsMancudeMatching attached (fun _ => none) := by
  constructor
  · simp
  · intro left right
    simp

private def mancudeMatchings (molecule : MoleculeGraph Atom) (attached : Atom) :
    Finset (Atom → Option Atom) := by
  classical
  exact Finset.univ.filter (molecule.IsMancudeMatching attached)

private theorem mancudeMatchings_nonempty (molecule : MoleculeGraph Atom) (attached : Atom) :
    (molecule.mancudeMatchings attached).Nonempty := by
  classical
  refine ⟨fun _ => none, ?_⟩
  simp [mancudeMatchings, molecule.empty_isMancudeMatching attached]

theorem maximumMancudeMatchings_nonempty (molecule : MoleculeGraph Atom) (attached : Atom) :
    (molecule.maximumMancudeMatchings attached).Nonempty := by
  classical
  let candidates := molecule.mancudeMatchings attached
  have hcandidates : candidates.Nonempty := molecule.mancudeMatchings_nonempty attached
  let saturations := candidates.image mancudeSaturation
  have hsaturations : saturations.Nonempty := hcandidates.image _
  let greatest := saturations.max' hsaturations
  have hgreatest : greatest ∈ saturations := saturations.max'_mem hsaturations
  rcases Finset.mem_image.1 hgreatest with ⟨partner, hpartner, hvalue⟩
  refine ⟨partner, ?_⟩
  simp only [maximumMancudeMatchings, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(Finset.mem_filter.1 hpartner).2, ?_⟩
  intro other hother
  have hotherMem : other ∈ candidates := by
    simp [candidates, mancudeMatchings, hother]
  have hotherSaturation : mancudeSaturation other ∈ saturations :=
    Finset.mem_image.2 ⟨other, hotherMem, rfl⟩
  have hle := saturations.le_max' (mancudeSaturation other) hotherSaturation
  simpa [greatest, hvalue] using hle

/-- Atomic-number contribution of the partner of `attached` in one matching.  An unmatched
attached atom contributes zero. -/
def mancudePartnerAtomicNumber (molecule : MoleculeGraph Atom) (attached : Atom)
    (partner : Atom → Option Atom) : ℕ :=
  match partner attached with
  | some atom => molecule.atomZ atom
  | none => 0

/-- Independent exact Rule-1a mean over all maximum matchings. -/
def exactMancudeAverage (molecule : MoleculeGraph Atom) (attached : Atom) :
    DeclarativeCIP.ExactAtomicNumber where
  numerator := (molecule.maximumMancudeMatchings attached).sum
    (molecule.mancudePartnerAtomicNumber attached)
  denominator := (molecule.maximumMancudeMatchings attached).card
  denominator_pos := Finset.card_pos.mpr (molecule.maximumMancudeMatchings_nonempty attached)

/-- Independent Rule-1a mancude averages depend only on atomic numbers and the localized mancude
edge relation. Written bond placement and every other graph field are observationally irrelevant
once those two semantic inputs agree. -/
theorem exactMancudeAverage_eq_of_atomZ_eq_of_localizedMancudeEdge_iff
    (leftGraph rightGraph : MoleculeGraph Atom)
    (atomZ : ∀ atom, leftGraph.atomZ atom = rightGraph.atomZ atom)
    (localized : ∀ left right,
      leftGraph.LocalizedMancudeEdge left right ↔
        rightGraph.LocalizedMancudeEdge left right)
    (attached : Atom) :
    leftGraph.exactMancudeAverage attached = rightGraph.exactMancudeAverage attached := by
  classical
  have component : ∀ atom,
      leftGraph.InMancudeComponent attached atom ↔
        rightGraph.InMancudeComponent attached atom := by
    intro atom
    constructor
    · intro path
      exact path.mono fun left right edge => (localized left right).mp edge
    · intro path
      exact path.mono fun left right edge => (localized left right).mpr edge
  have matching : ∀ partner,
      leftGraph.IsMancudeMatching attached partner ↔
        rightGraph.IsMancudeMatching attached partner := by
    intro partner
    constructor
    · rintro ⟨outside, paired⟩
      constructor
      · intro atom notComponent
        apply outside atom
        intro leftComponent
        exact notComponent ((component atom).mp leftComponent)
      · intro left right
        rw [paired left right]
        exact and_congr_right fun _ => localized left right
    · rintro ⟨outside, paired⟩
      constructor
      · intro atom notComponent
        apply outside atom
        intro rightComponent
        exact notComponent ((component atom).mpr rightComponent)
      · intro left right
        rw [paired left right]
        exact and_congr_right fun _ => (localized left right).symm
  have maximum : ∀ partner,
      leftGraph.IsMaximumMancudeMatching attached partner ↔
        rightGraph.IsMaximumMancudeMatching attached partner := by
    intro partner
    constructor
    · rintro ⟨partnerMatching, greatest⟩
      refine ⟨(matching partner).mp partnerMatching, ?_⟩
      intro other otherMatching
      exact greatest other ((matching other).mpr otherMatching)
    · rintro ⟨partnerMatching, greatest⟩
      refine ⟨(matching partner).mpr partnerMatching, ?_⟩
      intro other otherMatching
      exact greatest other ((matching other).mp otherMatching)
  have maximumFamily :
      leftGraph.maximumMancudeMatchings attached =
        rightGraph.maximumMancudeMatchings attached := by
    ext partner
    simp only [maximumMancudeMatchings, Finset.mem_filter, Finset.mem_univ, true_and]
    exact maximum partner
  apply DeclarativeCIP.ExactAtomicNumber.ext
  · change (leftGraph.maximumMancudeMatchings attached).sum
        (leftGraph.mancudePartnerAtomicNumber attached) =
      (rightGraph.maximumMancudeMatchings attached).sum
        (rightGraph.mancudePartnerAtomicNumber attached)
    rw [maximumFamily]
    apply Finset.sum_congr rfl
    intro partner _partnerPresent
    unfold mancudePartnerAtomicNumber
    cases observed : partner attached with
    | none => rfl
    | some atom => exact atomZ atom
  · change (leftGraph.maximumMancudeMatchings attached).card =
      (rightGraph.maximumMancudeMatchings attached).card
    exact congrArg Finset.card maximumFamily

/-- Total exact observation for a multiple-bond duplicate.  Nonlocalized written multiple bonds
retain the duplicated atom's integral atomic number. -/
def exactRule1aMultipleBond (molecule : MoleculeGraph Atom) (attached duplicated : Atom) :
    DeclarativeCIP.ExactAtomicNumber := by
  classical
  exact if molecule.LocalizedMancudeEdge attached duplicated then
    molecule.exactMancudeAverage attached
  else .ofNat (molecule.atomZ duplicated)

theorem exactRule1aMultipleBond_of_localized (molecule : MoleculeGraph Atom)
    {attached duplicated : Atom} (h : molecule.LocalizedMancudeEdge attached duplicated) :
    molecule.exactRule1aMultipleBond attached duplicated =
      molecule.exactMancudeAverage attached := by
  classical
  simp [exactRule1aMultipleBond, h]

theorem exactRule1aMultipleBond_of_not_localized (molecule : MoleculeGraph Atom)
    {attached duplicated : Atom} (h : ¬ molecule.LocalizedMancudeEdge attached duplicated) :
    molecule.exactRule1aMultipleBond attached duplicated =
      DeclarativeCIP.ExactAtomicNumber.ofNat (molecule.atomZ duplicated) := by
  classical
  simp [exactRule1aMultipleBond, h]

/-- Number of vertices covered by the written noncumulative double bonds in the component. -/
def writtenMancudeSaturation (molecule : MoleculeGraph Atom) (attached : Atom) : ℕ :=
  by
    classical
    exact ((Finset.univ : Finset Atom).filter fun atom =>
      molecule.InMancudeComponent attached atom ∧
        ∃ other, molecule.LocalizedMancudeEdge atom other ∧
          molecule.bond atom other = 2).card

/-- The written Kekule form is maximum for this component.  This is the declarative counterpart of
production's check that maximum-matching size equals the written-double-bond count. -/
def MancudeMaximumSupported (molecule : MoleculeGraph Atom) (attached : Atom) : Prop :=
  ∀ partner, molecule.IsMaximumMancudeMatching attached partner →
    mancudeSaturation partner = molecule.writtenMancudeSaturation attached

end
end MoleculeGraph

namespace DeclarativeCIP

noncomputable section

universe u

namespace RootedDigraph.Addressing

variable {Atom : Type u}

/-- Unique parent selected from the parent-preserving addressing.  The root has no parent. -/
def parent? {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    (node : graph.Node) : Option graph.Node := by
  classical
  exact if hroot : node = graph.root then none
    else some (Classical.choose (addressing.existsUnique_parent node hroot))

@[simp] theorem parent?_root {graph : RootedDigraph Atom} (addressing : graph.Addressing) :
    addressing.parent? graph.root = none := by
  classical
  simp [parent?]

theorem parent?_eq_some_iff {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    (node parent : graph.Node) :
    addressing.parent? node = some parent ↔ graph.child parent node := by
  classical
  by_cases hroot : node = graph.root
  · subst node
    simp [parent?, addressing.not_child_root]
  · let uniqueParent := addressing.existsUnique_parent node hroot
    have hchosen : graph.child (Classical.choose uniqueParent) node :=
      (Classical.choose_spec uniqueParent).1
    constructor
    · intro h
      simp [parent?, hroot] at h
      subst parent
      exact hchosen
    · intro hparent
      have heq : parent = Classical.choose uniqueParent :=
        addressing.parent_unique hparent hchosen
      simp [parent?, hroot, heq]

theorem transport_parent? {left right : RootedDigraph Atom}
    (addressing : left.Addressing) (iso : RootedDigraph.Iso left right)
    (node : left.Node) :
    (addressing.transport iso).parent? (iso.toEquiv node) =
      (addressing.parent? node).map iso.toEquiv := by
  classical
  cases hsource : addressing.parent? node with
  | none =>
      simp only [Option.map_none]
      cases htarget : (addressing.transport iso).parent? (iso.toEquiv node) with
      | none => rfl
      | some target =>
          have hchildRight : right.child target (iso.toEquiv node) :=
            ((addressing.transport iso).parent?_eq_some_iff _ _).1 htarget
          have hchildLeft : left.child (iso.toEquiv.symm target) node := by
            apply (iso.map_child (iso.toEquiv.symm target) node).2
            simpa using hchildRight
          have hparentSome : addressing.parent? node = some (iso.toEquiv.symm target) :=
            (addressing.parent?_eq_some_iff _ _).2 hchildLeft
          rw [hsource] at hparentSome
          simp at hparentSome
  | some source =>
      have hchildLeft : left.child source node :=
        (addressing.parent?_eq_some_iff _ _).1 hsource
      have hchildRight : right.child (iso.toEquiv source) (iso.toEquiv node) :=
        (iso.map_child source node).1 hchildLeft
      have htarget : (addressing.transport iso).parent? (iso.toEquiv node) =
          some (iso.toEquiv source) :=
        ((addressing.transport iso).parent?_eq_some_iff _ _).2 hchildRight
      simpa [hsource] using htarget

end RootedDigraph.Addressing

/-- Exact Rule-1a observation of one represented hierarchy node.

Ordinary real and duplicate nodes carry the represented atom's integral atomic number.  A
multiple-bond duplicate carries the independent maximum-matching average exactly when its
parent--duplicate edge belongs to the localized mancude graph.  Malformed atomless or parentless
nodes are totalized at zero or the duplicated atom's integral number; faithful expansions exclude
those cases, so this totalization adds no chemical license. -/
def exactRule1aNodeObservation {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) (node : graph.Node) : ExactAtomicNumber := by
  classical
  exact match (graph.label node).atom? with
    | none => .zero
    | some atom =>
        match (graph.label node).provenance with
        | .multipleBondDuplicate _ =>
            match (addressing.parent? node).bind fun parent => (graph.label parent).atom? with
            | none => .ofNat (molecule.atomZ atom)
            | some attached => molecule.exactRule1aMultipleBond attached atom
        | _ => .ofNat (molecule.atomZ atom)

@[simp] theorem exactRule1aNodeObservation_atomless
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) (node : graph.Node)
    (hatomless : (graph.label node).atom? = none) :
    exactRule1aNodeObservation molecule graph addressing node = .zero := by
  classical
  simp [exactRule1aNodeObservation, hatomless]

theorem exactRule1aNodeObservation_nonmultiple
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) (node : graph.Node) (atom : Atom)
    (hatom : (graph.label node).atom? = some atom)
    (hprovenance : ∀ distance,
      (graph.label node).provenance ≠ NodeProvenance.multipleBondDuplicate distance) :
    exactRule1aNodeObservation molecule graph addressing node =
      .ofNat (molecule.atomZ atom) := by
  classical
  unfold exactRule1aNodeObservation
  rw [hatom]
  cases h : (graph.label node).provenance <;> simp_all

theorem exactRule1aNodeObservation_multiple_of_parent
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) (parent node : graph.Node)
    (duplicated attached : Atom) (distance : ℕ)
    (hchild : graph.child parent node)
    (hnode : graph.label node =
      ⟨some duplicated, NodeProvenance.multipleBondDuplicate distance⟩)
    (hparent : (graph.label parent).atom? = some attached) :
    exactRule1aNodeObservation molecule graph addressing node =
      molecule.exactRule1aMultipleBond attached duplicated := by
  classical
  have hparentNode : addressing.parent? node = some parent :=
    (addressing.parent?_eq_some_iff node parent).2 hchild
  simp [exactRule1aNodeObservation, hnode, hparentNode, hparent]

/-- Exact node observations are invariant under every rooted-digraph representation isomorphism.
The molecule and atom carrier stay fixed; only the finite hierarchy-node representation changes. -/
theorem exactRule1aNodeObservation_transport
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) {left right : RootedDigraph Atom}
    (addressing : left.Addressing) (iso : RootedDigraph.Iso left right)
    (node : left.Node) :
    exactRule1aNodeObservation molecule left addressing node =
      exactRule1aNodeObservation molecule right (addressing.transport iso)
        (iso.toEquiv node) := by
  classical
  have hnodeLabel := iso.map_label node
  have hparent := addressing.transport_parent? iso node
  unfold exactRule1aNodeObservation
  rw [← hnodeLabel, hparent]
  cases hsource : addressing.parent? node with
  | none => simp
  | some source =>
      have hsourceLabel := iso.map_label source
      simp [hsourceLabel]

/-- Exact Rule-1a observation at a semantic address, including zero at an unoccupied sparse
position. -/
def ExactRule1aObservationAt
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) (position : List ℕ)
    (observation : ExactAtomicNumber) : Prop :=
  (∃ node, addressing.address node = position ∧
      observation = exactRule1aNodeObservation molecule graph addressing node) ∨
    (observation = .zero ∧ ∀ node, addressing.address node ≠ position)

theorem exactRule1aObservationAt_total
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) (position : List ℕ) :
    ∃ observation, ExactRule1aObservationAt molecule graph addressing position observation := by
  classical
  by_cases h : ∃ node, addressing.address node = position
  · obtain ⟨node, hnode⟩ := h
    exact ⟨_, Or.inl ⟨node, hnode, rfl⟩⟩
  · exact ⟨.zero, Or.inr ⟨rfl, by simpa only [not_exists] using h⟩⟩

theorem exactRule1aObservationAt_functional
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) (position : List ℕ)
    {first second : ExactAtomicNumber}
    (hfirst : ExactRule1aObservationAt molecule graph addressing position first)
    (hsecond : ExactRule1aObservationAt molecule graph addressing position second) :
    first = second := by
  rcases hfirst with ⟨firstNode, hfirstPosition, rfl⟩ | ⟨rfl, hfirstMissing⟩
  · rcases hsecond with ⟨secondNode, hsecondPosition, rfl⟩ | ⟨_, hsecondMissing⟩
    · have hnode : firstNode = secondNode :=
        addressing.address_injective (hfirstPosition.trans hsecondPosition.symm)
      subst secondNode
      rfl
    · exact (hsecondMissing firstNode hfirstPosition).elim
  · rcases hsecond with ⟨secondNode, hsecondPosition, _⟩ | ⟨rfl, _⟩
    · exact (hfirstMissing secondNode hsecondPosition).elim
    · rfl

theorem exactRule1aObservationAt_transport_iff
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) {left right : RootedDigraph Atom}
    (addressing : left.Addressing) (iso : RootedDigraph.Iso left right)
    (position : List ℕ) (observation : ExactAtomicNumber) :
    ExactRule1aObservationAt molecule left addressing position observation ↔
      ExactRule1aObservationAt molecule right (addressing.transport iso)
        position observation := by
  constructor
  · intro h
    rcases h with ⟨node, hposition, hobservation⟩ | ⟨hobservation, hmissing⟩
    · left
      refine ⟨iso.toEquiv node, ?_, ?_⟩
      · simpa using hposition
      · exact hobservation.trans
          (exactRule1aNodeObservation_transport molecule addressing iso node)
    · right
      refine ⟨hobservation, ?_⟩
      intro node hposition
      exact hmissing (iso.toEquiv.symm node) (by simpa using hposition)
  · intro h
    rcases h with ⟨node, hposition, hobservation⟩ | ⟨hobservation, hmissing⟩
    · left
      let source := iso.toEquiv.symm node
      refine ⟨source, ?_, ?_⟩
      · simpa [source] using hposition
      · have htransport :=
          exactRule1aNodeObservation_transport molecule addressing iso source
        have hnode : iso.toEquiv source = node := by simp [source]
        rw [hnode] at htransport
        exact hobservation.trans htransport.symm
    · right
      refine ⟨hobservation, ?_⟩
      intro node hposition
      exact hmissing (iso.toEquiv node) (by simpa using hposition)

/-- Exact Rule-1a comparison at one shared semantic address. -/
def ExactRule1aOutcomeAt
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (position : List ℕ) (outcome : Ordering) : Prop :=
  ∃ leftObservation rightObservation,
    ExactRule1aObservationAt molecule left leftAddressing position leftObservation ∧
      ExactRule1aObservationAt molecule right rightAddressing position rightObservation ∧
        ExactAtomicNumber.Outcome leftObservation rightObservation outcome

theorem exactRule1aOutcomeAt_total
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (position : List ℕ) :
    ∃ outcome, ExactRule1aOutcomeAt molecule left leftAddressing
      right rightAddressing position outcome := by
  obtain ⟨leftObservation, hleft⟩ :=
    exactRule1aObservationAt_total molecule left leftAddressing position
  obtain ⟨rightObservation, hright⟩ :=
    exactRule1aObservationAt_total molecule right rightAddressing position
  obtain ⟨outcome, houtcome⟩ := ExactAtomicNumber.Outcome.total
    leftObservation rightObservation
  exact ⟨outcome, leftObservation, rightObservation, hleft, hright, houtcome⟩

theorem exactRule1aOutcomeAt_functional
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (position : List ℕ) {first second : Ordering}
    (hfirst : ExactRule1aOutcomeAt molecule left leftAddressing
      right rightAddressing position first)
    (hsecond : ExactRule1aOutcomeAt molecule left leftAddressing
      right rightAddressing position second) :
    first = second := by
  obtain ⟨leftFirst, rightFirst, hleftFirst, hrightFirst, houtFirst⟩ := hfirst
  obtain ⟨leftSecond, rightSecond, hleftSecond, hrightSecond, houtSecond⟩ := hsecond
  have hleft : leftFirst = leftSecond :=
    exactRule1aObservationAt_functional molecule left leftAddressing position
      hleftFirst hleftSecond
  have hright : rightFirst = rightSecond :=
    exactRule1aObservationAt_functional molecule right rightAddressing position
      hrightFirst hrightSecond
  subst leftSecond
  subst rightSecond
  exact ExactAtomicNumber.Outcome.functional houtFirst houtSecond

theorem exactRule1aOutcomeAt_transport_iff
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    {left left' right right' : RootedDigraph Atom}
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing)
    (leftIso : RootedDigraph.Iso left left') (rightIso : RootedDigraph.Iso right right')
    (position : List ℕ) (outcome : Ordering) :
    ExactRule1aOutcomeAt molecule left leftAddressing
        right rightAddressing position outcome ↔
      ExactRule1aOutcomeAt molecule left' (leftAddressing.transport leftIso)
        right' (rightAddressing.transport rightIso) position outcome := by
  constructor
  · rintro ⟨leftObservation, rightObservation, hleft, hright, houtcome⟩
    exact ⟨leftObservation, rightObservation,
      (exactRule1aObservationAt_transport_iff molecule leftAddressing leftIso
        position leftObservation).1 hleft,
      (exactRule1aObservationAt_transport_iff molecule rightAddressing rightIso
        position rightObservation).1 hright,
      houtcome⟩
  · rintro ⟨leftObservation, rightObservation, hleft, hright, houtcome⟩
    exact ⟨leftObservation, rightObservation,
      (exactRule1aObservationAt_transport_iff molecule leftAddressing leftIso
        position leftObservation).2 hleft,
      (exactRule1aObservationAt_transport_iff molecule rightAddressing rightIso
        position rightObservation).2 hright,
      houtcome⟩

/-- Sphere-major, first-difference hierarchy semantics for exact rational Rule 1a. -/
def ExactRule1aHierarchyOutcome
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (outcome : Ordering) : Prop :=
  FirstDifferenceOutcome
    (ExactRule1aOutcomeAt molecule left leftAddressing right rightAddressing) outcome

theorem exactRule1aHierarchyOutcome_functional
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    {first second : Ordering}
    (hfirst : ExactRule1aHierarchyOutcome molecule left leftAddressing
      right rightAddressing first)
    (hsecond : ExactRule1aHierarchyOutcome molecule left leftAddressing
      right rightAddressing second) :
    first = second := by
  exact FirstDifferenceOutcome.functional
    (fun position first second => exactRule1aOutcomeAt_functional molecule
      left leftAddressing right rightAddressing position) hfirst hsecond

theorem exactRule1aHierarchyOutcome_transport_iff
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    {left left' right right' : RootedDigraph Atom}
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing)
    (leftIso : RootedDigraph.Iso left left') (rightIso : RootedDigraph.Iso right right')
    (outcome : Ordering) :
    ExactRule1aHierarchyOutcome molecule left leftAddressing
        right rightAddressing outcome ↔
      ExactRule1aHierarchyOutcome molecule left' (leftAddressing.transport leftIso)
        right' (rightAddressing.transport rightIso) outcome := by
  exact FirstDifferenceOutcome.congr
    (fun position localOutcome => exactRule1aOutcomeAt_transport_iff molecule
      leftAddressing rightAddressing leftIso rightIso position localOutcome) outcome

theorem exactRule1aObservationAt_zero_of_not_occupied
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) (position : List ℕ)
    (hposition : position ∉ addressing.occupiedAddresses graph) :
    ExactRule1aObservationAt molecule graph addressing position .zero := by
  right
  refine ⟨rfl, ?_⟩
  intro node hnode
  exact hposition ((RootedDigraph.Addressing.mem_occupiedAddresses_iff
    graph addressing position).2 ⟨node, hnode⟩)

theorem exactRule1aOutcomeAt_eq_of_outside
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (position : List ℕ)
    (hleft : position ∉ leftAddressing.occupiedAddresses left)
    (hright : position ∉ rightAddressing.occupiedAddresses right) :
    ExactRule1aOutcomeAt molecule left leftAddressing
      right rightAddressing position Ordering.eq := by
  refine ⟨.zero, .zero,
    exactRule1aObservationAt_zero_of_not_occupied molecule left leftAddressing position hleft,
    exactRule1aObservationAt_zero_of_not_occupied molecule right rightAddressing position hright,
    ?_⟩
  simp [ExactAtomicNumber.Outcome, ExactAtomicNumber.zero,
    ExactAtomicNumber.ofNat, ExactAtomicNumber.value]

theorem exactRule1aHierarchyOutcome_total
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing) :
    ∃ outcome, ExactRule1aHierarchyOutcome molecule left leftAddressing
      right rightAddressing outcome := by
  let support := leftAddressing.occupiedAddresses left ∪
    rightAddressing.occupiedAddresses right
  apply FirstDifferenceOutcome.total_of_finite_support
    (fun position => exactRule1aOutcomeAt_total molecule
      left leftAddressing right rightAddressing position) support
  intro position houtside
  have hboth : position ∉ leftAddressing.occupiedAddresses left ∧
      position ∉ rightAddressing.occupiedAddresses right := by
    simpa [support] using houtside
  exact exactRule1aOutcomeAt_eq_of_outside molecule left leftAddressing
    right rightAddressing position hboth.1 hboth.2

end
end DeclarativeCIP
end OneCenter
end TetraStereo
