import TetraStereo.OneCenter.DeclarativeCIPConstitutional
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

universe u

/-!
# Independent stereochemical rule observations

This module defines the semantic data compared by Rules 3, 4a, 4b, 4c, and 5 without importing
the production official-rule engine.  Rule 4b is represented by a unary, opponent-independent
canonical signature.  Its comparison is consequently a pullback of the lawful lexicographic order
on finite lists, rather than a binary procedure that can change a ligand's key depending on its
opponent.

Rule 3 is typed by its complete addressed hierarchy: a `Rule3Signature` carries
`AddressedHierarchy Rule3Geometry` and is compared by
`compareAddressedHierarchy Rule3Geometry.priority`.  There is no bare priority list semantics.
-/

/-! ## Shared descriptor senses -/

/-- Senior (`R`, `M`, `seqCis`) and junior (`S`, `P`, `seqTrans`) descriptor senses. -/
inductive DescriptorSense where
  | senior
  | junior
  deriving DecidableEq, Repr

namespace DescriptorSense

def priority : DescriptorSense → ℕ
  | senior => 1
  | junior => 0

end DescriptorSense

/-- Relational comparison by a natural-valued semantic priority. -/
def PriorityOutcome {α : Type*} (priority : α → ℕ)
    (left right : α) (outcome : Ordering) : Prop :=
  DescendingNatOutcome (priority left) (priority right) outcome

theorem priorityOutcome_functional {α : Type*} (priority : α → ℕ)
    (left right : α) {first second : Ordering}
    (hfirst : PriorityOutcome priority left right first)
    (hsecond : PriorityOutcome priority left right second) :
    first = second :=
  DescendingNatOutcome.functional hfirst hsecond

theorem priorityOutcome_total {α : Type*} (priority : α → ℕ) (left right : α) :
    ∃ outcome, PriorityOutcome priority left right outcome :=
  DescendingNatOutcome.total _ _

/-! ## Rule 3 and Rule 4a -/

inductive Rule3Geometry where
  | seqCis
  | seqTrans
  | nonstereogenic
  deriving DecidableEq, Repr

namespace Rule3Geometry

def priority : Rule3Geometry → ℕ
  | seqCis => 2
  | seqTrans => 1
  | nonstereogenic => 0

abbrev Outcome := PriorityOutcome priority

theorem outcome_functional (left right : Rule3Geometry) {first second : Ordering} :
    Outcome left right first → Outcome left right second → first = second :=
  priorityOutcome_functional priority left right

theorem outcome_total (left right : Rule3Geometry) : ∃ outcome, Outcome left right outcome :=
  priorityOutcome_total priority left right

end Rule3Geometry

/-! ## Complete unary addressed signatures -/

abbrev AddressedHierarchy (α : Type*) := List (List (List ℕ × α))

def compareSemanticAddress : List ℕ → List ℕ → Ordering :=
  List.compareLex compare

def compareAddressedEntry {α : Type*} (priority : α → ℕ) :
    (List ℕ × α) → (List ℕ × α) → Ordering :=
  compareLex
    (Ordering.byKey Prod.fst (flip compareSemanticAddress))
    (Ordering.byKey Prod.snd (Ordering.byKey priority compare))

def compareAddressedLayer {α : Type*} (priority : α → ℕ) :
    List (List ℕ × α) → List (List ℕ × α) → Ordering :=
  List.compareLex (compareAddressedEntry priority)

/-- Independent sphere-major comparison of complete unary addressed observations. -/
def compareAddressedHierarchy {α : Type*} (priority : α → ℕ) :
    AddressedHierarchy α → AddressedHierarchy α → Ordering :=
  List.compareLex (compareAddressedLayer priority)

/-- Complete opponent-independent Rule-3 reading after circular shared-unit cancellation.

The declarative and production semantics compare the whole finite addressed observation hierarchy;
representing only one geometry per arbitrary atom node cannot express coupled or repeated
geometrical units invariantly.  Each entry retains the canonical address of its observation and
is compared through `compareAddressedHierarchy Rule3Geometry.priority`. -/
structure Rule3Signature where
  layers : AddressedHierarchy Rule3Geometry
  deriving DecidableEq, Repr

namespace Rule3Signature

/-- Rule-3 outcome: sphere-major comparison of the complete addressed geometry hierarchy. -/
def Outcome (left right : Rule3Signature) (outcome : Ordering) : Prop :=
  compareAddressedHierarchy Rule3Geometry.priority left.layers right.layers = outcome

theorem outcome_functional (left right : Rule3Signature) {first second : Ordering}
    (hfirst : Outcome left right first) (hsecond : Outcome left right second) :
    first = second :=
  hfirst.symm.trans hsecond

theorem outcome_total (left right : Rule3Signature) :
    ∃ outcome, Outcome left right outcome :=
  ⟨compareAddressedHierarchy Rule3Geometry.priority left.layers right.layers, rfl⟩

end Rule3Signature

inductive StereogenicUnitKind where
  | chiral
  | pseudoasymmetric
  | nonstereogenic
  deriving DecidableEq, Repr

namespace StereogenicUnitKind

def priority : StereogenicUnitKind → ℕ
  | chiral => 2
  | pseudoasymmetric => 1
  | nonstereogenic => 0

abbrev Outcome := PriorityOutcome priority

theorem outcome_functional (left right : StereogenicUnitKind) {first second : Ordering} :
    Outcome left right first → Outcome left right second → first = second :=
  priorityOutcome_functional priority left right

theorem outcome_total (left right : StereogenicUnitKind) : ∃ outcome, Outcome left right outcome :=
  priorityOutcome_total priority left right

end StereogenicUnitKind

/-! ## Opponent-independent positional Rule 4b -/

/-- Like descriptor pairs have priority one; unlike pairs have priority zero. -/
inductive DescriptorPairKind where
  | like
  | unlike
  deriving DecidableEq, Repr

namespace DescriptorPairKind

def priority : DescriptorPairKind → ℕ
  | like => 1
  | unlike => 0

def ofSenses (reference observed : DescriptorSense) : DescriptorPairKind :=
  if reference = observed then like else unlike

end DescriptorPairKind

/-- A complete opponent-independent Rule-4b key.

Each inner list is one complete positional like/unlike reading encoded as `1/0`.  Criterion (b)
produces one reading and criterion (c) produces the two complementary readings.  The outer list is
stored in descending lexicographic order. -/
structure Rule4bSignature where
  readings : List (List ℕ)
  deriving DecidableEq, Repr

/-- Chemical well-formedness of an otherwise total Rule-4b semantic reading.  Keeping validity as
a predicate rather than a proof field lets independent observations be translated directly and
then certified, without making the relational comparator depend on proof-carrying data. -/
def Rule4bSignature.WellFormed (signature : Rule4bSignature) : Prop :=
  (∀ reading ∈ signature.readings, ∀ value ∈ reading, value = 0 ∨ value = 1) ∧
    signature.readings.length ≤ 2 ∧
    signature.readings.Pairwise (· ≥ ·)

namespace Rule4bSignature

/-- Rule-4b comparison is ordinary lexicographic comparison of two unary signatures. -/
def Outcome (left right : Rule4bSignature) (outcome : Ordering) : Prop :=
  compare left.readings right.readings = outcome

theorem outcome_functional (left right : Rule4bSignature) {first second : Ordering}
    (hfirst : Outcome left right first) (hsecond : Outcome left right second) :
    first = second :=
  hfirst.symm.trans hsecond

theorem outcome_total (left right : Rule4bSignature) :
    ∃ outcome, Outcome left right outcome :=
  ⟨compare left.readings right.readings, rfl⟩

/-- Strict Rule-4b priority is the strict order pulled back along `readings`. -/
def Higher (left right : Rule4bSignature) : Prop :=
  right.readings < left.readings

/-- Rule-4b ties are equality of canonical readings. -/
def Tied (left right : Rule4bSignature) : Prop :=
  left.readings = right.readings

/-- Weak Rule-4b priority. -/
def WeakPriority (left right : Rule4bSignature) : Prop :=
  right.readings ≤ left.readings

theorem weakPriority_refl (signature : Rule4bSignature) :
    WeakPriority signature signature :=
  le_rfl

theorem weakPriority_trans {first second third : Rule4bSignature}
    (hfirst : WeakPriority first second) (hsecond : WeakPriority second third) :
    WeakPriority first third :=
  hsecond.trans hfirst

theorem weakPriority_total (left right : Rule4bSignature) :
    WeakPriority left right ∨ WeakPriority right left :=
  le_total right.readings left.readings

theorem higher_trans {first second third : Rule4bSignature}
    (hfirst : Higher first second) (hsecond : Higher second third) :
    Higher first third :=
  hsecond.trans hfirst

theorem tied_trans {first second third : Rule4bSignature}
    (hfirst : Tied first second) (hsecond : Tied second third) :
    Tied first third :=
  hfirst.trans hsecond

end Rule4bSignature

/-! ## Context-restricted Rules 4c and 5 -/

inductive PseudoDescriptorFamily where
  | tetrahedral
  | axialOrPlanar
  deriving DecidableEq, Repr

structure Rule4cDescriptor where
  family : PseudoDescriptorFamily
  sense : DescriptorSense
  deriving DecidableEq, Repr

namespace Rule4cDescriptor

/-- Rule 4c is defined only inside a common pseudoasymmetric descriptor family. -/
def Outcome (left right : Rule4cDescriptor) (outcome : Ordering) : Prop :=
  left.family = right.family ∧ PriorityOutcome DescriptorSense.priority left.sense right.sense outcome

theorem outcome_functional (left right : Rule4cDescriptor) {first second : Ordering}
    (hfirst : Outcome left right first) (hsecond : Outcome left right second) :
    first = second :=
  priorityOutcome_functional DescriptorSense.priority left.sense right.sense hfirst.2 hsecond.2

theorem outcome_exists_of_same_family (left right : Rule4cDescriptor)
    (hfamily : left.family = right.family) :
    ∃ outcome, Outcome left right outcome := by
  rcases priorityOutcome_total DescriptorSense.priority left.sense right.sense with ⟨outcome, h⟩
  exact ⟨outcome, hfamily, h⟩

end Rule4cDescriptor

inductive Rule5DescriptorKind where
  | tetrahedralCenter
  | axisOrPlane
  | doubleBondOrCumulene
  deriving DecidableEq, Repr

structure Rule5Descriptor where
  kind : Rule5DescriptorKind
  auxiliary : Bool
  sense : DescriptorSense
  deriving DecidableEq, Repr

namespace Rule5Descriptor

/-- Rule 5 compares senior/junior sense only after descriptor family and auxiliary level agree. -/
def Outcome (left right : Rule5Descriptor) (outcome : Ordering) : Prop :=
  left.kind = right.kind ∧ left.auxiliary = right.auxiliary ∧
    PriorityOutcome DescriptorSense.priority left.sense right.sense outcome

theorem outcome_functional (left right : Rule5Descriptor) {first second : Ordering}
    (hfirst : Outcome left right first) (hsecond : Outcome left right second) :
    first = second :=
  priorityOutcome_functional DescriptorSense.priority left.sense right.sense hfirst.2.2 hsecond.2.2

theorem outcome_exists_of_compatible (left right : Rule5Descriptor)
    (hkind : left.kind = right.kind) (haux : left.auxiliary = right.auxiliary) :
    ∃ outcome, Outcome left right outcome := by
  rcases priorityOutcome_total DescriptorSense.priority left.sense right.sense with ⟨outcome, h⟩
  exact ⟨outcome, hkind, haux, h⟩

end Rule5Descriptor

/-! ## Remaining unary addressed signatures -/

structure Rule4aSignature where
  layers : AddressedHierarchy StereogenicUnitKind
  deriving DecidableEq, Repr

namespace Rule4aSignature

def Outcome (left right : Rule4aSignature) (outcome : Ordering) : Prop :=
  compareAddressedHierarchy StereogenicUnitKind.priority left.layers right.layers = outcome

theorem outcome_functional (left right : Rule4aSignature) {first second : Ordering}
    (hfirst : Outcome left right first) (hsecond : Outcome left right second) : first = second :=
  hfirst.symm.trans hsecond

theorem outcome_total (left right : Rule4aSignature) : ∃ outcome, Outcome left right outcome :=
  ⟨compareAddressedHierarchy StereogenicUnitKind.priority left.layers right.layers, rfl⟩

end Rule4aSignature

structure Rule4cSignature where
  /-- `0 = absent`, `1 = junior (s/p)`, `2 = senior (r/m)`. -/
  layers : AddressedHierarchy ℕ
  deriving DecidableEq, Repr

def Rule4cSignature.WellFormed (signature : Rule4cSignature) : Prop :=
  ∀ layer ∈ signature.layers, ∀ entry ∈ layer, entry.2 ≤ 2

namespace Rule4cSignature

def Outcome (left right : Rule4cSignature) (outcome : Ordering) : Prop :=
  compareAddressedHierarchy id left.layers right.layers = outcome

theorem outcome_functional (left right : Rule4cSignature) {first second : Ordering}
    (hfirst : Outcome left right first) (hsecond : Outcome left right second) : first = second :=
  hfirst.symm.trans hsecond

theorem outcome_total (left right : Rule4cSignature) : ∃ outcome, Outcome left right outcome :=
  ⟨compareAddressedHierarchy id left.layers right.layers, rfl⟩

end Rule4cSignature

structure Rule5Signature where
  /-- `0 = absent`, `1 = junior (S/P/seqTrans)`, `2 = senior (R/M/seqCis)`. -/
  layers : AddressedHierarchy ℕ
  deriving DecidableEq, Repr

def Rule5Signature.WellFormed (signature : Rule5Signature) : Prop :=
  ∀ layer ∈ signature.layers, ∀ entry ∈ layer, entry.2 ≤ 2

namespace Rule5Signature

def Outcome (left right : Rule5Signature) (outcome : Ordering) : Prop :=
  compareAddressedHierarchy id left.layers right.layers = outcome

theorem outcome_functional (left right : Rule5Signature) {first second : Ordering}
    (hfirst : Outcome left right first) (hsecond : Outcome left right second) : first = second :=
  hfirst.symm.trans hsecond

theorem outcome_total (left right : Rule5Signature) : ∃ outcome, Outcome left right outcome :=
  ⟨compareAddressedHierarchy id left.layers right.layers, rfl⟩

end Rule5Signature

/-! ## A common relational interface for Rules 3--5 -/

/-- The ordinary stereochemical sequence rules covered by this module. -/
inductive StereochemicalRule where
  | rule3DoubleBondGeometry
  | rule4aStereogenicUnitKind
  | rule4bLikeUnlikeDescriptorPairs
  | rule4cPseudoasymmetricDescriptor
  | rule5EnantiomorphicDescriptor
  deriving DecidableEq, Repr

namespace StereochemicalRule

def toSequenceRule : StereochemicalRule → SequenceRule
  | rule3DoubleBondGeometry => SequenceRule.rule3DoubleBondGeometry
  | rule4aStereogenicUnitKind => SequenceRule.rule4aStereogenicUnitKind
  | rule4bLikeUnlikeDescriptorPairs => SequenceRule.rule4bLikeUnlikeDescriptorPairs
  | rule4cPseudoasymmetricDescriptor => SequenceRule.rule4cPseudoasymmetricDescriptor
  | rule5EnantiomorphicDescriptor => SequenceRule.rule5EnantiomorphicDescriptor

end StereochemicalRule

/-- Comparison lifted to optional observations.  A present observation precedes an absent one.

This is the hierarchy padding convention: once one ligand hierarchy has ended at an address while
the other still contains a rule-relevant node, the present node is senior. -/
inductive OptionalOutcome {α : Type*} (relation : α → α → Ordering → Prop) :
    Option α → Option α → Ordering → Prop where
  | both {left right outcome} : relation left right outcome →
      OptionalOutcome relation (some left) (some right) outcome
  | leftOnly {left} : OptionalOutcome relation (some left) none Ordering.gt
  | rightOnly {right} : OptionalOutcome relation none (some right) Ordering.lt
  | neither : OptionalOutcome relation none none Ordering.eq

namespace OptionalOutcome

theorem functional {α : Type*} {relation : α → α → Ordering → Prop}
    (relationFunctional : ∀ left right first second,
      relation left right first → relation left right second → first = second)
    {left right : Option α} {first second : Ordering}
    (hfirst : OptionalOutcome relation left right first)
    (hsecond : OptionalOutcome relation left right second) :
    first = second := by
  cases hfirst <;> cases hsecond
  · exact relationFunctional _ _ _ _ ‹relation _ _ _› ‹relation _ _ _›
  · rfl
  · rfl
  · rfl

theorem total {α : Type*} {relation : α → α → Ordering → Prop}
    (relationTotal : ∀ left right, ∃ outcome, relation left right outcome)
    (left right : Option α) :
    ∃ outcome, OptionalOutcome relation left right outcome := by
  cases left with
  | none =>
      cases right with
      | none => exact ⟨Ordering.eq, neither⟩
      | some right => exact ⟨Ordering.lt, rightOnly⟩
  | some left =>
      cases right with
      | none => exact ⟨Ordering.gt, leftOnly⟩
      | some right =>
          rcases relationTotal left right with ⟨outcome, houtcome⟩
          exact ⟨outcome, both houtcome⟩

end OptionalOutcome

/-- All rule-local stereochemical facts attached to one hierarchy node.

The fields are semantic observations, not cached outputs of a comparator.  In particular, the
Rule-4b field is the complete unary canonical signature of this node. -/
structure StereochemicalObservation where
  rule3 : Option Rule3Signature
  rule4a : Option Rule4aSignature
  rule4b : Option Rule4bSignature
  rule4c : Option Rule4cSignature
  rule5 : Option Rule5Signature

/-- Rule-local comparison of two possibly absent node observations. -/
def StereochemicalNodeOutcome (rule : StereochemicalRule)
    (left right : Option StereochemicalObservation) (outcome : Ordering) : Prop :=
  match rule with
  | StereochemicalRule.rule3DoubleBondGeometry =>
      OptionalOutcome Rule3Signature.Outcome (left.bind (·.rule3)) (right.bind (·.rule3)) outcome
  | StereochemicalRule.rule4aStereogenicUnitKind =>
      OptionalOutcome Rule4aSignature.Outcome
        (left.bind (·.rule4a)) (right.bind (·.rule4a)) outcome
  | StereochemicalRule.rule4bLikeUnlikeDescriptorPairs =>
      OptionalOutcome Rule4bSignature.Outcome
        (left.bind (·.rule4b)) (right.bind (·.rule4b)) outcome
  | StereochemicalRule.rule4cPseudoasymmetricDescriptor =>
      OptionalOutcome Rule4cSignature.Outcome
        (left.bind (·.rule4c)) (right.bind (·.rule4c)) outcome
  | StereochemicalRule.rule5EnantiomorphicDescriptor =>
      OptionalOutcome Rule5Signature.Outcome
        (left.bind (·.rule5)) (right.bind (·.rule5)) outcome

/-- The exact domain condition under which a local Rule-4c or Rule-5 comparison exists. -/
def StereochemicalNodeCompatible (rule : StereochemicalRule)
    (_left _right : Option StereochemicalObservation) : Prop :=
  match rule with
  | _ => True

theorem stereochemicalNodeOutcome_functional (rule : StereochemicalRule)
    (left right : Option StereochemicalObservation) {first second : Ordering}
    (hfirst : StereochemicalNodeOutcome rule left right first)
    (hsecond : StereochemicalNodeOutcome rule left right second) :
    first = second := by
  cases rule
  · exact OptionalOutcome.functional
      (fun left right first second => Rule3Signature.outcome_functional left right) hfirst hsecond
  · exact OptionalOutcome.functional
      (fun left right first second => Rule4aSignature.outcome_functional left right)
      hfirst hsecond
  · exact OptionalOutcome.functional
      (fun left right first second => Rule4bSignature.outcome_functional left right)
      hfirst hsecond
  · exact OptionalOutcome.functional
      (fun left right first second => Rule4cSignature.outcome_functional left right)
      hfirst hsecond
  · exact OptionalOutcome.functional
      (fun left right first second => Rule5Signature.outcome_functional left right)
      hfirst hsecond

theorem stereochemicalNodeOutcome_total_of_compatible (rule : StereochemicalRule)
    (left right : Option StereochemicalObservation)
    (compatible : StereochemicalNodeCompatible rule left right) :
    ∃ outcome, StereochemicalNodeOutcome rule left right outcome := by
  cases rule
  · exact OptionalOutcome.total Rule3Signature.outcome_total _ _
  · exact OptionalOutcome.total Rule4aSignature.outcome_total _ _
  · exact OptionalOutcome.total Rule4bSignature.outcome_total _ _
  · exact OptionalOutcome.total Rule4cSignature.outcome_total _ _
  · exact OptionalOutcome.total Rule5Signature.outcome_total _ _

/-! ## Lifting observations to finite addressed hierarchies -/

/-- Semantic observations at the nodes of one representation. -/
abbrev StereochemicalEvidence {Atom : Type u} (graph : RootedDigraph Atom) :=
  graph.Node → StereochemicalObservation

namespace RootedDigraph.Addressing

/-- The observation at an address, or absence when that address is unoccupied. -/
def ObservationAt {Atom : Type u} (graph : RootedDigraph Atom) (addressing : graph.Addressing)
    (evidence : StereochemicalEvidence graph) (position : List ℕ) :
    Option StereochemicalObservation → Prop
  | some observation =>
      ∃ node, addressing.address node = position ∧ evidence node = observation
  | none => ∀ node, addressing.address node ≠ position

theorem observationAt_exists {Atom : Type u} (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) (evidence : StereochemicalEvidence graph)
    (position : List ℕ) :
    ∃ observation, ObservationAt graph addressing evidence position observation := by
  classical
  by_cases h : ∃ node, addressing.address node = position
  · rcases h with ⟨node, hnode⟩
    exact ⟨some (evidence node), node, hnode, rfl⟩
  · exact ⟨none, fun node hnode => h ⟨node, hnode⟩⟩

theorem observationAt_functional {Atom : Type u} (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) (evidence : StereochemicalEvidence graph)
    (position : List ℕ) {first second : Option StereochemicalObservation}
    (hfirst : ObservationAt graph addressing evidence position first)
    (hsecond : ObservationAt graph addressing evidence position second) :
    first = second := by
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second =>
          rcases hsecond with ⟨node, hnode, _⟩
          exact (hfirst node hnode).elim
  | some first =>
      rcases hfirst with ⟨firstNode, hfirstAddress, hfirstEvidence⟩
      cases second with
      | none => exact (hsecond firstNode hfirstAddress).elim
      | some second =>
          rcases hsecond with ⟨secondNode, hsecondAddress, hsecondEvidence⟩
          have hnode : firstNode = secondNode :=
            addressing.address_injective (hfirstAddress.trans hsecondAddress.symm)
          subst secondNode
          simp only [Option.some.injEq]
          exact hfirstEvidence.symm.trans hsecondEvidence

/-- Evidence is semantic under an isomorphism when corresponding nodes have identical facts. -/
def EvidencePreserved {Atom : Type u} {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right)
    (leftEvidence : StereochemicalEvidence left)
    (rightEvidence : StereochemicalEvidence right) : Prop :=
  ∀ node, leftEvidence node = rightEvidence (iso.toEquiv node)

theorem observationAt_transport_iff {Atom : Type u} {left right : RootedDigraph Atom}
    (addressing : left.Addressing) (iso : RootedDigraph.Iso left right)
    (leftEvidence : StereochemicalEvidence left)
    (rightEvidence : StereochemicalEvidence right)
    (preserved : EvidencePreserved iso leftEvidence rightEvidence)
    (position : List ℕ) (observation : Option StereochemicalObservation) :
    ObservationAt left addressing leftEvidence position observation ↔
      ObservationAt right (addressing.transport iso) rightEvidence position observation := by
  cases observation with
  | none =>
      constructor
      · intro h node hnode
        have hback := h (iso.toEquiv.symm node)
        apply hback
        simpa [Addressing.transport] using hnode
      · intro h node hnode
        have hforward := h (iso.toEquiv node)
        apply hforward
        simpa [Addressing.transport] using hnode
  | some observation =>
      constructor
      · rintro ⟨node, hnode, hevidence⟩
        exact ⟨iso.toEquiv node, by simpa [Addressing.transport] using hnode,
          (preserved node).symm.trans hevidence⟩
      · rintro ⟨node, hnode, hevidence⟩
        refine ⟨iso.toEquiv.symm node, ?_, ?_⟩
        · simpa [Addressing.transport] using hnode
        · calc
            leftEvidence (iso.toEquiv.symm node) =
                rightEvidence (iso.toEquiv (iso.toEquiv.symm node)) :=
              preserved (iso.toEquiv.symm node)
            _ = rightEvidence node := by simp
            _ = observation := hevidence

end RootedDigraph.Addressing

/-- Rule-local outcome at one shared hierarchy address. -/
def StereochemicalOutcomeAt {Atom : Type u} (rule : StereochemicalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (leftEvidence : StereochemicalEvidence left)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (rightEvidence : StereochemicalEvidence right)
    (position : List ℕ) (outcome : Ordering) : Prop :=
  ∃ leftObservation rightObservation,
    RootedDigraph.Addressing.ObservationAt
      left leftAddressing leftEvidence position leftObservation ∧
    RootedDigraph.Addressing.ObservationAt
      right rightAddressing rightEvidence position rightObservation ∧
    StereochemicalNodeOutcome rule leftObservation rightObservation outcome

/-- A whole-hierarchy Rule-3--5 judgment uses the earliest decisive semantic address. -/
def StereochemicalHierarchyOutcome {Atom : Type u} (rule : StereochemicalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (leftEvidence : StereochemicalEvidence left)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (rightEvidence : StereochemicalEvidence right)
    (outcome : Ordering) : Prop :=
  FirstDifferenceOutcome
    (StereochemicalOutcomeAt rule left leftAddressing leftEvidence
      right rightAddressing rightEvidence) outcome

/-- Compatibility of the observations at every common address. -/
def StereochemicalHierarchyCompatible {Atom : Type u} (rule : StereochemicalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (leftEvidence : StereochemicalEvidence left)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (rightEvidence : StereochemicalEvidence right) : Prop :=
  ∀ position leftObservation rightObservation,
    RootedDigraph.Addressing.ObservationAt
      left leftAddressing leftEvidence position leftObservation →
    RootedDigraph.Addressing.ObservationAt
      right rightAddressing rightEvidence position rightObservation →
    StereochemicalNodeCompatible rule leftObservation rightObservation

theorem stereochemicalOutcomeAt_functional {Atom : Type u} (rule : StereochemicalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (leftEvidence : StereochemicalEvidence left)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (rightEvidence : StereochemicalEvidence right) (position : List ℕ)
    {first second : Ordering}
    (hfirst : StereochemicalOutcomeAt rule left leftAddressing leftEvidence
      right rightAddressing rightEvidence position first)
    (hsecond : StereochemicalOutcomeAt rule left leftAddressing leftEvidence
      right rightAddressing rightEvidence position second) :
    first = second := by
  rcases hfirst with ⟨left₁, right₁, hleft₁, hright₁, hout₁⟩
  rcases hsecond with ⟨left₂, right₂, hleft₂, hright₂, hout₂⟩
  have hl := RootedDigraph.Addressing.observationAt_functional
    left leftAddressing leftEvidence position hleft₁ hleft₂
  have hr := RootedDigraph.Addressing.observationAt_functional
    right rightAddressing rightEvidence position hright₁ hright₂
  subst left₂
  subst right₂
  exact stereochemicalNodeOutcome_functional rule left₁ right₁ hout₁ hout₂

theorem stereochemicalOutcomeAt_total_of_compatible {Atom : Type u}
    (rule : StereochemicalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (leftEvidence : StereochemicalEvidence left)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (rightEvidence : StereochemicalEvidence right) (position : List ℕ)
    (compatible : StereochemicalHierarchyCompatible rule left leftAddressing leftEvidence
      right rightAddressing rightEvidence) :
    ∃ outcome, StereochemicalOutcomeAt rule left leftAddressing leftEvidence
      right rightAddressing rightEvidence position outcome := by
  rcases RootedDigraph.Addressing.observationAt_exists
    left leftAddressing leftEvidence position with ⟨leftObservation, hleft⟩
  rcases RootedDigraph.Addressing.observationAt_exists
    right rightAddressing rightEvidence position with ⟨rightObservation, hright⟩
  rcases stereochemicalNodeOutcome_total_of_compatible rule leftObservation rightObservation
    (compatible position leftObservation rightObservation hleft hright) with ⟨outcome, houtcome⟩
  exact ⟨outcome, leftObservation, rightObservation, hleft, hright, houtcome⟩

theorem stereochemicalOutcomeAt_eq_of_outside {Atom : Type u}
    (rule : StereochemicalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (leftEvidence : StereochemicalEvidence left)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (rightEvidence : StereochemicalEvidence right) (position : List ℕ)
    (hleft : position ∉ RootedDigraph.Addressing.occupiedAddresses left leftAddressing)
    (hright : position ∉ RootedDigraph.Addressing.occupiedAddresses right rightAddressing) :
    StereochemicalOutcomeAt rule left leftAddressing leftEvidence
      right rightAddressing rightEvidence position Ordering.eq := by
  have hleftObservation : RootedDigraph.Addressing.ObservationAt
      left leftAddressing leftEvidence position none := by
    intro node hnode
    exact hleft ((RootedDigraph.Addressing.mem_occupiedAddresses_iff
      left leftAddressing position).2 ⟨node, hnode⟩)
  have hrightObservation : RootedDigraph.Addressing.ObservationAt
      right rightAddressing rightEvidence position none := by
    intro node hnode
    exact hright ((RootedDigraph.Addressing.mem_occupiedAddresses_iff
      right rightAddressing position).2 ⟨node, hnode⟩)
  refine ⟨none, none, hleftObservation, hrightObservation, ?_⟩
  cases rule <;> exact OptionalOutcome.neither

theorem stereochemicalHierarchyOutcome_functional {Atom : Type u}
    (rule : StereochemicalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (leftEvidence : StereochemicalEvidence left)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (rightEvidence : StereochemicalEvidence right) {first second : Ordering}
    (hfirst : StereochemicalHierarchyOutcome rule left leftAddressing leftEvidence
      right rightAddressing rightEvidence first)
    (hsecond : StereochemicalHierarchyOutcome rule left leftAddressing leftEvidence
      right rightAddressing rightEvidence second) :
    first = second :=
  FirstDifferenceOutcome.functional
    (fun position _first _second => stereochemicalOutcomeAt_functional rule
      left leftAddressing leftEvidence right rightAddressing rightEvidence position)
    hfirst hsecond

theorem stereochemicalHierarchyOutcome_total_of_compatible {Atom : Type u}
    (rule : StereochemicalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (leftEvidence : StereochemicalEvidence left)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (rightEvidence : StereochemicalEvidence right)
    (compatible : StereochemicalHierarchyCompatible rule left leftAddressing leftEvidence
      right rightAddressing rightEvidence) :
    ∃ outcome, StereochemicalHierarchyOutcome rule left leftAddressing leftEvidence
      right rightAddressing rightEvidence outcome := by
  let support :=
    RootedDigraph.Addressing.occupiedAddresses left leftAddressing ∪
      RootedDigraph.Addressing.occupiedAddresses right rightAddressing
  apply FirstDifferenceOutcome.total_of_finite_support
    (fun position => stereochemicalOutcomeAt_total_of_compatible rule
      left leftAddressing leftEvidence right rightAddressing rightEvidence position compatible)
    support
  intro position houtside
  have hboth :
      position ∉ RootedDigraph.Addressing.occupiedAddresses left leftAddressing ∧
        position ∉ RootedDigraph.Addressing.occupiedAddresses right rightAddressing := by
    simpa [support] using houtside
  exact stereochemicalOutcomeAt_eq_of_outside rule
    left leftAddressing leftEvidence right rightAddressing rightEvidence position hboth.1 hboth.2

theorem stereochemicalOutcomeAt_transport_iff {Atom : Type u}
    (rule : StereochemicalRule)
    {left left' right right' : RootedDigraph Atom}
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing)
    (leftEvidence : StereochemicalEvidence left)
    (leftEvidence' : StereochemicalEvidence left')
    (rightEvidence : StereochemicalEvidence right)
    (rightEvidence' : StereochemicalEvidence right')
    (leftIso : RootedDigraph.Iso left left')
    (rightIso : RootedDigraph.Iso right right')
    (leftPreserved : RootedDigraph.Addressing.EvidencePreserved
      leftIso leftEvidence leftEvidence')
    (rightPreserved : RootedDigraph.Addressing.EvidencePreserved
      rightIso rightEvidence rightEvidence')
    (position : List ℕ) (outcome : Ordering) :
    StereochemicalOutcomeAt rule left leftAddressing leftEvidence
        right rightAddressing rightEvidence position outcome ↔
      StereochemicalOutcomeAt rule left' (leftAddressing.transport leftIso) leftEvidence'
        right' (rightAddressing.transport rightIso) rightEvidence' position outcome := by
  constructor
  · rintro ⟨leftObservation, rightObservation, hleft, hright, houtcome⟩
    exact ⟨leftObservation, rightObservation,
      (RootedDigraph.Addressing.observationAt_transport_iff
        leftAddressing leftIso leftEvidence leftEvidence' leftPreserved
        position leftObservation).1 hleft,
      (RootedDigraph.Addressing.observationAt_transport_iff
        rightAddressing rightIso rightEvidence rightEvidence' rightPreserved
        position rightObservation).1 hright,
      houtcome⟩
  · rintro ⟨leftObservation, rightObservation, hleft, hright, houtcome⟩
    exact ⟨leftObservation, rightObservation,
      (RootedDigraph.Addressing.observationAt_transport_iff
        leftAddressing leftIso leftEvidence leftEvidence' leftPreserved
        position leftObservation).2 hleft,
      (RootedDigraph.Addressing.observationAt_transport_iff
        rightAddressing rightIso rightEvidence rightEvidence' rightPreserved
        position rightObservation).2 hright,
      houtcome⟩

/-- The complete Rules-3--5 hierarchy judgment is invariant under arbitrary changes of finite
node representation, not merely under atom renaming. -/
theorem stereochemicalHierarchyOutcome_transport_iff {Atom : Type u}
    (rule : StereochemicalRule)
    {left left' right right' : RootedDigraph Atom}
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing)
    (leftEvidence : StereochemicalEvidence left)
    (leftEvidence' : StereochemicalEvidence left')
    (rightEvidence : StereochemicalEvidence right)
    (rightEvidence' : StereochemicalEvidence right')
    (leftIso : RootedDigraph.Iso left left')
    (rightIso : RootedDigraph.Iso right right')
    (leftPreserved : RootedDigraph.Addressing.EvidencePreserved
      leftIso leftEvidence leftEvidence')
    (rightPreserved : RootedDigraph.Addressing.EvidencePreserved
      rightIso rightEvidence rightEvidence')
    (outcome : Ordering) :
    StereochemicalHierarchyOutcome rule left leftAddressing leftEvidence
        right rightAddressing rightEvidence outcome ↔
      StereochemicalHierarchyOutcome rule left' (leftAddressing.transport leftIso) leftEvidence'
        right' (rightAddressing.transport rightIso) rightEvidence' outcome :=
  FirstDifferenceOutcome.congr
    (fun position localOutcome => stereochemicalOutcomeAt_transport_iff rule
      leftAddressing rightAddressing leftEvidence leftEvidence' rightEvidence rightEvidence'
      leftIso rightIso leftPreserved rightPreserved position localOutcome)
    outcome

/-! ## One independent problem carrying Rules 1a--5 -/

/-- Independent semantic data for a problem with concrete declarative judgments for every
ordinary revised-CIP rule through Rule 5.

The evidence and its naturality law are part of the specification input.  They can later be
instantiated by a chemical definition and separately related to the production implementation.
`hierarchy_compatible` records the applicability side conditions of Rules 4c and 5; unlike an
executable fallback, it cannot silently compare descriptors from incompatible families. -/
structure StereochemicalProblemData (Atom Unit : Type u)
    [Fintype Atom] [DecidableEq Atom]
    extends ConstitutionalProblemData Atom Unit where
  evidence : DescriptorMap Unit → Unit →
    (graph : RootedDigraph Atom) → StereochemicalEvidence graph
  evidence_invariant :
    ∀ descriptorMap unit {left right : RootedDigraph Atom}
      (iso : RootedDigraph.Iso left right),
      RootedDigraph.Addressing.EvidencePreserved iso
        (evidence descriptorMap unit left) (evidence descriptorMap unit right)
  hierarchy_compatible :
    ∀ descriptorMap unit rule
      (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
      (right : RootedDigraph Atom) (rightAddressing : right.Addressing),
      admissibleAddressing descriptorMap unit left leftAddressing →
      admissibleAddressing descriptorMap unit right rightAddressing →
      StereochemicalHierarchyCompatible rule
        left leftAddressing (evidence descriptorMap unit left)
        right rightAddressing (evidence descriptorMap unit right)

namespace StereochemicalProblemData

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- A canonical later-rule judgment holds for every admissible pair of semantic addressings.
Existence of both addressing families rules out vacuous universality. -/
def CanonicalOutcome (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : StereochemicalRule)
    (left right : RootedDigraph Atom) (outcome : Ordering) : Prop :=
  (∃ leftAddressing,
      data.admissibleAddressing descriptorMap unit left leftAddressing) ∧
    (∃ rightAddressing,
      data.admissibleAddressing descriptorMap unit right rightAddressing) ∧
    ∀ leftAddressing rightAddressing,
      data.admissibleAddressing descriptorMap unit left leftAddressing →
      data.admissibleAddressing descriptorMap unit right rightAddressing →
      StereochemicalHierarchyOutcome rule
        left leftAddressing (data.evidence descriptorMap unit left)
        right rightAddressing (data.evidence descriptorMap unit right) outcome

/-- Traversal/addressing independence is exposed as a proof obligation, not selected by an
algorithm. -/
def AddressingIndependent (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : StereochemicalRule)
    (left right : RootedDigraph Atom) : Prop :=
  ∀ firstLeft firstRight secondLeft secondRight firstOutcome secondOutcome,
    data.admissibleAddressing descriptorMap unit left firstLeft →
    data.admissibleAddressing descriptorMap unit right firstRight →
    data.admissibleAddressing descriptorMap unit left secondLeft →
    data.admissibleAddressing descriptorMap unit right secondRight →
    StereochemicalHierarchyOutcome rule
      left firstLeft (data.evidence descriptorMap unit left)
      right firstRight (data.evidence descriptorMap unit right) firstOutcome →
    StereochemicalHierarchyOutcome rule
      left secondLeft (data.evidence descriptorMap unit left)
      right secondRight (data.evidence descriptorMap unit right) secondOutcome →
    firstOutcome = secondOutcome

/-- Combine the constitutional and stereochemical declarative layers into the general kernel.
Rule 6 continues to use the separately quantified promotion relation. -/
def toProblem (data : StereochemicalProblemData Atom Unit) : Problem Atom Unit where
  molecule := data.molecule
  ligandAtom := data.ligandAtom
  admissibleExpansion := data.admissibleExpansion
  ordinaryRuleJudgment := fun descriptorMap rule unit left right outcome =>
    match rule with
    | SequenceRule.rule1aAtomicNumber =>
        data.toConstitutionalProblemData.CanonicalOutcome descriptorMap unit
          ConstitutionalRule.rule1aAtomicNumber left right outcome
    | SequenceRule.rule1bDuplicateNodeProximity =>
        data.toConstitutionalProblemData.CanonicalOutcome descriptorMap unit
          ConstitutionalRule.rule1bDuplicateNodeProximity left right outcome
    | SequenceRule.rule2AtomicMass =>
        data.toConstitutionalProblemData.CanonicalOutcome descriptorMap unit
          ConstitutionalRule.rule2AtomicMass left right outcome
    | SequenceRule.rule3DoubleBondGeometry =>
        data.CanonicalOutcome descriptorMap unit
          StereochemicalRule.rule3DoubleBondGeometry left right outcome
    | SequenceRule.rule4aStereogenicUnitKind =>
        data.CanonicalOutcome descriptorMap unit
          StereochemicalRule.rule4aStereogenicUnitKind left right outcome
    | SequenceRule.rule4bLikeUnlikeDescriptorPairs =>
        data.CanonicalOutcome descriptorMap unit
          StereochemicalRule.rule4bLikeUnlikeDescriptorPairs left right outcome
    | SequenceRule.rule4cPseudoasymmetricDescriptor =>
        data.CanonicalOutcome descriptorMap unit
          StereochemicalRule.rule4cPseudoasymmetricDescriptor left right outcome
    | SequenceRule.rule5EnantiomorphicDescriptor =>
        data.CanonicalOutcome descriptorMap unit
          StereochemicalRule.rule5EnantiomorphicDescriptor left right outcome
    | SequenceRule.rule6ReferencePromotion => False
  admissibleRule6Reference := data.admissibleRule6Reference
  rule6Judgment := data.rule6Judgment
  dependsOn := data.dependsOn
  orientationJudgment := data.orientationJudgment

theorem toProblem_expansion_sound (data : StereochemicalProblemData Atom Unit)
    (unit : Unit) (ligand : Fin 4) (graph : RootedDigraph Atom)
    (h : data.toProblem.admissibleExpansion unit ligand graph) :
    RootedDigraph.ExactExpansion data.molecule (data.centerAtom unit)
      (data.ligandAtom unit ligand) graph :=
  data.expansion_sound unit ligand graph h

@[simp] theorem toProblem_stereochemicalRule
    (data : StereochemicalProblemData Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (rule : StereochemicalRule)
    (left right : RootedDigraph Atom) (outcome : Ordering) :
    data.toProblem.OutcomeOnGraphs descriptorMap rule.toSequenceRule unit left right outcome ↔
      data.CanonicalOutcome descriptorMap unit rule left right outcome := by
  cases rule <;> rfl

/-- Canonical later-rule outcomes are single-valued. -/
theorem canonicalOutcome_functional (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : StereochemicalRule)
    (left right : RootedDigraph Atom) {first second : Ordering}
    (hfirst : data.CanonicalOutcome descriptorMap unit rule left right first)
    (hsecond : data.CanonicalOutcome descriptorMap unit rule left right second) :
    first = second := by
  rcases hfirst with ⟨⟨leftAddressing, hleft⟩, ⟨rightAddressing, hright⟩, hallFirst⟩
  rcases hsecond with ⟨_, _, hallSecond⟩
  exact stereochemicalHierarchyOutcome_functional rule
    left leftAddressing (data.evidence descriptorMap unit left)
    right rightAddressing (data.evidence descriptorMap unit right)
    (hallFirst leftAddressing rightAddressing hleft hright)
    (hallSecond leftAddressing rightAddressing hleft hright)

/-- Nonempty addressing families, compatibility, and traversal independence give existence of the
canonical Rules-3--5 outcome. -/
theorem canonicalOutcome_exists_of_addressingIndependent
    (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : StereochemicalRule)
    (left right : RootedDigraph Atom)
    (leftExists : ∃ addressing,
      data.admissibleAddressing descriptorMap unit left addressing)
    (rightExists : ∃ addressing,
      data.admissibleAddressing descriptorMap unit right addressing)
    (independent : data.AddressingIndependent descriptorMap unit rule left right) :
    ∃ outcome, data.CanonicalOutcome descriptorMap unit rule left right outcome := by
  rcases leftExists with ⟨firstLeft, hfirstLeft⟩
  rcases rightExists with ⟨firstRight, hfirstRight⟩
  have compatible := data.hierarchy_compatible descriptorMap unit rule
    left firstLeft right firstRight hfirstLeft hfirstRight
  rcases stereochemicalHierarchyOutcome_total_of_compatible rule
    left firstLeft (data.evidence descriptorMap unit left)
    right firstRight (data.evidence descriptorMap unit right) compatible with
    ⟨outcome, houtcome⟩
  refine ⟨outcome, ⟨firstLeft, hfirstLeft⟩, ⟨firstRight, hfirstRight⟩, ?_⟩
  intro secondLeft secondRight hsecondLeft hsecondRight
  have secondCompatible := data.hierarchy_compatible descriptorMap unit rule
    left secondLeft right secondRight hsecondLeft hsecondRight
  rcases stereochemicalHierarchyOutcome_total_of_compatible rule
    left secondLeft (data.evidence descriptorMap unit left)
    right secondRight (data.evidence descriptorMap unit right) secondCompatible with
    ⟨secondOutcome, hsecondOutcome⟩
  have heq := independent firstLeft firstRight secondLeft secondRight outcome secondOutcome
    hfirstLeft hfirstRight hsecondLeft hsecondRight houtcome hsecondOutcome
  simpa [heq] using hsecondOutcome

/-- Transport a canonical stereochemical outcome through arbitrary finite representation
isomorphisms. -/
theorem canonicalOutcome_transport
    (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : StereochemicalRule)
    {left left' right right' : RootedDigraph Atom}
    (leftIso : RootedDigraph.Iso left left') (rightIso : RootedDigraph.Iso right right')
    (outcome : Ordering)
    (h : data.CanonicalOutcome descriptorMap unit rule left right outcome) :
    data.CanonicalOutcome descriptorMap unit rule left' right' outcome := by
  rcases h with ⟨⟨leftAddressing, hleftAddressing⟩,
    ⟨rightAddressing, hrightAddressing⟩, hall⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨leftAddressing.transport leftIso,
      (data.addressing_invariant descriptorMap unit leftIso leftAddressing).1 hleftAddressing⟩
  · exact ⟨rightAddressing.transport rightIso,
      (data.addressing_invariant descriptorMap unit rightIso rightAddressing).1 hrightAddressing⟩
  · intro leftAddressing' rightAddressing' hleft' hright'
    let leftBack := leftAddressing'.transport leftIso.symm
    let rightBack := rightAddressing'.transport rightIso.symm
    have hleftBack : data.admissibleAddressing descriptorMap unit left leftBack :=
      (data.addressing_invariant descriptorMap unit leftIso.symm leftAddressing').1 hleft'
    have hrightBack : data.admissibleAddressing descriptorMap unit right rightBack :=
      (data.addressing_invariant descriptorMap unit rightIso.symm rightAddressing').1 hright'
    have houtcome := hall leftBack rightBack hleftBack hrightBack
    have htransported :=
      (stereochemicalHierarchyOutcome_transport_iff rule leftBack rightBack
        (data.evidence descriptorMap unit left) (data.evidence descriptorMap unit left')
        (data.evidence descriptorMap unit right) (data.evidence descriptorMap unit right')
        leftIso rightIso
        (data.evidence_invariant descriptorMap unit leftIso)
        (data.evidence_invariant descriptorMap unit rightIso) outcome).1 houtcome
    simpa [leftBack, rightBack] using htransported

theorem canonicalOutcome_transport_iff
    (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : StereochemicalRule)
    {left left' right right' : RootedDigraph Atom}
    (leftIso : RootedDigraph.Iso left left') (rightIso : RootedDigraph.Iso right right')
    (outcome : Ordering) :
    data.CanonicalOutcome descriptorMap unit rule left right outcome ↔
      data.CanonicalOutcome descriptorMap unit rule left' right' outcome := by
  constructor
  · exact data.canonicalOutcome_transport descriptorMap unit rule leftIso rightIso outcome
  · exact data.canonicalOutcome_transport descriptorMap unit rule
      leftIso.symm rightIso.symm outcome

/-- The constructed `Problem` is representation-invariant for every ordinary stereochemical rule
from Rule 3 through Rule 5. -/
theorem stereochemical_representationInvariant
    (data : StereochemicalProblemData Atom Unit) :
    ∀ descriptorMap (rule : StereochemicalRule) unit left left' right right' outcome,
      RootedDigraph.Iso left left' → RootedDigraph.Iso right right' →
      (data.toProblem.OutcomeOnGraphs descriptorMap rule.toSequenceRule unit left right outcome ↔
        data.toProblem.OutcomeOnGraphs descriptorMap rule.toSequenceRule
          unit left' right' outcome) := by
  intro descriptorMap rule unit left left' right right' outcome leftIso rightIso
  rw [toProblem_stereochemicalRule, toProblem_stereochemicalRule]
  exact data.canonicalOutcome_transport_iff descriptorMap unit rule leftIso rightIso outcome

/-- All concrete ordinary Rules 3--5 judgments are functional. -/
theorem stereochemical_outcome_functional
    (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (rule : StereochemicalRule) (unit : Unit)
    (left right : RootedDigraph Atom) {first second : Ordering}
    (hfirst : data.toProblem.OutcomeOnGraphs descriptorMap rule.toSequenceRule
      unit left right first)
    (hsecond : data.toProblem.OutcomeOnGraphs descriptorMap rule.toSequenceRule
      unit left right second) :
    first = second := by
  rw [toProblem_stereochemicalRule] at hfirst hsecond
  exact data.canonicalOutcome_functional descriptorMap unit rule left right hfirst hsecond

/-- Representation invariance of Rule 6, isolated as the only remaining representation premise
for the combined Rules-1a--6 problem. -/
def Rule6RepresentationInvariant (data : StereochemicalProblemData Atom Unit) : Prop :=
  ∀ descriptorMap unit left left' right right' outcome,
    RootedDigraph.Iso left left' → RootedDigraph.Iso right right' →
    (data.toProblem.OutcomeOnGraphs descriptorMap
        SequenceRule.rule6ReferencePromotion unit left right outcome ↔
      data.toProblem.OutcomeOnGraphs descriptorMap
        SequenceRule.rule6ReferencePromotion unit left' right' outcome)

/-- Every ordinary rule through Rule 5 is invariant under arbitrary rooted-digraph
representation isomorphisms. -/
theorem ordinary_representationInvariant
    (data : StereochemicalProblemData Atom Unit) :
    ∀ descriptorMap rule unit left left' right right' outcome,
      rule ≠ SequenceRule.rule6ReferencePromotion →
      RootedDigraph.Iso left left' → RootedDigraph.Iso right right' →
      (data.toProblem.OutcomeOnGraphs descriptorMap rule unit left right outcome ↔
        data.toProblem.OutcomeOnGraphs descriptorMap rule unit left' right' outcome) := by
  intro descriptorMap rule unit left left' right right' outcome hordinary leftIso rightIso
  cases rule with
  | rule1aAtomicNumber =>
      exact data.toConstitutionalProblemData.canonicalOutcome_transport_iff descriptorMap unit
        ConstitutionalRule.rule1aAtomicNumber leftIso rightIso outcome
  | rule1bDuplicateNodeProximity =>
      exact data.toConstitutionalProblemData.canonicalOutcome_transport_iff descriptorMap unit
        ConstitutionalRule.rule1bDuplicateNodeProximity leftIso rightIso outcome
  | rule2AtomicMass =>
      exact data.toConstitutionalProblemData.canonicalOutcome_transport_iff descriptorMap unit
        ConstitutionalRule.rule2AtomicMass leftIso rightIso outcome
  | rule3DoubleBondGeometry =>
      exact data.canonicalOutcome_transport_iff descriptorMap unit
        StereochemicalRule.rule3DoubleBondGeometry leftIso rightIso outcome
  | rule4aStereogenicUnitKind =>
      exact data.canonicalOutcome_transport_iff descriptorMap unit
        StereochemicalRule.rule4aStereogenicUnitKind leftIso rightIso outcome
  | rule4bLikeUnlikeDescriptorPairs =>
      exact data.canonicalOutcome_transport_iff descriptorMap unit
        StereochemicalRule.rule4bLikeUnlikeDescriptorPairs leftIso rightIso outcome
  | rule4cPseudoasymmetricDescriptor =>
      exact data.canonicalOutcome_transport_iff descriptorMap unit
        StereochemicalRule.rule4cPseudoasymmetricDescriptor leftIso rightIso outcome
  | rule5EnantiomorphicDescriptor =>
      exact data.canonicalOutcome_transport_iff descriptorMap unit
        StereochemicalRule.rule5EnantiomorphicDescriptor leftIso rightIso outcome
  | rule6ReferencePromotion => exact (hordinary rfl).elim

/-- Consequently, the general kernel's full representation-invariance obligation is equivalent to
supplying its Rule-6 case; no additional representation gap remains in Rules 1a--5. -/
theorem representationInvariant_of_rule6
    (data : StereochemicalProblemData Atom Unit)
    (rule6Invariant : data.Rule6RepresentationInvariant) :
    RepresentationInvariant data.toProblem := by
  intro descriptorMap rule unit left left' right right' outcome leftIso rightIso
  by_cases hrule6 : rule = SequenceRule.rule6ReferencePromotion
  · subst rule
    exact rule6Invariant descriptorMap unit left left' right right' outcome leftIso rightIso
  · exact data.ordinary_representationInvariant descriptorMap rule unit
      left left' right right' outcome hrule6 leftIso rightIso

/-- Every ordinary Rules-1a--5 graph judgment in the combined problem is single-valued. -/
theorem ordinary_outcome_functional
    (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (rule : SequenceRule)
    (hrule : rule ≠ SequenceRule.rule6ReferencePromotion)
    (unit : Unit) (left right : RootedDigraph Atom) {first second : Ordering}
    (hfirst : data.toProblem.OutcomeOnGraphs descriptorMap rule unit left right first)
    (hsecond : data.toProblem.OutcomeOnGraphs descriptorMap rule unit left right second) :
    first = second := by
  cases rule with
  | rule1aAtomicNumber =>
      exact data.toConstitutionalProblemData.canonicalOutcome_functional descriptorMap unit
        ConstitutionalRule.rule1aAtomicNumber left right hfirst hsecond
  | rule1bDuplicateNodeProximity =>
      exact data.toConstitutionalProblemData.canonicalOutcome_functional descriptorMap unit
        ConstitutionalRule.rule1bDuplicateNodeProximity left right hfirst hsecond
  | rule2AtomicMass =>
      exact data.toConstitutionalProblemData.canonicalOutcome_functional descriptorMap unit
        ConstitutionalRule.rule2AtomicMass left right hfirst hsecond
  | rule3DoubleBondGeometry =>
      exact data.canonicalOutcome_functional descriptorMap unit
        StereochemicalRule.rule3DoubleBondGeometry left right hfirst hsecond
  | rule4aStereogenicUnitKind =>
      exact data.canonicalOutcome_functional descriptorMap unit
        StereochemicalRule.rule4aStereogenicUnitKind left right hfirst hsecond
  | rule4bLikeUnlikeDescriptorPairs =>
      exact data.canonicalOutcome_functional descriptorMap unit
        StereochemicalRule.rule4bLikeUnlikeDescriptorPairs left right hfirst hsecond
  | rule4cPseudoasymmetricDescriptor =>
      exact data.canonicalOutcome_functional descriptorMap unit
        StereochemicalRule.rule4cPseudoasymmetricDescriptor left right hfirst hsecond
  | rule5EnantiomorphicDescriptor =>
      exact data.canonicalOutcome_functional descriptorMap unit
        StereochemicalRule.rule5EnantiomorphicDescriptor left right hfirst hsecond
  | rule6ReferencePromotion => exact (hrule rfl).elim

/-- Single-valuedness lifts from graph judgments to ligand judgments once the two ligand expansion
families are inhabited. -/
theorem ordinary_ruleOutcome_functional
    (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (rule : SequenceRule)
    (hrule : rule ≠ SequenceRule.rule6ReferencePromotion)
    (unit : Unit) (left right : Fin 4)
    (leftExists : ∃ graph, data.toProblem.admissibleExpansion unit left graph)
    (rightExists : ∃ graph, data.toProblem.admissibleExpansion unit right graph)
    {first second : Ordering}
    (hfirst : data.toProblem.RuleOutcome descriptorMap rule unit left right first)
    (hsecond : data.toProblem.RuleOutcome descriptorMap rule unit left right second) :
    first = second := by
  rcases leftExists with ⟨leftGraph, hleftGraph⟩
  rcases rightExists with ⟨rightGraph, hrightGraph⟩
  exact data.ordinary_outcome_functional descriptorMap rule hrule unit leftGraph rightGraph
    (hfirst leftGraph rightGraph hleftGraph hrightGraph)
    (hsecond leftGraph rightGraph hleftGraph hrightGraph)

/-- Under the independently stated Rule-6 promotion-independence law, every sequence-rule outcome
in a satisfying declarative specification is single-valued. -/
theorem ruleOutcome_functional_of_spec
    (data : StereochemicalProblemData Atom Unit)
    (promotionIndependent : Rule6PromotionIndependent data.toProblem)
    {descriptorMap : DescriptorMap Unit}
    (spec : CIPSpec data.toProblem descriptorMap)
    (rule : SequenceRule) (unit : Unit) (left right : Fin 4)
    {first second : Ordering}
    (hfirst : data.toProblem.RuleOutcome descriptorMap rule unit left right first)
    (hsecond : data.toProblem.RuleOutcome descriptorMap rule unit left right second) :
    first = second := by
  rcases spec.expansion_exists unit left with ⟨leftGraph, hleftGraph⟩
  rcases spec.expansion_exists unit right with ⟨rightGraph, hrightGraph⟩
  by_cases hrule6 : rule = SequenceRule.rule6ReferencePromotion
  · subst rule
    exact rule6_outcome_unique_of_promotion_independent data.toProblem promotionIndependent
      descriptorMap unit left right leftGraph rightGraph hleftGraph hrightGraph hfirst hsecond
  · exact data.ordinary_ruleOutcome_functional descriptorMap rule hrule6 unit left right
      ⟨leftGraph, hleftGraph⟩ ⟨rightGraph, hrightGraph⟩ hfirst hsecond

end StereochemicalProblemData

/-! ## Kernel-authority guards for the addressed Rule-3 signature -/

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Rule3Signature.outcome_functional
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.Rule3Signature.outcome_total

end
end DeclarativeCIP
end OneCenter
end TetraStereo
