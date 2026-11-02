import TetraStereo.OneCenter.DeclarativeCIPConstitutional
import TetraStereo.OneCenter.DeclarativeCIPStereochemical
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

open scoped Classical

universe u

/-!
# Molecular evidence at a fixed descriptor map

`StereochemicalProblemData.evidence` is an input field.  This module defines it from molecular and
occurrence facts only: the molecule, the ranked occurrence unit, the rooted occurrence graph, and a
fixed descriptor map on the detected occurrence units.  No production key, compiled signature,
successful build or comparison result is inspected.

## Units and occurrence context

* The detected inventory consists of the atoms with exactly four neighbours
  (`IsDetectedCenter`, the same set as the runtime's `tetrahedralCenterSet`).
* A unit is an *occurrence* of a detected center: an original root atom together with the atom path
  from that root (`OccurrenceUnit`).  Descriptors are therefore indexed by occurrence context, not
  by atom.  The final descriptor of a center is the value at its empty-path occurrence; values at
  longer paths are occurrence-specific auxiliary labels.  Nothing identifies the two.
* The context of a node of a ranked unit's ligand graph is the atom path from the graph root to that
  node (`ancestorAtoms`), reconstructed from the rooted graph itself.  It is defined exactly when
  that path is unique and atom-bearing; every graph with an addressing has unique paths
  (`ancestorPath_existsUnique_of_addressing`).

## The source-context adapter

`contextOccurrence` is the explicit finite adapter.  It walks the ancestor path from the ranked
unit's own path (`rerootWalk`): a step to the incoming atom returns to the carrier parent, any other
step moves outward.  The result is read only when it is strictly deeper than the ranked unit and
lies at a detected center, matching the runtime's depth dependency.  The absolute physical
interpretation of the values read is not claimed here.

## Rule-local observations

* Only real-atom nodes with a supported context read descriptors.  Duplicate, phantom, lone-pair and
  auxiliary nodes, and nodes without a unique atom path, carry explicitly unavailable observations
  (`none` in every field).
* Rule 3 observes only atoms with a multiple bond, so on single-bond molecules its absence is a
  theorem (`molecularEvidence_rule3_eq_none`).  This endpoint's inventory has no double-bond units;
  no Rule-3 fidelity is claimed for molecules with multiple bonds.
* Rule 4a reads the unit kind of the descriptor; Rules 4c and 5 read its pseudoasymmetric and
  chiral sense.
* Rule 4b: an occurrence is eligible when its descriptor is chiral.  The reference population is
  `empty` when nothing is eligible, `unique` when exactly one eligible occurrence lies at the
  nearest eligible depth, and `unsupported` otherwise (two or more nearest candidates; this is the
  follow-on criterion-(c)/ranked-selection domain).  With a unique reference, every eligible
  occurrence, deeper ones included, carries its like/unlike pairing with the reference.  In the
  `empty` and `unsupported` cases no Rule-4b observation is made.

Each observation sits at the empty relative address of its own node.  A ligand's complete reading
is therefore the address-ordered sequence of these node observations under the independent
canonical family; no production sorted key is consulted.
-/

/-! ## Detected occurrence units -/

/-- An occurrence of an atom: the original root atom and the atom path from it. -/
structure OccurrenceUnit (Atom : Type u) where
  root : Atom
  path : List Atom
  deriving DecidableEq

namespace OccurrenceUnit

variable {Atom : Type u}

/-- The atom at the end of the occurrence path. -/
def atom (unit : OccurrenceUnit Atom) : Atom :=
  unit.path.getLast?.getD unit.root

end OccurrenceUnit

section Inventory

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

/-- The detected tetrahedral inventory: atoms with exactly four neighbours. -/
def IsDetectedCenter (molecule : MoleculeGraph Atom) (atom : Atom) : Prop :=
  (molecule.neighborFinset atom).card = 4

instance (molecule : MoleculeGraph Atom) : DecidablePred (IsDetectedCenter molecule) :=
  fun atom => inferInstanceAs (Decidable ((molecule.neighborFinset atom).card = 4))

/-- Occurrences of detected centers: the declarative units of the molecular instance. -/
abbrev DetectedOccurrence (molecule : MoleculeGraph Atom) : Type u :=
  {unit : OccurrenceUnit Atom // IsDetectedCenter molecule unit.atom}

end Inventory

/-! ## The reroot walk -/

section Walk

variable {Atom : Type u} [DecidableEq Atom]

/-- The atom from which an occurrence path was entered, if any. -/
def incomingAtom? (root : Atom) (path : List Atom) : Option Atom :=
  match path.reverse with
  | [] => none
  | [_] => some root
  | _ :: incoming :: _ => some incoming

/-- One reroot step: back to the carrier parent along the incoming atom, otherwise outward. -/
def rerootStep (root : Atom) (path : List Atom) (next : Atom) : List Atom :=
  if incomingAtom? root path = some next then path.dropLast else path ++ [next]

/-- Walk a sequence of atom steps from a starting occurrence path. -/
def rerootWalk (root : Atom) (start : List Atom) (steps : List Atom) : List Atom :=
  steps.foldl (rerootStep root) start

theorem rerootWalk_nil (root : Atom) (start : List Atom) : rerootWalk root start [] = start := rfl

theorem rerootWalk_append (root : Atom) (start first second : List Atom) :
    rerootWalk root start (first ++ second) =
      rerootWalk root (rerootWalk root start first) second := by
  simp [rerootWalk, List.foldl_append]

/-- Outward steps from the empty path never return: from a root occurrence, a walk that never
revisits the root atom only extends the path. -/
theorem rerootStep_nil (root next : Atom) : rerootStep root [] next = [next] := by
  simp [rerootStep, incomingAtom?]

end Walk

/-! ## Occurrence contexts in a rooted graph -/

section Context

variable {Atom : Type u}

/-- `AncestorPath graph node path`: `path` lists the atom labels along a child path from the graph
root to `node`, root first. -/
inductive AncestorPath (graph : RootedDigraph Atom) : graph.Node → List (Option Atom) → Prop where
  | root : AncestorPath graph graph.root [(graph.label graph.root).atom?]
  | step {parent node : graph.Node} {path : List (Option Atom)} :
      graph.child parent node → AncestorPath graph parent path →
        AncestorPath graph node (path ++ [(graph.label node).atom?])

/-- The ancestor label path of a node, when it is unique. -/
def ancestorPath (graph : RootedDigraph Atom) (node : graph.Node) :
    Option (List (Option Atom)) :=
  if h : ∃! path, AncestorPath graph node path then some (Classical.choose h.exists) else none

/-- The ancestor atom path of a node, when it is unique and every node on it bears an atom. -/
def ancestorAtoms (graph : RootedDigraph Atom) (node : graph.Node) : Option (List Atom) :=
  (ancestorPath graph node).bind fun path => path.mapM id

theorem ancestorPath_eq_some {graph : RootedDigraph Atom} {node : graph.Node}
    {path : List (Option Atom)} (hpath : AncestorPath graph node path)
    (hunique : ∀ other, AncestorPath graph node other → other = path) :
    ancestorPath graph node = some path := by
  have h : ∃! path, AncestorPath graph node path := ⟨path, hpath, hunique⟩
  rw [ancestorPath, dif_pos h]
  exact congrArg some (hunique _ (Classical.choose_spec h.exists))

theorem exists_ancestorPath (graph : RootedDigraph Atom) (node : graph.Node) :
    ∃ path, AncestorPath graph node path := by
  induction graph.reachable node with
  | refl => exact ⟨_, AncestorPath.root⟩
  | tail _ hedge ih =>
      obtain ⟨path, hpath⟩ := ih
      exact ⟨_, AncestorPath.step hedge hpath⟩

/-- In a graph whose root has no parent and whose nodes have at most one parent, ancestor paths are
unique. -/
theorem ancestorPath_unique_of_parent_unique {graph : RootedDigraph Atom}
    (noParent : ∀ parent, ¬ graph.child parent graph.root)
    (parentUnique : ∀ {first second node}, graph.child first node → graph.child second node →
      first = second)
    {node : graph.Node} {first second : List (Option Atom)}
    (hfirst : AncestorPath graph node first) (hsecond : AncestorPath graph node second) :
    first = second := by
  induction hfirst generalizing second with
  | root =>
      cases hsecond with
      | root => rfl
      | step hedge _ => exact (noParent _ hedge).elim
  | step hedge _ ih =>
      cases hsecond with
      | root => exact (noParent _ hedge).elim
      | step hedge' hpath' =>
          have := parentUnique hedge hedge'
          subst this
          rw [ih hpath']

/-- In a graph with an addressing, ancestor paths are unique. -/
theorem ancestorPath_unique_of_addressing {graph : RootedDigraph Atom}
    (addressing : graph.Addressing) {node : graph.Node} {first second : List (Option Atom)}
    (hfirst : AncestorPath graph node first) (hsecond : AncestorPath graph node second) :
    first = second := by
  refine ancestorPath_unique_of_parent_unique ?_ (fun hfirst hsecond =>
    addressing.parent_unique hfirst hsecond) hfirst hsecond
  intro parent hedge
  obtain ⟨slot, hslot⟩ := (addressing.child_iff parent graph.root).1 hedge
  rw [addressing.root_address] at hslot
  simp at hslot

theorem ancestorPath_existsUnique_of_addressing {graph : RootedDigraph Atom}
    (addressing : graph.Addressing) (node : graph.Node) :
    ∃ path, AncestorPath graph node path ∧ ancestorPath graph node = some path := by
  obtain ⟨path, hpath⟩ := exists_ancestorPath graph node
  exact ⟨path, hpath, ancestorPath_eq_some hpath fun _ hother =>
    ancestorPath_unique_of_addressing addressing hother hpath⟩

end Context

/-! ## Readings at an occurrence -/

/-- What one node of a ranked unit's ligand graph reads from the fixed descriptor map. -/
inductive OccurrenceReading where
  /-- No real-atom node with a unique atom path: the observation is unavailable. -/
  | unavailable
  /-- A real occurrence with no dependent detected unit in this context. -/
  | outsideInventory
  /-- A dependent detected unit to which the fixed map assigns no descriptor. -/
  | unassigned
  /-- A dependent detected unit carrying the given descriptor. -/
  | descriptor (value : Descriptor)
  deriving DecidableEq

section Reading

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

/-- **The source-context adapter.**  The detected occurrence read at a node whose ancestor atom path
is `steps`, in the hierarchy of the ranked unit `unit`.  It is defined when the reroot walk ends
strictly deeper than the ranked unit, at a detected center. -/
def contextOccurrence (molecule : MoleculeGraph Atom) (unit : DetectedOccurrence molecule)
    (steps : List Atom) : Option (DetectedOccurrence molecule) :=
  let occurrence : OccurrenceUnit Atom :=
    ⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩
  if h : unit.1.path.length < occurrence.path.length ∧ IsDetectedCenter molecule occurrence.atom
  then some ⟨occurrence, h.2⟩ else none

variable (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

/-- The reading of a real occurrence with ancestor atom path `steps`. -/
def readContext (steps : List Atom) : OccurrenceReading :=
  match contextOccurrence molecule unit steps with
  | none => .outsideInventory
  | some source =>
      match descriptorMap source with
      | none => .unassigned
      | some value => .descriptor value

/-- The reading at one node. -/
def occurrenceReading (node : graph.Node) : OccurrenceReading :=
  match (graph.label node).provenance, ancestorAtoms graph node with
  | .realAtom, some steps => readContext molecule descriptorMap unit steps
  | _, _ => .unavailable

theorem occurrenceReading_eq_readContext {node : graph.Node} {steps : List Atom}
    (hreal : (graph.label node).provenance = .realAtom)
    (hsteps : ancestorAtoms graph node = some steps) :
    occurrenceReading molecule descriptorMap unit graph node =
      readContext molecule descriptorMap unit steps := by
  rw [occurrenceReading, hreal, hsteps]

end Reading

/-! ## Descriptor classification -/

namespace Descriptor

/-- Stereogenic-unit kind for Rule 4a.  Double-bond geometry descriptors belong to Rule 3 and are
outside this endpoint's tetrahedral inventory. -/
def unitKind : Descriptor → StereogenicUnitKind
  | .R | .S | .Ra | .Sa | .Rp | .Sp | .M | .P => .chiral
  | .r | .s => .pseudoasymmetric
  | .E | .Z | .seqCis | .seqTrans => .nonstereogenic

/-- Chiral sense for Rules 4b and 5: `R`, `Ra`, `Rp`, `M` senior; `S`, `Sa`, `Sp`, `P` junior. -/
def chiralSense : Descriptor → Option DescriptorSense
  | .R | .Ra | .Rp | .M => some .senior
  | .S | .Sa | .Sp | .P => some .junior
  | _ => none

/-- Pseudoasymmetric sense for Rule 4c: `r` senior, `s` junior. -/
def pseudoSense : Descriptor → Option DescriptorSense
  | .r => some .senior
  | .s => some .junior
  | _ => none

/-- Rule-3 geometry of a double-bond descriptor. -/
def doubleBondGeometry : Descriptor → Rule3Geometry
  | .Z | .seqCis => .seqCis
  | .E | .seqTrans => .seqTrans
  | _ => .nonstereogenic

theorem chiralSense_isSome_iff (value : Descriptor) :
    (chiralSense value).isSome ↔ unitKind value = .chiral := by
  cases value <;> simp [chiralSense, unitKind]

end Descriptor

/-- `0 = absent`, `1 = junior`, `2 = senior`, the encoding of `Rule4cSignature`/`Rule5Signature`. -/
def senseValue : Option DescriptorSense → ℕ
  | some .senior => 2
  | some .junior => 1
  | none => 0

/-- One observation at the empty relative address of its node. -/
def singleEntry {α : Type*} (value : α) : AddressedHierarchy α := [[([], value)]]

/-! ## Rule-local observations -/

section Observations

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

/-- The atom of a node has a multiple bond in the molecule. -/
def HasMultipleBond (molecule : MoleculeGraph Atom) (label : NodeLabel Atom) : Prop :=
  ∃ atom other, label.atom? = some atom ∧ 2 ≤ molecule.bond atom other

variable (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

def rule3Observation (node : graph.Node) : Option Rule3Signature :=
  if HasMultipleBond molecule (graph.label node) then
    match occurrenceReading molecule descriptorMap unit graph node with
    | .descriptor value => some ⟨singleEntry value.doubleBondGeometry⟩
    | .outsideInventory | .unassigned => some ⟨singleEntry .nonstereogenic⟩
    | .unavailable => none
  else none

def rule4aObservation (node : graph.Node) : Option Rule4aSignature :=
  match occurrenceReading molecule descriptorMap unit graph node with
  | .descriptor value => some ⟨singleEntry value.unitKind⟩
  | .outsideInventory | .unassigned => some ⟨singleEntry .nonstereogenic⟩
  | .unavailable => none

def rule4cObservation (node : graph.Node) : Option Rule4cSignature :=
  match occurrenceReading molecule descriptorMap unit graph node with
  | .descriptor value => some ⟨singleEntry (senseValue value.pseudoSense)⟩
  | .outsideInventory | .unassigned => some ⟨singleEntry 0⟩
  | .unavailable => none

def rule5Observation (node : graph.Node) : Option Rule5Signature :=
  match occurrenceReading molecule descriptorMap unit graph node with
  | .descriptor value => some ⟨singleEntry (senseValue value.chiralSense)⟩
  | .outsideInventory | .unassigned => some ⟨singleEntry 0⟩
  | .unavailable => none

/-- The chiral sense of a node eligible as a Rule-4b reference or partner. -/
def eligibleSense (node : graph.Node) : Option DescriptorSense :=
  match occurrenceReading molecule descriptorMap unit graph node with
  | .descriptor value => value.chiralSense
  | _ => none

def Eligible (node : graph.Node) : Prop :=
  (eligibleSense molecule descriptorMap unit graph node).isSome

/-- An eligible occurrence at the nearest eligible depth. -/
def NearestEligible (node : graph.Node) : Prop :=
  Eligible molecule descriptorMap unit graph node ∧
    ∀ other, Eligible molecule descriptorMap unit graph other → graph.depth node ≤ graph.depth other

theorem option_get_congr {α : Type*} {first second : Option α} (h : first = second)
    (hfirst : first.isSome) (hsecond : second.isSome) : first.get hfirst = second.get hsecond := by
  subst h
  rfl

/-- The Rule-4b reference population at the nearest eligible sphere. -/
inductive ReferencePopulation where
  | empty
  | unique (sense : DescriptorSense)
  /-- Two or more nearest candidates: outside this endpoint. -/
  | unsupported
  deriving DecidableEq

def referencePopulation : ReferencePopulation :=
  if ¬ ∃ node, Eligible molecule descriptorMap unit graph node then .empty
  else if h : ∃! node, NearestEligible molecule descriptorMap unit graph node then
    .unique ((eligibleSense molecule descriptorMap unit graph (Classical.choose h.exists)).get
      (Classical.choose_spec h.exists).1)
  else .unsupported

theorem referencePopulation_eq_empty
    (h : ∀ node, ¬ Eligible molecule descriptorMap unit graph node) :
    referencePopulation molecule descriptorMap unit graph = .empty := by
  rw [referencePopulation, if_pos]
  rintro ⟨node, hnode⟩
  exact h node hnode

theorem referencePopulation_eq_unique {reference : graph.Node}
    (hnearest : NearestEligible molecule descriptorMap unit graph reference)
    (hunique : ∀ other, NearestEligible molecule descriptorMap unit graph other → other = reference) :
    referencePopulation molecule descriptorMap unit graph =
      .unique ((eligibleSense molecule descriptorMap unit graph reference).get hnearest.1) := by
  have hexists : ∃! node, NearestEligible molecule descriptorMap unit graph node :=
    ⟨reference, hnearest, hunique⟩
  rw [referencePopulation, if_neg (fun h => h ⟨reference, hnearest.1⟩), dif_pos hexists]
  have hchoice := hunique _ (Classical.choose_spec hexists.exists)
  congr 1
  exact option_get_congr (congrArg _ hchoice) _ _

def rule4bObservation (node : graph.Node) : Option Rule4bSignature :=
  match referencePopulation molecule descriptorMap unit graph,
      eligibleSense molecule descriptorMap unit graph node with
  | .unique reference, some observed =>
      some ⟨[[(DescriptorPairKind.ofSenses reference observed).priority]]⟩
  | _, _ => none

end Observations

/-! ## The evidence -/

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

/-- **Molecular evidence at a fixed descriptor map.** -/
def molecularEvidence (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom) :
    StereochemicalEvidence graph := fun node =>
  { rule3 := rule3Observation molecule descriptorMap unit graph node
    rule4a := rule4aObservation molecule descriptorMap unit graph node
    rule4b := rule4bObservation molecule descriptorMap unit graph node
    rule4c := rule4cObservation molecule descriptorMap unit graph node
    rule5 := rule5Observation molecule descriptorMap unit graph node }

/-- **Rule-3 absence is derived from the molecule.**  Without multiple bonds, no node of any rooted
graph carries a Rule-3 observation. -/
theorem molecularEvidence_rule3_eq_none (molecule : MoleculeGraph Atom)
    (hsingle : ∀ atom other, molecule.bond atom other ≤ 1)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom) (node : graph.Node) :
    (molecularEvidence molecule descriptorMap unit graph node).rule3 = none := by
  show rule3Observation molecule descriptorMap unit graph node = none
  unfold rule3Observation
  rw [if_neg]
  rintro ⟨atom, other, _, hbond⟩
  exact Nat.not_succ_le_self 1 (hbond.trans (hsingle atom other))

/-- Unavailable nodes observe nothing. -/
theorem molecularEvidence_of_unavailable (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom) (node : graph.Node)
    (h : occurrenceReading molecule descriptorMap unit graph node = .unavailable) :
    molecularEvidence molecule descriptorMap unit graph node = ⟨none, none, none, none, none⟩ := by
  have helig : eligibleSense molecule descriptorMap unit graph node = none := by
    simp [eligibleSense, h]
  simp only [molecularEvidence, rule3Observation, rule4aObservation, rule4bObservation,
    rule4cObservation, rule5Observation, h, helig, ite_self]
  cases referencePopulation molecule descriptorMap unit graph <;> rfl

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ancestorPath_unique_of_parent_unique
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ancestorPath_unique_of_addressing
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.referencePopulation_eq_empty
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.referencePopulation_eq_unique
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ancestorPath_existsUnique_of_addressing
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.molecularEvidence_rule3_eq_none
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.molecularEvidence_of_unavailable
