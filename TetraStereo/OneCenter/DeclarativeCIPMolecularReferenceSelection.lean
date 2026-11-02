import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidence
import TetraStereo.OneCenter.DeclarativeCIPOrdinaryCanonicalAddressing
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

open scoped Classical

universe u

/-!
# General Rule-4b reference selection and the reflection-invariant ligand signature

`DeclarativeCIPMolecularEvidence.referencePopulation` handles an empty population and a uniquely
nearest eligible occurrence, and declares every other case `unsupported`.  This module defines the
complete P-92.5.2.1 selection independently of any runtime:

* **(a)** the reference descriptor is that of the highest-ranked chiral node — here: the nearest
  eligible sphere, and within it the nodes of greatest *rank path*, where the rank path of a node
  lists the ordinary keys of its ancestors (root first) computed from the evidence of the rules
  applied before Rule 4b (Rules 3 and 4a over the constitutional vector);
* **(b)** several equivalent highest-ranked nodes (equal rank paths) form the reference class, and
  the sense occurring most often in it is the reference;
* **(c)** equal numbers of `R` and `S` select both senses; **(c)(i)** one reference precedes two;
  **(c)(ii)** each reference is paired with every eligible node of the whole ligand.

The complete reading under one reference is the Rule-4b hierarchy component of the ordinary key at
the ligand root, computed from the evidence of Rules 3, 4a and the pairing with that reference
(later rules masked).  The **ligand signature** is the criterion-(c)(i) count followed by the
complete readings; with two references the two readings are taken in *descending* order.

The main theorem is **reflection invariance** (`ligandSignature_reflect`): reflecting every
descriptor of the map (`R ↔ S`, `M ↔ P`, …; `r/s` fixed) leaves the signature unchanged, as
P-92.1.3 requires of Rules 1--4.  The fixed normative order `[R, S]` would *not* have this
property: `reading_reflect` shows the two readings are exchanged.

Compatibility: `referenceSelection_eq_empty_iff` and `referenceSelection_eq_one_of_uniqueNearest`
identify the existing empty and uniquely-nearest cases with the new selection.
-/

/-! ## Reflection of descriptors and maps -/

namespace DescriptorSense

/-- The opposite sense. -/
def mirror : DescriptorSense → DescriptorSense
  | senior => junior
  | junior => senior

@[simp] theorem mirror_mirror (sense : DescriptorSense) : sense.mirror.mirror = sense := by
  cases sense <;> rfl

end DescriptorSense

namespace Descriptor

/-- Reflection of a descriptor: reflection-variant symbols are exchanged, pseudoasymmetric and
double-bond symbols are fixed (P-92.1.1(d), P-92.1.3). -/
def reflect : Descriptor → Descriptor
  | R => S | S => R | Ra => Sa | Sa => Ra | Rp => Sp | Sp => Rp | M => P | P => M
  | r => r | s => s | E => E | Z => Z | seqCis => seqCis | seqTrans => seqTrans

@[simp] theorem unitKind_reflect (d : Descriptor) : d.reflect.unitKind = d.unitKind := by
  cases d <;> rfl

@[simp] theorem chiralSense_reflect (d : Descriptor) :
    d.reflect.chiralSense = d.chiralSense.map DescriptorSense.mirror := by
  cases d <;> rfl

@[simp] theorem pseudoSense_reflect (d : Descriptor) : d.reflect.pseudoSense = d.pseudoSense := by
  cases d <;> rfl

@[simp] theorem doubleBondGeometry_reflect (d : Descriptor) :
    d.reflect.doubleBondGeometry = d.doubleBondGeometry := by
  cases d <;> rfl

end Descriptor

namespace DescriptorPairKind

@[simp] theorem ofSenses_mirror (reference observed : DescriptorSense) :
    ofSenses reference.mirror observed.mirror = ofSenses reference observed := by
  cases reference <;> cases observed <;> rfl

end DescriptorPairKind

/-- Reflect every descriptor of a map. -/
def DescriptorMap.reflect {Unit : Type u} (descriptorMap : DescriptorMap Unit) : DescriptorMap Unit :=
  fun unit => (descriptorMap unit).map Descriptor.reflect

namespace OccurrenceReading

/-- Reflection of a reading. -/
def reflect : OccurrenceReading → OccurrenceReading
  | descriptor value => descriptor value.reflect
  | reading => reading

end OccurrenceReading

/-! ## Ancestor chains and rank paths -/

section Chains

variable {Atom : Type u} (graph : RootedDigraph Atom)

/-- `AncestorChain graph node chain`: `chain` lists the nodes from the root to `node`, root first. -/
inductive AncestorChain : graph.Node → List graph.Node → Prop where
  | root : AncestorChain graph.root [graph.root]
  | step {parent node : graph.Node} {chain : List graph.Node} :
      graph.child parent node → AncestorChain parent chain → AncestorChain node (chain ++ [node])

/-- The ancestor chain of a node when it is unique, otherwise `[]`. -/
def ancestorChain (node : graph.Node) : List graph.Node :=
  if h : ∃! chain, AncestorChain graph node chain then Classical.choose h.exists else []

theorem exists_ancestorChain (node : graph.Node) : ∃ chain, AncestorChain graph node chain := by
  induction graph.reachable node with
  | refl => exact ⟨_, AncestorChain.root⟩
  | tail _ hedge ih =>
      obtain ⟨chain, hchain⟩ := ih
      exact ⟨_, AncestorChain.step hedge hchain⟩

theorem ancestorChain_unique_of_addressing (addressing : graph.Addressing) {node : graph.Node}
    {first second : List graph.Node}
    (hfirst : AncestorChain graph node first) (hsecond : AncestorChain graph node second) :
    first = second := by
  have noParent : ∀ parent, ¬ graph.child parent graph.root := by
    intro parent hedge
    obtain ⟨slot, hslot⟩ := (addressing.child_iff parent graph.root).1 hedge
    rw [addressing.root_address] at hslot
    simp at hslot
  induction hfirst generalizing second with
  | root =>
      cases hsecond with
      | root => rfl
      | step hedge _ => exact (noParent _ hedge).elim
  | step hedge _ ih =>
      cases hsecond with
      | root => exact (noParent _ hedge).elim
      | step hedge' hchain' =>
          have := addressing.parent_unique hedge hedge'
          subst this
          rw [ih hchain']

theorem ancestorChain_spec_of_addressing (addressing : graph.Addressing) (node : graph.Node) :
    AncestorChain graph node (ancestorChain graph node) := by
  obtain ⟨chain, hchain⟩ := exists_ancestorChain graph node
  have h : ∃! chain, AncestorChain graph node chain :=
    ⟨chain, hchain, fun _ hother => ancestorChain_unique_of_addressing graph addressing hother hchain⟩
  rw [ancestorChain, dif_pos h]
  exact Classical.choose_spec h.exists

end Chains

/-! ## Rank evidence, rank paths and the reference class -/

section Selection

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

/-- Evidence of the rules applied before Rule 4b: Rules 3 and 4a only. -/
def rankEvidence : StereochemicalEvidence graph := fun node =>
  { rule3 := rule3Observation molecule descriptorMap unit graph node
    rule4a := rule4aObservation molecule descriptorMap unit graph node
    rule4b := none
    rule4c := none
    rule5 := none }

/-- The ordinary key of a node under the pre-Rule-4b evidence. -/
def rankKey (node : graph.Node) : OrdinaryKey :=
  ordinaryKey molecule graph (rankEvidence molecule descriptorMap unit graph) graph.width graph.height
    node

/-- The rank path of a node: the rank keys of its ancestors, root first.  Comparing rank paths
lexicographically from the root is the hierarchical ranking of nodes. -/
def rankPath (node : graph.Node) : List OrdinaryKey :=
  (ancestorChain graph node).map (rankKey molecule descriptorMap unit graph)

/-- **The reference class** (P-92.5.2.1(a),(b)): nearest eligible nodes of greatest rank path. -/
def InReferenceClass (node : graph.Node) : Prop :=
  NearestEligible molecule descriptorMap unit graph node ∧
    ∀ other, NearestEligible molecule descriptorMap unit graph other →
      rankPath molecule descriptorMap unit graph other ≤ rankPath molecule descriptorMap unit graph node

local instance selectionNodeFintype1 : Fintype graph.Node := graph.nodeFintype

def referenceClass : Finset graph.Node :=
  Finset.univ.filter (InReferenceClass molecule descriptorMap unit graph)

def seniorCount : ℕ :=
  ((referenceClass molecule descriptorMap unit graph).filter fun node =>
    eligibleSense molecule descriptorMap unit graph node = some .senior).card

def juniorCount : ℕ :=
  ((referenceClass molecule descriptorMap unit graph).filter fun node =>
    eligibleSense molecule descriptorMap unit graph node = some .junior).card

/-- The P-92.5.2.1 selection: no reference, one sense, or both senses. -/
inductive ReferenceSelection where
  | empty
  | one (sense : DescriptorSense)
  | both
  deriving DecidableEq

namespace ReferenceSelection

def mirror : ReferenceSelection → ReferenceSelection
  | empty => empty
  | one sense => one sense.mirror
  | both => both

/-- Criterion (c)(i): one reference descriptor precedes two. -/
def countPriority : ReferenceSelection → ℕ
  | one _ => 2
  | both => 1
  | empty => 0

@[simp] theorem countPriority_mirror (selection : ReferenceSelection) :
    selection.mirror.countPriority = selection.countPriority := by
  cases selection <;> rfl

end ReferenceSelection

def referenceSelection : ReferenceSelection :=
  if ¬ ∃ node, Eligible molecule descriptorMap unit graph node then .empty
  else if juniorCount molecule descriptorMap unit graph < seniorCount molecule descriptorMap unit graph
    then .one .senior
  else if seniorCount molecule descriptorMap unit graph < juniorCount molecule descriptorMap unit graph
    then .one .junior
  else .both

/-! ## Complete readings and the ligand signature -/

/-- Evidence for one reference: Rules 3, 4a and the like/unlike pairing with `reference` at every
eligible node of the whole ligand (criterion (c)(ii)); later rules masked. -/
def readingEvidence (reference : DescriptorSense) : StereochemicalEvidence graph := fun node =>
  { rule3 := rule3Observation molecule descriptorMap unit graph node
    rule4a := rule4aObservation molecule descriptorMap unit graph node
    rule4b := (eligibleSense molecule descriptorMap unit graph node).map fun observed =>
      ⟨[[(DescriptorPairKind.ofSenses reference observed).priority]]⟩
    rule4c := none
    rule5 := none }

/-- The complete reading under one reference: the Rule-4b hierarchy component of the ligand root's
ordinary key over the reference's evidence. -/
def reading (reference : DescriptorSense) : Certificate.CanonicalSphereKey.Key StereoLabel :=
  ((ofLex (ordinaryKey molecule graph (readingEvidence molecule descriptorMap unit graph reference)
      graph.width graph.height graph.root)).2).getD
    (stereoIndex .rule4bLikeUnlikeDescriptorPairs) []

/-- **The ligand-level Rule-4b signature**: the criterion-(c)(i) count, then the complete readings
in descending order. -/
def ligandSignature : ℕ × List (Certificate.CanonicalSphereKey.Key StereoLabel) :=
  match referenceSelection molecule descriptorMap unit graph with
  | .empty => (0, [])
  | .one reference => (2, [reading molecule descriptorMap unit graph reference])
  | .both =>
      (1, [max (reading molecule descriptorMap unit graph .senior)
             (reading molecule descriptorMap unit graph .junior),
           min (reading molecule descriptorMap unit graph .senior)
             (reading molecule descriptorMap unit graph .junior)])

end Selection

/-- Rule-4b priority between two ligand signatures: count first, then the readings in order. -/
def LigandSignatureOutcome
    (left right : ℕ × List (Certificate.CanonicalSphereKey.Key StereoLabel)) (outcome : Ordering) :
    Prop :=
  compare (toLex left) (toLex right) = outcome

/-! ## Reflection -/

section Reflection

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

theorem readContext_reflect (steps : List Atom) :
    readContext molecule descriptorMap.reflect unit steps =
      (readContext molecule descriptorMap unit steps).reflect := by
  unfold readContext
  cases contextOccurrence molecule unit steps with
  | none => rfl
  | some source =>
      simp only [DescriptorMap.reflect]
      cases descriptorMap source <;> rfl

theorem occurrenceReading_reflect (node : graph.Node) :
    occurrenceReading molecule descriptorMap.reflect unit graph node =
      (occurrenceReading molecule descriptorMap unit graph node).reflect := by
  unfold occurrenceReading
  cases (graph.label node).provenance <;> cases ancestorAtoms graph node <;>
    first | rfl | exact readContext_reflect molecule descriptorMap unit _

theorem rule3Observation_reflect (node : graph.Node) :
    rule3Observation molecule descriptorMap.reflect unit graph node =
      rule3Observation molecule descriptorMap unit graph node := by
  unfold rule3Observation
  rw [occurrenceReading_reflect]
  cases occurrenceReading molecule descriptorMap unit graph node <;>
    simp [OccurrenceReading.reflect]

theorem rule4aObservation_reflect (node : graph.Node) :
    rule4aObservation molecule descriptorMap.reflect unit graph node =
      rule4aObservation molecule descriptorMap unit graph node := by
  unfold rule4aObservation
  rw [occurrenceReading_reflect]
  cases occurrenceReading molecule descriptorMap unit graph node <;>
    simp [OccurrenceReading.reflect]

theorem eligibleSense_reflect (node : graph.Node) :
    eligibleSense molecule descriptorMap.reflect unit graph node =
      (eligibleSense molecule descriptorMap unit graph node).map DescriptorSense.mirror := by
  unfold eligibleSense
  rw [occurrenceReading_reflect]
  cases occurrenceReading molecule descriptorMap unit graph node <;>
    simp [OccurrenceReading.reflect]

theorem eligible_reflect (node : graph.Node) :
    Eligible molecule descriptorMap.reflect unit graph node ↔
      Eligible molecule descriptorMap unit graph node := by
  unfold Eligible
  rw [eligibleSense_reflect]
  cases eligibleSense molecule descriptorMap unit graph node <;> simp

theorem nearestEligible_reflect (node : graph.Node) :
    NearestEligible molecule descriptorMap.reflect unit graph node ↔
      NearestEligible molecule descriptorMap unit graph node := by
  unfold NearestEligible
  simp only [eligible_reflect]

theorem rankEvidence_reflect :
    rankEvidence molecule descriptorMap.reflect unit graph =
      rankEvidence molecule descriptorMap unit graph := by
  funext node
  simp only [rankEvidence, rule3Observation_reflect, rule4aObservation_reflect]

theorem rankPath_reflect (node : graph.Node) :
    rankPath molecule descriptorMap.reflect unit graph node =
      rankPath molecule descriptorMap unit graph node := by
  unfold rankPath rankKey
  rw [rankEvidence_reflect]

theorem inReferenceClass_reflect (node : graph.Node) :
    InReferenceClass molecule descriptorMap.reflect unit graph node ↔
      InReferenceClass molecule descriptorMap unit graph node := by
  unfold InReferenceClass
  simp only [nearestEligible_reflect, rankPath_reflect]

theorem referenceClass_reflect :
    referenceClass molecule descriptorMap.reflect unit graph =
      referenceClass molecule descriptorMap unit graph := by
  unfold referenceClass
  ext node
  simp only [Finset.mem_filter, inReferenceClass_reflect]

theorem seniorCount_reflect :
    seniorCount molecule descriptorMap.reflect unit graph =
      juniorCount molecule descriptorMap unit graph := by
  unfold seniorCount juniorCount
  rw [referenceClass_reflect]
  congr 1
  ext node
  simp only [Finset.mem_filter, eligibleSense_reflect]
  constructor
  · rintro ⟨hmem, h⟩
    refine ⟨hmem, ?_⟩
    cases hsense : eligibleSense molecule descriptorMap unit graph node with
    | none => simp [hsense] at h
    | some sense => cases sense <;> simp_all [DescriptorSense.mirror]
  · rintro ⟨hmem, h⟩
    exact ⟨hmem, by simp [h, DescriptorSense.mirror]⟩

theorem juniorCount_reflect :
    juniorCount molecule descriptorMap.reflect unit graph =
      seniorCount molecule descriptorMap unit graph := by
  unfold seniorCount juniorCount
  rw [referenceClass_reflect]
  congr 1
  ext node
  simp only [Finset.mem_filter, eligibleSense_reflect]
  constructor
  · rintro ⟨hmem, h⟩
    refine ⟨hmem, ?_⟩
    cases hsense : eligibleSense molecule descriptorMap unit graph node with
    | none => simp [hsense] at h
    | some sense => cases sense <;> simp_all [DescriptorSense.mirror]
  · rintro ⟨hmem, h⟩
    exact ⟨hmem, by simp [h, DescriptorSense.mirror]⟩

theorem referenceSelection_reflect :
    referenceSelection molecule descriptorMap.reflect unit graph =
      (referenceSelection molecule descriptorMap unit graph).mirror := by
  unfold referenceSelection
  simp only [eligible_reflect, seniorCount_reflect, juniorCount_reflect]
  by_cases hex : ∃ node, Eligible molecule descriptorMap unit graph node
  · simp only [hex, not_true_eq_false, if_false]
    by_cases hlt : seniorCount molecule descriptorMap unit graph <
        juniorCount molecule descriptorMap unit graph
    · have : ¬ juniorCount molecule descriptorMap unit graph <
          seniorCount molecule descriptorMap unit graph := lt_asymm hlt
      simp [hlt, this, ReferenceSelection.mirror, DescriptorSense.mirror]
    · by_cases hgt : juniorCount molecule descriptorMap unit graph <
          seniorCount molecule descriptorMap unit graph
      · simp [hlt, hgt, ReferenceSelection.mirror, DescriptorSense.mirror]
      · simp [hlt, hgt, ReferenceSelection.mirror]
  · simp [hex, ReferenceSelection.mirror]

theorem readingEvidence_reflect (reference : DescriptorSense) :
    readingEvidence molecule descriptorMap.reflect unit graph reference =
      readingEvidence molecule descriptorMap unit graph reference.mirror := by
  funext node
  simp only [readingEvidence, rule3Observation_reflect, rule4aObservation_reflect,
    eligibleSense_reflect]
  congr 1
  cases eligibleSense molecule descriptorMap unit graph node with
  | none => rfl
  | some observed =>
      simp only [Option.map_some]
      cases reference <;> cases observed <;> rfl

/-- Under reflection the reading for `reference` becomes the reading for the opposite reference:
the two readings of a tied population are exchanged. -/
theorem reading_reflect (reference : DescriptorSense) :
    reading molecule descriptorMap.reflect unit graph reference =
      reading molecule descriptorMap unit graph reference.mirror := by
  simp only [reading, readingEvidence_reflect]

/-- **Reflection invariance of the ligand signature** (P-92.1.3). -/
theorem ligandSignature_reflect :
    ligandSignature molecule descriptorMap.reflect unit graph =
      ligandSignature molecule descriptorMap unit graph := by
  unfold ligandSignature
  rw [referenceSelection_reflect]
  cases referenceSelection molecule descriptorMap unit graph with
  | empty => rfl
  | one reference =>
      simp only [ReferenceSelection.mirror, reading_reflect, DescriptorSense.mirror_mirror]
  | both =>
      simp only [ReferenceSelection.mirror, reading_reflect, DescriptorSense.mirror]
      rw [max_comm, min_comm]

end Reflection

/-! ## Compatibility with the empty and uniquely-nearest cases -/

section Compatibility

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

theorem referenceSelection_eq_empty_iff :
    referenceSelection molecule descriptorMap unit graph = .empty ↔
      ¬ ∃ node, Eligible molecule descriptorMap unit graph node := by
  unfold referenceSelection
  by_cases hex : ∃ node, Eligible molecule descriptorMap unit graph node
  · simp only [hex, not_true_eq_false, if_false, iff_false]
    split
    · simp
    · split <;> simp
  · simp [hex]

local instance selectionNodeFintype2 : Fintype graph.Node := graph.nodeFintype

/-- A uniquely nearest eligible node is the whole reference class. -/
theorem referenceClass_eq_singleton_of_uniqueNearest {reference : graph.Node}
    (hnearest : NearestEligible molecule descriptorMap unit graph reference)
    (hunique : ∀ other, NearestEligible molecule descriptorMap unit graph other → other = reference) :
    referenceClass molecule descriptorMap unit graph = {reference} := by
  ext node
  simp only [referenceClass, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    InReferenceClass]
  constructor
  · rintro ⟨hnode, _⟩
    exact hunique node hnode
  · rintro rfl
    exact ⟨hnearest, fun other hother => by rw [hunique other hother]⟩

/-- The existing uniquely-nearest case selects exactly the unique node's sense. -/
theorem referenceSelection_eq_one_of_uniqueNearest {reference : graph.Node}
    (hnearest : NearestEligible molecule descriptorMap unit graph reference)
    (hunique : ∀ other, NearestEligible molecule descriptorMap unit graph other → other = reference)
    {sense : DescriptorSense}
    (hsense : eligibleSense molecule descriptorMap unit graph reference = some sense) :
    referenceSelection molecule descriptorMap unit graph = .one sense := by
  have hclass := referenceClass_eq_singleton_of_uniqueNearest molecule descriptorMap unit graph
    hnearest hunique
  have hex : ∃ node, Eligible molecule descriptorMap unit graph node := ⟨reference, hnearest.1⟩
  have hsenior : seniorCount molecule descriptorMap unit graph =
      if sense = .senior then 1 else 0 := by
    unfold seniorCount
    rw [hclass]
    cases sense <;> simp [Finset.filter_singleton, hsense]
  have hjunior : juniorCount molecule descriptorMap unit graph =
      if sense = .junior then 1 else 0 := by
    unfold juniorCount
    rw [hclass]
    cases sense <;> simp [Finset.filter_singleton, hsense]
  unfold referenceSelection
  cases sense <;> simp [hex, hsenior, hjunior]

end Compatibility

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ancestorChain_unique_of_addressing
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ancestorChain_spec_of_addressing
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.referenceSelection
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ligandSignature
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.reading_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.referenceSelection_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ligandSignature_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.referenceSelection_eq_empty_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.referenceSelection_eq_one_of_uniqueNearest
