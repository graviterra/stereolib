









































































import TetraStereo.OneCenter.Rule1bSourceProfileFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace AuxiliarySourceProfileAudit

open Rule1bSourceProfile

/-! ### Auxiliary protocol: computation from strictly higher spheres -/

/-- Two sphere assignments agree above a cutoff depth. -/
def AgreesAbove {α : Type*} (left right : ℕ → α) (depth : ℕ) : Prop :=
  ∀ sphere, depth < sphere → left sphere = right sphere

/-- A value at `depth` is computed from the values of strictly higher spheres through `step`.
This is the abstract content of the auxiliary-descriptor protocol: an auxiliary descriptor may
use descriptors of higher spheres (already assigned) but no descriptor between it and the root. -/
def ComputedFromHigher {α : Type*} (depth : ℕ) (value : α)
    (higher : (sphere : ℕ) → depth < sphere → α)
    (step : ((sphere : ℕ) → depth < sphere → α) → α) : Prop :=
  value = step higher

/-- The higher-sphere part of a total sphere assignment. -/
def assignmentHigher {α : Type*} (assignment : ℕ → α) (depth : ℕ) :
    (sphere : ℕ) → depth < sphere → α :=
  fun sphere _ => assignment sphere

/-- Congruence of the protocol: if two higher-sphere contexts agree, the computed values agree. -/
theorem computedFromHigher_congr {α : Type*} {depth : ℕ}
    {step : ((sphere : ℕ) → depth < sphere → α) → α}
    {value value' : α}
    {higher higher' : (sphere : ℕ) → depth < sphere → α}
    (hvalue : ComputedFromHigher depth value higher step)
    (hvalue' : ComputedFromHigher depth value' higher' step)
    (hagree : ∀ sphere (hsphere : depth < sphere), higher' sphere hsphere = higher sphere hsphere) :
    value' = value := by
  unfold ComputedFromHigher at hvalue hvalue'
  rw [hvalue, hvalue']
  congr 1
  funext sphere hsphere
  exact hagree sphere hsphere

/-- The protocol value at `depth` is unchanged when the assignment is changed only above
`depth`. -/
theorem computedFromHigher_agreesAbove {α : Type*} {depth : ℕ}
    {step : ((sphere : ℕ) → depth < sphere → α) → α}
    {assignment assignment' : ℕ → α}
    (h : ComputedFromHigher depth (assignment depth) (assignmentHigher assignment depth) step)
    (h' : ComputedFromHigher depth (assignment' depth) (assignmentHigher assignment' depth) step)
    (hagree : AgreesAbove assignment' assignment depth) :
    assignment' depth = assignment depth := by
  unfold ComputedFromHigher at h h'
  rw [h', h]
  congr 1
  funext sphere hsphere
  exact hagree sphere hsphere

/-- Replacing the root entry of an assignment at positive depth leaves all strictly higher
spheres unchanged. -/
theorem rootReplacement_agreesAbove {α : Type*} (assignment : ℕ → α) (replacement : α)
    (depth : ℕ) (hpos : 0 < depth) :
    AgreesAbove (fun sphere => if sphere = 0 then replacement else assignment sphere)
      assignment depth := by
  intro sphere hsphere
  have hne : sphere ≠ 0 := by omega
  simp [hne]

/-- Root blindness of the abstract protocol: a value computed from strictly higher spheres at
positive depth does not depend on the label of the root sphere.  This is a statement about
`ComputedFromHigher`, not about the implementation's stored Rule-1b distance and not about any
auxiliary stereodescriptor or root label. -/
theorem root_label_not_read {α : Type*} {depth : ℕ}
    {step : ((sphere : ℕ) → depth < sphere → α) → α}
    {assignment : ℕ → α}
    (h : ComputedFromHigher depth (assignment depth) (assignmentHigher assignment depth) step)
    (replacement : α) (hpos : 0 < depth) :
    (fun sphere => if sphere = 0 then replacement else assignment sphere) depth =
      assignment depth := by
  let modified : ℕ → α := fun sphere => if sphere = 0 then replacement else assignment sphere
  have hmodifiedDepth : modified depth = assignment depth := by
    dsimp [modified]
    rw [if_neg (Nat.ne_of_gt hpos)]
  have hmodifiedHigher : assignmentHigher modified depth = assignmentHigher assignment depth := by
    funext sphere hsphere
    exact rootReplacement_agreesAbove assignment replacement depth hpos sphere hsphere
  have h' : ComputedFromHigher depth (modified depth) (assignmentHigher modified depth) step := by
    unfold ComputedFromHigher
    rw [hmodifiedDepth, hmodifiedHigher]
    exact h
  show modified depth = assignment depth
  exact computedFromHigher_agreesAbove h h'
    (rootReplacement_agreesAbove assignment replacement depth hpos)

/-! ### The implementation's Rule-1b datum is local -/

/-- The local record from which the implementation's total Rule 1b is computed. -/
structure LocalRule1bRecord where
  depth : ℕ
  provenance : RawMolecule.CanonicalNodeProvenance
  deriving DecidableEq, Repr

/-- Read the local Rule-1b record of a canonical node. -/
def localRule1bRecord (node : RawMolecule.CanonicalBranchNode) : LocalRule1bRecord where
  depth := node.depth
  provenance := node.provenance

/-- The stored Rule-1b distance, as a function of the local record only.  The constructor order
matches `CanonicalBranchNode.rule1bRootDistance`. -/
def localStoredDistance (record : LocalRule1bRecord) : ℕ :=
  match record.provenance with
  | RawMolecule.CanonicalNodeProvenance.multipleBondDuplicate distance => distance
  | RawMolecule.CanonicalNodeProvenance.ringDuplicate distance => distance
  | RawMolecule.CanonicalNodeProvenance.phantom distance => distance
  | RawMolecule.CanonicalNodeProvenance.realAtom => record.depth

/-- The implementation's Rule-1b distance is exactly the local stored distance.  In particular it
has no access to the node's branch history. -/
theorem rule1bRootDistance_eq_localStoredDistance (node : RawMolecule.CanonicalBranchNode) :
    node.rule1bRootDistance = localStoredDistance (localRule1bRecord node) := by
  obtain ⟨atom, parent, history, provenance⟩ := node
  cases provenance <;> rfl

/-- Equal local records give a total Rule-1b tie in every molecule. -/
theorem compareCanonicalNodeRule_rule1b_eq_of_local_eq
    (left right : RawMolecule.CanonicalBranchNode)
    (hrecord : localRule1bRecord left = localRule1bRecord right) :
    ∀ mol : RawMolecule,
      mol.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule1b left right =
        Ordering.eq := by
  intro mol
  have hdistance : left.rule1bRootDistance = right.rule1bRootDistance := by
    rw [rule1bRootDistance_eq_localStoredDistance left,
      rule1bRootDistance_eq_localStoredDistance right, hrecord]
  show (if left.rule1bRootDistance < right.rule1bRootDistance then Ordering.gt
        else if right.rule1bRootDistance < left.rule1bRootDistance then Ordering.lt
        else Ordering.eq) = Ordering.eq
  rw [hdistance, if_neg (Nat.lt_irrefl _), if_neg (Nat.lt_irrefl _)]

/-- When Rule 1a ties, `compareCanonicalNodeThrough` at stage `.rule1b` is the total Rule-1b
comparator.  This isolates the node-level decision from the Rule-1a label computation. -/
theorem compareCanonicalNodeThrough_rule1b_of_rule1a_eq
    (mol : RawMolecule) (left right : RawMolecule.CanonicalBranchNode)
    (hrule1a : mol.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule1a left right =
      Ordering.eq) :
    mol.compareCanonicalNodeThrough RawMolecule.CanonicalRuleStage.rule1b left right =
      mol.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule1b left right := by
  simp [RawMolecule.compareCanonicalNodeThrough, hrule1a]

/-! ### Profile characterization of generated children -/

/-- Every positive copy seed is a multiple-bond duplicate carrying exactly the parent depth. -/
theorem childOfCopy_positive_rule1bRootDistance
    (node : RawMolecule.CanonicalBranchNode) (atom : ℕ) :
    (Canonical.childOfCopy node (atom, 1)).rule1bRootDistance = node.depth := by
  simp [Canonical.childOfCopy, RawMolecule.CanonicalBranchNode.rule1bRootDistance]

/-- For a forward multiple-bond copy the 2013 observation is the child's own sphere. -/
theorem childOfCopy_forward_bb2013_eq_depth
    (node : RawMolecule.CanonicalBranchNode) (atom : ℕ) (hnotMem : atom ∉ node.history) :
    bb2013Observation .multipleBondDuplicate
        (Canonical.childSpheres node (Canonical.childOfCopy node (atom, 1))) =
      (Canonical.childOfCopy node (atom, 1)).depth := by
  simp [bb2013Observation, Canonical.childSpheres, Canonical.childOfCopy, hnotMem]

/-- Exact if-and-only-if characterization: the 2013 observation of a multiple-bond copy is the
represented atom's branch distance when the atom already occurs in the parent history (a backward
copy) and the child's own sphere otherwise (a forward copy).  This is the additional argument
that the 2013 profile requires and that the local record cannot supply. -/
theorem contextSensitive_bb2013_childOfCopy
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hcopy : copy.2 ≠ 0) :
    bb2013Observation .multipleBondDuplicate
        (Canonical.childSpheres node (Canonical.childOfCopy node copy)) =
      if copy.1 ∈ node.history then RawMolecule.canonicalHistoryDistance node copy.1
      else (Canonical.childOfCopy node copy).depth := by
  by_cases hmem : copy.1 ∈ node.history
  · rw [if_pos hmem]
    exact (Canonical.childOfCopy_multipleBond_backward_reads_history node copy hcopy hmem).1
  · rw [if_neg hmem]
    simp [bb2013Observation, Canonical.childSpheres, Canonical.childOfCopy, hcopy, hmem]

/-- Two generated children with the same stored Rule-1b distance can nevertheless have different
2013 observations.  The hypotheses are exactly the structural facts available from the
construction: one copy atom lies on the parent branch history, the other does not, and the
represented branch distance is not the forward sphere. -/
theorem sameStoredDistance_bb2013_differs
    (node : RawMolecule.CanonicalBranchNode) (backwardAtom forwardAtom : ℕ)
    (hback : backwardAtom ∈ node.history) (hforward : forwardAtom ∉ node.history)
    (hnonempty : 0 < node.history.length)
    (hdistinct : RawMolecule.canonicalHistoryDistance node backwardAtom ≠ node.depth + 1) :
    (Canonical.childOfCopy node (backwardAtom, 1)).rule1bRootDistance =
        (Canonical.childOfCopy node (forwardAtom, 1)).rule1bRootDistance ∧
      bb2013Observation .multipleBondDuplicate
          (Canonical.childSpheres node (Canonical.childOfCopy node (backwardAtom, 1))) ≠
        bb2013Observation .multipleBondDuplicate
          (Canonical.childSpheres node (Canonical.childOfCopy node (forwardAtom, 1))) := by
  refine ⟨?_, ?_⟩
  · rw [childOfCopy_positive_rule1bRootDistance, childOfCopy_positive_rule1bRootDistance]
  · have hbackward :=
      (Canonical.childOfCopy_multipleBond_backward_reads_history node (backwardAtom, 1)
        (by simp) hback).1
    have hforwardObservation := childOfCopy_forward_bb2013_eq_depth node forwardAtom hforward
    have hdepth := Canonical.childOfCopy_depth_eq_parent_add_one node (forwardAtom, 1) hnonempty
    rw [hbackward, hforwardObservation, hdepth]
    exact hdistinct

/-! ### Concrete allene branch witness

Atoms `0 = 1 = 2` (allene).  The digraph root is atom `0`; the branch node `middleNode` is atom
`1` at depth 1.  Its two multiple-bond children `(0, 1)` and `(2, 1)` are both emitted by
`canonicalChildren`.  The backward copy duplicates the root itself, so the 2013 distance is 0,
while the forward copy duplicates the terminal atom at distance 2.  Both stored distances are
the attachment sphere 1.
-/

/-- Carbon atom specification used by the fixture. -/
def carbon : AtomSpec := { element := Element.C }

/-- The allene fixture molecule. -/
def allene : RawMolecule where
  atoms := [carbon, carbon, carbon]
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.double },
      { source := 1, target := 2, kind := ParsedBondKind.double } ]

/-- Digraph root: atom 0. -/
def rootNode : RawMolecule.CanonicalBranchNode where
  atom := 0
  parent := 0
  history := [0]
  provenance := RawMolecule.CanonicalNodeProvenance.realAtom

/-- The middle allene atom reached from the root through the double bond. -/
def middleNode : RawMolecule.CanonicalBranchNode where
  atom := 1
  parent := 0
  history := [1, 0]
  provenance := RawMolecule.CanonicalNodeProvenance.realAtom

/-- Backward multiple-bond child: duplicates the root atom 0. -/
def backwardDuplicate : RawMolecule.CanonicalBranchNode :=
  Canonical.childOfCopy middleNode (0, 1)

/-- Forward multiple-bond child: duplicates the terminal atom 2. -/
def forwardDuplicate : RawMolecule.CanonicalBranchNode :=
  Canonical.childOfCopy middleNode (2, 1)

/-- Source sphere data for the backward duplicate. -/
def backwardSpheres : SphereData := Canonical.childSpheres middleNode backwardDuplicate

/-- Source sphere data for the forward duplicate. -/
def forwardSpheres : SphereData := Canonical.childSpheres middleNode forwardDuplicate

/-- The 2013 profile's pairwise comparison, written directly from the source observation. -/
def sourceCompare (observe : NodeKind → SphereData → ℕ) (leftKind : NodeKind)
    (left : SphereData) (rightKind : NodeKind) (right : SphereData) : Ordering :=
  TetraStereo.OneCenter.MoleculeGraph.compareCloserRootDistance
    (observe leftKind left) (observe rightKind right)

/-! #### Reachability of the witness in the canonical construction -/

theorem middleNode_eq_childOfCopy :
    middleNode = Canonical.childOfCopy rootNode (1, 0) := by decide

theorem copySeed_mem_root :
    (1, 0) ∈ allene.canonicalChildCopies rootNode := by decide

theorem middleNode_mem_canonicalChildren :
    middleNode ∈ allene.canonicalChildren rootNode := by
  rw [middleNode_eq_childOfCopy, Canonical.canonicalChildren_eq_map_childOfCopy]
  rw [if_neg]
  · exact List.mem_map.mpr ⟨(1, 0), copySeed_mem_root, rfl⟩
  · decide

theorem backwardSeed_mem :
    (0, 1) ∈ allene.canonicalChildCopies middleNode := by decide

theorem forwardSeed_mem :
    (2, 1) ∈ allene.canonicalChildCopies middleNode := by decide

theorem backwardDuplicate_eq :
    backwardDuplicate = Canonical.childOfCopy middleNode (0, 1) := rfl

theorem forwardDuplicate_eq :
    forwardDuplicate = Canonical.childOfCopy middleNode (2, 1) := rfl

theorem backwardDuplicate_mem_canonicalChildren :
    backwardDuplicate ∈ allene.canonicalChildren middleNode := by
  rw [backwardDuplicate_eq, Canonical.canonicalChildren_eq_map_childOfCopy]
  rw [if_neg]
  · exact List.mem_map.mpr ⟨(0, 1), backwardSeed_mem, rfl⟩
  · decide

theorem forwardDuplicate_mem_canonicalChildren :
    forwardDuplicate ∈ allene.canonicalChildren middleNode := by
  rw [forwardDuplicate_eq, Canonical.canonicalChildren_eq_map_childOfCopy]
  rw [if_neg]
  · exact List.mem_map.mpr ⟨(2, 1), forwardSeed_mem, rfl⟩
  · decide

/-! #### Basic computed facts about the witness -/

theorem middleNode_depth : middleNode.depth = 1 := by decide

theorem middleNode_history_nonempty : 0 < middleNode.history.length := by decide

theorem backwardAtom_mem_history : (0 : ℕ) ∈ middleNode.history := by decide

theorem forwardAtom_not_mem_history : (2 : ℕ) ∉ middleNode.history := by decide

theorem root_history_distance_zero :
    RawMolecule.canonicalHistoryDistance middleNode 0 = 0 := by decide

theorem backward_stored_distance : backwardDuplicate.rule1bRootDistance = 1 := by decide

theorem forward_stored_distance : forwardDuplicate.rule1bRootDistance = 1 := by decide

theorem backward_representedSphere_zero : backwardSpheres.representedSphere = 0 := by decide

theorem backward_attachedSphere_one : backwardSpheres.attachedSphere = 1 := by decide

theorem forward_representedSphere_two : forwardSpheres.representedSphere = 2 := by decide

theorem forward_attachedSphere_one : forwardSpheres.attachedSphere = 1 := by decide

theorem backward_bb2013_eq_zero :
    bb2013Observation .multipleBondDuplicate backwardSpheres = 0 := by decide

theorem forward_bb2013_eq_two :
    bb2013Observation .multipleBondDuplicate forwardSpheres = 2 := by decide

theorem backward_hanson2018_eq_one :
    hanson2018Observation .multipleBondDuplicate backwardSpheres = 1 := by decide

theorem forward_hanson2018_eq_one :
    hanson2018Observation .multipleBondDuplicate forwardSpheres = 1 := by decide

/-! #### The profile disagreement -/

theorem implementation_rule1b_tie :
    allene.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule1b
      backwardDuplicate forwardDuplicate = Ordering.eq := by decide

/-- The two sibling duplicates also tie under Rule 1a: the allene has no localized mancude ring
edges, so both multiple-bond duplicates receive the duplicated atom's atomic-number label
(carbon 6 in both cases). -/
theorem implementation_rule1a_tie :
    allene.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule1a
      backwardDuplicate forwardDuplicate = Ordering.eq := by decide

/-- The rule-major through-comparator at stage `.rule1b` therefore ties on this pair: this is the
comparison the sibling ranking actually performs once Rule 1a has failed to decide. -/
theorem implementation_through_rule1b_tie :
    allene.compareCanonicalNodeThrough RawMolecule.CanonicalRuleStage.rule1b
      backwardDuplicate forwardDuplicate = Ordering.eq := by
  rw [compareCanonicalNodeThrough_rule1b_of_rule1a_eq allene backwardDuplicate
      forwardDuplicate implementation_rule1a_tie,
    implementation_rule1b_tie]

theorem hanson2018_source_tie :
    sourceCompare hanson2018Observation .multipleBondDuplicate backwardSpheres
      .multipleBondDuplicate forwardSpheres = Ordering.eq := by decide

theorem bb2013_source_strict :
    sourceCompare bb2013Observation .multipleBondDuplicate backwardSpheres
      .multipleBondDuplicate forwardSpheres = Ordering.gt := by decide


theorem stored_distance_matches_hanson2018 :
    backwardDuplicate.rule1bRootDistance =
        hanson2018Observation .multipleBondDuplicate backwardSpheres ∧
      forwardDuplicate.rule1bRootDistance =
        hanson2018Observation .multipleBondDuplicate forwardSpheres := by
  refine ⟨?_, ?_⟩
  · rw [backward_stored_distance, backward_hanson2018_eq_one]
  · rw [forward_stored_distance, forward_hanson2018_eq_one]

/-- The stored distance of the root duplicate is not the 2013 root distance: the provenance
record carries no "is the root" marker. -/
theorem root_clause_not_stored :
    backwardDuplicate.rule1bRootDistance ≠
      bb2013Observation .multipleBondDuplicate backwardSpheres := by
  rw [backward_stored_distance, backward_bb2013_eq_zero]
  decide

/-- The two reachable siblings have equal local records but different 2013 observations. -/
theorem duplicate_local_records_eq :
    localRule1bRecord backwardDuplicate = localRule1bRecord forwardDuplicate := by decide

/-- Main concrete counterexample: equal local records, implementation tie, 2013 strict order. -/
theorem concrete_counterexample :
    localRule1bRecord backwardDuplicate = localRule1bRecord forwardDuplicate ∧
      allene.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule1b
        backwardDuplicate forwardDuplicate = Ordering.eq ∧
      sourceCompare bb2013Observation .multipleBondDuplicate backwardSpheres
        .multipleBondDuplicate forwardSpheres = Ordering.gt := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Pipeline-relevant form of the counterexample: Rule 1a ties, the sibling through-comparator at
stage `.rule1b` ties, but the 2013 Rule-1b comparison of the same pair is strict. -/
theorem concrete_counterexample_through :
    allene.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule1a
        backwardDuplicate forwardDuplicate = Ordering.eq ∧
      allene.compareCanonicalNodeThrough RawMolecule.CanonicalRuleStage.rule1b
        backwardDuplicate forwardDuplicate = Ordering.eq ∧
      sourceCompare bb2013Observation .multipleBondDuplicate backwardSpheres
        .multipleBondDuplicate forwardSpheres = Ordering.gt :=
  ⟨implementation_rule1a_tie, implementation_through_rule1b_tie, bb2013_source_strict⟩

/-- Insufficiency, in existential form: parent separation is implemented by equal stored
distances, but the 2013 observation discriminates the two children. -/
theorem parentSeparation_insufficient_for_2013 :
    ∃ (node : RawMolecule.CanonicalBranchNode) (backwardAtom forwardAtom : ℕ),
      backwardAtom ∈ node.history ∧ forwardAtom ∉ node.history ∧
      (Canonical.childOfCopy node (backwardAtom, 1)).rule1bRootDistance =
        (Canonical.childOfCopy node (forwardAtom, 1)).rule1bRootDistance ∧
      bb2013Observation .multipleBondDuplicate
          (Canonical.childSpheres node (Canonical.childOfCopy node (backwardAtom, 1))) ≠
        bb2013Observation .multipleBondDuplicate
          (Canonical.childSpheres node (Canonical.childOfCopy node (forwardAtom, 1))) := by
  refine ⟨middleNode, 0, 2, backwardAtom_mem_history, forwardAtom_not_mem_history, ?_⟩
  exact sameStoredDistance_bb2013_differs middleNode 0 2 backwardAtom_mem_history
    forwardAtom_not_mem_history middleNode_history_nonempty (by
      rw [root_history_distance_zero, middleNode_depth]
      decide)

end AuxiliarySourceProfileAudit
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.computedFromHigher_congr
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.computedFromHigher_agreesAbove
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.rootReplacement_agreesAbove
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.root_label_not_read
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.rule1bRootDistance_eq_localStoredDistance
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.compareCanonicalNodeRule_rule1b_eq_of_local_eq
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.compareCanonicalNodeThrough_rule1b_of_rule1a_eq
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.childOfCopy_positive_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.childOfCopy_forward_bb2013_eq_depth
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.contextSensitive_bb2013_childOfCopy
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.sameStoredDistance_bb2013_differs
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.middleNode_eq_childOfCopy
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.copySeed_mem_root
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.middleNode_mem_canonicalChildren
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.backwardSeed_mem
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.forwardSeed_mem
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.backwardDuplicate_eq
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.forwardDuplicate_eq
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.backwardDuplicate_mem_canonicalChildren
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.forwardDuplicate_mem_canonicalChildren
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.middleNode_depth
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.middleNode_history_nonempty
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.backwardAtom_mem_history
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.forwardAtom_not_mem_history
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.root_history_distance_zero
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.backward_stored_distance
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.forward_stored_distance
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.backward_representedSphere_zero
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.backward_attachedSphere_one
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.forward_representedSphere_two
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.forward_attachedSphere_one
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.backward_bb2013_eq_zero
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.forward_bb2013_eq_two
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.backward_hanson2018_eq_one
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.forward_hanson2018_eq_one
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.implementation_rule1b_tie
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.implementation_rule1a_tie
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.implementation_through_rule1b_tie
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.hanson2018_source_tie
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.bb2013_source_strict
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.stored_distance_matches_hanson2018
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.root_clause_not_stored
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.duplicate_local_records_eq
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.concrete_counterexample
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.concrete_counterexample_through
assert_kernel_only TetraStereo.OneCenter.AuxiliarySourceProfileAudit.parentSeparation_insufficient_for_2013
