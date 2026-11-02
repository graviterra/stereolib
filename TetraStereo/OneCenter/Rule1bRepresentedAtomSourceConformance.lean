











































import TetraStereo.OneCenter.Rule1bRepresentedAtomObservation
import TetraStereo.OneCenter.Rule1bSourceProfileFidelity
import TetraStereo.OneCenter.SourceProfileRule1bCompiler
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace Rule1bRepresentedAtomSourceConformance

open Rule1bSourceProfile
open Rule1bRepresentedAtomObservation

variable {V : Type*} [DecidableEq V]

/-! ## Definitional bridges -/


theorem officialRepresentedSphere_eq_branchRepresentedSphere (node : OfficialCIPNode V) :
    officialRepresentedSphere node =
      Rule1bSourceProfileCompiler.branchRepresentedSphere node :=
  rfl



theorem officialSourceObservation2013_eq_compiler (node : OfficialCIPNode V) :
    officialSourceObservation2013 node =
      Rule1bSourceProfileCompiler.sourceObservation2013 node :=
  rfl

/-- The low-level canonical child constructor is definitionally the fidelity constructor. -/
theorem canonicalChildOfCopy_eq_fidelity (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ) :
    canonicalChildOfCopy node copy =
      Rule1bSourceProfile.Canonical.childOfCopy node copy :=
  rfl

/-- The low-level `canonicalChildren` decomposition is the fidelity one. -/
theorem canonicalChildren_eq_fidelity_map (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode) :
    mol.canonicalChildren node =
      if node.forcedLeaf then []
      else (mol.canonicalChildCopies node).map
        (Rule1bSourceProfile.Canonical.childOfCopy node) :=
  Rule1bSourceProfile.Canonical.canonicalChildren_eq_map_childOfCopy mol node

/-! ## Constructor conformance -/




theorem officialSourceObservation2013_extend_conformance
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ) :
    officialSourceObservation2013 (parent.extend next copyIndex) =
      bb2013Observation
        (Rule1bSourceProfile.Official.sourceKind
          (parent.childProvenance next copyIndex))
        (Rule1bSourceProfile.Official.extendedSpheres parent next copyIndex) := by
  rw [officialSourceObservation2013_eq_compiler]
  exact Rule1bSourceProfileCompiler.sourceObservation2013_extend_conformance
    parent next copyIndex

/-- **Canonical constructor conformance for the 2013 observation.**  Every actual canonical child
copy satisfies the source equation, split exactly on the copy index and branch membership used by
`canonicalChildren`. -/
theorem canonicalSourceObservation2013_childOfCopy_conformance
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ) :
    canonicalSourceObservation2013 (canonicalChildOfCopy node copy) =
      bb2013Observation
        (Rule1bSourceProfile.Canonical.sourceKind
          (canonicalChildOfCopy node copy).provenance)
        (Rule1bSourceProfile.Canonical.childSpheres node
          (canonicalChildOfCopy node copy)) := by
  by_cases hzero : copy.2 = 0
  · by_cases hmem : copy.1 ∈ node.history
    · rw [canonicalSourceObservation2013_childOfCopy_ring node copy hzero hmem]
      simp [Rule1bSourceProfile.Canonical.sourceKind,
        Rule1bSourceProfile.Canonical.childSpheres, bb2013Observation,
        canonicalChildOfCopy, hzero, hmem]
    · rw [canonicalSourceObservation2013_childOfCopy_real node copy hzero hmem]
      simp [Rule1bSourceProfile.Canonical.sourceKind,
        Rule1bSourceProfile.Canonical.childSpheres, bb2013Observation,
        canonicalChildOfCopy, hzero, hmem]
  · rw [canonicalSourceObservation2013_childOfCopy_positive node copy hzero]
    by_cases hmem : copy.1 ∈ node.history <;>
      simp [Rule1bSourceProfile.Canonical.sourceKind,
        Rule1bSourceProfile.Canonical.childSpheres, bb2013Observation,
        canonicalChildOfCopy, hzero, hmem]

/-! ## Arbitrary generated duplicate-pair agreement -/




theorem official_generated_pair_bb2013_agreement
    (leftParent : OfficialCIPNode V) (leftNext : V) (leftCopyIndex : ℕ)
    (rightParent : OfficialCIPNode V) (rightNext : V) (rightCopyIndex : ℕ) :
    (Rule1bSourceProfileCompiler.compileRule1bDecision officialSourceObservation2013
        (leftParent.extend leftNext leftCopyIndex)
        (rightParent.extend rightNext rightCopyIndex)).outcome =
      sourceRule1bDecision bb2013Observation
        (Rule1bSourceProfile.Official.sourceKind
          (leftParent.childProvenance leftNext leftCopyIndex))
        (Rule1bSourceProfile.Official.extendedSpheres leftParent leftNext leftCopyIndex)
        (bb2013Observation
          (Rule1bSourceProfile.Official.sourceKind
            (rightParent.childProvenance rightNext rightCopyIndex))
          (Rule1bSourceProfile.Official.extendedSpheres
            rightParent rightNext rightCopyIndex)) := by
  rw [Rule1bSourceProfileCompiler.compileRule1bDecision_outcome,
    Rule1bSourceProfile.sourceRule1bDecision_eq_compareCloserRootDistance]
  rw [officialSourceObservation2013_extend_conformance,
    officialSourceObservation2013_extend_conformance]

/-- **Arbitrary generated official DUPLICATE-pair agreement.**  Restriction of the pair agreement to
positive-index copies: both children are genuine multiple-bond duplicates, and the source kind is
`multipleBondDuplicate` on both sides. -/
theorem official_generated_positive_pair_bb2013_agreement
    (leftParent : OfficialCIPNode V) (leftNext : V) (leftCopyIndex : ℕ)
    (rightParent : OfficialCIPNode V) (rightNext : V) (rightCopyIndex : ℕ)
    (hleftCopy : leftCopyIndex ≠ 0) (hrightCopy : rightCopyIndex ≠ 0) :
    (Rule1bSourceProfileCompiler.compileRule1bDecision officialSourceObservation2013
        (leftParent.extend leftNext leftCopyIndex)
        (rightParent.extend rightNext rightCopyIndex)).outcome =
      sourceRule1bDecision bb2013Observation NodeKind.multipleBondDuplicate
        (Rule1bSourceProfile.Official.extendedSpheres leftParent leftNext leftCopyIndex)
        (bb2013Observation NodeKind.multipleBondDuplicate
          (Rule1bSourceProfile.Official.extendedSpheres
            rightParent rightNext rightCopyIndex)) := by
  rw [official_generated_pair_bb2013_agreement]
  simp [Rule1bSourceProfile.Official.sourceKind, OfficialCIPNode.childProvenance,
    hleftCopy, hrightCopy]

/-- **Backward positive-copy pair decision.**  When both represented atoms already occur on their
parent paths, the compiled decision reads exactly the parent history indices. -/
theorem official_generated_backward_pair_decision
    (leftParent : OfficialCIPNode V) (leftNext : V) (leftCopyIndex : ℕ)
    (rightParent : OfficialCIPNode V) (rightNext : V) (rightCopyIndex : ℕ)
    (hleftCopy : leftCopyIndex ≠ 0) (hrightCopy : rightCopyIndex ≠ 0)
    (hleftMem : leftNext ∈ leftParent.history)
    (hrightMem : rightNext ∈ rightParent.history) :
    (Rule1bSourceProfileCompiler.compileRule1bDecision officialSourceObservation2013
        (leftParent.extend leftNext leftCopyIndex)
        (rightParent.extend rightNext rightCopyIndex)).outcome =
      MoleculeGraph.compareCloserRootDistance
        (leftParent.duplicateRootDistance leftNext)
        (rightParent.duplicateRootDistance rightNext) := by
  rw [Rule1bSourceProfileCompiler.compileRule1bDecision_outcome,
    officialSourceObservation2013_extend_multipleBond leftParent leftNext leftCopyIndex hleftCopy,
    officialSourceObservation2013_extend_multipleBond rightParent rightNext rightCopyIndex hrightCopy,
    if_pos hleftMem, if_pos hrightMem]

/-- **Forward positive-copy pair decision.**  When both represented atoms are new, the compiled
decision reads exactly the children's own spheres. -/
theorem official_generated_forward_pair_decision
    (leftParent : OfficialCIPNode V) (leftNext : V) (leftCopyIndex : ℕ)
    (rightParent : OfficialCIPNode V) (rightNext : V) (rightCopyIndex : ℕ)
    (hleftCopy : leftCopyIndex ≠ 0) (hrightCopy : rightCopyIndex ≠ 0)
    (hleftNot : leftNext ∉ leftParent.history)
    (hrightNot : rightNext ∉ rightParent.history) :
    (Rule1bSourceProfileCompiler.compileRule1bDecision officialSourceObservation2013
        (leftParent.extend leftNext leftCopyIndex)
        (rightParent.extend rightNext rightCopyIndex)).outcome =
      MoleculeGraph.compareCloserRootDistance
        (leftParent.extend leftNext leftCopyIndex).depth
        (rightParent.extend rightNext rightCopyIndex).depth := by
  rw [Rule1bSourceProfileCompiler.compileRule1bDecision_outcome,
    officialSourceObservation2013_extend_multipleBond leftParent leftNext leftCopyIndex hleftCopy,
    officialSourceObservation2013_extend_multipleBond rightParent rightNext rightCopyIndex hrightCopy,
    if_neg hleftNot, if_neg hrightNot]

/-- **Arbitrary generated canonical DUPLICATE-pair agreement.**  For any two positive-index canonical
child copies, the comparison of the history-derived 2013 observations equals the comparison of the
source-level 2013 observations on the constructor sphere data.  (`canonicalChildren` has no
compiler hook in this repository; the existing comparator is used directly.) -/
theorem canonical_generated_positive_pair_bb2013_agreement
    (leftNode : RawMolecule.CanonicalBranchNode) (leftCopy : ℕ × ℕ)
    (rightNode : RawMolecule.CanonicalBranchNode) (rightCopy : ℕ × ℕ)
    (hleftCopy : leftCopy.2 ≠ 0) (hrightCopy : rightCopy.2 ≠ 0) :
    MoleculeGraph.compareCloserRootDistance
        (canonicalSourceObservation2013 (canonicalChildOfCopy leftNode leftCopy))
        (canonicalSourceObservation2013 (canonicalChildOfCopy rightNode rightCopy)) =
      MoleculeGraph.compareCloserRootDistance
        (bb2013Observation NodeKind.multipleBondDuplicate
          (Rule1bSourceProfile.Canonical.childSpheres leftNode
            (canonicalChildOfCopy leftNode leftCopy)))
        (bb2013Observation NodeKind.multipleBondDuplicate
          (Rule1bSourceProfile.Canonical.childSpheres rightNode
            (canonicalChildOfCopy rightNode rightCopy))) := by
  rw [canonicalSourceObservation2013_childOfCopy_conformance leftNode leftCopy,
    canonicalSourceObservation2013_childOfCopy_conformance rightNode rightCopy]
  simp [Rule1bSourceProfile.Canonical.sourceKind, canonicalChildOfCopy,
    hleftCopy, hrightCopy]

/-- **Canonical backward positive copy.**  The observation reads the parent history index. -/
theorem canonical_generated_backward_positive_observation
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hcopy : copy.2 ≠ 0) (hmem : copy.1 ∈ node.history) :
    canonicalSourceObservation2013 (canonicalChildOfCopy node copy) =
      RawMolecule.canonicalHistoryDistance node copy.1 := by
  rw [canonicalSourceObservation2013_childOfCopy_positive node copy hcopy, if_pos hmem]

/-- **Canonical forward positive copy.**  The observation reads the child's own sphere. -/
theorem canonical_generated_forward_positive_observation
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hcopy : copy.2 ≠ 0) (hnot : copy.1 ∉ node.history) :
    canonicalSourceObservation2013 (canonicalChildOfCopy node copy) =
      (canonicalChildOfCopy node copy).depth := by
  rw [canonicalSourceObservation2013_childOfCopy_positive node copy hcopy, if_neg hnot]

/-! ## Concrete allene actual-source children

The fixture is the `0 = 1 = 2` allene.  `middleNode` is atom 1 reached from atom 0 with
root-to-node history `[1, 0]`.  The double bond at atom 1 emits two positive copies: a backward
copy of atom 0 (already on the path) and a forward copy of atom 2 (new). -/

namespace Allene

/-- Carbon atom specification used by the fixture. -/
def carbon : AtomSpec := { element := Element.C }

/-- The allene fixture molecule. -/
def molecule : RawMolecule where
  atoms := [carbon, carbon, carbon]
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.double },
      { source := 1, target := 2, kind := ParsedBondKind.double } ]

/-- Middle allene atom reached from the root through the first double bond. -/
def middleNode : RawMolecule.CanonicalBranchNode where
  atom := 1
  parent := 0
  history := [1, 0]
  provenance := RawMolecule.CanonicalNodeProvenance.realAtom

/-- Backward multiple-bond child of the actual canonical constructor: duplicates atom 0. -/
abbrev backwardDuplicate : RawMolecule.CanonicalBranchNode :=
  canonicalChildOfCopy middleNode (0, 1)

/-- Forward multiple-bond child of the actual canonical constructor: duplicates atom 2. -/
abbrev forwardDuplicate : RawMolecule.CanonicalBranchNode :=
  canonicalChildOfCopy middleNode (2, 1)

/-- Source sphere data for the backward duplicate. -/
def backwardSpheres : SphereData :=
  Rule1bSourceProfile.Canonical.childSpheres middleNode backwardDuplicate

/-- Source sphere data for the forward duplicate. -/
def forwardSpheres : SphereData :=
  Rule1bSourceProfile.Canonical.childSpheres middleNode forwardDuplicate

/-! ### Reachability: both children are actually generated -/

theorem middleNode_forcedLeaf : middleNode.forcedLeaf = false := by decide

theorem backwardSeed_mem : (0, 1) ∈ molecule.canonicalChildCopies middleNode := by decide

theorem forwardSeed_mem : (2, 1) ∈ molecule.canonicalChildCopies middleNode := by decide

/-- The backward duplicate is actually emitted by `canonicalChildren`. -/
theorem backwardDuplicate_mem :
    backwardDuplicate ∈ molecule.canonicalChildren middleNode :=
  canonicalChildOfCopy_mem_canonicalChildren molecule middleNode (0, 1)
    backwardSeed_mem middleNode_forcedLeaf

/-- The forward duplicate is actually emitted by `canonicalChildren`. -/
theorem forwardDuplicate_mem :
    forwardDuplicate ∈ molecule.canonicalChildren middleNode :=
  canonicalChildOfCopy_mem_canonicalChildren molecule middleNode (2, 1)
    forwardSeed_mem middleNode_forcedLeaf

/-! ### Computed facts -/

theorem middleNode_depth : middleNode.depth = 1 := by decide

theorem backwardAtom_mem : (0 : ℕ) ∈ middleNode.history := by decide

theorem forwardAtom_not_mem : (2 : ℕ) ∉ middleNode.history := by decide

theorem backward_distance_zero :
    RawMolecule.canonicalHistoryDistance middleNode 0 = 0 := by decide

theorem backward_stored_distance : backwardDuplicate.rule1bRootDistance = 1 := by decide

theorem forward_stored_distance : forwardDuplicate.rule1bRootDistance = 1 := by decide

/-- The observer on the actual backward child reads the parent history index. -/
theorem backward_representedSphere :
    canonicalRepresentedSphere? backwardDuplicate =
      some (RawMolecule.canonicalHistoryDistance middleNode 0) :=
  canonicalRepresentedSphere?_canonicalChildOfCopy_of_mem middleNode (0, 1) (by decide)

/-- The observer on the actual forward child reads the child's own sphere. -/
theorem forward_representedSphere :
    canonicalRepresentedSphere? forwardDuplicate = some forwardDuplicate.depth :=
  canonicalRepresentedSphere?_canonicalChildOfCopy_of_not_mem middleNode (2, 1) (by decide)

/-- The forward child's own sphere is 2. -/
theorem forward_depth : forwardDuplicate.depth = 2 := by decide

/-- The backward child's observation is 0. -/
theorem backward_representedSphere_eq : canonicalRepresentedSphere? backwardDuplicate = some 0 := by
  rw [backward_representedSphere, backward_distance_zero]

/-- The forward child's observation is 2. -/
theorem forward_representedSphere_eq : canonicalRepresentedSphere? forwardDuplicate = some 2 := by
  rw [forward_representedSphere, forward_depth]

/-- Observation success certifies actual path membership for the backward child. -/
theorem backward_observer_mem : (0 : ℕ) ∈ backwardDuplicate.history :=
  (canonicalRepresentedSphere?_eq_some_imp_mem backwardDuplicate 0
    backward_representedSphere_eq).1

/-- Observation success certifies actual path membership for the forward child. -/
theorem forward_observer_mem : (2 : ℕ) ∈ forwardDuplicate.history :=
  (canonicalRepresentedSphere?_eq_some_imp_mem forwardDuplicate 2
    forward_representedSphere_eq).1

/-! ### Source observations and the strict/tie contrast -/

theorem backward_source_observation :
    canonicalSourceObservation2013 backwardDuplicate = 0 := by decide

theorem forward_source_observation :
    canonicalSourceObservation2013 forwardDuplicate = 2 := by decide

theorem backward_bb2013 :
    bb2013Observation NodeKind.multipleBondDuplicate backwardSpheres = 0 := by decide

theorem forward_bb2013 :
    bb2013Observation NodeKind.multipleBondDuplicate forwardSpheres = 2 := by decide

/-- The actual backward child satisfies the 2013 source equation. -/
theorem backward_actual_source_conformance :
    canonicalSourceObservation2013 backwardDuplicate =
      bb2013Observation NodeKind.multipleBondDuplicate backwardSpheres := by
  rw [backward_source_observation, backward_bb2013]

/-- The actual forward child satisfies the 2013 source equation. -/
theorem forward_actual_source_conformance :
    canonicalSourceObservation2013 forwardDuplicate =
      bb2013Observation NodeKind.multipleBondDuplicate forwardSpheres := by
  rw [forward_source_observation, forward_bb2013]

/-- The 2013 represented distances on the two actual children are strict: 0 versus 2. -/
theorem source_distances_strict :
    MoleculeGraph.compareCloserRootDistance
        (canonicalSourceObservation2013 backwardDuplicate)
        (canonicalSourceObservation2013 forwardDuplicate) = Ordering.gt := by
  rw [backward_source_observation, forward_source_observation]
  decide

/-- The stored 2018 distances on the same two children tie at 1. -/
theorem stored_distances_tie :
    MoleculeGraph.compareCloserRootDistance
        backwardDuplicate.rule1bRootDistance
        forwardDuplicate.rule1bRootDistance = Ordering.eq := by
  rw [backward_stored_distance, forward_stored_distance]
  decide

/-- The source-level 2013 decision between the two actual children is strict. -/
theorem source_decision_strict :
    sourceRule1bDecision bb2013Observation NodeKind.multipleBondDuplicate
        backwardSpheres
        (bb2013Observation NodeKind.multipleBondDuplicate forwardSpheres) =
      Ordering.gt := by
  rw [sourceRule1bDecision_eq_compareCloserRootDistance, backward_bb2013, forward_bb2013]
  decide

/-- The generated-pair agreement instantiated on the allene children. -/
theorem generated_pair_agreement :
    MoleculeGraph.compareCloserRootDistance
        (canonicalSourceObservation2013 backwardDuplicate)
        (canonicalSourceObservation2013 forwardDuplicate) =
      MoleculeGraph.compareCloserRootDistance
        (bb2013Observation NodeKind.multipleBondDuplicate backwardSpheres)
        (bb2013Observation NodeKind.multipleBondDuplicate forwardSpheres) :=
  canonical_generated_positive_pair_bb2013_agreement middleNode (0, 1) middleNode (2, 1)
    (by decide) (by decide)

/-- Backward child: the total observation reads the parent history index. -/
theorem backward_uses_history :
    canonicalSourceObservation2013 backwardDuplicate =
      RawMolecule.canonicalHistoryDistance middleNode 0 :=
  canonical_generated_backward_positive_observation middleNode (0, 1)
    (by decide) (by decide)

/-- Forward child: the total observation reads the child's own sphere. -/
theorem forward_uses_depth :
    canonicalSourceObservation2013 forwardDuplicate = forwardDuplicate.depth :=
  canonical_generated_forward_positive_observation middleNode (2, 1)
    (by decide) (by decide)

/-! ### Official allene children -/

/-- Official counterpart of the allene middle node. -/
def officialMiddleNode : OfficialCIPNode ℕ where
  current? := some 1
  history := [1, 0]
  provenance := OfficialCIPNodeProvenance.realAtom

/-- Official backward positive copy of atom 0. -/
abbrev officialBackwardDuplicate : OfficialCIPNode ℕ := officialMiddleNode.extend 0 1

/-- Official forward positive copy of atom 2. -/
abbrev officialForwardDuplicate : OfficialCIPNode ℕ := officialMiddleNode.extend 2 1

theorem officialMiddleNode_depth : officialMiddleNode.depth = 1 := by decide

theorem officialBackward_mem : (0 : ℕ) ∈ officialMiddleNode.history := by decide

theorem officialForward_not_mem : (2 : ℕ) ∉ officialMiddleNode.history := by decide

theorem official_backward_observation :
    officialSourceObservation2013 officialBackwardDuplicate = 0 := by
  rw [officialSourceObservation2013_extend_multipleBond officialMiddleNode 0 1 (by decide),
    if_pos officialBackward_mem]
  decide

theorem official_forward_observation :
    officialSourceObservation2013 officialForwardDuplicate = 2 := by
  rw [officialSourceObservation2013_extend_multipleBond officialMiddleNode 2 1 (by decide),
    if_neg officialForward_not_mem]
  decide

theorem official_backward_stored : officialBackwardDuplicate.rule1bRootDistance = 1 := by
  decide

theorem official_forward_stored : officialForwardDuplicate.rule1bRootDistance = 1 := by
  decide

/-- The official stored 2018 distances tie at 1. -/
theorem official_stored_tie :
    MoleculeGraph.compareCloserRootDistance
        officialBackwardDuplicate.rule1bRootDistance
        officialForwardDuplicate.rule1bRootDistance = Ordering.eq := by
  rw [official_backward_stored, official_forward_stored]
  decide


theorem official_compiled_source_strict :
    (Rule1bSourceProfileCompiler.compileRule1bDecision officialSourceObservation2013
        officialBackwardDuplicate officialForwardDuplicate).outcome = Ordering.gt := by
  rw [Rule1bSourceProfileCompiler.compileRule1bDecision_outcome,
    official_backward_observation, official_forward_observation]
  decide

/-- The generated official duplicate-pair agreement instantiated on the allene. -/
theorem official_generated_pair_agreement :
    (Rule1bSourceProfileCompiler.compileRule1bDecision officialSourceObservation2013
        officialBackwardDuplicate officialForwardDuplicate).outcome =
      sourceRule1bDecision bb2013Observation NodeKind.multipleBondDuplicate
        (Rule1bSourceProfile.Official.extendedSpheres officialMiddleNode 0 1)
        (bb2013Observation NodeKind.multipleBondDuplicate
          (Rule1bSourceProfile.Official.extendedSpheres officialMiddleNode 2 1)) :=
  official_generated_positive_pair_bb2013_agreement officialMiddleNode 0 1
    officialMiddleNode 2 1 (by decide) (by decide)

/-- The official backward child's observation reads the parent history index. -/
theorem official_backward_uses_history :
    officialSourceObservation2013 officialBackwardDuplicate =
      officialMiddleNode.duplicateRootDistance 0 := by
  rw [officialSourceObservation2013_extend_multipleBond officialMiddleNode 0 1 (by decide),
    if_pos officialBackward_mem]

/-- The official forward child's observation reads the child's own sphere. -/
theorem official_forward_uses_depth :
    officialSourceObservation2013 officialForwardDuplicate = officialForwardDuplicate.depth := by
  rw [officialSourceObservation2013_extend_multipleBond officialMiddleNode 2 1 (by decide),
    if_neg officialForward_not_mem]

end Allene

end Rule1bRepresentedAtomSourceConformance
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.officialRepresentedSphere_eq_branchRepresentedSphere
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.officialSourceObservation2013_eq_compiler
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.canonicalChildOfCopy_eq_fidelity
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.canonicalChildren_eq_fidelity_map
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.officialSourceObservation2013_extend_conformance
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.canonicalSourceObservation2013_childOfCopy_conformance
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.official_generated_pair_bb2013_agreement
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.official_generated_positive_pair_bb2013_agreement
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.official_generated_backward_pair_decision
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.official_generated_forward_pair_decision
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.canonical_generated_positive_pair_bb2013_agreement
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.canonical_generated_backward_positive_observation
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.canonical_generated_forward_positive_observation
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.middleNode_forcedLeaf
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.backwardSeed_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.forwardSeed_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.backwardDuplicate_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.forwardDuplicate_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.middleNode_depth
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.backwardAtom_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.forwardAtom_not_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.backward_distance_zero
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.backward_stored_distance
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.forward_stored_distance
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.backward_representedSphere
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.forward_representedSphere
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.forward_depth
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.backward_representedSphere_eq
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.forward_representedSphere_eq
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.backward_observer_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.forward_observer_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.backward_source_observation
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.forward_source_observation
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.backward_bb2013
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.forward_bb2013
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.backward_actual_source_conformance
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.forward_actual_source_conformance
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.source_distances_strict
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.stored_distances_tie
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.source_decision_strict
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.generated_pair_agreement
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.backward_uses_history
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.forward_uses_depth
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.officialMiddleNode_depth
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.officialBackward_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.officialForward_not_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.official_backward_observation
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.official_forward_observation
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.official_backward_stored
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.official_forward_stored
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.official_stored_tie
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.official_compiled_source_strict
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.official_generated_pair_agreement
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.official_backward_uses_history
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomSourceConformance.Allene.official_forward_uses_depth
