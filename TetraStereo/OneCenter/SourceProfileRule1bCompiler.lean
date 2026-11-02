



















































import TetraStereo.OneCenter.Rule1bSourceProfileFidelity

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace Rule1bSourceProfileCompiler

open Rule1bSourceProfile

variable {V : Type*} [DecidableEq V]

/-! ## The single observation-parametric compiler hook -/

/-- The sphere at which the atom represented by `node` occurs on the actual branch history.

This is derived only from the node's `current?` atom and its `history`; the distance stored in the
provenance is not consulted.  Consequences:

* a ring-closure duplicate or a backward multiple-bond copy (the atom already occurs on the parent
  path) reads the index of the existing occurrence;
* a forward multiple-bond copy (the atom has not yet occurred on the parent path) reads the index of
  the node's own occurrence, which is the sphere of the real copy of the duplicated atom;
* a real child also reads its own sphere.

The `none`/missing fallback is a totality convention for nodes that are not constructor-generated
from a nonempty branch; it is not a source rule. -/
def branchRepresentedSphere (node : OfficialCIPNode V) : ℕ :=
  match node.current? with
  | some atom => (firstIndexOf? atom node.history.reverse).getD node.depth
  | none => node.depth

/-- The 2013 represented-atom observation of an actual official node.

The duplicate branches derive the represented sphere from the branch history via
`branchRepresentedSphere`; the stored provenance distance is never read.

The `realAtom` branch (the node's own sphere) is the **shared comparison-totality convention** used
by the existing total observation.  It is deliberately *not* presented as a normative 2013 clause:
P-92.1.3.1(b) and P-92.2.2 only rank duplicate nodes.  The `placeholder` branch likewise uses the
stored placeholder sphere only to keep the observation total. -/
def sourceObservation2013 (node : OfficialCIPNode V) : ℕ :=
  match node.provenance with
  | OfficialCIPNodeProvenance.realAtom => node.depth
  | OfficialCIPNodeProvenance.multipleBondDuplicate _ => branchRepresentedSphere node
  | OfficialCIPNodeProvenance.ringDuplicate _ => branchRepresentedSphere node
  | OfficialCIPNodeProvenance.placeholder _ distance => distance

/-- Compilation of a source profile to one total observation on actual official nodes.

This is the whole profile-dependent surface of the Rule-1b compiler.  Everything downstream is the
existing comparator. -/
def profileObservation (profile : SourceProfile) (node : OfficialCIPNode V) : ℕ :=
  match profile with
  | .bb2013 => sourceObservation2013 node
  | .hanson2018Proposed => node.rule1bRootDistance

@[simp] theorem profileObservation_bb2013 (node : OfficialCIPNode V) :
    profileObservation .bb2013 node = sourceObservation2013 node :=
  rfl

@[simp] theorem profileObservation_hanson2018Proposed (node : OfficialCIPNode V) :
    profileObservation .hanson2018Proposed node = node.rule1bRootDistance :=
  rfl

/-- The shared Rule-1b decision constructor.  It is parameterized by the observation and delegates
the entire comparison to the existing total comparator `compareCloserRootDistance`. -/
def compileRule1bDecision (observe : OfficialCIPNode V → ℕ)
    (left right : OfficialCIPNode V) : CIPRuleDecision where
  rule := CIPRuleFamily.duplicateAtom
  outcome := MoleculeGraph.compareCloserRootDistance (observe left) (observe right)

omit [DecidableEq V] in
/-- Both source profiles use exactly the same comparator; only the observation differs. -/
theorem compileRule1bDecision_outcome (observe : OfficialCIPNode V → ℕ)
    (left right : OfficialCIPNode V) :
    (compileRule1bDecision observe left right).outcome =
      MoleculeGraph.compareCloserRootDistance (observe left) (observe right) :=
  rfl




theorem compileRule1bDecision_hanson2018_eq_stored
    (left right : OfficialCIPNode V) :
    compileRule1bDecision (profileObservation .hanson2018Proposed) left right =
      MoleculeGraph.duplicateRootDistanceDecision left right :=
  rfl

omit [DecidableEq V] in
/-- **Conditional comparator equivalence.**  If two observation functions agree on both compared
nodes, the compiled decisions are equal.  This is the only general equivalence statement; any
stronger claim needs the pointwise hypotheses (or a source-specific proof). -/
theorem compileRule1bDecision_eq_of_observe_eq
    (first second : OfficialCIPNode V → ℕ)
    (left right : OfficialCIPNode V)
    (hleft : first left = second left) (hright : first right = second right) :
    compileRule1bDecision first left right = compileRule1bDecision second left right := by
  simp [compileRule1bDecision, hleft, hright]

/-! ## Path-index lemmas for the derived represented sphere -/

/-- If `firstIndexOf?` succeeds on `left`, appending a suffix does not change it. -/
theorem firstIndexOf?_append_eq_left_of_found {α : Type*} [DecidableEq α]
    (target : α) :
    ∀ (left right : List α), (∃ index, firstIndexOf? target left = some index) →
      firstIndexOf? target (left ++ right) = firstIndexOf? target left
  | [], _right, ⟨_index, found⟩ => by
      simp [firstIndexOf?] at found
  | value :: values, right, ⟨index, found⟩ => by
      by_cases head : value = target
      · simp [firstIndexOf?, head]
      · have tailFound : ∃ tailIndex, firstIndexOf? target values = some tailIndex := by
          have mapped : (firstIndexOf? target values).map Nat.succ = some index := by
            simpa [firstIndexOf?, head] using found
          obtain ⟨tailIndex, tailValue, _⟩ := Option.map_eq_some_iff.mp mapped
          exact ⟨tailIndex, tailValue⟩
        have ih := firstIndexOf?_append_eq_left_of_found target values right tailFound
        simp [firstIndexOf?, head, ih]

/-- If the target does not occur in `left`, then in `left ++ [target]` it is first found at the end,
i.e. at index `left.length`. -/
theorem firstIndexOf?_append_singleton_of_not_mem {α : Type*} [DecidableEq α]
    (target : α) :
    ∀ (left : List α), target ∉ left →
      firstIndexOf? target (left ++ [target]) = some left.length
  | [], _hnot => by
      simp
  | value :: values, hnot => by
      have head : value ≠ target := by
        intro equal
        exact hnot (by simp [equal])
      have tailNot : target ∉ values := by
        intro present
        exact hnot (List.mem_cons_of_mem value present)
      have ih := firstIndexOf?_append_singleton_of_not_mem target values tailNot
      simp [firstIndexOf?, head, ih]

/-! ## Constructor conformance: `OfficialCIPNode.extend` -/

/-- Unfolded form of the derived sphere on an extension. -/
theorem branchRepresentedSphere_extend (parent : OfficialCIPNode V) (next : V)
    (copyIndex : ℕ) :
    branchRepresentedSphere (parent.extend next copyIndex) =
      (firstIndexOf? next (parent.history.reverse ++ [next])).getD
        (parent.extend next copyIndex).depth := by
  simp [branchRepresentedSphere, OfficialCIPNode.extend]

/-- If the duplicated atom already occurs on the parent branch, the derived represented sphere is
the existing path index, i.e. `parent.duplicateRootDistance next`. -/
theorem branchRepresentedSphere_extend_of_mem (parent : OfficialCIPNode V) (next : V)
    (copyIndex : ℕ) (hmem : next ∈ parent.history) :
    branchRepresentedSphere (parent.extend next copyIndex) =
      parent.duplicateRootDistance next := by
  obtain ⟨index, found⟩ :=
    firstIndexOf?_eq_some_of_mem next (List.mem_reverse.mpr hmem)
  have appended :=
    firstIndexOf?_append_eq_left_of_found next parent.history.reverse [next] ⟨index, found⟩
  rw [branchRepresentedSphere_extend, appended, found]
  simp [OfficialCIPNode.duplicateRootDistance, found]

/-- If the duplicated atom does not occur on the parent branch, the derived represented sphere is
the extension's own sphere, i.e. the sphere of the real copy of the duplicated atom. -/
theorem branchRepresentedSphere_extend_of_not_mem (parent : OfficialCIPNode V) (next : V)
    (copyIndex : ℕ) (hnot : next ∉ parent.history) :
    branchRepresentedSphere (parent.extend next copyIndex) =
      (parent.extend next copyIndex).depth := by
  have hnotReverse : next ∉ parent.history.reverse := by
    simpa using hnot
  have appended :=
    firstIndexOf?_append_singleton_of_not_mem next parent.history.reverse hnotReverse
  rw [branchRepresentedSphere_extend, appended]
  simp only [Option.getD_some]
  have hdepth : (parent.extend next copyIndex).depth = parent.history.length := by
    simp [OfficialCIPNode.depth]
  rw [hdepth, List.length_reverse]

/-- **Real constructor case.**  A zero-index copy of an atom not on the branch is a real atom.  Its
2013 observation is its own sphere (the shared totality convention, not a normative 2013 clause). -/
theorem sourceObservation2013_extend_real (parent : OfficialCIPNode V) (next : V)
    (hnot : next ∉ parent.history) :
    sourceObservation2013 (parent.extend next 0) =
      bb2013Observation .realAtom (Official.extendedSpheres parent next 0) := by
  simp [sourceObservation2013, bb2013Observation, Official.extendedSpheres,
    OfficialCIPNode.extend, OfficialCIPNode.childProvenance, hnot]

/-- **Ring-closure constructor case.**  A zero-index copy of an atom already on the branch creates a
ring duplicate.  The derived represented sphere is the existing path index of that atom, exactly
the 2013 observation. -/
theorem sourceObservation2013_extend_ring (parent : OfficialCIPNode V) (next : V)
    (hmem : next ∈ parent.history) :
    sourceObservation2013 (parent.extend next 0) =
      bb2013Observation .ringClosureDuplicate (Official.extendedSpheres parent next 0) := by
  have unfoldSource :
      sourceObservation2013 (parent.extend next 0) =
        branchRepresentedSphere (parent.extend next 0) := by
    simp [sourceObservation2013, OfficialCIPNode.extend,
      OfficialCIPNode.childProvenance, hmem]
  have branch := branchRepresentedSphere_extend_of_mem parent next 0 hmem
  rw [unfoldSource, branch]
  simp [bb2013Observation, Official.extendedSpheres, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, hmem]

/-- **Forward multiple-bond case.**  A positive-index copy of an atom not yet on the branch is a
forward multiple-bond duplicate.  The 2013 represented sphere is the extension's own sphere. -/
theorem sourceObservation2013_extend_multipleBond_forward
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ)
    (hcopy : copyIndex ≠ 0) (hnot : next ∉ parent.history) :
    sourceObservation2013 (parent.extend next copyIndex) =
      bb2013Observation .multipleBondDuplicate
        (Official.extendedSpheres parent next copyIndex) := by
  have unfoldSource :
      sourceObservation2013 (parent.extend next copyIndex) =
        branchRepresentedSphere (parent.extend next copyIndex) := by
    simp [sourceObservation2013, OfficialCIPNode.extend,
      OfficialCIPNode.childProvenance, hcopy]
  have branch := branchRepresentedSphere_extend_of_not_mem parent next copyIndex hnot
  rw [unfoldSource, branch]
  simp [bb2013Observation, Official.extendedSpheres, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, hcopy, hnot]

/-- **Backward multiple-bond case.**  A positive-index copy of an atom already on the branch is a
backward multiple-bond duplicate.  The 2013 represented sphere is the existing path index. -/
theorem sourceObservation2013_extend_multipleBond_backward
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ)
    (hcopy : copyIndex ≠ 0) (hmem : next ∈ parent.history) :
    sourceObservation2013 (parent.extend next copyIndex) =
      bb2013Observation .multipleBondDuplicate
        (Official.extendedSpheres parent next copyIndex) := by
  have unfoldSource :
      sourceObservation2013 (parent.extend next copyIndex) =
        branchRepresentedSphere (parent.extend next copyIndex) := by
    simp [sourceObservation2013, OfficialCIPNode.extend,
      OfficialCIPNode.childProvenance, hcopy]
  have branch := branchRepresentedSphere_extend_of_mem parent next copyIndex hmem
  rw [unfoldSource, branch]
  simp [bb2013Observation, Official.extendedSpheres, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, hcopy, hmem]

/-- The multiple-bond constructor case, split internally on branch membership. -/
theorem sourceObservation2013_extend_multipleBond
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ)
    (hcopy : copyIndex ≠ 0) :
    sourceObservation2013 (parent.extend next copyIndex) =
      bb2013Observation .multipleBondDuplicate
        (Official.extendedSpheres parent next copyIndex) := by
  by_cases hmem : next ∈ parent.history
  · exact sourceObservation2013_extend_multipleBond_backward parent next copyIndex hcopy hmem
  · exact sourceObservation2013_extend_multipleBond_forward parent next copyIndex hcopy hmem

/-- **Every one-step official extension conforms to the derived 2013 observation equation**, with the
source node kind taken from the actual constructor provenance. -/
theorem sourceObservation2013_extend_conformance
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ) :
    sourceObservation2013 (parent.extend next copyIndex) =
      bb2013Observation (Official.sourceKind (parent.childProvenance next copyIndex))
        (Official.extendedSpheres parent next copyIndex) := by
  by_cases hzero : copyIndex = 0
  · subst copyIndex
    by_cases hmem : next ∈ parent.history
    · simpa [OfficialCIPNode.childProvenance, hmem, Official.sourceKind] using
        sourceObservation2013_extend_ring parent next hmem
    · simpa [OfficialCIPNode.childProvenance, hmem, Official.sourceKind] using
        sourceObservation2013_extend_real parent next hmem
  · simpa [OfficialCIPNode.childProvenance, hzero, Official.sourceKind] using
      sourceObservation2013_extend_multipleBond parent next copyIndex hzero

/-- **The shared hook conforms for either source profile.**  The 2018 branch reuses the existing
`Official.constructor_implements_hanson2018` theorem directly, so the two profiles are two
instantiations of one compiler rather than two solvers. -/
theorem profileObservation_extend_conformance
    (profile : SourceProfile) (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ) :
    profileObservation profile (parent.extend next copyIndex) =
      observation profile (Official.sourceKind (parent.childProvenance next copyIndex))
        (Official.extendedSpheres parent next copyIndex) := by
  cases profile with
  | bb2013 =>
      simpa [profileObservation, observation] using
        sourceObservation2013_extend_conformance parent next copyIndex
  | hanson2018Proposed =>
      simpa [profileObservation, observation] using
        Official.constructor_implements_hanson2018 parent next copyIndex

/-! ## Where the profiles agree and where they differ at the constructor -/

/-- Real constructor case: the 2013 totality value and the 2018 observation coincide. -/
theorem sourceObservation2013_extend_real_eq_hanson2018
    (parent : OfficialCIPNode V) (next : V) (hnot : next ∉ parent.history) :
    sourceObservation2013 (parent.extend next 0) =
      hanson2018Observation .realAtom (Official.extendedSpheres parent next 0) := by
  rw [sourceObservation2013_extend_real parent next hnot]
  exact bb2013Observation_eq_hanson2018Observation_of_not_multipleBond
    .realAtom _ (by intro equal; cases equal)

/-- Ring-closure constructor case: both profiles read the same represented sphere. -/
theorem sourceObservation2013_extend_ring_eq_hanson2018
    (parent : OfficialCIPNode V) (next : V) (hmem : next ∈ parent.history) :
    sourceObservation2013 (parent.extend next 0) =
      hanson2018Observation .ringClosureDuplicate (Official.extendedSpheres parent next 0) := by
  rw [sourceObservation2013_extend_ring parent next hmem]
  exact bb2013Observation_eq_hanson2018Observation_of_not_multipleBond
    .ringClosureDuplicate _ (by intro equal; cases equal)

/-- Real constructor case: the derived 2013 value equals the implemented stored distance. -/
theorem sourceObservation2013_extend_real_eq_stored
    (parent : OfficialCIPNode V) (next : V) (hnot : next ∉ parent.history) :
    sourceObservation2013 (parent.extend next 0) =
      (parent.extend next 0).rule1bRootDistance := by
  rw [sourceObservation2013_extend_real_eq_hanson2018 parent next hnot,
    Official.extend_real_implements_hanson2018 parent next hnot]

/-- Ring-closure constructor case: the derived 2013 value equals the implemented stored distance. -/
theorem sourceObservation2013_extend_ring_eq_stored
    (parent : OfficialCIPNode V) (next : V) (hmem : next ∈ parent.history) :
    sourceObservation2013 (parent.extend next 0) =
      (parent.extend next 0).rule1bRootDistance := by
  rw [sourceObservation2013_extend_ring_eq_hanson2018 parent next hmem,
    Official.extend_ring_implements_hanson2018 parent next hmem]

/-- **Forward multiple-bond constructor case: exact values and genuine profile difference.**

On a nonempty branch the extension's own sphere is one beyond the attachment sphere, so the derived
2013 observation and the stored (2018) observation differ.  This is the only constructor case in
which the profiles are proved to differ; the backward case below is not claimed to differ. -/
theorem sourceObservation2013_extend_multipleBond_forward_ne_stored
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ)
    (hcopy : copyIndex ≠ 0) (hnot : next ∉ parent.history)
    (hnonempty : 0 < parent.history.length) :
    sourceObservation2013 (parent.extend next copyIndex) =
        (parent.extend next copyIndex).depth ∧
      (parent.extend next copyIndex).rule1bRootDistance = parent.depth ∧
      sourceObservation2013 (parent.extend next copyIndex) ≠
        (parent.extend next copyIndex).rule1bRootDistance := by
  have hsource :
      sourceObservation2013 (parent.extend next copyIndex) =
        (parent.extend next copyIndex).depth := by
    rw [sourceObservation2013_extend_multipleBond_forward parent next copyIndex hcopy hnot]
    simp [bb2013Observation, Official.extendedSpheres, OfficialCIPNode.childProvenance,
      hcopy, hnot]
  have hstored :
      (parent.extend next copyIndex).rule1bRootDistance = parent.depth := by
    simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
      OfficialCIPNode.childProvenance, hcopy]
  refine ⟨hsource, hstored, ?_⟩
  rw [hsource, hstored]
  have hdepth := Official.extend_depth_eq_attached_add_one parent next copyIndex hnonempty
  rw [hdepth]
  exact Nat.succ_ne_self parent.depth

/-- **Backward multiple-bond constructor case.**  If the duplicated atom already occurs on the
parent path, the derived 2013 observation is an actual existing path index, while the stored (2018)
observation is the attachment sphere.  The indices may or may not differ; no distinction is claimed
here. -/
theorem sourceObservation2013_extend_multipleBond_backward_reads_history
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ)
    (hcopy : copyIndex ≠ 0) (hmem : next ∈ parent.history) :
    sourceObservation2013 (parent.extend next copyIndex) = parent.duplicateRootDistance next ∧
      parent.history.reverse[parent.duplicateRootDistance next]? = some next ∧
      (parent.extend next copyIndex).rule1bRootDistance = parent.depth := by
  refine ⟨?_, Official.duplicateRootDistance_indexes_represented parent next hmem, ?_⟩
  · rw [sourceObservation2013_extend_multipleBond_backward parent next copyIndex hcopy hmem]
    simp [bb2013Observation, Official.extendedSpheres, OfficialCIPNode.childProvenance,
      hcopy, hmem]
  · simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
      OfficialCIPNode.childProvenance, hcopy]

/-- Restricted comparator equivalence: if the derived 2013 observation coincides with the stored
distance on both compared nodes, the two compiled decisions coincide.  This covers, in particular,
real and ring-closure constructor cases via the two `_eq_stored` lemmas above. -/
theorem compile_decisions_eq_of_sourceObservation_eq_stored
    {left right : OfficialCIPNode V}
    (hleft : sourceObservation2013 left = left.rule1bRootDistance)
    (hright : sourceObservation2013 right = right.rule1bRootDistance) :
    compileRule1bDecision (profileObservation .bb2013) left right =
      compileRule1bDecision (profileObservation .hanson2018Proposed) left right := by
  simp [compileRule1bDecision, profileObservation, hleft, hright]

/-- Concrete restricted equivalence: a real extension against a ring-closure extension.  Each source
profile compiles to the same decision on this pair. -/
theorem compile_decisions_eq_on_real_and_ring_extensions
    (parentLeft : OfficialCIPNode V) (nextLeft : V) (hnotLeft : nextLeft ∉ parentLeft.history)
    (parentRight : OfficialCIPNode V) (nextRight : V) (hmemRight : nextRight ∈ parentRight.history) :
    compileRule1bDecision (profileObservation .bb2013)
        (parentLeft.extend nextLeft 0) (parentRight.extend nextRight 0) =
      compileRule1bDecision (profileObservation .hanson2018Proposed)
        (parentLeft.extend nextLeft 0) (parentRight.extend nextRight 0) :=
  compile_decisions_eq_of_sourceObservation_eq_stored
    (sourceObservation2013_extend_real_eq_stored parentLeft nextLeft hnotLeft)
    (sourceObservation2013_extend_ring_eq_stored parentRight nextRight hmemRight)

/-! ## Concrete counterexample: comparator equivalence fails on a forward duplicate

The fixture is the official analogue of the pinned P-92.2.2 branch used by the fidelity module:
the branch is `C5 -> C4 -> C3` (sphere 2 at C3), and the double bond contributes a forward
multiple-bond duplicate of C2 at sphere 3.  The stored distance is the attachment sphere 2, whereas
the 2013 represented C2 occurs at sphere 3.

Against the real node at sphere 2, the stored observations tie (2 = 2), while the 2013 observations
are 3 and 2.  Hence the compiled Rule-1b decisions differ: `eq` under the implemented 2018
compilation versus `lt` under the 2013 compilation.  No global comparator equivalence is claimed.
-/

namespace Concrete

/-- Root at atom 5. -/
def root5 : OfficialCIPNode ℕ := OfficialCIPNode.root 5

/-- C5 -> C4 branch node at sphere 1. -/
def node4 : OfficialCIPNode ℕ := root5.extend 4 0

/-- C5 -> C4 -> C3 branch node at sphere 2. -/
def node3 : OfficialCIPNode ℕ := node4.extend 3 0

/-- Forward multiple-bond duplicate of C2 attached to C3.  Its stored distance is the attachment
sphere 2; its 2013 represented sphere is the real C2 copy at sphere 3. -/
def forwardDuplicateC2 : OfficialCIPNode ℕ := node3.extend 2 1

theorem node3_depth : node3.depth = 2 := by decide

theorem node3_stored : node3.rule1bRootDistance = 2 := by decide

theorem node3_sourceObservation2013 : sourceObservation2013 node3 = 2 := by decide

theorem forwardDuplicate_depth : forwardDuplicateC2.depth = 3 := by decide

theorem forwardDuplicate_stored : forwardDuplicateC2.rule1bRootDistance = 2 := by decide

/-- The derived 2013 represented sphere is 3 (the real C2 copy). -/
theorem forwardDuplicate_sourceObservation2013 : sourceObservation2013 forwardDuplicateC2 = 3 := by
  decide

/-- The forward duplicate is an actual constructor output for copy seed `(2, 1)`. -/
theorem forwardDuplicate_eq_extend : forwardDuplicateC2 = node3.extend 2 1 := rfl

/-- Constructor conformance instantiated on the forward duplicate. -/
theorem forwardDuplicate_source_conformance :
    sourceObservation2013 forwardDuplicateC2 =
      bb2013Observation (Official.sourceKind (node3.childProvenance 2 1))
        (Official.extendedSpheres node3 2 1) :=
  sourceObservation2013_extend_conformance node3 2 1

/-- The source-level 2013 equation reads 3 on the extension's sphere data. -/
theorem forwardDuplicate_bb2013_source_eq_three :
    bb2013Observation .multipleBondDuplicate
      (Official.extendedSpheres node3 2 1) = 3 := by
  decide

/-- The source-level 2018 equation reads 2 on the same sphere data. -/
theorem forwardDuplicate_hanson2018_source_eq_two :
    hanson2018Observation .multipleBondDuplicate
      (Official.extendedSpheres node3 2 1) = 2 := by
  decide

/-- Stored observations tie against the real sphere-2 node. -/
theorem forwardDuplicate_stored_tie :
    forwardDuplicateC2.rule1bRootDistance = node3.rule1bRootDistance := by
  decide

/-- The derived 2013 observations differ. -/
theorem forwardDuplicate_representations_differ :
    sourceObservation2013 forwardDuplicateC2 ≠ sourceObservation2013 node3 := by
  decide

/-- Under the implemented 2018 compilation the decision is a tie. -/
theorem stored_outcome_forward_tie :
    (compileRule1bDecision (profileObservation .hanson2018Proposed)
      forwardDuplicateC2 node3).outcome = Ordering.eq := by
  decide

/-- Under the 2013 compilation the forward duplicate ranks lower than the sphere-2 node. -/
theorem source2013_outcome_forward_lt :
    (compileRule1bDecision (profileObservation .bb2013)
      forwardDuplicateC2 node3).outcome = Ordering.lt := by
  decide

/-- **Comparator non-equivalence.**  The two profiles produce different Rule-1b decisions on the
concrete forward-duplicate pair. -/
theorem forward_duplicate_profiles_differ :
    compileRule1bDecision (profileObservation .hanson2018Proposed)
        forwardDuplicateC2 node3 ≠
      compileRule1bDecision (profileObservation .bb2013)
        forwardDuplicateC2 node3 := by
  decide

/-- Existential form of the counterexample: no global comparator-equivalence theorem can hold. -/
theorem exists_forward_difference :
    ∃ left right : OfficialCIPNode ℕ,
      compileRule1bDecision (profileObservation .hanson2018Proposed) left right ≠
        compileRule1bDecision (profileObservation .bb2013) left right :=
  ⟨forwardDuplicateC2, node3, forward_duplicate_profiles_differ⟩

end Concrete

end Rule1bSourceProfileCompiler
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.profileObservation_bb2013
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.profileObservation_hanson2018Proposed
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.compileRule1bDecision_outcome
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.compileRule1bDecision_hanson2018_eq_stored
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.compileRule1bDecision_eq_of_observe_eq
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.firstIndexOf?_append_eq_left_of_found
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.firstIndexOf?_append_singleton_of_not_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.branchRepresentedSphere_extend
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.branchRepresentedSphere_extend_of_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.branchRepresentedSphere_extend_of_not_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.sourceObservation2013_extend_real
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.sourceObservation2013_extend_ring
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.sourceObservation2013_extend_multipleBond_forward
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.sourceObservation2013_extend_multipleBond_backward
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.sourceObservation2013_extend_multipleBond
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.sourceObservation2013_extend_conformance
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.profileObservation_extend_conformance
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.sourceObservation2013_extend_real_eq_hanson2018
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.sourceObservation2013_extend_ring_eq_hanson2018
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.sourceObservation2013_extend_real_eq_stored
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.sourceObservation2013_extend_ring_eq_stored
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.sourceObservation2013_extend_multipleBond_forward_ne_stored
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.sourceObservation2013_extend_multipleBond_backward_reads_history
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.compile_decisions_eq_of_sourceObservation_eq_stored
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.compile_decisions_eq_on_real_and_ring_extensions
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.node3_depth
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.node3_stored
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.node3_sourceObservation2013
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.forwardDuplicate_depth
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.forwardDuplicate_stored
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.forwardDuplicate_sourceObservation2013
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.forwardDuplicate_eq_extend
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.forwardDuplicate_source_conformance
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.forwardDuplicate_bb2013_source_eq_three
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.forwardDuplicate_hanson2018_source_eq_two
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.forwardDuplicate_stored_tie
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.forwardDuplicate_representations_differ
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.stored_outcome_forward_tie
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.source2013_outcome_forward_lt
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.forward_duplicate_profiles_differ
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfileCompiler.Concrete.exists_forward_difference
