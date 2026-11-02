














































import TetraStereo.OneCenter.OfficialHierarchicalDigraph
import TetraStereo.OneCenter.BranchSphereKey
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace Rule1bSourceProfile

/-! ## Independent source observation equations -/

/-- The two source profiles relevant to Rule 1b. -/
inductive SourceProfile where
  | bb2013
  | hanson2018Proposed
  deriving DecidableEq, Repr

/-- Source-level classification of a hierarchical-digraph node.  This is stated independently of
any implementation provenance type. -/
inductive NodeKind where
  | realAtom
  | multipleBondDuplicate
  | ringClosureDuplicate
  | phantom
  deriving DecidableEq, Repr







structure SphereData where
  ownSphere : ℕ
  attachedSphere : ℕ
  representedSphere : ℕ
  deriving DecidableEq, Repr

/-- 2013 Blue Book observation.

P-92.1.3.1(b): "a duplicate atom node whose corresponding nonduplicated atom node is the root or is
closer to the root ranks higher than a duplicate atom node whose corresponding nonduplicated atom
node is farther from the root".  P-92.2.2 restates this as "a nearer duplicate atom node takes
precedence over a further away duplicate atom node".

The source clauses speak only about duplicate nodes.  Non-duplicate and placeholder nodes are given
their own sphere so that the induced observation is total; this is the shared comparison-totality
convention, not a 2013 duplicate-distance claim. -/
def bb2013Observation : NodeKind → SphereData → ℕ
  | .realAtom, data => data.ownSphere
  | .multipleBondDuplicate, data => data.representedSphere
  | .ringClosureDuplicate, data => data.representedSphere
  | .phantom, data => data.ownSphere

/-- 2018 proposed observation (Hanson2018-preprint.txt:458-470).

(a) ring-closure duplicate nodes: the sphere of the duplicated atom;
(b) multiple-bond duplicate nodes: the sphere of the atom to which the duplicate node is attached;
(c) all other cases: the sphere of the atom itself. -/
def hanson2018Observation : NodeKind → SphereData → ℕ
  | .realAtom, data => data.ownSphere
  | .multipleBondDuplicate, data => data.attachedSphere
  | .ringClosureDuplicate, data => data.representedSphere
  | .phantom, data => data.ownSphere

/-- The observation equation selected by a source profile. -/
def observation (profile : SourceProfile) : NodeKind → SphereData → ℕ :=
  match profile with
  | .bb2013 => bb2013Observation
  | .hanson2018Proposed => hanson2018Observation

@[simp] theorem bb2013Observation_realAtom (data : SphereData) :
    bb2013Observation .realAtom data = data.ownSphere := rfl

@[simp] theorem bb2013Observation_multipleBondDuplicate (data : SphereData) :
    bb2013Observation .multipleBondDuplicate data = data.representedSphere := rfl

@[simp] theorem bb2013Observation_ringClosureDuplicate (data : SphereData) :
    bb2013Observation .ringClosureDuplicate data = data.representedSphere := rfl

@[simp] theorem bb2013Observation_phantom (data : SphereData) :
    bb2013Observation .phantom data = data.ownSphere := rfl

@[simp] theorem hanson2018Observation_realAtom (data : SphereData) :
    hanson2018Observation .realAtom data = data.ownSphere := rfl

@[simp] theorem hanson2018Observation_multipleBondDuplicate (data : SphereData) :
    hanson2018Observation .multipleBondDuplicate data = data.attachedSphere := rfl

@[simp] theorem hanson2018Observation_ringClosureDuplicate (data : SphereData) :
    hanson2018Observation .ringClosureDuplicate data = data.representedSphere := rfl

@[simp] theorem hanson2018Observation_phantom (data : SphereData) :
    hanson2018Observation .phantom data = data.ownSphere := rfl




theorem bb2013Observation_eq_hanson2018Observation_of_not_multipleBond
    (kind : NodeKind) (data : SphereData) (hkind : kind ≠ .multipleBondDuplicate) :
    bb2013Observation kind data = hanson2018Observation kind data := by
  cases kind <;> simp_all [bb2013Observation, hanson2018Observation]

/-- The profiles genuinely differ on a multiple-bond duplicate exactly when the attached sphere and
the represented sphere differ. -/
theorem bb2013Observation_ne_hanson2018Observation_of_multipleBond
    (data : SphereData) (hdiff : data.attachedSphere ≠ data.representedSphere) :
    bb2013Observation .multipleBondDuplicate data ≠
      hanson2018Observation .multipleBondDuplicate data := by
  simp only [bb2013Observation, hanson2018Observation]
  exact fun equal => hdiff equal.symm

/-- Pointwise source-level Rule-1b decision: the smaller observed root distance has higher
priority.  This is deliberately parameterized by the source observation equation. -/
def sourceRule1bDecision (observe : NodeKind → SphereData → ℕ)
    (leftKind : NodeKind) (leftData : SphereData) (rightDistance : ℕ) : Ordering :=
  if observe leftKind leftData < rightDistance then Ordering.gt
  else if rightDistance < observe leftKind leftData then Ordering.lt
  else Ordering.eq

/-- The source decision is exactly the implementation's total Rule-1b distance comparator applied
to the source observation. -/
theorem sourceRule1bDecision_eq_compareCloserRootDistance
    (observe : NodeKind → SphereData → ℕ)
    (leftKind : NodeKind) (leftData : SphereData) (rightDistance : ℕ) :
    sourceRule1bDecision observe leftKind leftData rightDistance =
      MoleculeGraph.compareCloserRootDistance (observe leftKind leftData) rightDistance :=
  rfl

/-! ## Path-index lemmas -/

theorem firstIndexOf?_eq_some_of_mem {α : Type*} [DecidableEq α] (target : α) :
    ∀ {values : List α}, target ∈ values → ∃ index, firstIndexOf? target values = some index
  | [], present => by simp at present
  | value :: values, present => by
      by_cases head : value = target
      · subst value
        exact ⟨0, firstIndexOf?_cons_self target values⟩
      · have tailPresent : target ∈ values :=
          (List.mem_cons.mp present).resolve_left (Ne.symm head)
        obtain ⟨index, found⟩ := firstIndexOf?_eq_some_of_mem target tailPresent
        exact ⟨index + 1, by simp [firstIndexOf?, head, found]⟩

/-- The index returned by `firstIndexOf?` is an actual occurrence of the searched atom.  This is the
path invariant used to read a ring duplicate's represented sphere from the stored history. -/
theorem firstIndexOf?_eq_some_imp_getElem? {α : Type*} [DecidableEq α] (target : α) :
    ∀ (values : List α) (index : ℕ),
      firstIndexOf? target values = some index → values[index]? = some target
  | [], index, found => by simp [firstIndexOf?] at found
  | value :: values, index, found => by
      unfold firstIndexOf? at found
      by_cases head : value = target
      · simp [head] at found
        subst index
        simp [head]
      · simp only [head, ↓reduceIte, Option.map_eq_some_iff] at found
        obtain ⟨tailIndex, tailFound, rfl⟩ := found
        simpa using firstIndexOf?_eq_some_imp_getElem? target values tailIndex tailFound

theorem firstNatIndex?_eq_some_of_mem (target : ℕ) :
    ∀ {values : List ℕ}, target ∈ values →
      ∃ index, RawMolecule.firstNatIndex? target values = some index
  | [], present => by simp at present
  | value :: values, present => by
      by_cases head : value = target
      · subst value
        exact ⟨0, by simp [RawMolecule.firstNatIndex?]⟩
      · have tailPresent : target ∈ values :=
          (List.mem_cons.mp present).resolve_left (Ne.symm head)
        obtain ⟨index, found⟩ := firstNatIndex?_eq_some_of_mem target tailPresent
        exact ⟨index + 1, by simp [RawMolecule.firstNatIndex?, head, found]⟩

/-- Nat-indexed counterpart of `firstIndexOf?_eq_some_imp_getElem?`. -/
theorem firstNatIndex?_eq_some_imp_getElem? (target : ℕ) :
    ∀ (values : List ℕ) (index : ℕ),
      RawMolecule.firstNatIndex? target values = some index → values[index]? = some target
  | [], index, found => by simp [RawMolecule.firstNatIndex?] at found
  | value :: values, index, found => by
      unfold RawMolecule.firstNatIndex? at found
      by_cases head : value = target
      · simp [head] at found
        subst index
        simp [head]
      · simp only [head, ↓reduceIte, Option.map_eq_some_iff] at found
        obtain ⟨tailIndex, tailFound, rfl⟩ := found
        simpa using firstNatIndex?_eq_some_imp_getElem? target values tailIndex tailFound

/-! ## `OfficialCIPNode` constructor conformance -/

namespace Official

variable {V : Type*} [DecidableEq V]

/-- Source classification of an official-node provenance. -/
def sourceKind : OfficialCIPNodeProvenance → NodeKind
  | .realAtom => .realAtom
  | .multipleBondDuplicate _ => .multipleBondDuplicate
  | .ringDuplicate _ => .ringClosureDuplicate
  | .placeholder _ _ => .phantom

/-- Source sphere data read from a one-step `OfficialCIPNode` extension.

`ownSphere` is the sphere of the extended node and `attachedSphere` is the parent's sphere (the
sphere of the atom to which a multiple-bond duplicate is attached).  `representedSphere` is the
sphere of the corresponding nonduplicated atom, derived from the branch path: for a duplicate of an
atom already on the branch it is the existing path index returned by `duplicateRootDistance`; for a
forward duplicate it is the newly created child sphere. -/
def extendedSpheres (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ) : SphereData where
  ownSphere := (parent.extend next copyIndex).depth
  attachedSphere := parent.depth
  representedSphere :=
    match parent.childProvenance next copyIndex with
    | .ringDuplicate _ => parent.duplicateRootDistance next
    | .multipleBondDuplicate _ =>
        if next ∈ parent.history then parent.duplicateRootDistance next
        else (parent.extend next copyIndex).depth
    | _ => (parent.extend next copyIndex).depth

/-- **Real case.** A zero-index copy of an atom that is not already on the branch extends the
branch by a real atom; its own sphere is the 2018 observation. -/
theorem extend_real_implements_hanson2018 (parent : OfficialCIPNode V) (next : V)
    (hnotMem : next ∉ parent.history) :
    (parent.extend next 0).rule1bRootDistance =
      hanson2018Observation .realAtom (extendedSpheres parent next 0) := by
  simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, hnotMem, extendedSpheres,
    hanson2018Observation]

/-- **Ring-closure case.** A zero-index copy of an atom already on the branch creates a ring
duplicate.  Its stored distance is the parent-path distance of the represented atom, which is the
2018 observation (sphere of the duplicated atom). -/
theorem extend_ring_implements_hanson2018 (parent : OfficialCIPNode V) (next : V)
    (hmem : next ∈ parent.history) :
    (parent.extend next 0).rule1bRootDistance =
      hanson2018Observation .ringClosureDuplicate (extendedSpheres parent next 0) := by
  simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, hmem, extendedSpheres,
    hanson2018Observation]

/-- **Multiple-bond case.** A positive-index copy is a multiple-bond duplicate and stores the
parent sphere, exactly the 2018 attachment-sphere observation. -/
theorem extend_multipleBond_implements_hanson2018 (parent : OfficialCIPNode V) (next : V)
    {copyIndex : ℕ} (hcopy : copyIndex ≠ 0) :
    (parent.extend next copyIndex).rule1bRootDistance =
      hanson2018Observation .multipleBondDuplicate
        (extendedSpheres parent next copyIndex) := by
  simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, hcopy, extendedSpheres,
    hanson2018Observation]

/-- Every one-step `OfficialCIPNode` extension implements the 2018 proposed observation, with the
case determined by the actual copy index and branch membership. -/
theorem extend_implements_hanson2018 (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ) :
    (parent.extend next copyIndex).rule1bRootDistance =
      hanson2018Observation (sourceKind (parent.childProvenance next copyIndex))
        (extendedSpheres parent next copyIndex) := by
  by_cases realCopy : copyIndex = 0
  · subst copyIndex
    by_cases ring : next ∈ parent.history
    · simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
        OfficialCIPNode.childProvenance, ring, sourceKind, extendedSpheres,
        hanson2018Observation]
    · simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
        OfficialCIPNode.childProvenance, ring, sourceKind, extendedSpheres,
        hanson2018Observation]
  · simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
      OfficialCIPNode.childProvenance, realCopy, sourceKind, extendedSpheres,
      hanson2018Observation]

/-- Path invariant for ring duplicates: the stored distance is the index of the represented atom
in the root-to-parent path. -/
theorem duplicateRootDistance_indexes_represented (node : OfficialCIPNode V) (atom : V)
    (hmem : atom ∈ node.history) :
    node.history.reverse[node.duplicateRootDistance atom]? = some atom := by
  obtain ⟨index, found⟩ := firstIndexOf?_eq_some_of_mem atom (List.mem_reverse.mpr hmem)
  have distanceEq : node.duplicateRootDistance atom = index := by
    simp [OfficialCIPNode.duplicateRootDistance, found]
  rw [distanceEq]
  exact firstIndexOf?_eq_some_imp_getElem? atom node.history.reverse index found

/-- Actual-path invariant: every extension of a nonempty branch places its copies one sphere
beyond the parent. -/
theorem extend_depth_eq_attached_add_one (parent : OfficialCIPNode V) (next : V)
    (copyIndex : ℕ) (hnonempty : 0 < parent.history.length) :
    (parent.extend next copyIndex).depth = parent.depth + 1 := by
  simp [OfficialCIPNode.extend, OfficialCIPNode.depth]
  omega

/-- Under the actual extension invariant, the 2013 represented-atom observation of a **forward**
multiple-bond duplicate (the duplicated atom is not yet on the branch) is the sphere of the real
copy, one step beyond the 2018 attachment sphere.  Hence the two profiles genuinely disagree on
this constructor case.

The forward restriction is essential: `canonicalChildCopies` also retains backward copies of an atom
already on the branch, for which the represented atom is an existing path occurrence rather than a
new child.  No universal distinction over all multiple-bond copies is claimed. -/
theorem extend_profiles_differ_on_multipleBond (parent : OfficialCIPNode V) (next : V)
    (copyIndex : ℕ) (hcopy : copyIndex ≠ 0) (hnotMem : next ∉ parent.history)
    (hnonempty : 0 < parent.history.length) :
    bb2013Observation .multipleBondDuplicate (extendedSpheres parent next copyIndex) =
        (parent.extend next copyIndex).depth ∧
      hanson2018Observation .multipleBondDuplicate (extendedSpheres parent next copyIndex) =
        parent.depth ∧
      bb2013Observation .multipleBondDuplicate (extendedSpheres parent next copyIndex) ≠
        hanson2018Observation .multipleBondDuplicate (extendedSpheres parent next copyIndex) := by
  have h2013 :
      bb2013Observation .multipleBondDuplicate (extendedSpheres parent next copyIndex) =
        (parent.extend next copyIndex).depth := by
    simp [bb2013Observation, extendedSpheres, OfficialCIPNode.childProvenance, hcopy, hnotMem]
  have h2018 :
      hanson2018Observation .multipleBondDuplicate (extendedSpheres parent next copyIndex) =
        parent.depth := by
    simp [hanson2018Observation, extendedSpheres]
  refine ⟨h2013, h2018, ?_⟩
  rw [h2013, h2018, extend_depth_eq_attached_add_one parent next copyIndex hnonempty]
  exact Nat.succ_ne_self parent.depth

/-- **Backward multiple-bond copy.**  If the duplicated atom already occurs on the branch, the 2013
observation is the existing path sphere of that occurrence (an actual `history` index), while the
2018 observation remains the attachment sphere.  This case is not claimed to distinguish the
profiles. -/
theorem extend_multipleBond_backward_reads_history (parent : OfficialCIPNode V) (next : V)
    (copyIndex : ℕ) (hcopy : copyIndex ≠ 0) (hmem : next ∈ parent.history) :
    bb2013Observation .multipleBondDuplicate (extendedSpheres parent next copyIndex) =
        parent.duplicateRootDistance next ∧
      parent.history.reverse[parent.duplicateRootDistance next]? = some next ∧
      hanson2018Observation .multipleBondDuplicate (extendedSpheres parent next copyIndex) =
        parent.depth := by
  have h2013 :
      bb2013Observation .multipleBondDuplicate (extendedSpheres parent next copyIndex) =
        parent.duplicateRootDistance next := by
    simp [bb2013Observation, extendedSpheres, OfficialCIPNode.childProvenance, hcopy, hmem]
  have h2018 :
      hanson2018Observation .multipleBondDuplicate (extendedSpheres parent next copyIndex) =
        parent.depth := by
    simp [hanson2018Observation, extendedSpheres]
  exact ⟨h2013, duplicateRootDistance_indexes_represented parent next hmem, h2018⟩

/-- Public fidelity statement for the official hierarchical-digraph constructor. -/
theorem constructor_implements_hanson2018 (parent : OfficialCIPNode V) (next : V)
    (copyIndex : ℕ) :
    (parent.extend next copyIndex).rule1bRootDistance =
      observation .hanson2018Proposed
        (sourceKind (parent.childProvenance next copyIndex))
        (extendedSpheres parent next copyIndex) := by
  simpa [observation] using extend_implements_hanson2018 parent next copyIndex

end Official

/-! ## `CanonicalBranchNode` constructor conformance -/

namespace Canonical

/-- Source classification of a canonical-node provenance. -/
def sourceKind : RawMolecule.CanonicalNodeProvenance → NodeKind
  | .realAtom => .realAtom
  | .multipleBondDuplicate _ => .multipleBondDuplicate
  | .ringDuplicate _ => .ringClosureDuplicate
  | .phantom _ => .phantom

/-- The canonical child that one copy seed produces, matching the body of `canonicalChildren`. -/
def childOfCopy (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ) :
    RawMolecule.CanonicalBranchNode :=
  let next := copy.1
  let provenance :=
    if copy.2 != 0 then
      RawMolecule.CanonicalNodeProvenance.multipleBondDuplicate node.depth
    else if node.history.contains next then
      RawMolecule.CanonicalNodeProvenance.ringDuplicate
        (RawMolecule.canonicalHistoryDistance node next)
    else
      RawMolecule.CanonicalNodeProvenance.realAtom
  { atom := next
    parent := node.atom
    history := next :: node.history
    provenance := provenance }

/-- `canonicalChildren` is exactly the map of `childOfCopy` over the copy seeds.  This is the
constructor identity used below, stated once so that membership and per-copy reasoning agree. -/
theorem canonicalChildren_eq_map_childOfCopy (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode) :
    mol.canonicalChildren node =
      if node.forcedLeaf then []
      else (mol.canonicalChildCopies node).map (childOfCopy node) :=
  rfl

/-- Source sphere data read from the canonical parent/child paths.

`ownSphere` is the child's own sphere and `attachedSphere` is the parent's sphere.
`representedSphere` is the sphere of the corresponding nonduplicated atom, derived from the
parent path: a ring-closure duplicate and a backward multiple-bond copy use the existing path index
returned by `canonicalHistoryDistance`; a forward multiple-bond copy and a real child use the
child's own sphere. -/
def childSpheres (parent child : RawMolecule.CanonicalBranchNode) : SphereData where
  ownSphere := child.depth
  attachedSphere := parent.depth
  representedSphere :=
    match child.provenance with
    | .ringDuplicate _ => RawMolecule.canonicalHistoryDistance parent child.atom
    | .multipleBondDuplicate _ =>
        if child.atom ∈ parent.history then
          RawMolecule.canonicalHistoryDistance parent child.atom
        else child.depth
    | _ => child.depth

/-- Every canonical child copy implements the 2018 proposed observation.  The proof splits on the
actual copy index and branch membership that `canonicalChildren` uses. -/
theorem childOfCopy_implements_hanson2018 (node : RawMolecule.CanonicalBranchNode)
    (copy : ℕ × ℕ) :
    (childOfCopy node copy).rule1bRootDistance =
      hanson2018Observation (sourceKind (childOfCopy node copy).provenance)
        (childSpheres node (childOfCopy node copy)) := by
  by_cases copyZero : copy.2 = 0
  · by_cases hmem : copy.1 ∈ node.history
    · simp [childOfCopy, copyZero, hmem, sourceKind, childSpheres,
        RawMolecule.CanonicalBranchNode.rule1bRootDistance, hanson2018Observation]
    · simp [childOfCopy, copyZero, hmem, sourceKind, childSpheres,
        RawMolecule.CanonicalBranchNode.rule1bRootDistance, hanson2018Observation]
  · simp [childOfCopy, copyZero, sourceKind, childSpheres,
      RawMolecule.CanonicalBranchNode.rule1bRootDistance, hanson2018Observation]

/-- Membership form: every child actually emitted by `canonicalChildren` implements the 2018
observation. -/
theorem canonicalChildren_implements_hanson2018 (mol : RawMolecule)
    {node child : RawMolecule.CanonicalBranchNode}
    (hchild : child ∈ mol.canonicalChildren node) :
    child.rule1bRootDistance =
      hanson2018Observation (sourceKind child.provenance)
        (childSpheres node child) := by
  rw [canonicalChildren_eq_map_childOfCopy] at hchild
  by_cases hleaf : node.forcedLeaf = true
  · simp [hleaf] at hchild
  · have hmemMap : child ∈ (mol.canonicalChildCopies node).map (childOfCopy node) := by
      simpa [hleaf] using hchild
    obtain ⟨pair, _hpairMem, hEq⟩ := List.mem_map.mp hmemMap
    subst child
    exact childOfCopy_implements_hanson2018 node pair

/-- Path invariant for canonical ring duplicates: the stored distance is the index of the
represented atom in the root-to-parent path. -/
theorem canonicalHistoryDistance_indexes_represented
    (node : RawMolecule.CanonicalBranchNode) (atom : ℕ) (hmem : atom ∈ node.history) :
    node.history.reverse[RawMolecule.canonicalHistoryDistance node atom]? = some atom := by
  obtain ⟨index, found⟩ := firstNatIndex?_eq_some_of_mem atom (List.mem_reverse.mpr hmem)
  have distanceEq : RawMolecule.canonicalHistoryDistance node atom = index := by
    simp [RawMolecule.canonicalHistoryDistance, found]
  rw [distanceEq]
  exact firstNatIndex?_eq_some_imp_getElem? atom node.history.reverse index found

/-- Actual-path invariant: child copies are one sphere beyond the parent. -/
theorem childOfCopy_depth_eq_parent_add_one (node : RawMolecule.CanonicalBranchNode)
    (copy : ℕ × ℕ) (hnonempty : 0 < node.history.length) :
    (childOfCopy node copy).depth = node.depth + 1 := by
  simp [childOfCopy, RawMolecule.CanonicalBranchNode.depth]
  omega





theorem childOfCopy_profiles_differ_on_multipleBond
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hcopy : copy.2 ≠ 0) (hnotMem : copy.1 ∉ node.history)
    (hnonempty : 0 < node.history.length) :
    bb2013Observation .multipleBondDuplicate (childSpheres node (childOfCopy node copy)) =
        (childOfCopy node copy).depth ∧
      hanson2018Observation .multipleBondDuplicate
          (childSpheres node (childOfCopy node copy)) = node.depth ∧
      bb2013Observation .multipleBondDuplicate (childSpheres node (childOfCopy node copy)) ≠
        hanson2018Observation .multipleBondDuplicate
          (childSpheres node (childOfCopy node copy)) := by
  have h2013 :
      bb2013Observation .multipleBondDuplicate (childSpheres node (childOfCopy node copy)) =
        (childOfCopy node copy).depth := by
    simp [bb2013Observation, childSpheres, childOfCopy, hcopy, hnotMem]
  have h2018 :
      hanson2018Observation .multipleBondDuplicate (childSpheres node (childOfCopy node copy)) =
        node.depth := by
    simp [hanson2018Observation, childSpheres]
  refine ⟨h2013, h2018, ?_⟩
  rw [h2013, h2018, childOfCopy_depth_eq_parent_add_one node copy hnonempty]
  exact Nat.succ_ne_self node.depth

/-- **Backward multiple-bond child copy.**  If the duplicated atom already occurs on the parent
path, the 2013 observation is the existing path sphere of that occurrence, while the 2018
observation remains the attachment sphere.  No distinction between the profiles is claimed here. -/
theorem childOfCopy_multipleBond_backward_reads_history
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hcopy : copy.2 ≠ 0) (hmem : copy.1 ∈ node.history) :
    bb2013Observation .multipleBondDuplicate (childSpheres node (childOfCopy node copy)) =
        RawMolecule.canonicalHistoryDistance node copy.1 ∧
      node.history.reverse[RawMolecule.canonicalHistoryDistance node copy.1]? = some copy.1 ∧
      hanson2018Observation .multipleBondDuplicate
          (childSpheres node (childOfCopy node copy)) = node.depth := by
  have h2013 :
      bb2013Observation .multipleBondDuplicate (childSpheres node (childOfCopy node copy)) =
        RawMolecule.canonicalHistoryDistance node copy.1 := by
    simp [bb2013Observation, childSpheres, childOfCopy, hcopy, hmem]
  have h2018 :
      hanson2018Observation .multipleBondDuplicate (childSpheres node (childOfCopy node copy)) =
        node.depth := by
    simp [hanson2018Observation, childSpheres]
  exact ⟨h2013, canonicalHistoryDistance_indexes_represented node copy.1 hmem, h2018⟩

/-- Public fidelity statement for the canonical branch constructor. -/
theorem constructor_implements_hanson2018 (node : RawMolecule.CanonicalBranchNode)
    (copy : ℕ × ℕ) :
    (childOfCopy node copy).rule1bRootDistance =
      observation .hanson2018Proposed
        (sourceKind (childOfCopy node copy).provenance)
        (childSpheres node (childOfCopy node copy)) := by
  simpa [observation] using childOfCopy_implements_hanson2018 node copy

end Canonical














namespace P92

/-- Carbon atom specification used by the small branch fixture. -/
def carbon : AtomSpec := { element := Element.C }

/-- The local constitution of the P-92.2.2 branch: a double bond C2=C3, followed by the single
bonds C3-C4 and C4-C5 that carry the C5 -> C4 -> C3 path. -/
def molecule : RawMolecule where
  atoms := [carbon, carbon, carbon, carbon, carbon, carbon]
  bonds :=
    [ { source := 2, target := 3, kind := ParsedBondKind.double },
      { source := 3, target := 4, kind := ParsedBondKind.single },
      { source := 4, target := 5, kind := ParsedBondKind.single } ]

/-- The branch node C3 at sphere 2, with root-to-node history C5 -> C4 -> C3. -/
def parentNode : RawMolecule.CanonicalBranchNode where
  atom := 3
  parent := 4
  history := [3, 4, 5]
  provenance := RawMolecule.CanonicalNodeProvenance.realAtom

/-- The real (nonduplicated) copy of C2 at sphere 3. -/
def realCopyNode : RawMolecule.CanonicalBranchNode where
  atom := 2
  parent := 3
  history := [2, 3, 4, 5]
  provenance := RawMolecule.CanonicalNodeProvenance.realAtom

/-- The multiple-bond duplicate copy of C2 attached to C3, storing the attached sphere 2. -/
def duplicateNode : RawMolecule.CanonicalBranchNode where
  atom := 2
  parent := 3
  history := [2, 3, 4, 5]
  provenance := RawMolecule.CanonicalNodeProvenance.multipleBondDuplicate 2

/-- The duplicate is the constructor output for copy seed `(2, 1)` (the second copy of the
double bond). -/
theorem duplicateNode_eq_childOfCopy :
    duplicateNode = Canonical.childOfCopy parentNode (2, 1) := by
  decide

/-- The second copy of the C2=C3 double bond is an actual child-copy seed. -/
theorem copySeed_mem :
    (2, 1) ∈ molecule.canonicalChildCopies parentNode := by
  decide

/-- The duplicate is actually emitted by `canonicalChildren` on the fixture molecule, so the
observation below is constructor-generated rather than hand-assembled. -/
theorem duplicateNode_mem_canonicalChildren :
    duplicateNode ∈ molecule.canonicalChildren parentNode := by
  rw [duplicateNode_eq_childOfCopy, Canonical.canonicalChildren_eq_map_childOfCopy]
  rw [if_neg]
  · exact List.mem_map.mpr ⟨(2, 1), copySeed_mem, rfl⟩
  · decide

/-- The C2 copy is a forward duplicate: C2 has not yet occurred on the C5 -> C4 -> C3 path. -/
theorem duplicateAtom_not_mem_parent_history : (2 : ℕ) ∉ parentNode.history := by decide

/-- Source sphere data for the C2 duplicate, read through the canonical constructor: represented C2
at sphere 3, attached C3 at sphere 2. -/
def duplicateSpheres : SphereData := Canonical.childSpheres parentNode duplicateNode

theorem parentNode_sphere2 : parentNode.depth = 2 := by decide

theorem realCopyNode_representedSphere3 : duplicateSpheres.representedSphere = 3 := by decide

theorem attachedSphere2 : duplicateSpheres.attachedSphere = 2 := by decide

/-- The concrete duplicate is the forward constructor case, so its 2013 observation is its own
sphere (3), one beyond the attachment sphere. -/
theorem duplicateSpheres_forward_represented :
    duplicateSpheres.representedSphere = duplicateNode.depth := by decide

/-- The stored distance of the real-source multiple-bond duplicate is the 2018 observation. -/
theorem duplicateNode_implements_hanson2018 :
    duplicateNode.rule1bRootDistance =
      hanson2018Observation .multipleBondDuplicate duplicateSpheres := by
  decide

/-- The 2013 profile inspects the represented C2 at sphere 3. -/
theorem bb2013_observation_eq_three :
    bb2013Observation .multipleBondDuplicate duplicateSpheres = 3 := by
  decide


theorem hanson2018_observation_eq_two :
    hanson2018Observation .multipleBondDuplicate duplicateSpheres = 2 := by
  decide



theorem observation_difference :
    bb2013Observation .multipleBondDuplicate duplicateSpheres = 3 ∧
      hanson2018Observation .multipleBondDuplicate duplicateSpheres = 2 ∧
      duplicateNode.rule1bRootDistance = 2 ∧
      bb2013Observation .multipleBondDuplicate duplicateSpheres ≠
        hanson2018Observation .multipleBondDuplicate duplicateSpheres := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- A competitor duplicate at sphere 0, corresponding to the stereogenic center in the source
example's other branch. -/
def zeroCompetitorDistance : ℕ := 0

/-- The differing observation leaves the Rule-1b decision against the distance-0 competitor
unchanged: both profiles place the C2 duplicate below the competitor.

Scope: this pins one Rule-1b comparison outcome.  It does not assert that the final descriptor or
rank of the example, or of any other molecule, is unchanged. -/
theorem zero_competitor_decision_same :
    sourceRule1bDecision bb2013Observation .multipleBondDuplicate duplicateSpheres
        zeroCompetitorDistance =
      sourceRule1bDecision hanson2018Observation .multipleBondDuplicate duplicateSpheres
        zeroCompetitorDistance ∧
    sourceRule1bDecision hanson2018Observation .multipleBondDuplicate duplicateSpheres
        zeroCompetitorDistance = Ordering.lt := by
  decide

/-- The implementation comparator, applied to the stored distance, gives the same decision as the
2018 source equation. -/
theorem stored_decision_eq_hanson2018_source_decision :
    MoleculeGraph.compareCloserRootDistance duplicateNode.rule1bRootDistance
        zeroCompetitorDistance =
      sourceRule1bDecision hanson2018Observation .multipleBondDuplicate duplicateSpheres
        zeroCompetitorDistance := by
  rw [duplicateNode_implements_hanson2018]
  exact (sourceRule1bDecision_eq_compareCloserRootDistance hanson2018Observation
    .multipleBondDuplicate duplicateSpheres zeroCompetitorDistance).symm

end P92

end Rule1bSourceProfile
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.bb2013Observation_realAtom
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.bb2013Observation_multipleBondDuplicate
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.bb2013Observation_ringClosureDuplicate
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.bb2013Observation_phantom
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.hanson2018Observation_realAtom
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.hanson2018Observation_multipleBondDuplicate
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.hanson2018Observation_ringClosureDuplicate
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.hanson2018Observation_phantom
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.bb2013Observation_eq_hanson2018Observation_of_not_multipleBond
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.bb2013Observation_ne_hanson2018Observation_of_multipleBond
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.sourceRule1bDecision_eq_compareCloserRootDistance
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.firstIndexOf?_eq_some_of_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.firstIndexOf?_eq_some_imp_getElem?
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.firstNatIndex?_eq_some_of_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.firstNatIndex?_eq_some_imp_getElem?
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Official.extend_real_implements_hanson2018
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Official.extend_ring_implements_hanson2018
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Official.extend_multipleBond_implements_hanson2018
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Official.extend_implements_hanson2018
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Official.duplicateRootDistance_indexes_represented
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Official.extend_depth_eq_attached_add_one
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Official.extend_profiles_differ_on_multipleBond
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Official.extend_multipleBond_backward_reads_history
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Official.constructor_implements_hanson2018
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Canonical.canonicalChildren_eq_map_childOfCopy
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Canonical.childOfCopy_implements_hanson2018
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Canonical.canonicalChildren_implements_hanson2018
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Canonical.canonicalHistoryDistance_indexes_represented
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Canonical.childOfCopy_depth_eq_parent_add_one
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Canonical.childOfCopy_profiles_differ_on_multipleBond
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Canonical.childOfCopy_multipleBond_backward_reads_history
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.Canonical.constructor_implements_hanson2018
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.duplicateNode_eq_childOfCopy
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.copySeed_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.duplicateNode_mem_canonicalChildren
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.duplicateAtom_not_mem_parent_history
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.parentNode_sphere2
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.realCopyNode_representedSphere3
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.attachedSphere2
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.duplicateSpheres_forward_represented
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.duplicateNode_implements_hanson2018
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.bb2013_observation_eq_three
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.hanson2018_observation_eq_two
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.observation_difference
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.zero_competitor_decision_same
assert_kernel_only TetraStereo.OneCenter.Rule1bSourceProfile.P92.stored_decision_eq_hanson2018_source_decision
