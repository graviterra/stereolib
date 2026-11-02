


































































import TetraStereo.OneCenter.OfficialHierarchicalDigraph
import TetraStereo.OneCenter.BranchSphereKey
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace Rule1bRepresentedAtomObservation

/-! ## Generic path-index lemmas -/

/-- If the target occurs in a list, `firstIndexOf?` succeeds. -/
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

/-- A successful `firstIndexOf?` indexes an actual occurrence. -/
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

/-- Once the target is found in `left`, appending a suffix does not move its first index. -/
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

/-- If the target is absent from `left`, its first index in `left ++ [target]` is `left.length`. -/
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

/-- Nat-indexed counterpart of `firstIndexOf?_eq_some_of_mem`. -/
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

/-- Nat-indexed counterpart of `firstIndexOf?_append_eq_left_of_found`. -/
theorem firstNatIndex?_append_eq_left_of_found (target : ℕ) :
    ∀ (left right : List ℕ),
      (∃ index, RawMolecule.firstNatIndex? target left = some index) →
      RawMolecule.firstNatIndex? target (left ++ right) =
        RawMolecule.firstNatIndex? target left
  | [], _right, ⟨_index, found⟩ => by
      simp [RawMolecule.firstNatIndex?] at found
  | value :: values, right, ⟨index, found⟩ => by
      by_cases head : value = target
      · simp [RawMolecule.firstNatIndex?, head]
      · have tailFound : ∃ tailIndex, RawMolecule.firstNatIndex? target values = some tailIndex := by
          have mapped : (RawMolecule.firstNatIndex? target values).map Nat.succ = some index := by
            simpa [RawMolecule.firstNatIndex?, head] using found
          obtain ⟨tailIndex, tailValue, _⟩ := Option.map_eq_some_iff.mp mapped
          exact ⟨tailIndex, tailValue⟩
        have ih := firstNatIndex?_append_eq_left_of_found target values right tailFound
        simp [RawMolecule.firstNatIndex?, head, ih]

/-- Nat-indexed counterpart of `firstIndexOf?_append_singleton_of_not_mem`. -/
theorem firstNatIndex?_append_singleton_of_not_mem (target : ℕ) :
    ∀ (left : List ℕ), target ∉ left →
      RawMolecule.firstNatIndex? target (left ++ [target]) = some left.length
  | [], _hnot => by
      simp [RawMolecule.firstNatIndex?]
  | value :: values, hnot => by
      have head : value ≠ target := by
        intro equal
        exact hnot (by simp [equal])
      have tailNot : target ∉ values := by
        intro present
        exact hnot (List.mem_cons_of_mem value present)
      have ih := firstNatIndex?_append_singleton_of_not_mem target values tailNot
      simp [RawMolecule.firstNatIndex?, head, ih]

/-! ## The represented-atom observers -/

variable {V : Type*} [DecidableEq V]

/-- The sphere at which the atom represented by an official node occurs on the actual
root-to-node path.  Only `current?` and `history` are read; the stored provenance distance is not
consulted and is not modified. -/
def officialRepresentedSphere? (node : OfficialCIPNode V) : Option ℕ :=
  match node.current? with
  | some atom => firstIndexOf? atom node.history.reverse
  | none => none

/-- Total form of the official represented-atom sphere.  The fallback `node.depth` is the shared
totalization convention (the same fallback as
`Rule1bSourceProfileCompiler.sourceObservation2013`); it is not a source rule. -/
def officialRepresentedSphere (node : OfficialCIPNode V) : ℕ :=
  match node.current? with
  | some atom => (firstIndexOf? atom node.history.reverse).getD node.depth
  | none => node.depth

/-- The sphere at which the atom represented by a canonical branch node occurs on the actual
root-to-node path.  Only `atom` and `history` are read. -/
def canonicalRepresentedSphere? (node : RawMolecule.CanonicalBranchNode) : Option ℕ :=
  RawMolecule.firstNatIndex? node.atom node.history.reverse

/-- Total form of the canonical represented-atom sphere.  The fallback `node.depth` is the shared
totalization convention, not a source rule. -/
def canonicalRepresentedSphere (node : RawMolecule.CanonicalBranchNode) : ℕ :=
  (RawMolecule.firstNatIndex? node.atom node.history.reverse).getD node.depth

/-- Total Rule-1b source observation on official nodes.

Only the duplicate branches consult the represented-atom history.  `realAtom` uses the node's own
sphere and `placeholder` uses its stored root distance: these are the **shared comparison-totality
convention**, not normative 2013 clauses. -/
def officialSourceObservation2013 (node : OfficialCIPNode V) : ℕ :=
  match node.provenance with
  | OfficialCIPNodeProvenance.realAtom => node.depth
  | OfficialCIPNodeProvenance.multipleBondDuplicate _ => officialRepresentedSphere node
  | OfficialCIPNodeProvenance.ringDuplicate _ => officialRepresentedSphere node
  | OfficialCIPNodeProvenance.placeholder _ distance => distance

/-- Total Rule-1b source observation on canonical nodes, with the same explicit convention. -/
def canonicalSourceObservation2013 (node : RawMolecule.CanonicalBranchNode) : ℕ :=
  match node.provenance with
  | RawMolecule.CanonicalNodeProvenance.realAtom => node.depth
  | RawMolecule.CanonicalNodeProvenance.multipleBondDuplicate _ =>
      canonicalRepresentedSphere node
  | RawMolecule.CanonicalNodeProvenance.ringDuplicate _ => canonicalRepresentedSphere node
  | RawMolecule.CanonicalNodeProvenance.phantom distance => distance

/-- **A successful official observation is an actual path occurrence.**  In particular the
represented atom occurs in `node.history`; a missing occurrence yields `none`. -/
theorem officialRepresentedSphere?_eq_some_imp_mem
    (node : OfficialCIPNode V) (index : ℕ)
    (hfound : officialRepresentedSphere? node = some index) :
    ∃ atom, node.current? = some atom ∧ atom ∈ node.history ∧
      node.history.reverse[index]? = some atom := by
  cases hcurrent : node.current? with
  | none =>
      have hnone : officialRepresentedSphere? node = none := by
        simp [officialRepresentedSphere?, hcurrent]
      rw [hnone] at hfound
      simp at hfound
  | some atom =>
      have hindex : firstIndexOf? atom node.history.reverse = some index := by
        simpa [officialRepresentedSphere?, hcurrent] using hfound
      have hget : node.history.reverse[index]? = some atom :=
        firstIndexOf?_eq_some_imp_getElem? atom node.history.reverse index hindex
      -- `cases` has already rewritten `node.current?` to `some atom` in the goal, so the
      -- equality component is `some atom = some atom`.
      exact ⟨atom, rfl, List.mem_reverse.mp (List.mem_of_getElem? hget), hget⟩

/-- **A successful canonical observation is an actual path occurrence.** -/
theorem canonicalRepresentedSphere?_eq_some_imp_mem
    (node : RawMolecule.CanonicalBranchNode) (index : ℕ)
    (hfound : canonicalRepresentedSphere? node = some index) :
    node.atom ∈ node.history ∧ node.history.reverse[index]? = some node.atom := by
  have hget : node.history.reverse[index]? = some node.atom :=
    firstNatIndex?_eq_some_imp_getElem? node.atom node.history.reverse index hfound
  exact ⟨List.mem_reverse.mp (List.mem_of_getElem? hget), hget⟩

/-- The total official observer is the `Option` observer with the shared fallback. -/
theorem officialRepresentedSphere_eq_getD (node : OfficialCIPNode V) :
    officialRepresentedSphere node = (officialRepresentedSphere? node).getD node.depth := by
  cases hcurrent : node.current? <;>
    simp [officialRepresentedSphere, officialRepresentedSphere?, hcurrent]

/-- The total canonical observer is exactly the `Option` observer with the shared fallback. -/
theorem canonicalRepresentedSphere_eq_getD (node : RawMolecule.CanonicalBranchNode) :
    canonicalRepresentedSphere node = (canonicalRepresentedSphere? node).getD node.depth :=
  rfl

/-- The official observer does not read provenance: replacing the stored provenance leaves the
observation unchanged.  Stored attachment distances therefore never need to be overwritten. -/
theorem officialRepresentedSphere?_provenance_irrel (node : OfficialCIPNode V)
    (provenance : OfficialCIPNodeProvenance) :
    officialRepresentedSphere? { node with provenance := provenance } =
      officialRepresentedSphere? node :=
  rfl

/-- The canonical observer does not read provenance. -/
theorem canonicalRepresentedSphere?_provenance_irrel (node : RawMolecule.CanonicalBranchNode)
    (provenance : RawMolecule.CanonicalNodeProvenance) :
    canonicalRepresentedSphere? { node with provenance := provenance } =
      canonicalRepresentedSphere? node :=
  rfl

/-- Path invariant: the stored ring-duplicate distance indexes the represented atom. -/
theorem duplicateRootDistance_indexes_represented
    (node : OfficialCIPNode V) (atom : V) (hmem : atom ∈ node.history) :
    node.history.reverse[node.duplicateRootDistance atom]? = some atom := by
  obtain ⟨index, found⟩ := firstIndexOf?_eq_some_of_mem atom (List.mem_reverse.mpr hmem)
  have distanceEq : node.duplicateRootDistance atom = index := by
    simp [OfficialCIPNode.duplicateRootDistance, found]
  rw [distanceEq]
  exact firstIndexOf?_eq_some_imp_getElem? atom node.history.reverse index found

/-- Path invariant: the canonical stored ring-duplicate distance indexes the represented atom. -/
theorem canonicalHistoryDistance_indexes_represented
    (node : RawMolecule.CanonicalBranchNode) (atom : ℕ) (hmem : atom ∈ node.history) :
    node.history.reverse[RawMolecule.canonicalHistoryDistance node atom]? = some atom := by
  obtain ⟨index, found⟩ := firstNatIndex?_eq_some_of_mem atom (List.mem_reverse.mpr hmem)
  have distanceEq : RawMolecule.canonicalHistoryDistance node atom = index := by
    simp [RawMolecule.canonicalHistoryDistance, found]
  rw [distanceEq]
  exact firstNatIndex?_eq_some_imp_getElem? atom node.history.reverse index found

/-! ## `OfficialCIPNode.extend`: generated children -/

/-- Unfolded observer on a one-step official extension. -/
@[simp] theorem officialRepresentedSphere?_extend
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ) :
    officialRepresentedSphere? (parent.extend next copyIndex) =
      firstIndexOf? next (parent.history.reverse ++ [next]) := by
  simp [officialRepresentedSphere?, OfficialCIPNode.extend]

/-- **Backward copy / ring candidate.**  If the represented atom already occurs on the parent
path, the generated child's observer reads the parent's existing history index. -/
theorem officialRepresentedSphere?_extend_of_mem
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ)
    (hmem : next ∈ parent.history) :
    officialRepresentedSphere? (parent.extend next copyIndex) =
      some (parent.duplicateRootDistance next) := by
  obtain ⟨index, found⟩ :=
    firstIndexOf?_eq_some_of_mem next (List.mem_reverse.mpr hmem)
  have appended :=
    firstIndexOf?_append_eq_left_of_found next parent.history.reverse [next] ⟨index, found⟩
  rw [officialRepresentedSphere?_extend, appended, found]
  simp [OfficialCIPNode.duplicateRootDistance, found]

/-- **Forward copy.**  If the represented atom has not yet occurred on the parent path, the
generated child's observer reads the child's own sphere. -/
theorem officialRepresentedSphere?_extend_of_not_mem
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ)
    (hnot : next ∉ parent.history) :
    officialRepresentedSphere? (parent.extend next copyIndex) =
      some (parent.extend next copyIndex).depth := by
  have hnotReverse : next ∉ parent.history.reverse := by
    simpa using hnot
  have appended :=
    firstIndexOf?_append_singleton_of_not_mem next parent.history.reverse hnotReverse
  rw [officialRepresentedSphere?_extend, appended]
  have hdepth : (parent.extend next copyIndex).depth = parent.history.length := by
    simp [OfficialCIPNode.depth]
  rw [hdepth, List.length_reverse]

/-- **Ring closure agrees with the existing stored distance.**  A zero-index copy of an atom
already on the branch is a ring duplicate; the observer returns exactly the stored ring-duplicate
distance. -/
theorem officialRepresentedSphere?_extend_ring
    (parent : OfficialCIPNode V) (next : V) (hmem : next ∈ parent.history) :
    officialRepresentedSphere? (parent.extend next 0) =
      some (parent.extend next 0).rule1bRootDistance := by
  rw [officialRepresentedSphere?_extend_of_mem parent next 0 hmem]
  congr 1
  simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, hmem,
    OfficialCIPNode.rule1bRootDistance]

/-- **Positive-copy split.**  A positive copy is a multiple-bond duplicate; the observer reads the
parent history index when the atom is already represented (backward) and the child's own sphere
otherwise (forward). -/
theorem officialRepresentedSphere?_extend_multipleBond
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ)
    (_hcopy : copyIndex ≠ 0) :
    officialRepresentedSphere? (parent.extend next copyIndex) =
      some (if next ∈ parent.history then parent.duplicateRootDistance next
        else (parent.extend next copyIndex).depth) := by
  by_cases hmem : next ∈ parent.history
  · rw [if_pos hmem]
    exact officialRepresentedSphere?_extend_of_mem parent next copyIndex hmem
  · rw [if_neg hmem]
    exact officialRepresentedSphere?_extend_of_not_mem parent next copyIndex hmem

/-! ### Total observation on generated official children -/

/-- Real child: the total observation is the shared own-sphere convention. -/
theorem officialSourceObservation2013_extend_real
    (parent : OfficialCIPNode V) (next : V) (hnot : next ∉ parent.history) :
    officialSourceObservation2013 (parent.extend next 0) = (parent.extend next 0).depth := by
  simp [officialSourceObservation2013, OfficialCIPNode.childProvenance, hnot]

/-- Ring child: the total observation is the parent history index. -/
theorem officialSourceObservation2013_extend_ring
    (parent : OfficialCIPNode V) (next : V) (hmem : next ∈ parent.history) :
    officialSourceObservation2013 (parent.extend next 0) =
      parent.duplicateRootDistance next := by
  have hreduce : officialSourceObservation2013 (parent.extend next 0) =
      officialRepresentedSphere (parent.extend next 0) := by
    simp [officialSourceObservation2013, OfficialCIPNode.childProvenance, hmem]
  rw [hreduce, officialRepresentedSphere_eq_getD,
    officialRepresentedSphere?_extend_of_mem parent next 0 hmem, Option.getD_some]

/-- Positive child: the total observation is the represented-atom observer. -/
theorem officialSourceObservation2013_extend_multipleBond
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ)
    (hcopy : copyIndex ≠ 0) :
    officialSourceObservation2013 (parent.extend next copyIndex) =
      if next ∈ parent.history then parent.duplicateRootDistance next
      else (parent.extend next copyIndex).depth := by
  have hreduce : officialSourceObservation2013 (parent.extend next copyIndex) =
      officialRepresentedSphere (parent.extend next copyIndex) := by
    simp [officialSourceObservation2013, OfficialCIPNode.childProvenance, hcopy]
  rw [hreduce, officialRepresentedSphere_eq_getD,
    officialRepresentedSphere?_extend_multipleBond parent next copyIndex hcopy, Option.getD_some]

/-! ### Stored distances are preserved exactly -/

/-- Positive copies keep the stored attachment sphere: `parent.depth`.  The source observer is an
additional datum and never overwrites this field. -/
theorem extend_rule1bRootDistance_positive
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ)
    (hcopy : copyIndex ≠ 0) :
    (parent.extend next copyIndex).rule1bRootDistance = parent.depth := by
  simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, hcopy]

/-- Ring closures keep the stored represented-atom distance. -/
theorem extend_rule1bRootDistance_ring
    (parent : OfficialCIPNode V) (next : V) (hmem : next ∈ parent.history) :
    (parent.extend next 0).rule1bRootDistance = parent.duplicateRootDistance next := by
  simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, hmem]

/-- Real children keep the stored own-sphere distance. -/
theorem extend_rule1bRootDistance_real
    (parent : OfficialCIPNode V) (next : V) (hnot : next ∉ parent.history) :
    (parent.extend next 0).rule1bRootDistance = (parent.extend next 0).depth := by
  simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, hnot]

/-! ## Canonical child copies

`Rule1bSourceProfileFidelity.Canonical.childOfCopy` is definitionally the constructor used by
`RawMolecule.canonicalChildren`.  It cannot be imported here (import discipline), so the identical
constructor is reproduced. -/

/-- One canonical child copy, matching the body of `RawMolecule.canonicalChildren`. -/
def canonicalChildOfCopy (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ) :
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

/-- `canonicalChildren` is the map of the local `canonicalChildOfCopy` over the emitted copy
seeds.  This is the constructor identity, definitionally equal to the fidelity module's
`Canonical.canonicalChildren_eq_map_childOfCopy`. -/
theorem canonicalChildren_eq_map_canonicalChildOfCopy (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode) :
    mol.canonicalChildren node =
      if node.forcedLeaf then []
      else (mol.canonicalChildCopies node).map (canonicalChildOfCopy node) :=
  rfl

/-- A copy seed actually emitted by `canonicalChildren` yields an actual child. -/
theorem canonicalChildOfCopy_mem_canonicalChildren
    (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hcopyMem : copy ∈ mol.canonicalChildCopies node)
    (hleaf : node.forcedLeaf = false) :
    canonicalChildOfCopy node copy ∈ mol.canonicalChildren node := by
  rw [canonicalChildren_eq_map_canonicalChildOfCopy]
  have hnot : ¬ node.forcedLeaf = true := by simp [hleaf]
  rw [if_neg hnot]
  exact List.mem_map.mpr ⟨copy, hcopyMem, rfl⟩

/-- Unfolded observer on a generated canonical child. -/
@[simp] theorem canonicalRepresentedSphere?_canonicalChildOfCopy
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ) :
    canonicalRepresentedSphere? (canonicalChildOfCopy node copy) =
      RawMolecule.firstNatIndex? copy.1 (node.history.reverse ++ [copy.1]) := by
  simp [canonicalRepresentedSphere?, canonicalChildOfCopy]

/-- **Backward copy.**  The observer reads the parent's existing history index. -/
theorem canonicalRepresentedSphere?_canonicalChildOfCopy_of_mem
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hmem : copy.1 ∈ node.history) :
    canonicalRepresentedSphere? (canonicalChildOfCopy node copy) =
      some (RawMolecule.canonicalHistoryDistance node copy.1) := by
  obtain ⟨index, found⟩ :=
    firstNatIndex?_eq_some_of_mem copy.1 (List.mem_reverse.mpr hmem)
  have appended :=
    firstNatIndex?_append_eq_left_of_found copy.1 node.history.reverse [copy.1]
      ⟨index, found⟩
  rw [canonicalRepresentedSphere?_canonicalChildOfCopy, appended, found]
  simp [RawMolecule.canonicalHistoryDistance, found]

/-- **Forward copy.**  The observer reads the child's own sphere. -/
theorem canonicalRepresentedSphere?_canonicalChildOfCopy_of_not_mem
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hnot : copy.1 ∉ node.history) :
    canonicalRepresentedSphere? (canonicalChildOfCopy node copy) =
      some (canonicalChildOfCopy node copy).depth := by
  have hnotReverse : copy.1 ∉ node.history.reverse := by
    simpa using hnot
  have appended :=
    firstNatIndex?_append_singleton_of_not_mem copy.1 node.history.reverse hnotReverse
  rw [canonicalRepresentedSphere?_canonicalChildOfCopy, appended]
  have hdepth : (canonicalChildOfCopy node copy).depth = node.history.length := by
    simp [canonicalChildOfCopy, RawMolecule.CanonicalBranchNode.depth]
  rw [hdepth, List.length_reverse]

/-- **Ring closure agrees with the existing stored distance.** -/
theorem canonicalRepresentedSphere?_canonicalChildOfCopy_ring
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hzero : copy.2 = 0) (hmem : copy.1 ∈ node.history) :
    canonicalRepresentedSphere? (canonicalChildOfCopy node copy) =
      some (canonicalChildOfCopy node copy).rule1bRootDistance := by
  rw [canonicalRepresentedSphere?_canonicalChildOfCopy_of_mem node copy hmem]
  congr 1
  simp [canonicalChildOfCopy, RawMolecule.CanonicalBranchNode.rule1bRootDistance,
    hzero, hmem]

/-- **Positive-copy split.** -/
theorem canonicalRepresentedSphere?_canonicalChildOfCopy_positive
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (_hcopy : copy.2 ≠ 0) :
    canonicalRepresentedSphere? (canonicalChildOfCopy node copy) =
      some (if copy.1 ∈ node.history then RawMolecule.canonicalHistoryDistance node copy.1
        else (canonicalChildOfCopy node copy).depth) := by
  by_cases hmem : copy.1 ∈ node.history
  · rw [if_pos hmem]
    exact canonicalRepresentedSphere?_canonicalChildOfCopy_of_mem node copy hmem
  · rw [if_neg hmem]
    exact canonicalRepresentedSphere?_canonicalChildOfCopy_of_not_mem node copy hmem

/-! ### Provenance of generated canonical children -/

theorem canonicalChildOfCopy_provenance_positive
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hcopy : copy.2 ≠ 0) :
    (canonicalChildOfCopy node copy).provenance =
      RawMolecule.CanonicalNodeProvenance.multipleBondDuplicate node.depth := by
  simp [canonicalChildOfCopy, hcopy]

theorem canonicalChildOfCopy_provenance_ring
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hzero : copy.2 = 0) (hmem : copy.1 ∈ node.history) :
    (canonicalChildOfCopy node copy).provenance =
      RawMolecule.CanonicalNodeProvenance.ringDuplicate
        (RawMolecule.canonicalHistoryDistance node copy.1) := by
  simp [canonicalChildOfCopy, hzero, hmem]

theorem canonicalChildOfCopy_provenance_real
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hzero : copy.2 = 0) (hnot : copy.1 ∉ node.history) :
    (canonicalChildOfCopy node copy).provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom := by
  simp [canonicalChildOfCopy, hzero, hnot]

/-! ### Total observation on generated canonical children -/

theorem canonicalSourceObservation2013_childOfCopy_ring
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hzero : copy.2 = 0) (hmem : copy.1 ∈ node.history) :
    canonicalSourceObservation2013 (canonicalChildOfCopy node copy) =
      RawMolecule.canonicalHistoryDistance node copy.1 := by
  have hprov := canonicalChildOfCopy_provenance_ring node copy hzero hmem
  have hreduce : canonicalSourceObservation2013 (canonicalChildOfCopy node copy) =
      canonicalRepresentedSphere (canonicalChildOfCopy node copy) := by
    simp [canonicalSourceObservation2013, hprov]
  have hobs : canonicalRepresentedSphere (canonicalChildOfCopy node copy) =
      RawMolecule.canonicalHistoryDistance node copy.1 := by
    rw [canonicalRepresentedSphere_eq_getD,
      canonicalRepresentedSphere?_canonicalChildOfCopy_of_mem node copy hmem,
      Option.getD_some]
  rw [hreduce, hobs]

theorem canonicalSourceObservation2013_childOfCopy_real
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hzero : copy.2 = 0) (hnot : copy.1 ∉ node.history) :
    canonicalSourceObservation2013 (canonicalChildOfCopy node copy) =
      (canonicalChildOfCopy node copy).depth := by
  have hprov := canonicalChildOfCopy_provenance_real node copy hzero hnot
  simp [canonicalSourceObservation2013, hprov]

theorem canonicalSourceObservation2013_childOfCopy_positive
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hcopy : copy.2 ≠ 0) :
    canonicalSourceObservation2013 (canonicalChildOfCopy node copy) =
      if copy.1 ∈ node.history then RawMolecule.canonicalHistoryDistance node copy.1
      else (canonicalChildOfCopy node copy).depth := by
  have hprov := canonicalChildOfCopy_provenance_positive node copy hcopy
  have hreduce : canonicalSourceObservation2013 (canonicalChildOfCopy node copy) =
      canonicalRepresentedSphere (canonicalChildOfCopy node copy) := by
    simp [canonicalSourceObservation2013, hprov]
  rw [hreduce, canonicalRepresentedSphere_eq_getD,
    canonicalRepresentedSphere?_canonicalChildOfCopy_positive node copy hcopy,
    Option.getD_some]

/-! ### Stored canonical distances are preserved exactly -/

theorem canonicalChildOfCopy_rule1bRootDistance_positive
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hcopy : copy.2 ≠ 0) :
    (canonicalChildOfCopy node copy).rule1bRootDistance = node.depth := by
  simp [canonicalChildOfCopy, RawMolecule.CanonicalBranchNode.rule1bRootDistance, hcopy]

theorem canonicalChildOfCopy_rule1bRootDistance_ring
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hzero : copy.2 = 0) (hmem : copy.1 ∈ node.history) :
    (canonicalChildOfCopy node copy).rule1bRootDistance =
      RawMolecule.canonicalHistoryDistance node copy.1 := by
  simp [canonicalChildOfCopy, RawMolecule.CanonicalBranchNode.rule1bRootDistance,
    hzero, hmem]

theorem canonicalChildOfCopy_rule1bRootDistance_real
    (node : RawMolecule.CanonicalBranchNode) (copy : ℕ × ℕ)
    (hzero : copy.2 = 0) (hnot : copy.1 ∉ node.history) :
    (canonicalChildOfCopy node copy).rule1bRootDistance =
      (canonicalChildOfCopy node copy).depth := by
  simp [canonicalChildOfCopy, RawMolecule.CanonicalBranchNode.rule1bRootDistance,
    hzero, hnot]

/-! ## The shared totalization convention on atomic node kinds -/

/-- Real official nodes use their own sphere (shared totalization convention, not a 2013 rule). -/
theorem officialSourceObservation2013_realAtom (node : OfficialCIPNode V)
    (hreal : node.provenance = OfficialCIPNodeProvenance.realAtom) :
    officialSourceObservation2013 node = node.depth := by
  simp [officialSourceObservation2013, hreal]

/-- Placeholder official nodes use their stored root distance (totalization only). -/
theorem officialSourceObservation2013_placeholder
    (kind : OfficialPhantomNodeKind) (distance : ℕ) :
    officialSourceObservation2013
      (OfficialCIPNode.placeholder (V := V) kind distance) = distance := by
  simp [officialSourceObservation2013, OfficialCIPNode.placeholder]

/-- Real canonical nodes use their own sphere (shared totalization convention, not a 2013 rule). -/
theorem canonicalSourceObservation2013_realAtom
    (node : RawMolecule.CanonicalBranchNode)
    (hreal : node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom) :
    canonicalSourceObservation2013 node = node.depth := by
  simp [canonicalSourceObservation2013, hreal]

/-- Canonical phantom nodes use their stored root distance (totalization only). -/
theorem canonicalSourceObservation2013_phantom
    (node : RawMolecule.CanonicalBranchNode) (distance : ℕ)
    (hphantom : node.provenance = RawMolecule.CanonicalNodeProvenance.phantom distance) :
    canonicalSourceObservation2013 node = distance := by
  simp [canonicalSourceObservation2013, hphantom]

end Rule1bRepresentedAtomObservation
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.firstIndexOf?_eq_some_of_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.firstIndexOf?_eq_some_imp_getElem?
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.firstIndexOf?_append_eq_left_of_found
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.firstIndexOf?_append_singleton_of_not_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.firstNatIndex?_eq_some_of_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.firstNatIndex?_eq_some_imp_getElem?
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.firstNatIndex?_append_eq_left_of_found
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.firstNatIndex?_append_singleton_of_not_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialRepresentedSphere?_eq_some_imp_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalRepresentedSphere?_eq_some_imp_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialRepresentedSphere_eq_getD
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalRepresentedSphere_eq_getD
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialRepresentedSphere?_provenance_irrel
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalRepresentedSphere?_provenance_irrel
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.duplicateRootDistance_indexes_represented
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalHistoryDistance_indexes_represented
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialRepresentedSphere?_extend
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialRepresentedSphere?_extend_of_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialRepresentedSphere?_extend_of_not_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialRepresentedSphere?_extend_ring
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialRepresentedSphere?_extend_multipleBond
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialSourceObservation2013_extend_real
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialSourceObservation2013_extend_ring
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialSourceObservation2013_extend_multipleBond
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.extend_rule1bRootDistance_positive
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.extend_rule1bRootDistance_ring
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.extend_rule1bRootDistance_real
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalChildren_eq_map_canonicalChildOfCopy
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalChildOfCopy_mem_canonicalChildren
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalRepresentedSphere?_canonicalChildOfCopy
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalRepresentedSphere?_canonicalChildOfCopy_of_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalRepresentedSphere?_canonicalChildOfCopy_of_not_mem
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalRepresentedSphere?_canonicalChildOfCopy_ring
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalRepresentedSphere?_canonicalChildOfCopy_positive
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalChildOfCopy_provenance_positive
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalChildOfCopy_provenance_ring
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalChildOfCopy_provenance_real
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalSourceObservation2013_childOfCopy_ring
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalSourceObservation2013_childOfCopy_real
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalSourceObservation2013_childOfCopy_positive
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalChildOfCopy_rule1bRootDistance_positive
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalChildOfCopy_rule1bRootDistance_ring
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalChildOfCopy_rule1bRootDistance_real
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialSourceObservation2013_realAtom
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.officialSourceObservation2013_placeholder
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalSourceObservation2013_realAtom
assert_kernel_only TetraStereo.OneCenter.Rule1bRepresentedAtomObservation.canonicalSourceObservation2013_phantom
