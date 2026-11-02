import TetraStereo.OneCenter.DeclarativeCIPOrdinaryCanonicalAddressing
import TetraStereo.KernelOnly

set_option autoImplicit false


























namespace TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical

noncomputable section
open scoped Classical
open RootedDigraph
open Certificate.CanonicalSphereKey (sortDesc slotOf)

universe u

/-- Sphere-major promotion values. Missing positions contain zero. -/
abbrev MarkerKey := List (List Nat)

/-- The earlier-rule key is decisive before the promotion column. -/
abbrev CompleteKey (P : Type*) := Lex (P × MarkerKey)

def markerPad (W level : Nat) : List Nat := List.replicate (W ^ level) 0

/-- One marker followed by the sphere-major columns of the first `W` children. -/
def assembleMarker (W D mark : Nat) (children : List MarkerKey) : MarkerKey :=
  [mark] :: (List.range D).map fun level =>
    (List.range W).flatMap fun slot =>
      (children.getD slot []).getD level (markerPad W level)

def MarkerWellShaped (W D : Nat) (key : MarkerKey) : Prop :=
  key.length = D + 1 ∧ ∀ level (h : level < key.length), key[level].length = W ^ level

theorem markerSlotLevel_length {W D : Nat} {keys : List MarkerKey}
    (shaped : ∀ key ∈ keys, MarkerWellShaped W D key)
    {level : Nat} (bound : level < D) (slot : Nat) :
    ((keys.getD slot []).getD level (markerPad W level)).length = W ^ level := by
  by_cases present : slot < keys.length
  · obtain ⟨length, levels⟩ := shaped _ (List.getElem_mem present)
    have levelBound : level < keys[slot].length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem present,
      List.getElem?_eq_getElem levelBound, levels level levelBound]
  · simp [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega : keys.length ≤ slot), markerPad]

theorem assembleMarker_wellShaped (W D mark : Nat) (children : List MarkerKey)
    (shaped : ∀ key ∈ children, MarkerWellShaped W D key) :
    MarkerWellShaped W D (assembleMarker W D mark children) := by
  refine ⟨by simp [assembleMarker], ?_⟩
  intro level bound
  cases level with
  | zero => simp [assembleMarker]
  | succ level =>
      have levelBound : level < D := by simpa [assembleMarker] using bound
      simp only [assembleMarker, List.getElem_cons_succ, List.getElem_map, List.getElem_range]
      have widths : ∀ slot ∈ List.range W,
          ((children.getD slot []).getD level (markerPad W level)).length = W ^ level :=
        fun slot _ => markerSlotLevel_length shaped levelBound slot
      rw [List.length_flatMap, List.map_congr_left widths]
      simp [Nat.pow_succ, Nat.mul_comm]

section Construction

variable {Atom : Type u} (graph : RootedDigraph Atom)
  {P : Type*} [LinearOrder P] (prior : graph.Node → P) (mark : graph.Node → Nat)

local instance nodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Independent complete key, with one immutable earlier-rule prefix per node. -/
def key (W D : Nat) (node : graph.Node) : CompleteKey P :=
  let ranked := sortDesc ((graph.childList node).attach.map fun child => key W D child.1)
  toLex (prior node, assembleMarker W D (mark node) (ranked.map fun child => (ofLex child).2))
termination_by graph.height + 1 - graph.depth node
decreasing_by
  have edge := (graph.mem_childList).1 child.2
  have depth := graph.child_depth edge
  have bound := graph.depth_le_height child.1
  omega

def rankedKeys (W D : Nat) (node : graph.Node) : List (CompleteKey P) :=
  sortDesc ((graph.childList node).map (key graph prior mark W D))

def markerKey (W D : Nat) (node : graph.Node) : MarkerKey :=
  (ofLex (key graph prior mark W D node)).2

theorem key_eq (W D : Nat) (node : graph.Node) :
    key graph prior mark W D node = toLex (prior node,
      assembleMarker W D (mark node)
        ((rankedKeys graph prior mark W D node).map fun child => (ofLex child).2)) := by
  rw [key]
  simp only [List.attach_map_val, rankedKeys]

theorem key_prior (W D : Nat) (node : graph.Node) :
    (ofLex (key graph prior mark W D node)).1 = prior node := by
  rw [key_eq]
  rfl

theorem markerKey_eq (W D : Nat) (node : graph.Node) :
    markerKey graph prior mark W D node = assembleMarker W D (mark node)
      ((rankedKeys graph prior mark W D node).map fun child => (ofLex child).2) := by
  unfold markerKey
  rw [key_eq]
  rfl

theorem markerKey_wellShaped (W D : Nat) :
    ∀ node, MarkerWellShaped W D (markerKey graph prior mark W D node) := by
  refine node_induction graph (motive := fun node =>
    MarkerWellShaped W D (markerKey graph prior mark W D node)) ?_
  intro node ih
  rw [markerKey_eq]
  apply assembleMarker_wellShaped
  intro column member
  obtain ⟨complete, completeMember, rfl⟩ := List.mem_map.1 member
  obtain ⟨child, childMember, rfl⟩ :=
    List.mem_map.1 (Certificate.CanonicalSphereKey.sortDesc_mem completeMember)
  exact ih child ((graph.mem_childList).1 childMember)

/-- Refining by a later column cannot reverse the earlier prefix. -/
theorem prior_le_of_key_le (W D : Nat) {left right : graph.Node}
    (ordered : key graph prior mark W D left ≤ key graph prior mark W D right) :
    prior left ≤ prior right := by
  rcases Prod.Lex.le_iff.mp ordered with earlier | ⟨equal, _⟩
  · simpa only [key_prior] using earlier.le
  · simpa only [key_prior] using equal.le

/-- Sorting complete child keys preserves exactly the sorted list of earlier child keys. -/
theorem rankedKeys_prior (W D : Nat) (node : graph.Node) :
    (rankedKeys graph prior mark W D node).map (fun complete => (ofLex complete).1) =
      sortDesc ((graph.childList node).map prior) := by
  have monotone : ∀ a b : CompleteKey P, a ≤ b → (ofLex a).1 ≤ (ofLex b).1 := by
    intro a b ordered
    rcases Prod.Lex.le_iff.mp ordered with earlier | ⟨equal, _⟩
    · exact earlier.le
    · exact equal.le
  have sorted : ((rankedKeys graph prior mark W D node).map
      (fun complete => (ofLex complete).1)).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_map]
    exact (Certificate.CanonicalSphereKey.sortDesc_pairwise _).imp
      fun ordered => monotone _ _ ordered
  have permutation : ((rankedKeys graph prior mark W D node).map
      (fun complete => (ofLex complete).1)).Perm ((graph.childList node).map prior) := by
    refine ((Certificate.CanonicalSphereKey.sortDesc_perm _).map
      (fun complete : CompleteKey P => (ofLex complete).1)).trans ?_
    rw [List.map_map]
    exact List.Perm.of_eq (List.map_congr_left fun child _ => key_prior graph prior mark W D child)
  exact (Certificate.CanonicalSphereKey.sortDesc_of_pairwise sorted).symm.trans
    (Certificate.CanonicalSphereKey.sortDesc_eq_of_perm permutation)

/-- Dense sibling slots ordered by the complete independent key. -/
def CanonicalAddressing (W D : Nat) (addressing : graph.Addressing) : Prop :=
  Dense addressing ∧ KeySorted (key graph prior mark W D) addressing

theorem canonicalAddressing_prior_sorted (W D : Nat) {addressing : graph.Addressing}
    (canonical : CanonicalAddressing graph prior mark W D addressing) :
    KeySorted prior addressing := by
  intro parent first second firstSlot secondSlot firstAddress secondAddress slotOrder
  exact prior_le_of_key_le graph prior mark W D
    (canonical.2 parent first second firstSlot secondSlot firstAddress secondAddress slotOrder)

/-- A base addressing supplies only the rooted tree structure, not its priority order. -/
theorem exists_canonicalAddressing (W D : Nat) (base : graph.Addressing) :
    ∃ addressing, CanonicalAddressing graph prior mark W D addressing :=
  ⟨keyAddressing base (key graph prior mark W D),
    keyAddressing_dense_sorted base (key graph prior mark W D)⟩

end Construction

section Representation

variable {Atom : Type u} {left right : RootedDigraph Atom}
  {P : Type*} [LinearOrder P]

/-- The independent complete key depends only on the represented hierarchy and its observations.
The same finite layout is used on both sides; no runtime comparison or chosen child order is
assumed. -/
theorem key_iso (iso : RootedDigraph.Iso left right)
    (leftPrior : left.Node → P) (rightPrior : right.Node → P)
    (leftMark : left.Node → Nat) (rightMark : right.Node → Nat)
    (priorPreserved : ∀ node, rightPrior (iso.toEquiv node) = leftPrior node)
    (markPreserved : ∀ node, rightMark (iso.toEquiv node) = leftMark node)
    (W D : Nat) :
    ∀ node, key right rightPrior rightMark W D (iso.toEquiv node) =
      key left leftPrior leftMark W D node := by
  refine node_induction left ?_
  intro node ih
  have children : rankedKeys right rightPrior rightMark W D (iso.toEquiv node) =
      rankedKeys left leftPrior leftMark W D node := by
    unfold rankedKeys
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
      ((childList_iso_perm iso node).map (key right rightPrior rightMark W D)), List.map_map]
    congr 1
    exact List.map_congr_left fun child member => ih child ((left.mem_childList).1 member)
  rw [key_eq, key_eq, children, priorPreserved, markPreserved]

theorem markerKey_iso (iso : RootedDigraph.Iso left right)
    (leftPrior : left.Node → P) (rightPrior : right.Node → P)
    (leftMark : left.Node → Nat) (rightMark : right.Node → Nat)
    (priorPreserved : ∀ node, rightPrior (iso.toEquiv node) = leftPrior node)
    (markPreserved : ∀ node, rightMark (iso.toEquiv node) = leftMark node)
    (W D : Nat) (node : left.Node) :
    markerKey right rightPrior rightMark W D (iso.toEquiv node) =
      markerKey left leftPrior leftMark W D node := by
  unfold markerKey
  rw [key_iso iso leftPrior rightPrior leftMark rightMark priorPreserved markPreserved]

end Representation

section Observations

variable {Atom : Type u} {graph : RootedDigraph Atom} (mark : graph.Node → Nat)

/-- The marker at an occupied address; absent positions have the unmarked value zero. -/
def addressMarker (addressing : graph.Addressing) (position : List Nat) : Nat :=
  if h : ∃ node, addressing.address node = position then mark (Classical.choose h) else 0

theorem addressMarker_of_address (addressing : graph.Addressing) (node : graph.Node) :
    addressMarker mark addressing (addressing.address node) = mark node := by
  have present : ∃ found, addressing.address found = addressing.address node := ⟨node, rfl⟩
  unfold addressMarker
  rw [dif_pos present]
  exact congrArg mark (addressing.address_injective (Classical.choose_spec present))

theorem addressMarker_of_unoccupied (addressing : graph.Addressing) {position : List Nat}
    (absent : ∀ node, addressing.address node ≠ position) :
    addressMarker mark addressing position = 0 := by
  unfold addressMarker
  rw [dif_neg (by simpa using absent)]

end Observations

section Readback

variable {Atom : Type u} (graph : RootedDigraph Atom)
  {P : Type*} [LinearOrder P] (prior : graph.Node → P) (mark : graph.Node → Nat)

local instance readbackNodeFintype : Fintype graph.Node := graph.nodeFintype

def markerObservation (column : MarkerKey) (level slot : Nat) : Nat :=
  (column.getD level []).getD slot 0

/-- Every bounded path observation is read from the same independent marker column. -/
theorem addressMarker_eq_keyObservation (W D : Nat) {addressing : graph.Addressing}
    (dense : Dense addressing) (sorted : KeySorted (key graph prior mark W D) addressing) :
    ∀ (path : List Nat) (node : graph.Node), (∀ slot ∈ path, slot < W) → path.length ≤ D →
      markerObservation (markerKey graph prior mark W D node) path.length (slotOf W path) =
        addressMarker mark addressing (addressing.address node ++ path)
  | [], node, _, _ => by
      rw [List.append_nil, addressMarker_of_address, markerKey_eq]
      simp [markerObservation, assembleMarker, slotOf]
  | slot :: path, node, digits, length => by
      have slotBound : slot < W := digits slot (by simp)
      have pathDigits : ∀ i ∈ path, i < W := fun i member => digits i (by simp [member])
      have pathBound : path.length < D := by simp at length; omega
      have indexBound := Certificate.CanonicalSphereKey.slotOf_lt pathDigits
      obtain ⟨count, countDense⟩ := dense node
      have ranked := sortDesc_childKeys_eq_slotOrder (key graph prior mark W D) countDense sorted
      have shapes : ∀ column ∈
          ((slotList addressing node count).map (key graph prior mark W D)).map
            (fun complete => (ofLex complete).2), MarkerWellShaped W D column := by
        intro column member
        obtain ⟨complete, completeMember, rfl⟩ := List.mem_map.1 member
        obtain ⟨child, _, rfl⟩ := List.mem_map.1 completeMember
        exact markerKey_wellShaped graph prior mark W D child
      rw [markerKey_eq, rankedKeys, ranked]
      simp only [markerObservation, assembleMarker, List.length_cons, slotOf,
        List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
        List.getElem?_range pathBound, Option.map_some, Option.getD_some,
        Certificate.CanonicalSphereKey.getD_flatMap_range _ _ W
          (fun i _ => markerSlotLevel_length shapes pathBound i) slotBound indexBound]
      by_cases occupied : slot < count
      · obtain ⟨child, childFound, childAddress⟩ := slotList_getD_of_lt countDense occupied
        have ih := addressMarker_eq_keyObservation W D dense sorted path child pathDigits (by omega)
        have position : addressing.address node ++ slot :: path = addressing.address child ++ path := by
          rw [childAddress]
          simp
        rw [position, ← ih]
        have levelBound : path.length < (markerKey graph prior mark W D child).length := by
          rw [(markerKey_wellShaped graph prior mark W D child).1]
          omega
        change path.length < (ofLex (key graph prior mark W D child)).2.length at levelBound
        simp [markerObservation, markerKey, List.getD_eq_getElem?_getD, List.getElem?_map,
          childFound, List.getElem?_eq_getElem levelBound]
      · have noChild : ((slotList addressing node count).map (key graph prior mark W D))[slot]? =
            none := by
          simp [slotList]
          omega
        have unoccupied : ∀ found,
            addressing.address found ≠ addressing.address node ++ slot :: path := by
          intro found foundAddress
          obtain ⟨ancestor, ancestorAddress⟩ := addressing.prefix_occupied found
            (addressing.address node ++ [slot]) path (by rw [foundAddress]; simp)
          exact occupied ((countDense slot).1 ⟨ancestor, ancestorAddress⟩)
        rw [addressMarker_of_unoccupied mark addressing unoccupied]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, noChild, Option.map_none,
          Option.getD_none, List.getElem?_nil, markerPad, List.getElem?_replicate]
        split <;> rfl

/-- Any two complete-key canonical addressings agree at every covered address. -/
theorem addressMarker_canonical_eq_of_bounds (W D : Nat)
    (widthBound : graph.width ≤ W) (heightBound : graph.height ≤ D)
    {first second : graph.Addressing}
    (firstCanonical : CanonicalAddressing graph prior mark W D first)
    (secondCanonical : CanonicalAddressing graph prior mark W D second)
    (position : List Nat) :
    addressMarker mark first position = addressMarker mark second position := by
  by_cases inside : (∀ slot ∈ position, slot < W) ∧ position.length ≤ D
  · have left := addressMarker_eq_keyObservation graph prior mark W D
      firstCanonical.1 firstCanonical.2 position graph.root inside.1 inside.2
    have right := addressMarker_eq_keyObservation graph prior mark W D
      secondCanonical.1 secondCanonical.2 position graph.root inside.1 inside.2
    rw [first.root_address, List.nil_append] at left
    rw [second.root_address, List.nil_append] at right
    exact left.symm.trans right
  · have outside : ∀ addressing : graph.Addressing, Dense addressing →
        ∀ node, addressing.address node ≠ position := by
      intro addressing dense node equal
      apply inside
      constructor
      · intro slot member
        rw [← equal] at member
        exact (address_slots_lt_width dense node slot member).trans_le widthBound
      · rw [← equal]
        exact (address_length_le_height addressing node).trans heightBound
    rw [addressMarker_of_unoccupied mark first (outside first firstCanonical.1),
      addressMarker_of_unoccupied mark second (outside second secondCanonical.1)]

/-- The finite graph's own layout covers every address; no depth restriction is imposed on input. -/
theorem addressMarker_canonical_eq {first second : graph.Addressing}
    (firstCanonical : CanonicalAddressing graph prior mark graph.width graph.height first)
    (secondCanonical : CanonicalAddressing graph prior mark graph.width graph.height second)
    (position : List Nat) :
    addressMarker mark first position = addressMarker mark second position :=
  addressMarker_canonical_eq_of_bounds graph prior mark graph.width graph.height
    le_rfl le_rfl firstCanonical secondCanonical position

end Readback
end
end TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.assembleMarker_wellShaped
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.key_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.key_prior
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.markerKey_wellShaped
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.prior_le_of_key_le
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.rankedKeys_prior
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.canonicalAddressing_prior_sorted
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.exists_canonicalAddressing
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.key_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.markerKey_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.addressMarker_eq_keyObservation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.addressMarker_canonical_eq_of_bounds
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.PromotedCanonical.addressMarker_canonical_eq
