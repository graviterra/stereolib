import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey
import TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalMarker
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000









































namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey

open CertifiedLocalizedCIPInput DeclarativeCIP DeclarativeCIP.PromotedCanonical
open LocalizedMarkedRetainedCanonicalMarker LocalizedMarkedRetainedSubtreeContext
open LocalizedCumulativeDecoratedTree
open Certificate.CanonicalSphereKey (sortDesc slotOf)
open LocalizedMarkedRetainedPromotedKey Rule4aTableBridge

noncomputable section
open scoped Classical
open RootedDigraph

universe u

/-! ## Joint marker vectors over ordinary marker columns -/

/-- The joint marker: one ordinary marker column per mark. -/
abbrev JointMarker := List MarkerKey

/-- Assemble `n` ordinary marker columns from the mark vector at a node and the child joint
vectors.  Column `index` is the standard `assembleMarker` column for mark `index`. -/
def assembleJointMarker (W D n : Nat) (marks : List Nat)
    (children : List JointMarker) : JointMarker :=
  (List.range n).map fun index =>
    assembleMarker W D (marks.getD index 0)
      (children.map fun columns => columns.getD index [])

theorem assembleJointMarker_getD (W D n : Nat) (marks : List Nat)
    (children : List JointMarker) {index : Nat} (bound : index < n) :
    (assembleJointMarker W D n marks children).getD index [] =
      assembleMarker W D (marks.getD index 0)
        (children.map fun columns => columns.getD index []) := by
  unfold assembleJointMarker
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range bound,
    Option.map_some, Option.getD_some]

theorem assembleJointMarker_congr {W D n : Nat} {marksL marksR : List Nat}
    {childrenL childrenR : List JointMarker}
    (marksEq : ∀ index, index < n → marksL.getD index 0 = marksR.getD index 0)
    (childrenEq : childrenL = childrenR) :
    assembleJointMarker W D n marksL childrenL =
      assembleJointMarker W D n marksR childrenR := by
  cases childrenEq
  unfold assembleJointMarker
  apply List.map_congr_left
  intro index member
  rw [marksEq index (List.mem_range.1 member)]

/-! ## Independent finite joint key -/

section Construction

variable {Atom : Type u} (graph : RootedDigraph Atom)
  {P : Type*} [LinearOrder P] (prior : graph.Node → P) (marks : graph.Node → List Nat)

local instance nodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Complete independent joint key: immutable prior prefix, then the whole joint marker vector.
Children are sorted once by this complete key. -/
def jointKey (W D n : Nat) (node : graph.Node) : Lex (P × JointMarker) :=
  let ranked := sortDesc ((graph.childList node).attach.map fun child =>
    jointKey W D n child.1)
  toLex (prior node, assembleJointMarker W D n (marks node)
    (ranked.map fun child => (ofLex child).2))
termination_by graph.height + 1 - graph.depth node
decreasing_by
  have edge := (graph.mem_childList).1 child.2
  have depth := graph.child_depth edge
  have bound := graph.depth_le_height child.1
  omega

def rankedJointKeys (W D n : Nat) (node : graph.Node) : List (Lex (P × JointMarker)) :=
  sortDesc ((graph.childList node).map (jointKey graph prior marks W D n))

def jointMarkerKey (W D n : Nat) (node : graph.Node) : JointMarker :=
  (ofLex (jointKey graph prior marks W D n node)).2

theorem jointKey_eq (W D n : Nat) (node : graph.Node) :
    jointKey graph prior marks W D n node = toLex (prior node,
      assembleJointMarker W D n (marks node)
        ((rankedJointKeys graph prior marks W D n node).map fun child =>
          (ofLex child).2)) := by
  rw [jointKey]
  simp only [List.attach_map_val, rankedJointKeys]

theorem jointKey_prior (W D n : Nat) (node : graph.Node) :
    (ofLex (jointKey graph prior marks W D n node)).1 = prior node := by
  rw [jointKey_eq]
  rfl

theorem jointMarkerKey_eq (W D n : Nat) (node : graph.Node) :
    jointMarkerKey graph prior marks W D n node = assembleJointMarker W D n (marks node)
      ((rankedJointKeys graph prior marks W D n node).map fun child =>
        (ofLex child).2) := by
  unfold jointMarkerKey
  rw [jointKey_eq]
  rfl

theorem jointKey_eq_marker (W D n : Nat) (node : graph.Node) :
    jointKey graph prior marks W D n node =
      toLex (prior node, jointMarkerKey graph prior marks W D n node) := by
  rw [jointKey_eq, jointMarkerKey_eq]

/-- Every one of the `n` columns is an ordinary well-shaped marker key. -/
theorem jointMarkerKey_wellShaped (W D n : Nat) :
    ∀ node (index : Nat), index < n →
      MarkerWellShaped W D ((jointMarkerKey graph prior marks W D n node).getD index []) := by
  refine node_induction graph (motive := fun node => ∀ index, index < n →
    MarkerWellShaped W D ((jointMarkerKey graph prior marks W D n node).getD index [])) ?_
  intro node ih index bound
  rw [jointMarkerKey_eq]
  rw [assembleJointMarker_getD W D n (marks node)
    (((rankedJointKeys graph prior marks W D n node).map fun child =>
      (ofLex child).2)) bound]
  apply assembleMarker_wellShaped
  intro column member
  obtain ⟨columns, columnsMember, rfl⟩ := List.mem_map.1 member
  obtain ⟨complete, completeMember, rfl⟩ := List.mem_map.1 columnsMember
  obtain ⟨child, childMember, rfl⟩ :=
    List.mem_map.1 (Certificate.CanonicalSphereKey.sortDesc_mem completeMember)
  exact ih child ((graph.mem_childList).1 childMember) index bound

/-- Refining by the joint marker vector cannot reverse the earlier prefix. -/
theorem prior_le_of_jointKey_le (W D n : Nat) {left right : graph.Node}
    (ordered : jointKey graph prior marks W D n left ≤
      jointKey graph prior marks W D n right) :
    prior left ≤ prior right := by
  rcases Prod.Lex.le_iff.mp ordered with earlier | ⟨equal, _⟩
  · simpa only [jointKey_prior] using earlier.le
  · simpa only [jointKey_prior] using equal.le

/-- Sorting complete joint child keys preserves exactly the sorted list of earlier child keys. -/
theorem rankedJointKeys_prior (W D n : Nat) (node : graph.Node) :
    (rankedJointKeys graph prior marks W D n node).map
        (fun complete => (ofLex complete).1) =
      sortDesc ((graph.childList node).map prior) := by
  have monotone : ∀ a b : Lex (P × JointMarker), a ≤ b →
      (ofLex a).1 ≤ (ofLex b).1 := by
    intro a b ordered
    rcases Prod.Lex.le_iff.mp ordered with earlier | ⟨equal, _⟩
    · exact earlier.le
    · exact equal.le
  have sorted : ((rankedJointKeys graph prior marks W D n node).map
      (fun complete => (ofLex complete).1)).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_map]
    exact (Certificate.CanonicalSphereKey.sortDesc_pairwise _).imp
      fun ordered => monotone _ _ ordered
  have permutation : ((rankedJointKeys graph prior marks W D n node).map
      (fun complete => (ofLex complete).1)).Perm ((graph.childList node).map prior) := by
    refine ((Certificate.CanonicalSphereKey.sortDesc_perm _).map
      (fun complete : Lex (P × JointMarker) => (ofLex complete).1)).trans ?_
    rw [List.map_map]
    exact List.Perm.of_eq (List.map_congr_left fun child _ =>
      jointKey_prior graph prior marks W D n child)
  exact (Certificate.CanonicalSphereKey.sortDesc_of_pairwise sorted).symm.trans
    (Certificate.CanonicalSphereKey.sortDesc_eq_of_perm permutation)

/-- Dense sibling slots ordered by the complete joint key. -/
def JointCanonicalAddressing (W D n : Nat) (addressing : graph.Addressing) : Prop :=
  Dense addressing ∧ KeySorted (jointKey graph prior marks W D n) addressing

theorem jointCanonicalAddressing_prior_sorted (W D n : Nat)
    {addressing : graph.Addressing}
    (canonical : JointCanonicalAddressing graph prior marks W D n addressing) :
    KeySorted prior addressing := by
  intro parent first second firstSlot secondSlot firstAddress secondAddress slotOrder
  exact prior_le_of_jointKey_le graph prior marks W D n
    (canonical.2 parent first second firstSlot secondSlot firstAddress secondAddress slotOrder)

/-- A base addressing supplies only the rooted tree structure, not its priority order. -/
theorem exists_jointCanonicalAddressing (W D n : Nat) (base : graph.Addressing) :
    ∃ addressing, JointCanonicalAddressing graph prior marks W D n addressing :=
  ⟨keyAddressing base (jointKey graph prior marks W D n),
    keyAddressing_dense_sorted base (jointKey graph prior marks W D n)⟩

end Construction

/-! ## Covariance under one isomorphism preserving all marks -/

section Representation

variable {Atom : Type u} {left right : RootedDigraph Atom}
  {P : Type*} [LinearOrder P]

/-- One graph isomorphism preserving the prior and every mark coordinate fixes the complete joint
key.  This is covariance, not a reconstruction: the isomorphism is supplied. -/
theorem jointKey_iso (iso : RootedDigraph.Iso left right)
    (leftPrior : left.Node → P) (rightPrior : right.Node → P)
    (leftMarks : left.Node → List Nat) (rightMarks : right.Node → List Nat)
    (W D n : Nat)
    (priorPreserved : ∀ node, rightPrior (iso.toEquiv node) = leftPrior node)
    (markPreserved : ∀ node index, index < n →
      (rightMarks (iso.toEquiv node)).getD index 0 = (leftMarks node).getD index 0) :
    ∀ node, jointKey right rightPrior rightMarks W D n (iso.toEquiv node) =
      jointKey left leftPrior leftMarks W D n node := by
  refine node_induction left ?_
  intro node ih
  have children : rankedJointKeys right rightPrior rightMarks W D n (iso.toEquiv node) =
      rankedJointKeys left leftPrior leftMarks W D n node := by
    unfold rankedJointKeys
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
      ((childList_iso_perm iso node).map
        (jointKey right rightPrior rightMarks W D n)), List.map_map]
    congr 1
    exact List.map_congr_left fun child member =>
      ih child ((left.mem_childList).1 member)
  rw [jointKey_eq, jointKey_eq, children, priorPreserved]
  have markerEq : assembleJointMarker W D n (rightMarks (iso.toEquiv node))
      ((rankedJointKeys left leftPrior leftMarks W D n node).map fun child =>
        (ofLex child).2) =
    assembleJointMarker W D n (leftMarks node)
      ((rankedJointKeys left leftPrior leftMarks W D n node).map fun child =>
        (ofLex child).2) :=
    assembleJointMarker_congr
      (fun index bound => markPreserved node index bound) rfl
  rw [markerEq]

theorem jointMarkerKey_iso (iso : RootedDigraph.Iso left right)
    (leftPrior : left.Node → P) (rightPrior : right.Node → P)
    (leftMarks : left.Node → List Nat) (rightMarks : right.Node → List Nat)
    (W D n : Nat)
    (priorPreserved : ∀ node, rightPrior (iso.toEquiv node) = leftPrior node)
    (markPreserved : ∀ node index, index < n →
      (rightMarks (iso.toEquiv node)).getD index 0 = (leftMarks node).getD index 0)
    (node : left.Node) :
    jointMarkerKey right rightPrior rightMarks W D n (iso.toEquiv node) =
      jointMarkerKey left leftPrior leftMarks W D n node := by
  unfold jointMarkerKey
  rw [jointKey_iso iso leftPrior rightPrior leftMarks rightMarks W D n
    priorPreserved markPreserved]

end Representation

/-! ## Joint address readback and the decoder structure -/

section Addressing

variable {Atom : Type u} {P : Type*} [LinearOrder P]

/-- Address digits need a bound on each child list, not on the total expanded-node count. -/
theorem address_slots_lt_of_branching {graph : RootedDigraph Atom}
    {addressing : graph.Addressing} (dense : Dense addressing) {W : Nat}
    (branching : ∀ node, (graph.childList node).length ≤ W) (node : graph.Node) :
    ∀ slot ∈ addressing.address node, slot < W := by
  induction graph.reachable node with
  | refl => simp [addressing.root_address]
  | @tail parent node _ edge ih =>
      obtain ⟨last, address⟩ := (addressing.child_iff parent node).mp edge
      obtain ⟨count, countDense⟩ := dense parent
      have countEq : count = (graph.childList parent).length := by
        simpa [slotList] using (slotList_perm countDense).length_eq
      have lastBound : last < count := (countDense last).mp ⟨node, address⟩
      intro slot member
      rw [address, List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact ih slot member
      · exact lastBound.trans_le (countEq ▸ branching parent)

private theorem mark_zero_outside {Atom : Type u} {graph : RootedDigraph Atom}
    (marks : graph.Node → List Nat) (index : Nat) (addressing : graph.Addressing)
    (dense : Dense addressing)
    {W D : Nat} (width : ∀ node, (graph.childList node).length ≤ W)
    (height : graph.height ≤ D) (position : List Nat)
    (outside : ¬ ((∀ slot ∈ position, slot < W) ∧ position.length ≤ D)) :
    addressMarker (fun x => (marks x).getD index 0) addressing position = 0 := by
  apply addressMarker_of_unoccupied
  intro node equal
  apply outside
  constructor
  · intro slot member
    rw [← equal] at member
    exact address_slots_lt_of_branching dense width node slot member
  · rw [← equal]
    exact (address_length_le_height addressing node).trans height

section Readback

variable (graph : RootedDigraph Atom)
  {P : Type*} [LinearOrder P] (prior : graph.Node → P) (marks : graph.Node → List Nat)

local instance readbackNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Every bounded path observation of every mark column is read from the same independent joint
marker. -/
theorem addressJointMarker_eq_keyObservation (W D n : Nat) {addressing : graph.Addressing}
    (dense : Dense addressing)
    (sorted : KeySorted (jointKey graph prior marks W D n) addressing)
    (index : Nat) (indexBound : index < n) :
    ∀ (path : List Nat) (node : graph.Node), (∀ slot ∈ path, slot < W) →
      path.length ≤ D →
      markerObservation ((jointMarkerKey graph prior marks W D n node).getD index [])
          path.length (slotOf W path) =
        addressMarker (fun x => (marks x).getD index 0) addressing
          (addressing.address node ++ path) := by
  intro path
  induction path with
  | nil =>
      intro node _ _
      rw [List.append_nil, addressMarker_of_address, jointMarkerKey_eq]
      rw [assembleJointMarker_getD W D n (marks node)
        ((rankedJointKeys graph prior marks W D n node).map fun child =>
          (ofLex child).2) indexBound]
      simp [markerObservation, assembleMarker, slotOf]
  | cons slot path ih =>
      intro node digits length
      have slotBound : slot < W := digits slot (by simp)
      have pathDigits : ∀ i ∈ path, i < W := fun i member => digits i (by simp [member])
      have pathBound : path.length < D := by simp at length; omega
      have tailIndexBound := Certificate.CanonicalSphereKey.slotOf_lt pathDigits
      obtain ⟨count, countDense⟩ := dense node
      have ranked := sortDesc_childKeys_eq_slotOrder
        (jointKey graph prior marks W D n) countDense sorted
      have shapes : ∀ column ∈
          (((slotList addressing node count).map
            (jointKey graph prior marks W D n)).map
              (fun child => (ofLex child).2)).map
                (fun columns => columns.getD index []),
          MarkerWellShaped W D column := by
        intro column member
        obtain ⟨columns, columnsMember, rfl⟩ := List.mem_map.1 member
        obtain ⟨complete, completeMember, rfl⟩ := List.mem_map.1 columnsMember
        obtain ⟨child, _, rfl⟩ := List.mem_map.1 completeMember
        exact jointMarkerKey_wellShaped graph prior marks W D n child index indexBound
      rw [jointMarkerKey_eq, rankedJointKeys, ranked]
      rw [assembleJointMarker_getD W D n (marks node)
        (((slotList addressing node count).map
          (jointKey graph prior marks W D n)).map
            (fun child => (ofLex child).2)) indexBound]
      simp only [markerObservation, assembleMarker, List.length_cons, slotOf,
        List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
        List.getElem?_range pathBound, Option.map_some, Option.getD_some,
        Certificate.CanonicalSphereKey.getD_flatMap_range _ _ W
          (fun i _ => markerSlotLevel_length shapes pathBound i) slotBound tailIndexBound]
      by_cases occupied : slot < count
      · obtain ⟨child, childFound, childAddress⟩ := slotList_getD_of_lt countDense occupied
        have hrec := ih child pathDigits (by omega)
        have position : addressing.address node ++ slot :: path =
            addressing.address child ++ path := by
          rw [childAddress]
          simp
        rw [position, ← hrec]
        have levelBound : path.length <
            ((jointMarkerKey graph prior marks W D n child).getD index []).length := by
          rw [(jointMarkerKey_wellShaped graph prior marks W D n child index indexBound).1]
          omega
        change path.length < ((ofLex (jointKey graph prior marks W D n child)).2.getD
          index []).length at levelBound
        simp only [List.getD_eq_getElem?_getD] at levelBound
        simp [markerObservation, jointMarkerKey, List.getD_eq_getElem?_getD,
          List.getElem?_map, childFound, List.getElem?_eq_getElem levelBound]
      · have noSlot : (slotList addressing node count)[slot]? = none := by
          simp [slotList]
          omega
        have unoccupied : ∀ found,
            addressing.address found ≠ addressing.address node ++ slot :: path := by
          intro found foundAddress
          obtain ⟨ancestor, ancestorAddress⟩ := addressing.prefix_occupied found
            (addressing.address node ++ [slot]) path (by rw [foundAddress]; simp)
          exact occupied ((countDense slot).1 ⟨ancestor, ancestorAddress⟩)
        rw [addressMarker_of_unoccupied (fun x => (marks x).getD index 0) addressing unoccupied]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, noSlot, Option.map_none,
          Option.getD_none, List.getElem?_nil, markerPad, List.getElem?_replicate]
        split <;> rfl

end Readback

/-- Equal root joint markers give equal observations for every mark coordinate between two different
covered hierarchies. -/
theorem addressMarkers_eq_of_root_jointMarker_eq
    (left right : RootedDigraph Atom)
    (priorL : left.Node → P) (priorR : right.Node → P)
    (marksL : left.Node → List Nat) (marksR : right.Node → List Nat)
    (n W D : Nat) (widthL : ∀ node, (left.childList node).length ≤ W)
    (heightL : left.height ≤ D)
    (widthR : ∀ node, (right.childList node).length ≤ W) (heightR : right.height ≤ D)
    {addressL : left.Addressing} {addressR : right.Addressing}
    (canonicalL : JointCanonicalAddressing left priorL marksL W D n addressL)
    (canonicalR : JointCanonicalAddressing right priorR marksR W D n addressR)
    (equal : jointMarkerKey left priorL marksL W D n left.root =
      jointMarkerKey right priorR marksR W D n right.root)
    (index : Nat) (indexBound : index < n) (position : List Nat) :
    addressMarker (fun x => (marksL x).getD index 0) addressL position =
      addressMarker (fun x => (marksR x).getD index 0) addressR position := by
  by_cases inside : (∀ slot ∈ position, slot < W) ∧ position.length ≤ D
  · have readL := addressJointMarker_eq_keyObservation left priorL marksL W D n
      canonicalL.1 canonicalL.2 index indexBound position left.root inside.1 inside.2
    have readR := addressJointMarker_eq_keyObservation right priorR marksR W D n
      canonicalR.1 canonicalR.2 index indexBound position right.root inside.1 inside.2
    rw [addressL.root_address, List.nil_append] at readL
    rw [addressR.root_address, List.nil_append] at readR
    exact readL.symm.trans ((congrArg
      (fun columns => markerObservation (columns.getD index []) position.length
        (Certificate.CanonicalSphereKey.slotOf W position)) equal).trans readR)
  · rw [mark_zero_outside marksL index addressL canonicalL.1 widthL heightL position inside,
      mark_zero_outside marksR index addressR canonicalR.1 widthR heightR position inside]

/-- Two constructed joint-canonical addressings with every mark coordinate agreeing at every
address.  The structure asserts no map, no occupancy equality and no isomorphism. -/
structure MatchedJointMarkerAddressings (left right : RootedDigraph Atom)
    (priorL : left.Node → P) (priorR : right.Node → P)
    (marksL : left.Node → List Nat) (marksR : right.Node → List Nat)
    (n W D : Nat) where
  leftAddressing : left.Addressing
  rightAddressing : right.Addressing
  leftCanonical : JointCanonicalAddressing left priorL marksL W D n leftAddressing
  rightCanonical : JointCanonicalAddressing right priorR marksR W D n rightAddressing
  same : ∀ position index, index < n →
    addressMarker (fun x => (marksL x).getD index 0) leftAddressing position =
      addressMarker (fun x => (marksR x).getD index 0) rightAddressing position

namespace MatchedJointMarkerAddressings

variable {left right : RootedDigraph Atom}
  {priorL : left.Node → P} {priorR : right.Node → P}
  {marksL : left.Node → List Nat} {marksR : right.Node → List Nat} {n W D : Nat}
  (matched : MatchedJointMarkerAddressings left right priorL priorR marksL marksR n W D)

/-- Joint promotion only refines the independent earlier priority at every parent. -/
theorem prior_sorted : KeySorted priorL matched.leftAddressing ∧
    KeySorted priorR matched.rightAddressing :=
  ⟨jointCanonicalAddressing_prior_sorted left priorL marksL W D n matched.leftCanonical,
    jointCanonicalAddressing_prior_sorted right priorR marksR W D n matched.rightCanonical⟩

/-- At jointly occupied addresses every one of the `n` mark coordinates agrees. -/
theorem marks_eq (x : left.Node) (y : right.Node)
    (address : matched.leftAddressing.address x = matched.rightAddressing.address y)
    (index : Nat) (indexBound : index < n) :
    (marksL x).getD index 0 = (marksR y).getD index 0 := by
  have same := matched.same (matched.leftAddressing.address x) index indexBound
  rw [addressMarker_of_address, address, addressMarker_of_address] at same
  exact same

/-- One supplied address-aligned map preserves all marks simultaneously.  The alignment is an
explicit premise: this is the decoder, not a reconstruction. -/
theorem marks_preserved_of_address_alignment
    (f : left.Node → right.Node)
    (aligned : ∀ x,
      matched.leftAddressing.address x = matched.rightAddressing.address (f x))
    (index : Nat) (indexBound : index < n) (x : left.Node) :
    (marksL x).getD index 0 = (marksR (f x)).getD index 0 :=
  matched.marks_eq x (f x) (aligned x) index indexBound

end MatchedJointMarkerAddressings

/-- Canonicality is constructed from arbitrary base addressings and equal root joint markers. -/
theorem exists_matched_joint_marker_addressings
    (left right : RootedDigraph Atom)
    (priorL : left.Node → P) (priorR : right.Node → P)
    (marksL : left.Node → List Nat) (marksR : right.Node → List Nat)
    (n W D : Nat) (widthL : ∀ node, (left.childList node).length ≤ W)
    (heightL : left.height ≤ D)
    (widthR : ∀ node, (right.childList node).length ≤ W) (heightR : right.height ≤ D)
    (baseL : left.Addressing) (baseR : right.Addressing)
    (equal : jointMarkerKey left priorL marksL W D n left.root =
      jointMarkerKey right priorR marksR W D n right.root) :
    Nonempty (MatchedJointMarkerAddressings left right priorL priorR marksL marksR n W D) := by
  obtain ⟨addressL, canonicalL⟩ :=
    exists_jointCanonicalAddressing left priorL marksL W D n baseL
  obtain ⟨addressR, canonicalR⟩ :=
    exists_jointCanonicalAddressing right priorR marksR W D n baseR
  exact ⟨⟨addressL, addressR, canonicalL, canonicalR,
    fun position index indexBound =>
      addressMarkers_eq_of_root_jointMarker_eq left right priorL priorR marksL marksR n W D
        widthL heightL widthR heightR canonicalL canonicalR equal index indexBound position⟩⟩

end Addressing

/-! ## Runtime joint promoted key algebra -/

section Runtime

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}

/-- Complete ordinary priority followed by the whole joint marker vector. -/
structure JointPromotedKey where
  prior : input.LocalizedRerootCompoundRule45Key
  markers : JointMarker

/-- The ordered vector of reference-membership bits at one cursor. -/
def referenceVector (references : List input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel) : List Nat :=
  references.map fun reference => referenceBit input reference cursor

/-- The joint marker at one node, with child joint vectors zipped column by column. -/
def jointMarkers (references : List input.Atom) (W D : Nat)
    (children : List (JointPromotedKey input))
    (cursor : input.LocalizedRerootCursor carrierFuel) : JointMarker :=
  assembleJointMarker W D references.length (referenceVector input references cursor)
    (children.map JointPromotedKey.markers)

/-- An earlier ordinary decision is immutable; when it ties, the whole joint vector decides. -/
def compareJointKeys (left right : JointPromotedKey input) : Ordering :=
  (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering.then
    (compare left.markers right.markers)

def sortJointKeys (keys : List (JointPromotedKey input)) : List (JointPromotedKey input) :=
  keys.insertionSort fun a b => compareJointKeys input a b ≠ .lt

theorem compareJointKeys_of_prior_ne (left right : JointPromotedKey input)
    (strict : (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering
      ≠ .eq) :
    compareJointKeys input left right =
      (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering := by
  unfold compareJointKeys
  cases h : (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering
    <;> simp_all

theorem compareJointKeys_of_prior_eq (left right : JointPromotedKey input)
    (tie : (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering
      = .eq) :
    compareJointKeys input left right = compare left.markers right.markers := by
  simp [compareJointKeys, tie]

/-- A joint-key tie is exactly an ordinary tie together with equality of the whole mark vector. -/
theorem compareJointKeys_eq_iff (left right : JointPromotedKey input) :
    compareJointKeys input left right = .eq ↔
      (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering = .eq
        ∧ left.markers = right.markers := by
  unfold compareJointKeys
  cases h : (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering <;>
    simp

private theorem natList_compare_lt_iff (left right : List Nat) :
    compare left right = .lt ↔ left < right :=
  compareLex_eq_lt_iff_of compare (fun _ _ => compare_lt_iff_lt)
    (fun _ _ => compare_eq_iff_eq) left right

private theorem natList_compare_eq_iff (left right : List Nat) :
    compare left right = .eq ↔ left = right :=
  compareLex_eq_eq_iff_of compare (fun _ _ => compare_eq_iff_eq) left right

private theorem marker_compare_lt_iff (left right : MarkerKey) :
    compare left right = .lt ↔ left < right :=
  compareLex_eq_lt_iff_of compare natList_compare_lt_iff natList_compare_eq_iff left right

private theorem marker_compare_eq_iff (left right : MarkerKey) :
    compare left right = .eq ↔ left = right :=
  compareLex_eq_eq_iff_of compare natList_compare_eq_iff left right

private theorem jointMarker_compare_lt_iff (left right : JointMarker) :
    compare left right = .lt ↔ left < right :=
  compareLex_eq_lt_iff_of compare marker_compare_lt_iff marker_compare_eq_iff left right

/-- The actual joint test is the complete-key order for any independent prior refining the actual
ordinary ordering. -/
theorem compareJointKeys_ne_lt_iff {P : Type*} [LinearOrder P]
    (x y : JointPromotedKey input) (p q : P)
    (prior : (input.compareLocalizedRerootCompoundThroughRule5 x.prior y.prior).ordering =
      compare p q) :
    compareJointKeys input x y ≠ .lt ↔
      toLex (q, y.markers) ≤ toLex (p, x.markers) := by
  unfold compareJointKeys
  rw [prior, Ne, then_eq_lt_iff_lex compare compare (fun _ _ => compare_lt_iff_lt)
    (fun _ _ => compare_eq_iff_eq) jointMarker_compare_lt_iff, not_lt]

/-- The actual stable insertion sort projects to the independent descending joint-key sort,
whatever order the actual tied keys take. -/
theorem sortJointKeys_markers_eq {P : Type*} [LinearOrder P]
    (keys : List (JointPromotedKey input))
    (φ : JointPromotedKey input → Lex (P × JointMarker))
    (markerEq : ∀ x, (ofLex (φ x)).2 = x.markers)
    (order : ∀ x ∈ keys, ∀ y ∈ keys, compareJointKeys input x y ≠ .lt ↔ φ y ≤ φ x) :
    (sortJointKeys input keys).map JointPromotedKey.markers =
      (Certificate.CanonicalSphereKey.sortDesc (keys.map φ)).map
        fun complete => (ofLex complete).2 := by
  have mapped : (sortJointKeys input keys).map φ =
      Certificate.CanonicalSphereKey.sortDesc (keys.map φ) :=
    List.map_insertionSort (fun a b => compareJointKeys input a b ≠ .lt)
      Certificate.CanonicalSphereKey.Desc φ keys order
  rw [← mapped, List.map_map]
  exact List.map_congr_left fun x _ => (markerEq x).symm

/-- Actual children are sorted once by full earlier priority, then by the recursively built joint
marker vector. -/
def buildJoint? (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat) :
    Nat → input.LocalizedRerootCursor carrierFuel → Option (JointPromotedKey input)
  | 0, cursor => do
      let prior ← ordinaryKey? input target view cursor
      let children ← input.executableLocalizedRerootChildren? cursor
      if children = [] then
        some ⟨prior, jointMarkers input references W D [] cursor⟩
      else none
  | fuel + 1, cursor => do
      let prior ← ordinaryKey? input target view cursor
      let children ← input.executableLocalizedRerootChildren? cursor
      let keys ← children.mapM (buildJoint? target view references W D fuel)
      some ⟨prior, jointMarkers input references W D (sortJointKeys input keys) cursor⟩

/-- Comparison of two actual joint-key branches. -/
def compareJointAt? (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor carrierFuel) : Option Ordering := do
  let l ← buildJoint? input target view references W D (2 * (carrierFuel + 1)) left
  let r ← buildJoint? input target view references W D (2 * (carrierFuel + 1)) right
  some (compareJointKeys input l r)

private theorem mapM_exists {α β : Type} (f : α → Option β) :
    ∀ xs : List α, (∀ x ∈ xs, ∃ y, f x = some y) → ∃ ys, xs.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: xs, available => by
      obtain ⟨y, hy⟩ := available x List.mem_cons_self
      obtain ⟨ys, hys⟩ := mapM_exists f xs
        (fun z hz => available z (List.mem_cons_of_mem x hz))
      exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- Adequate marker budget derives success, including rings and every reference population. -/
theorem buildJoint?_exists_of_budget (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat) :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor ≤ fuel →
      ∃ key, buildJoint? input target view references W D fuel cursor = some key := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor valid covered
      obtain ⟨prior, priorEq⟩ := ordinaryKey?_exists input target view cursor valid
      have derived := input.executableLocalizedRerootChildren_declarative cursor
      have empty : input.executableLocalizedRerootChildren cursor = [] := by
        by_contra nonempty
        obtain ⟨child, member⟩ := List.exists_mem_of_ne_nil _ nonempty
        have less := input.localizedRerootChild_budget_lt cursor child _ valid derived member
        omega
      refine ⟨⟨prior, jointMarkers input references W D [] cursor⟩, ?_⟩
      simp [buildJoint?, priorEq, input.executableLocalizedRerootChildren?_eq_some, empty]
  | succ fuel ih =>
      intro cursor valid covered
      obtain ⟨prior, priorEq⟩ := ordinaryKey?_exists input target view cursor valid
      have derived := input.executableLocalizedRerootChildren_declarative cursor
      have childComplete : ∀ child ∈ input.executableLocalizedRerootChildren cursor,
          ∃ key, buildJoint? input target view references W D fuel child = some key := by
        intro child member
        have childValid := input.localizedRerootChild_valid cursor child _ derived member
        have less := input.localizedRerootChild_budget_lt cursor child _ valid derived member
        exact ih child childValid (by omega)
      obtain ⟨keys, keysEq⟩ := mapM_exists
        (buildJoint? input target view references W D fuel) _ childComplete
      refine ⟨⟨prior, jointMarkers input references W D (sortJointKeys input keys) cursor⟩, ?_⟩
      simp [buildJoint?, priorEq, input.executableLocalizedRerootChildren?_eq_some, keysEq]

theorem buildJoint?_exists (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, buildJoint? input target view references W D (2 * (carrierFuel + 1)) cursor =
      some key :=
  buildJoint?_exists_of_budget input target view references W D _ cursor valid
    (input.localizedRerootCursorBudget_le_twice cursor)

/-- Every successful result retains exactly the actual full ordinary key at that cursor. -/
theorem buildJoint?_prior (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D fuel : Nat)
    (cursor : input.LocalizedRerootCursor carrierFuel) (key : JointPromotedKey input)
    (built : buildJoint? input target view references W D fuel cursor = some key) :
    ordinaryKey? input target view cursor = some key.prior := by
  cases fuel <;>
    simp only [buildJoint?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
  · obtain ⟨prior, hp, children, _, rest⟩ := built
    split at rest
    · cases Option.some.inj rest
      exact hp
    · cases rest
  · obtain ⟨prior, hp, children, _, keys, _, same⟩ := built
    cases Option.some.inj same
    exact hp

private theorem getD_map_of_lt {α β : Type*} (f : α → β) (default : β)
    (list : List α) (index : Nat) (bound : index < list.length) :
    (list.map f).getD index default = f list[index] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem bound,
    Option.map_some, Option.getD_some]

theorem referenceVector_getD (references : List input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel) (index : Nat)
    (indexBound : index < references.length) :
    (referenceVector input references cursor).getD index 0 =
      referenceBit input references[index] cursor := by
  rw [referenceVector, getD_map_of_lt
    (fun reference => referenceBit input reference cursor) 0 references index indexBound]

/-- A successful joint build records the node's own mark vector at level zero. -/
theorem buildJoint?_markers_head (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D fuel : Nat)
    (cursor : input.LocalizedRerootCursor carrierFuel) (key : JointPromotedKey input)
    (built : buildJoint? input target view references W D fuel cursor = some key)
    (index : Nat) (indexBound : index < references.length) :
    ((key.markers.getD index []).getD 0 []).getD 0 0 =
      (referenceVector input references cursor).getD index 0 := by
  cases fuel <;>
    simp only [buildJoint?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
  · obtain ⟨prior, _, children, _, rest⟩ := built
    split at rest
    · cases Option.some.inj rest
      unfold jointMarkers
      rw [assembleJointMarker_getD W D references.length _ _ indexBound]
      simp [assembleMarker]
    · cases rest
  · obtain ⟨prior, _, children, _, keys, _, same⟩ := built
    cases Option.some.inj same
    unfold jointMarkers
    rw [assembleJointMarker_getD W D references.length _ _ indexBound]
    simp [assembleMarker]

/-- The node's own reference bit is read back from the corresponding column. -/
theorem buildJoint?_bit (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D fuel : Nat)
    (cursor : input.LocalizedRerootCursor carrierFuel) (key : JointPromotedKey input)
    (built : buildJoint? input target view references W D fuel cursor = some key)
    (index : Nat) (indexBound : index < references.length) :
    ((key.markers.getD index []).getD 0 []).getD 0 0 =
      referenceBit input references[index] cursor := by
  rw [buildJoint?_markers_head input target view references W D fuel cursor key built index
    indexBound, referenceVector_getD input references cursor index indexBound]

/-- Comparison succeeds without assuming successful child builds or sorting. -/
theorem compareJointAt?_exists (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid left)
    (rightValid : input.LocalizedRerootCursorValid right) :
    ∃ order, compareJointAt? input target view references W D left right = some order := by
  obtain ⟨l, hl⟩ := buildJoint?_exists input target view references W D left leftValid
  obtain ⟨r, hr⟩ := buildJoint?_exists input target view references W D right rightValid
  exact ⟨compareJointKeys input l r, by simp [compareJointAt?, hl, hr]⟩

/-- At every valid recursive cursor, a strict complete ordinary decision survives joint promotion.
The original target/view are fixed; ordinary keys are the actual full compound builds. -/
theorem compareJointAt?_preserves_ordinary (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid left)
    (rightValid : input.LocalizedRerootCursorValid right)
    (leftKey rightKey : input.LocalizedRerootCompoundRule45Key)
    (leftBuilt : ordinaryKey? input target view left = some leftKey)
    (rightBuilt : ordinaryKey? input target view right = some rightKey)
    (strict : (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey).ordering
      ≠ .eq) :
    compareJointAt? input target view references W D left right =
      some (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey).ordering := by
  obtain ⟨l, hl⟩ := buildJoint?_exists input target view references W D left leftValid
  obtain ⟨r, hr⟩ := buildJoint?_exists input target view references W D right rightValid
  have lp : l.prior = leftKey := Option.some.inj
    ((buildJoint?_prior input target view references W D _ left l hl).symm.trans leftBuilt)
  have rp : r.prior = rightKey := Option.some.inj
    ((buildJoint?_prior input target view references W D _ right r hr).symm.trans rightBuilt)
  simp only [compareJointAt?, hl, hr, Option.bind_eq_bind, Option.bind_some]
  congr 1
  have strict' : (input.compareLocalizedRerootCompoundThroughRule5 l.prior r.prior).ordering
      ≠ .eq := by
    simpa only [lp, rp] using strict
  rw [compareJointKeys_of_prior_ne input l r strict', lp, rp]

end Runtime

/-! ## Realized-tree bridge: runtime joint marker = independent joint key -/

section Bridge

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}

/-- The ordered vector of independent reference observations at a hierarchy node. -/
def referenceMarks (references : List input.Atom)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (node : (ruleMajorTreeGraph tree).Node) : List Nat :=
  references.map fun reference => referenceMark input reference tree node

/-! ### List helper re-statements

The corresponding helpers are private in `LocalizedMarkedRetainedCanonicalMarker`; these are
independent copies with the same statements, kept private to this module. -/

private theorem mapM_forall₂ {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys →
      List.Forall₂ (fun x y => f x = some y) xs ys
  | [], ys, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      exact .nil
  | x :: xs, ys, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at h
      obtain ⟨y, hy, rest, hrest, rfl⟩ := h
      exact .cons hy (mapM_forall₂ f xs rest hrest)

private theorem forall₂_imp_mem {α β : Type*} {R S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, (∀ a ∈ l, ∀ b, R a b → S a b) →
      List.Forall₂ R l m → List.Forall₂ S l m
  | [], [], _, _ => .nil
  | a :: _, _ :: _, h, .cons hab rest =>
      .cons (h a (by simp) _ hab)
        (forall₂_imp_mem (fun x hx y hy => h x (by simp [hx]) y hy) rest)

private theorem exists_of_mem_forall₂_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ b ∈ m, ∃ a ∈ l, R a b
  | [], [], _, b, hb => by simp at hb
  | a :: _, _ :: _, .cons h rest, b, hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨a, by simp, h⟩
      · obtain ⟨a', ha', h'⟩ := exists_of_mem_forall₂_right rest b hb
        exact ⟨a', by simp [ha'], h'⟩

private theorem map_eq_of_forall₂ {α β γ : Type*} {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {m : List β}, List.Forall₂ (fun a b => f a = g b) l m → l.map f = m.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h rest => by
      simp only [List.map_cons, h, map_eq_of_forall₂ rest]

/-- At every node of any realized tree, every successful actual joint build returns the independent
canonical joint marker of that node for the independent prior and all references.  Sibling prior
agreement is the only premise; it mentions no marker, sort result or reference selection. -/
theorem buildJoint?_markers_eq_jointMarkerKey
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (references : List input.Atom) (W D : Nat)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {P : Type*} [LinearOrder P] (prior : (ruleMajorTreeGraph tree).Node → P)
    (agree : SiblingPriorAgreement input target view tree prior) :
    ∀ node fuel result,
      buildJoint? input target view references W D fuel
          (nodeSource input tree node) = some result →
      result.markers = jointMarkerKey (ruleMajorTreeGraph tree) prior
        (referenceMarks input references tree) W D references.length node := by
  refine node_induction (ruleMajorTreeGraph tree) ?_
  intro node ih fuel result built
  obtain ⟨sub, lookup⟩ := exists_local_subtree tree node
  have source := nodeSource_of_lookup input tree lookup
  obtain ⟨slots, slotsPerm, execPerm⟩ := slot_children input tree realizes node sub lookup
  have childOf : ∀ a ∈ slots, (ruleMajorTreeGraph tree).child node a := fun a member =>
    ((ruleMajorTreeGraph tree).mem_childList).1 (slotsPerm.subset member)
  rw [jointMarkerKey_eq]
  unfold rankedJointKeys
  rw [← Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
    (slotsPerm.map (jointKey (ruleMajorTreeGraph tree) prior
      (referenceMarks input references tree) W D references.length))]
  rw [source] at built
  cases fuel with
  | zero =>
      simp only [buildJoint?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        executableLocalizedRerootChildren?_eq_some, Option.some.injEq] at built
      obtain ⟨prior₀, _, children, childrenEq, rest⟩ := built
      split at rest
      · rename_i empty
        cases Option.some.inj rest
        subst childrenEq
        rw [empty] at execPerm
        have noSlots : slots = [] := List.map_eq_nil_iff.1 execPerm.eq_nil
        subst noSlots
        unfold jointMarkers
        simp [referenceVector, referenceMarks, referenceMark, source,
          Certificate.CanonicalSphereKey.sortDesc]
      · cases rest
  | succ fuel =>
      classical
      simp only [buildJoint?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        executableLocalizedRerootChildren?_eq_some, Option.some.injEq] at built
      obtain ⟨prior₀, _, children, childrenEq, keys, keysEq, same⟩ := built
      subst childrenEq
      subst same
      have related := mapM_forall₂ _ _ _ keysEq
      obtain ⟨keys₀, related₀, perm₀⟩ := List.perm_comp_forall₂ execPerm related
      have slotRelated : List.Forall₂ (fun a x =>
          buildJoint? input target view references W D fuel (nodeSource input tree a) = some x)
          slots keys₀ := List.forall₂_map_left_iff.1 related₀
      let priorOf : JointPromotedKey input → P := fun x =>
        if h : ∃ a ∈ slots, buildJoint? input target view references W D fuel
            (nodeSource input tree a) = some x then prior (Classical.choose h) else prior node
      have priorOf_eq : ∀ a ∈ slots, ∀ x,
          buildJoint? input target view references W D fuel (nodeSource input tree a) = some x →
            priorOf x = prior a := by
        intro a member x builtA
        have present : ∃ a ∈ slots, buildJoint? input target view references W D fuel
            (nodeSource input tree a) = some x := ⟨a, member, builtA⟩
        simp only [priorOf]
        rw [dif_pos present]
        obtain ⟨member', built'⟩ := Classical.choose_spec present
        have ordA := buildJoint?_prior input target view references W D _ _ _ builtA
        have ordA' := buildJoint?_prior input target view references W D _ _ _ built'
        have cross := agree node _ a (childOf _ member') (childOf a member) _ _ ordA' ordA
        have self := agree node a a (childOf a member) (childOf a member) _ _ ordA ordA
        rw [show compare (prior a) (prior a) = .eq from compare_eq_iff_eq.2 rfl] at self
        exact compare_eq_iff_eq.1 (cross.symm.trans self)
      let φ : JointPromotedKey input → Lex (P × JointMarker) :=
        fun x => toLex (priorOf x, x.markers)
      have keyMembers : ∀ x ∈ keys, ∃ a ∈ slots,
          buildJoint? input target view references W D fuel (nodeSource input tree a) = some x :=
        fun x member => exists_of_mem_forall₂_right slotRelated x (perm₀.symm.subset member)
      have order : ∀ x ∈ keys, ∀ y ∈ keys, compareJointKeys input x y ≠ .lt ↔ φ y ≤ φ x := by
        intro x xMember y yMember
        obtain ⟨a, aMember, builtA⟩ := keyMembers x xMember
        obtain ⟨b, bMember, builtB⟩ := keyMembers y yMember
        have ordA := buildJoint?_prior input target view references W D _ _ _ builtA
        have ordB := buildJoint?_prior input target view references W D _ _ _ builtB
        have pairwise := agree node a b (childOf a aMember) (childOf b bMember) _ _ ordA ordB
        simp only [φ, priorOf_eq a aMember x builtA, priorOf_eq b bMember y builtB]
        exact compareJointKeys_ne_lt_iff input x y (prior a) (prior b) pairwise
      have sorted := sortJointKeys_markers_eq input keys φ (fun _ => rfl) order
      have keyed : keys₀.map φ = slots.map
          (jointKey (ruleMajorTreeGraph tree) prior
            (referenceMarks input references tree) W D references.length) := by
        symm
        apply map_eq_of_forall₂
        refine forall₂_imp_mem ?_ slotRelated
        intro a member x builtA
        rw [jointKey_eq_marker, ← ih a (childOf a member) fuel x builtA]
        simp only [φ, priorOf_eq a member x builtA]
      unfold jointMarkers
      simp only [referenceVector, referenceMarks, referenceMark, source]
      congr 1
      rw [sorted, Certificate.CanonicalSphereKey.sortDesc_eq_of_perm (perm₀.map φ).symm,
        keyed]

/-- At the tree's root: the actual joint marker of the ligand is the independent joint marker of
its realized hierarchy. -/
theorem root_jointMarkerKey_eq
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (references : List input.Atom) (W D : Nat)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {P : Type*} [LinearOrder P] (prior : (ruleMajorTreeGraph tree).Node → P)
    (agree : SiblingPriorAgreement input target view tree prior) (fuel : Nat)
    (result : JointPromotedKey input)
    (built : buildJoint? input target view references W D fuel tree.source = some result) :
    result.markers = jointMarkerKey (ruleMajorTreeGraph tree) prior
      (referenceMarks input references tree) W D references.length
        (ruleMajorTreeGraph tree).root := by
  apply buildJoint?_markers_eq_jointMarkerKey input target view references W D tree realizes prior
    agree
  simpa only [nodeSource_root] using built

/-- From an actual tie of two realized-tree joint builds, construct the pair of joint-canonical
addressings on which every reference coordinate agrees.  The tie is at the built keys; converting
a frame-level refined-key tie into this hypothesis is the documented missing adapter. -/
theorem matched_joint_marker_addressings_of_built_tie
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (references : List input.Atom) (W D : Nat)
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realR : LocalizedCumulativeTreeRealizes input readR treeR)
    {P : Type*} [LinearOrder P]
    (priorL : (ruleMajorTreeGraph treeL).Node → P)
    (priorR : (ruleMajorTreeGraph treeR).Node → P)
    (agreeL : SiblingPriorAgreement input target view treeL priorL)
    (agreeR : SiblingPriorAgreement input target view treeR priorR)
    (fuelL fuelR : Nat) (resultL resultR : JointPromotedKey input)
    (builtL : buildJoint? input target view references W D fuelL treeL.source = some resultL)
    (builtR : buildJoint? input target view references W D fuelR treeR.source = some resultR)
    (tie : compareJointKeys input resultL resultR = .eq)
    (widthL : ∀ node, ((ruleMajorTreeGraph treeL).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph treeL).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph treeR).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph treeR).height ≤ D)
    (baseL : (ruleMajorTreeGraph treeL).Addressing)
    (baseR : (ruleMajorTreeGraph treeR).Addressing) :
    Nonempty (MatchedJointMarkerAddressings (ruleMajorTreeGraph treeL)
      (ruleMajorTreeGraph treeR) priorL priorR
      (referenceMarks input references treeL) (referenceMarks input references treeR)
      references.length W D) := by
  have markers : resultL.markers = resultR.markers :=
    ((compareJointKeys_eq_iff input resultL resultR).1 tie).2
  have leftRoot : resultL.markers =
      jointMarkerKey (ruleMajorTreeGraph treeL) priorL
        (referenceMarks input references treeL) W D references.length
          (ruleMajorTreeGraph treeL).root :=
    root_jointMarkerKey_eq input target view references W D treeL realL priorL agreeL fuelL
      resultL builtL
  have rightRoot : resultR.markers =
      jointMarkerKey (ruleMajorTreeGraph treeR) priorR
        (referenceMarks input references treeR) W D references.length
          (ruleMajorTreeGraph treeR).root :=
    root_jointMarkerKey_eq input target view references W D treeR realR priorR agreeR fuelR
      resultR builtR
  have equal : jointMarkerKey (ruleMajorTreeGraph treeL) priorL
        (referenceMarks input references treeL) W D references.length
          (ruleMajorTreeGraph treeL).root =
      jointMarkerKey (ruleMajorTreeGraph treeR) priorR
        (referenceMarks input references treeR) W D references.length
          (ruleMajorTreeGraph treeR).root := by
    rw [← leftRoot, ← rightRoot, markers]
  exact exists_matched_joint_marker_addressings (ruleMajorTreeGraph treeL)
    (ruleMajorTreeGraph treeR) priorL priorR
    (referenceMarks input references treeL) (referenceMarks input references treeR)
    references.length W D widthL heightL widthR heightR baseL baseR equal

/-- At jointly occupied addresses, every listed reference predicate agrees, including duplicate
occurrences bearing the same atom.  This is address-level agreement, not a graph isomorphism. -/
theorem reference_atoms_iff_of_matched_joint_addresses
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel)
    (references : List input.Atom) (W D : Nat)
    {P : Type*} [LinearOrder P]
    {priorL : (ruleMajorTreeGraph treeL).Node → P}
    {priorR : (ruleMajorTreeGraph treeR).Node → P}
    (matched : MatchedJointMarkerAddressings (ruleMajorTreeGraph treeL)
      (ruleMajorTreeGraph treeR) priorL priorR
      (referenceMarks input references treeL) (referenceMarks input references treeR)
      references.length W D)
    (x : (ruleMajorTreeGraph treeL).Node) (y : (ruleMajorTreeGraph treeR).Node)
    (address : matched.leftAddressing.address x = matched.rightAddressing.address y)
    (index : Nat) (indexBound : index < references.length) :
    (nodeSource input treeL x).occurrence.1.node.current? = some references[index] ↔
      (nodeSource input treeR y).occurrence.1.node.current? = some references[index] := by
  have same := matched.marks_eq x y address index indexBound
  have leftBit : (referenceMarks input references treeL x).getD index 0 =
      referenceBit input references[index] (nodeSource input treeL x) := by
    rw [referenceMarks, getD_map_of_lt
      (fun reference => referenceMark input reference treeL x) 0 references index indexBound]
    simp [referenceMark]
  have rightBit : (referenceMarks input references treeR y).getD index 0 =
      referenceBit input references[index] (nodeSource input treeR y) := by
    rw [referenceMarks, getD_map_of_lt
      (fun reference => referenceMark input reference treeR y) 0 references index indexBound]
    simp [referenceMark]
  rw [leftBit, rightBit] at same
  unfold referenceBit at same
  by_cases left : (nodeSource input treeL x).occurrence.1.node.current? =
      some references[index] <;>
    by_cases right : (nodeSource input treeR y).occurrence.1.node.current? =
      some references[index] <;>
    simp_all

end Bridge

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.assembleJointMarker_getD
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.assembleJointMarker_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.jointKey_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.jointKey_prior
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.jointMarkerKey_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.jointKey_eq_marker
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.jointMarkerKey_wellShaped
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.prior_le_of_jointKey_le
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.rankedJointKeys_prior
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.jointCanonicalAddressing_prior_sorted
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.exists_jointCanonicalAddressing
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.jointKey_iso
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.jointMarkerKey_iso
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.address_slots_lt_of_branching
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.addressJointMarker_eq_keyObservation
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.addressMarkers_eq_of_root_jointMarker_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.MatchedJointMarkerAddressings
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.MatchedJointMarkerAddressings.prior_sorted
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.MatchedJointMarkerAddressings.marks_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.MatchedJointMarkerAddressings.marks_preserved_of_address_alignment
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.exists_matched_joint_marker_addressings
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.compareJointKeys_eq_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.compareJointKeys_ne_lt_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.sortJointKeys_markers_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?_exists_of_budget
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?_prior
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.referenceVector_getD
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?_markers_head
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?_bit
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.compareJointAt?_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.compareJointAt?_preserves_ordinary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?_markers_eq_jointMarkerKey
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.root_jointMarkerKey_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.matched_joint_marker_addressings_of_built_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.reference_atoms_iff_of_matched_joint_addresses
