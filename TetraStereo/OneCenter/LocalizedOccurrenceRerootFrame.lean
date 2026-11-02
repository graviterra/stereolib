import TetraStereo.OneCenter.LocalizedOccurrenceCarrier

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Occurrence-local reroot frames

Auxiliary descriptors are assigned at an occurrence, not by looking up an atom-global label.
This module constructs the format-neutral analogue of the revised-CIP zipper: an occurrence can
move once toward its original root or into any official outward child, while the immediately
previous occurrence is cut from the next step.  Ring and multiple-bond duplicates remain terminal
because that fact is retained in `OfficialCIPNode.provenance`.

Every cursor coordinate is a member of the finite carrier from `LocalizedOccurrenceCarrier`.
Frame construction is fail-closed if an intended neighbor is absent from that carrier.  A
successful result proves exact ordered equality with the independently defined intended neighbor
frames, rather than merely proving that each emitted cursor is plausible.
-/

namespace CertifiedLocalizedCIPInput

/-- Carrier parents at the immediately shorter root-relative address.  The complete official
occurrence tree has at most one; retaining a list makes membership and adjacency symmetry
structural rather than dependent on a search-choice theorem. -/
def localizedCarrierParentFrames
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedCIPOccurrenceFrame) :
    List input.LocalizedCIPOccurrenceFrame :=
  (input.localizedOccurrences fuel).filter fun candidate =>
    candidate.root == frame.root &&
      candidate.address.length + 1 == frame.address.length &&
      candidate.address == frame.address.dropLast

/-- Every selected shorter-address parent frame is an actual member of the finite carrier. -/
theorem mem_localizedOccurrences_of_mem_localizedCarrierParentFrames
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (source frame : input.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ input.localizedCarrierParentFrames (fuel := fuel) source) :
    frame ∈ input.localizedOccurrences fuel := by
  exact List.mem_of_mem_filter present

/-- The canonical first-axis occurrence has exactly its terminal-root occurrence as carrier
parent. Shared-root family duplication cannot create ambiguity because the common carrier is
deduplicated. -/
theorem localizedCarrierParentFrames_evenAxialFirstChild_eq_singleton
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    input.localizedCarrierParentFrames (fuel := fuel)
        (input.localizedEvenAxialFirstChildOccurrence fuel axis).1 =
      [(input.localizedEvenAxialRootOccurrence fuel axis).1] := by
  let child := input.localizedEvenAxialFirstChildOccurrence fuel axis
  let root := input.localizedEvenAxialRootOccurrence fuel axis
  have rootPresent : root.1 ∈
      input.localizedCarrierParentFrames (fuel := fuel) child.1 := by
    rw [localizedCarrierParentFrames, List.mem_filter]
    refine ⟨root.2, ?_⟩
    simp [root, child]
  have onlyRoot : ∀ candidate,
      candidate ∈ input.localizedCarrierParentFrames (fuel := fuel) child.1 →
        candidate = root.1 := by
    intro candidate present
    rw [localizedCarrierParentFrames, List.mem_filter] at present
    rcases present with ⟨candidatePresent, conditions⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at conditions
    have candidateAddress : candidate.address = [] := by
      simpa [child] using conditions.2
    have candidateRoot : candidate.root = axis.1.root.terminal := by
      simpa [child] using conditions.1.1
    have identity :=
      input.declarativeLocalizedOccurrence_eq_root_of_address_nil
        ((input.mem_localizedOccurrences_iff fuel candidate).mp candidatePresent)
        candidateAddress
    rw [identity]
    apply LocalizedCIPOccurrenceFrame.ext <;>
      simp [root, candidateRoot]
  have parentNodup :
      (input.localizedCarrierParentFrames (fuel := fuel) child.1).Nodup := by
    unfold localizedCarrierParentFrames
    exact (input.localizedOccurrences_nodup fuel).filter _
  have sameMembers : ∀ candidate,
      candidate ∈ input.localizedCarrierParentFrames (fuel := fuel) child.1 ↔
        candidate ∈ [root.1] := by
    intro candidate
    constructor
    · intro present
      simp [onlyRoot candidate present]
    · intro present
      simp only [List.mem_singleton] at present
      subst candidate
      exact rootPresent
  have permutation :
      List.Perm (input.localizedCarrierParentFrames (fuel := fuel) child.1) [root.1] :=
    (List.perm_ext_iff_of_nodup parentNodup (by simp)).mpr sameMembers
  exact List.perm_singleton.mp permutation

/-- The first child of any perceived maximal open consecutive-double-bond root has exactly its
atom-root occurrence as carrier parent, independently of later odd/even parity. -/
theorem localizedCarrierParentFrames_axialRootFirstChild_eq_singleton
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axialRoot : input.LocalizedAxialRoot) :
    input.localizedCarrierParentFrames (fuel := fuel)
        (input.localizedAxialRootFirstChildOccurrence fuel axialRoot).1 =
      [(input.localizedAxialRootOccurrence fuel axialRoot).1] := by
  let child := input.localizedAxialRootFirstChildOccurrence fuel axialRoot
  let root := input.localizedAxialRootOccurrence fuel axialRoot
  have rootPresent : root.1 ∈
      input.localizedCarrierParentFrames (fuel := fuel) child.1 := by
    rw [localizedCarrierParentFrames, List.mem_filter]
    refine ⟨root.2, ?_⟩
    simp [root, child]
  have onlyRoot : ∀ candidate,
      candidate ∈ input.localizedCarrierParentFrames (fuel := fuel) child.1 →
        candidate = root.1 := by
    intro candidate present
    rw [localizedCarrierParentFrames, List.mem_filter] at present
    rcases present with ⟨candidatePresent, conditions⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at conditions
    have candidateAddress : candidate.address = [] := by
      simpa [child] using conditions.2
    have candidateRoot : candidate.root = axialRoot.1.terminal := by
      simpa [child] using conditions.1.1
    have identity :=
      input.declarativeLocalizedOccurrence_eq_root_of_address_nil
        ((input.mem_localizedOccurrences_iff fuel candidate).mp candidatePresent)
        candidateAddress
    rw [identity]
    apply LocalizedCIPOccurrenceFrame.ext <;>
      simp [root, candidateRoot, localizedAxialRootOccurrence,
        localizedAtomRootOccurrence]
  have parentNodup :
      (input.localizedCarrierParentFrames (fuel := fuel) child.1).Nodup := by
    unfold localizedCarrierParentFrames
    exact (input.localizedOccurrences_nodup fuel).filter _
  have sameMembers : ∀ candidate,
      candidate ∈ input.localizedCarrierParentFrames (fuel := fuel) child.1 ↔
        candidate ∈ [root.1] := by
    intro candidate
    constructor
    · intro present
      simp [onlyRoot candidate present]
    · intro present
      simp only [List.mem_singleton] at present
      subst candidate
      exact rootPresent
  have permutation :
      List.Perm (input.localizedCarrierParentFrames (fuel := fuel) child.1) [root.1] :=
    (List.perm_ext_iff_of_nodup parentNodup (by simp)).mpr sameMembers
  exact List.perm_singleton.mp permutation

/-- A canonical molecule-wide double-bond first child has exactly its arbitrary-atom root as
carrier parent. -/
theorem localizedCarrierParentFrames_canonicalDoubleBondFirstChild_eq_singleton
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    input.localizedCarrierParentFrames (fuel := fuel)
        (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond).1 =
      [(input.localizedAtomRootOccurrence fuel bond.1.1).1] := by
  let child := input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond
  let root := input.localizedAtomRootOccurrence fuel bond.1.1
  have rootPresent : root.1 ∈
      input.localizedCarrierParentFrames (fuel := fuel) child.1 := by
    rw [localizedCarrierParentFrames, List.mem_filter]
    refine ⟨root.2, ?_⟩
    simp [root, child]
  have onlyRoot : ∀ candidate,
      candidate ∈ input.localizedCarrierParentFrames (fuel := fuel) child.1 →
        candidate = root.1 := by
    intro candidate present
    rw [localizedCarrierParentFrames, List.mem_filter] at present
    rcases present with ⟨candidatePresent, conditions⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at conditions
    have candidateAddress : candidate.address = [] := by
      simpa [child] using conditions.2
    have candidateRoot : candidate.root = bond.1.1 := by
      simpa [child] using conditions.1.1
    have identity :=
      input.declarativeLocalizedOccurrence_eq_root_of_address_nil
        ((input.mem_localizedOccurrences_iff fuel candidate).mp candidatePresent)
        candidateAddress
    rw [identity]
    apply LocalizedCIPOccurrenceFrame.ext <;>
      simp [root, candidateRoot]
  have parentNodup :
      (input.localizedCarrierParentFrames (fuel := fuel) child.1).Nodup := by
    unfold localizedCarrierParentFrames
    exact (input.localizedOccurrences_nodup fuel).filter _
  have sameMembers : ∀ candidate,
      candidate ∈ input.localizedCarrierParentFrames (fuel := fuel) child.1 ↔
        candidate ∈ [root.1] := by
    intro candidate
    constructor
    · intro present
      simp [onlyRoot candidate present]
    · intro present
      simp only [List.mem_singleton] at present
      subst candidate
      exact rootPresent
  have permutation :
      List.Perm (input.localizedCarrierParentFrames (fuel := fuel) child.1) [root.1] :=
    (List.perm_ext_iff_of_nodup parentNodup (by simp)).mpr sameMembers
  exact List.perm_singleton.mp permutation

/-- All immediate carrier children in their original official depth-first sibling order. -/
def localizedCarrierOutwardChildFrames
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedCIPOccurrenceFrame) :
    List input.LocalizedCIPOccurrenceFrame :=
  (input.localizedOccurrences fuel).filter fun candidate =>
    candidate.root == frame.root &&
      candidate.address.length == frame.address.length + 1 &&
      candidate.address.dropLast == frame.address

/-- The uncut finite-tree zipper neighborhood: carrier parent first, then exact carrier children. -/
def localizedRerootNeighborFrames
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedCIPOccurrenceFrame) :
    List input.LocalizedCIPOccurrenceFrame :=
  input.localizedCarrierParentFrames (fuel := fuel) frame ++
    input.localizedCarrierOutwardChildFrames (fuel := fuel) frame

/-- Address grading separates parent and outward coordinates, so the uncut carrier neighborhood
inherits duplicate-freedom from the shared occurrence carrier. -/
theorem localizedRerootNeighborFrames_nodup
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (input.localizedRerootNeighborFrames (fuel := fuel) frame).Nodup := by
  rw [localizedRerootNeighborFrames, List.nodup_append]
  refine ⟨(input.localizedOccurrences_nodup fuel).filter _,
    (input.localizedOccurrences_nodup fuel).filter _, ?_⟩
  intro candidate parentPresent _sameCandidate outwardPresent identity
  subst identity
  rw [localizedCarrierParentFrames, List.mem_filter] at parentPresent
  rw [localizedCarrierOutwardChildFrames, List.mem_filter] at outwardPresent
  simp only [Bool.and_eq_true, beq_iff_eq] at parentPresent outwardPresent
  omega

/-- A reroot cursor retains its exact carrier coordinate and the incoming coordinate that must be
cut before its next expansion. -/
structure LocalizedRerootCursor
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  occurrence : input.LocalizedCIPOccurrence fuel
  previous? : Option (input.LocalizedCIPOccurrence fuel) := none

@[ext] theorem LocalizedRerootCursor.ext
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {left right : input.LocalizedRerootCursor fuel}
    (occurrence : left.occurrence = right.occurrence)
    (previous : left.previous? = right.previous?) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Intended children of one cursor before carrier-membership certification.  Duplicate nodes
are forced leaves.  Otherwise only the exact incoming coordinate is removed. -/
def intendedLocalizedRerootChildFrames
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    List input.LocalizedCIPOccurrenceFrame :=
  if cursor.occurrence.1.node.isDuplicateLeaf then []
  else
    match cursor.previous? with
    | none => input.localizedRerootNeighborFrames (fuel := fuel) cursor.occurrence.1
    | some previous =>
        (input.localizedRerootNeighborFrames (fuel := fuel)
          cursor.occurrence.1).filter fun frame =>
          frame.address != previous.1.address

/-- Cutting an incoming address and making duplicate nodes terminal preserve coordinate
duplicate-freedom. -/
theorem intendedLocalizedRerootChildFrames_nodup
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.intendedLocalizedRerootChildFrames cursor).Nodup := by
  unfold intendedLocalizedRerootChildFrames
  split
  · exact List.nodup_nil
  · split
    · exact input.localizedRerootNeighborFrames_nodup cursor.occurrence.1
    · exact (input.localizedRerootNeighborFrames_nodup cursor.occurrence.1).filter _

/-- Every uncut zipper neighbor is an actual member of the finite occurrence carrier. -/
theorem mem_localizedOccurrences_of_mem_localizedRerootNeighborFrames
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (source frame : input.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ input.localizedRerootNeighborFrames (fuel := fuel) source) :
    frame ∈ input.localizedOccurrences fuel := by
  rw [localizedRerootNeighborFrames, List.mem_append] at present
  rcases present with parent | child
  · exact List.mem_of_mem_filter parent
  · exact List.mem_of_mem_filter child

/-- Every intended cut-neighborhood frame is present in the finite carrier. -/
theorem mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (frame : input.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ input.intendedLocalizedRerootChildFrames cursor) :
    frame ∈ input.localizedOccurrences fuel := by
  unfold intendedLocalizedRerootChildFrames at present
  split at present
  · simp at present
  · split at present
    · exact input.mem_localizedOccurrences_of_mem_localizedRerootNeighborFrames
        cursor.occurrence.1 frame present
    · exact input.mem_localizedOccurrences_of_mem_localizedRerootNeighborFrames
        cursor.occurrence.1 frame (List.mem_of_mem_filter present)

/-- Fail-closed zipper expansion.  No intended coordinate can disappear: all must be proved to
belong to the finite molecular occurrence carrier before any child list is returned. -/
noncomputable def localizedRerootChildren?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    Option (List (input.LocalizedRerootCursor fuel)) := by
  classical
  let intended := input.intendedLocalizedRerootChildFrames cursor
  if present : ∀ frame ∈ intended, frame ∈ input.localizedOccurrences fuel then
    exact some (intended.attach.map fun frame =>
      { occurrence := ⟨frame.1, present frame.1 frame.2⟩
        previous? := some cursor.occurrence })
  else
    exact none

/-- Fail-closed expansion cannot fail on a cursor whose coordinate belongs to the carrier. -/
theorem exists_localizedRerootChildren
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    ∃ children, input.localizedRerootChildren? cursor = some children := by
  classical
  unfold localizedRerootChildren?
  rw [dif_pos]
  · exact ⟨_, rfl⟩
  · intro frame present
    exact input.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames
      cursor frame present

/-- Independent exact meaning of a successful zipper expansion. -/
def DeclarativeLocalizedRerootChildren
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel)) : Prop :=
  children.map (fun child => child.occurrence.1) =
      input.intendedLocalizedRerootChildFrames cursor ∧
    ∀ child ∈ children, child.previous? = some cursor.occurrence

/-- Every successful zipper expansion is exactly the independently specified ordered frame. -/
theorem localizedRerootChildren?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    input.DeclarativeLocalizedRerootChildren cursor children := by
  classical
  simp only [localizedRerootChildren?] at computed
  split at computed
  · rename_i present
    simp only [Option.some.injEq] at computed
    subst children
    constructor
    · simp
    · intro child childPresent
      rw [List.mem_map] at childPresent
      rcases childPresent with ⟨frame, _framePresent, childIdentity⟩
      subst child
      rfl
  · simp at computed

/-- A successful zipper expansion never repeats a cursor. -/
theorem localizedRerootChildren_nodup
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (derived : input.DeclarativeLocalizedRerootChildren cursor children) :
    children.Nodup := by
  have mappedNodup :
      (children.map (fun child => child.occurrence.1)).Nodup := by
    rw [derived.1]
    exact input.intendedLocalizedRerootChildFrames_nodup cursor
  rw [List.nodup_iff_pairwise_ne] at mappedNodup ⊢
  rw [List.pairwise_map] at mappedNodup
  apply mappedNodup.imp
  intro left right frameDifferent cursorIdentity
  exact frameDifferent (congrArg (fun child => child.occurrence.1) cursorIdentity)

/-- Two cursor lists with the same ordered occurrence frames and the same incoming coordinate are
equal.  Subtype membership proofs are erased by extensionality. -/
private theorem localizedRerootCursorLists_unique
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (previous : Option (input.LocalizedCIPOccurrence fuel)) :
    ∀ (first second : List (input.LocalizedRerootCursor fuel)),
      first.map (fun child => child.occurrence.1) =
          second.map (fun child => child.occurrence.1) →
      (∀ child ∈ first, child.previous? = previous) →
      (∀ child ∈ second, child.previous? = previous) →
      first = second
  | [], [], _mapped, _firstPrevious, _secondPrevious => rfl
  | [], _ :: _, mapped, _firstPrevious, _secondPrevious => by
      simp at mapped
  | _ :: _, [], mapped, _firstPrevious, _secondPrevious => by
      simp at mapped
  | first :: firstTail, second :: secondTail, mapped,
      firstPrevious, secondPrevious => by
      simp only [List.map_cons, List.cons.injEq] at mapped
      rcases mapped with ⟨headFrame, tailFrames⟩
      have headPrevious : first.previous? = second.previous? :=
        (firstPrevious first (by simp)).trans
          (secondPrevious second (by simp)).symm
      have headIdentity : first = second := by
        cases first with
        | mk firstOccurrence firstPreviousCoordinate =>
            cases second with
            | mk secondOccurrence secondPreviousCoordinate =>
                have occurrenceIdentity : firstOccurrence = secondOccurrence :=
                  Subtype.ext headFrame
                subst secondOccurrence
                cases headPrevious
                rfl
      subst second
      congr 1
      exact input.localizedRerootCursorLists_unique previous
        firstTail secondTail tailFrames
        (fun child present => firstPrevious child (by simp [present]))
        (fun child present => secondPrevious child (by simp [present]))

/-- The independent exact ordered-frame relation characterizes successful zipper expansion in
both directions. -/
theorem localizedRerootChildren?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel)) :
    input.localizedRerootChildren? cursor = some children ↔
      input.DeclarativeLocalizedRerootChildren cursor children := by
  constructor
  · exact input.localizedRerootChildren?_sound cursor children
  · intro derived
    classical
    unfold localizedRerootChildren?
    by_cases present : ∀ frame ∈ input.intendedLocalizedRerootChildFrames cursor,
        frame ∈ input.localizedOccurrences fuel
    · rw [dif_pos present]
      let built : List (input.LocalizedRerootCursor fuel) :=
        (input.intendedLocalizedRerootChildFrames cursor).attach.map fun frame =>
          { occurrence := ⟨frame.1, present frame.1 frame.2⟩
            previous? := some cursor.occurrence }
      have builtDerived : input.DeclarativeLocalizedRerootChildren cursor built := by
        constructor
        · simp [built]
        · intro child childPresent
          rw [List.mem_map] at childPresent
          rcases childPresent with ⟨frame, _framePresent, rfl⟩
          rfl
      apply congrArg some
      apply input.localizedRerootCursorLists_unique (some cursor.occurrence)
      · exact builtDerived.1.trans derived.1.symm
      · exact builtDerived.2
      · exact derived.2
    · rw [dif_neg present]
      exfalso
      apply present
      intro frame framePresent
      have childFramePresent : frame ∈
          children.map (fun child => child.occurrence.1) := by
        rw [derived.1]
        exact framePresent
      rw [List.mem_map] at childFramePresent
      rcases childFramePresent with ⟨child, _childPresent, frameIdentity⟩
      rw [← frameIdentity]
      exact child.occurrence.2

/-- Every executable outward child below positive carrier depth appears in the exact reroot list,
provided it is not the cursor's incoming coordinate. -/
theorem exists_mem_localizedRerootChildren_of_executable_child
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (nonduplicate : cursor.occurrence.1.node.isDuplicateLeaf = false)
    (positive : 0 < cursor.occurrence.1.remaining)
    (child : OfficialCIPNode input.Atom) (slot : Nat)
    (childAtSlot : (child, slot) ∈
      (input.executableOfficialCIPChildren cursor.occurrence.1.node).zipIdx)
    (notIncoming : ∀ previous,
      cursor.previous? = some previous →
        cursor.occurrence.1.address ++ [slot] ≠ previous.1.address) :
    ∃ children childCursor,
      input.localizedRerootChildren? cursor = some children ∧
        childCursor ∈ children ∧
        childCursor.occurrence.1 =
          { root := cursor.occurrence.1.root
            address := cursor.occurrence.1.address ++ [slot]
            node := child
            remaining := cursor.occurrence.1.remaining - 1 } := by
  let childFrame : input.LocalizedCIPOccurrenceFrame :=
    { root := cursor.occurrence.1.root
      address := cursor.occurrence.1.address ++ [slot]
      node := child
      remaining := cursor.occurrence.1.remaining - 1 }
  have sourceDerived :=
    (input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp cursor.occurrence.2
  have childDerived : input.DeclarativeLocalizedOccurrence fuel childFrame := by
    exact sourceDerived.immediateChild input positive childAtSlot
  have childPresent : childFrame ∈ input.localizedOccurrences fuel :=
    (input.mem_localizedOccurrences_iff fuel childFrame).mpr childDerived
  have outwardPresent : childFrame ∈
      input.localizedCarrierOutwardChildFrames (fuel := fuel) cursor.occurrence.1 := by
    rw [localizedCarrierOutwardChildFrames, List.mem_filter]
    refine ⟨childPresent, ?_⟩
    simp [childFrame]
  have neighborPresent : childFrame ∈
      input.localizedRerootNeighborFrames (fuel := fuel) cursor.occurrence.1 := by
    rw [localizedRerootNeighborFrames, List.mem_append]
    exact Or.inr outwardPresent
  have intendedPresent : childFrame ∈
      input.intendedLocalizedRerootChildFrames cursor := by
    unfold intendedLocalizedRerootChildFrames
    rw [if_neg (by simpa using nonduplicate)]
    cases previousIdentity : cursor.previous? with
    | none => simpa [previousIdentity] using neighborPresent
    | some previous =>
        rw [List.mem_filter]
        exact ⟨neighborPresent, by
          simpa [childFrame] using notIncoming previous previousIdentity⟩
  obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
  have exactChildren := input.localizedRerootChildren?_sound
    cursor children childrenComputed
  have mappedPresent : childFrame ∈ children.map (fun child => child.occurrence.1) := by
    rw [exactChildren.1]
    exact intendedPresent
  rw [List.mem_map] at mappedPresent
  rcases mappedPresent with ⟨childCursor, childCursorPresent, childCursorFrame⟩
  exact ⟨children, childCursor, childrenComputed, childCursorPresent,
    by simpa [childFrame] using childCursorFrame⟩

/-- The four-ligand frame requested at an occurrence is the exact first zipper expansion from
that occurrence, with no incoming cut yet.  Cardinality and stereogenic applicability are checked
by the descriptor evaluator rather than assumed here. -/
noncomputable def localizedOccurrenceLigandFrame?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option (List (input.LocalizedRerootCursor fuel)) :=
  input.localizedRerootChildren?
    { occurrence := occurrence, previous? := none }

/-- Successful occurrence-frame construction preserves the exact intended neighborhood and
records the source occurrence as the incoming cut on every ligand cursor. -/
theorem localizedOccurrenceLigandFrame?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (frame : List (input.LocalizedRerootCursor fuel))
    (computed : input.localizedOccurrenceLigandFrame? occurrence = some frame) :
    input.DeclarativeLocalizedRerootChildren
      { occurrence := occurrence, previous? := none } frame :=
  input.localizedRerootChildren?_sound
    { occurrence := occurrence, previous? := none } frame computed

/-- The exact first zipper frame is also characterized in both directions. -/
theorem localizedOccurrenceLigandFrame?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (frame : List (input.LocalizedRerootCursor fuel)) :
    input.localizedOccurrenceLigandFrame? occurrence = some frame ↔
      input.DeclarativeLocalizedRerootChildren
        { occurrence := occurrence, previous? := none } frame := by
  exact input.localizedRerootChildren?_eq_some_iff
    { occurrence := occurrence, previous? := none } frame

/-- Every carrier-tree neighbor retains the same final-center root. -/
theorem localizedRerootNeighborFrames_root_eq
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (source frame : input.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ input.localizedRerootNeighborFrames (fuel := fuel) source) :
    frame.root = source.root := by
  rw [localizedRerootNeighborFrames, List.mem_append] at present
  rcases present with parent | child
  · rw [localizedCarrierParentFrames, List.mem_filter] at parent
    simp only [Bool.and_eq_true, beq_iff_eq] at parent
    exact parent.2.1.1
  · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at child
    simp only [Bool.and_eq_true, beq_iff_eq] at child
    exact child.2.1.1

/-- Every emitted reroot child retains the same final-center root as its target cursor. -/
theorem localizedRerootChildren_root_eq
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (derived : input.DeclarativeLocalizedRerootChildren cursor children)
    (present : child ∈ children) :
    child.occurrence.1.root = cursor.occurrence.1.root := by
  have framePresent : child.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames cursor := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  unfold intendedLocalizedRerootChildFrames at framePresent
  split at framePresent
  · simp at framePresent
  · split at framePresent
    · exact input.localizedRerootNeighborFrames_root_eq
        cursor.occurrence.1 child.occurrence.1 framePresent
    · exact input.localizedRerootNeighborFrames_root_eq
        cursor.occurrence.1 child.occurrence.1
        (List.mem_of_mem_filter framePresent)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
