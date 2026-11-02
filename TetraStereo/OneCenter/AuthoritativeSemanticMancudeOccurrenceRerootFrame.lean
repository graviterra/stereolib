import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceFixedPoint

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Source-canonical occurrence reroot frames

This is the zipper used by recursive Rules 3--6 on the canonical mancude occurrence tree.  Its
neighbors are selected only from the exact finite carrier: the immediately shorter address first,
then all immediately longer addresses, with the incoming coordinate cut on subsequent steps.
Duplicate provenance nodes are terminal by construction.
-/

/-- Carrier coordinates at the immediately shorter address. -/
def aromaticCanonicalCarrierParentFrames
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceFrame) :
    List source.AromaticCanonicalOccurrenceFrame :=
  (source.aromaticCanonicalOccurrences fuel).filter fun candidate =>
    candidate.root == frame.root &&
      candidate.address.length + 1 == frame.address.length &&
      candidate.address == frame.address.dropLast

/-- Carrier coordinates at an immediately longer address. -/
def aromaticCanonicalCarrierOutwardChildFrames
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceFrame) :
    List source.AromaticCanonicalOccurrenceFrame :=
  (source.aromaticCanonicalOccurrences fuel).filter fun candidate =>
    candidate.root == frame.root &&
      candidate.address.length == frame.address.length + 1 &&
      candidate.address.dropLast == frame.address

/-- Parent first, followed by source-canonical outward children in carrier order. -/
def aromaticCanonicalRerootNeighborFrames
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceFrame) :
    List source.AromaticCanonicalOccurrenceFrame :=
  source.aromaticCanonicalCarrierParentFrames (fuel := fuel) frame ++
    source.aromaticCanonicalCarrierOutwardChildFrames (fuel := fuel) frame

/-- Address grading makes the parent and outward portions disjoint. -/
theorem aromaticCanonicalRerootNeighborFrames_nodup
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceFrame) :
    (source.aromaticCanonicalRerootNeighborFrames (fuel := fuel) frame).Nodup := by
  rw [aromaticCanonicalRerootNeighborFrames, List.nodup_append]
  refine ⟨(source.aromaticCanonicalOccurrences_nodup fuel).filter _,
    (source.aromaticCanonicalOccurrences_nodup fuel).filter _, ?_⟩
  intro candidate parentPresent _sameCandidate outwardPresent identity
  subst identity
  rw [aromaticCanonicalCarrierParentFrames, List.mem_filter] at parentPresent
  rw [aromaticCanonicalCarrierOutwardChildFrames, List.mem_filter] at outwardPresent
  simp only [Bool.and_eq_true, beq_iff_eq] at parentPresent outwardPresent
  omega

/-- A canonical reroot cursor and the coordinate cut from its next expansion. -/
structure AromaticCanonicalRerootCursor
    (source : AuthoritativeChemicalInput) (fuel : Nat) where
  occurrence : source.AromaticCanonicalOccurrence fuel
  previous? : Option (source.AromaticCanonicalOccurrence fuel) := none

@[ext] theorem AromaticCanonicalRerootCursor.ext
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    {left right : source.AromaticCanonicalRerootCursor fuel}
    (occurrence : left.occurrence = right.occurrence)
    (previous : left.previous? = right.previous?) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Exact cut-neighborhood before attaching carrier-membership proofs. -/
def intendedAromaticCanonicalRerootChildFrames
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) :
    List source.AromaticCanonicalOccurrenceFrame :=
  if cursor.occurrence.1.node.isDuplicateLeaf then []
  else
    match cursor.previous? with
    | none => source.aromaticCanonicalRerootNeighborFrames
        (fuel := fuel) cursor.occurrence.1
    | some previous =>
        (source.aromaticCanonicalRerootNeighborFrames
          (fuel := fuel) cursor.occurrence.1).filter fun frame =>
          frame.address != previous.1.address

theorem intendedAromaticCanonicalRerootChildFrames_nodup
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) :
    (source.intendedAromaticCanonicalRerootChildFrames cursor).Nodup := by
  unfold intendedAromaticCanonicalRerootChildFrames
  split
  · exact List.nodup_nil
  · split
    · exact source.aromaticCanonicalRerootNeighborFrames_nodup cursor.occurrence.1
    · exact (source.aromaticCanonicalRerootNeighborFrames_nodup
        cursor.occurrence.1).filter _

/-- Every intended zipper coordinate belongs to the exact source-canonical carrier. -/
theorem mem_aromaticCanonicalOccurrences_of_mem_intendedRerootChildFrames
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (frame : source.AromaticCanonicalOccurrenceFrame)
    (present : frame ∈ source.intendedAromaticCanonicalRerootChildFrames cursor) :
    frame ∈ source.aromaticCanonicalOccurrences fuel := by
  unfold intendedAromaticCanonicalRerootChildFrames at present
  split at present
  · simp at present
  · split at present
    · rw [aromaticCanonicalRerootNeighborFrames, List.mem_append] at present
      rcases present with parent | outward
      · exact List.mem_of_mem_filter parent
      · exact List.mem_of_mem_filter outward
    · have neighbor := List.mem_of_mem_filter present
      rw [aromaticCanonicalRerootNeighborFrames, List.mem_append] at neighbor
      rcases neighbor with parent | outward
      · exact List.mem_of_mem_filter parent
      · exact List.mem_of_mem_filter outward

/-- Total executable source-canonical zipper expansion. -/
noncomputable def aromaticCanonicalRerootChildren
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) :
    List (source.AromaticCanonicalRerootCursor fuel) := by
  classical
  exact (source.intendedAromaticCanonicalRerootChildFrames cursor).attach.map fun frame =>
    { occurrence := ⟨frame.1,
        source.mem_aromaticCanonicalOccurrences_of_mem_intendedRerootChildFrames
          cursor frame.1 frame.2⟩
      previous? := some cursor.occurrence }

/-- Optional wrapper retained for the descriptor compiler's fail-closed interface.  It is proved
total because the exact carrier contains every intended coordinate. -/
noncomputable def aromaticCanonicalRerootChildren?
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) :
    Option (List (source.AromaticCanonicalRerootCursor fuel)) :=
  some (source.aromaticCanonicalRerootChildren cursor)

theorem aromaticCanonicalRerootChildren?_isSome
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) :
    (source.aromaticCanonicalRerootChildren? cursor).isSome = true := by
  simp [aromaticCanonicalRerootChildren?]

/-- Independent exact meaning of an ordered canonical zipper expansion. -/
def DeclarativeAromaticCanonicalRerootChildren
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (children : List (source.AromaticCanonicalRerootCursor fuel)) : Prop :=
  children.map (fun child => child.occurrence.1) =
      source.intendedAromaticCanonicalRerootChildFrames cursor ∧
    ∀ child ∈ children, child.previous? = some cursor.occurrence

/-- Execution preserves the exact independent ordered cut-neighborhood. -/
theorem aromaticCanonicalRerootChildren_sound
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) :
    source.DeclarativeAromaticCanonicalRerootChildren cursor
      (source.aromaticCanonicalRerootChildren cursor) := by
  classical
  constructor
  · simp [aromaticCanonicalRerootChildren]
  · intro child childPresent
    rw [aromaticCanonicalRerootChildren, List.mem_map] at childPresent
    rcases childPresent with ⟨frame, _framePresent, rfl⟩
    rfl

theorem aromaticCanonicalRerootChildren?_sound
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (children : List (source.AromaticCanonicalRerootCursor fuel))
    (computed : source.aromaticCanonicalRerootChildren? cursor = some children) :
    source.DeclarativeAromaticCanonicalRerootChildren cursor children := by
  simp only [aromaticCanonicalRerootChildren?, Option.some.injEq] at computed
  subst children
  exact source.aromaticCanonicalRerootChildren_sound cursor

/-- Canonical zipper expansion never repeats a cursor. -/
theorem aromaticCanonicalRerootChildren_nodup
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) :
    (source.aromaticCanonicalRerootChildren cursor).Nodup := by
  have mappedNodup :
      ((source.aromaticCanonicalRerootChildren cursor).map
        (fun child => child.occurrence.1)).Nodup := by
    rw [(source.aromaticCanonicalRerootChildren_sound cursor).1]
    exact source.intendedAromaticCanonicalRerootChildFrames_nodup cursor
  rw [List.nodup_iff_pairwise_ne] at mappedNodup ⊢
  rw [List.pairwise_map] at mappedNodup
  apply mappedNodup.imp
  intro left right frameDifferent cursorIdentity
  exact frameDifferent (congrArg (fun child => child.occurrence.1) cursorIdentity)

/-- Two source-canonical cursor lists are equal when they contain the same ordered occurrence
frames and every cursor records the same incoming coordinate.  The carrier-membership proofs in
the occurrence subtypes are propositionally irrelevant. -/
private theorem aromaticCanonicalRerootCursorLists_unique
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (previous : Option (source.AromaticCanonicalOccurrence fuel)) :
    ∀ (first second : List (source.AromaticCanonicalRerootCursor fuel)),
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
      exact source.aromaticCanonicalRerootCursorLists_unique previous
        firstTail secondTail tailFrames
        (fun child present => firstPrevious child (by simp [present]))
        (fun child present => secondPrevious child (by simp [present]))

/-- The independent ordered cut-neighborhood characterizes source-canonical zipper expansion in
both directions.  This is the missing completeness converse to
`aromaticCanonicalRerootChildren?_sound`. -/
theorem aromaticCanonicalRerootChildren?_eq_some_iff
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (children : List (source.AromaticCanonicalRerootCursor fuel)) :
    source.aromaticCanonicalRerootChildren? cursor = some children ↔
      source.DeclarativeAromaticCanonicalRerootChildren cursor children := by
  constructor
  · exact source.aromaticCanonicalRerootChildren?_sound cursor children
  · intro derived
    classical
    unfold aromaticCanonicalRerootChildren?
    apply congrArg some
    have builtDerived := source.aromaticCanonicalRerootChildren_sound cursor
    apply source.aromaticCanonicalRerootCursorLists_unique (some cursor.occurrence)
    · exact builtDerived.1.trans derived.1.symm
    · exact builtDerived.2
    · exact derived.2

/-- Every emitted child remains below the same source root. -/
theorem aromaticCanonicalRerootChildren_root_eq
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor child : source.AromaticCanonicalRerootCursor fuel)
    (present : child ∈ source.aromaticCanonicalRerootChildren cursor) :
    child.occurrence.1.root = cursor.occurrence.1.root := by
  have exactChildren := source.aromaticCanonicalRerootChildren_sound cursor
  have framePresent : child.occurrence.1 ∈
      source.intendedAromaticCanonicalRerootChildFrames cursor := by
    rw [← exactChildren.1]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  unfold intendedAromaticCanonicalRerootChildFrames at framePresent
  split at framePresent
  · simp at framePresent
  · split at framePresent
    · rw [aromaticCanonicalRerootNeighborFrames, List.mem_append] at framePresent
      rcases framePresent with parent | outward
      · rw [aromaticCanonicalCarrierParentFrames, List.mem_filter] at parent
        simp only [Bool.and_eq_true, beq_iff_eq] at parent
        exact parent.2.1.1
      · rw [aromaticCanonicalCarrierOutwardChildFrames, List.mem_filter] at outward
        simp only [Bool.and_eq_true, beq_iff_eq] at outward
        exact outward.2.1.1
    · have neighbor := List.mem_of_mem_filter framePresent
      rw [aromaticCanonicalRerootNeighborFrames, List.mem_append] at neighbor
      rcases neighbor with parent | outward
      · rw [aromaticCanonicalCarrierParentFrames, List.mem_filter] at parent
        simp only [Bool.and_eq_true, beq_iff_eq] at parent
        exact parent.2.1.1
      · rw [aromaticCanonicalCarrierOutwardChildFrames, List.mem_filter] at outward
        simp only [Bool.and_eq_true, beq_iff_eq] at outward
        exact outward.2.1.1

/-- First four-ligand zipper frame at one occurrence, before any incoming cut. -/
noncomputable def aromaticCanonicalOccurrenceLigandFrame?
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence fuel) :
    Option (List (source.AromaticCanonicalRerootCursor fuel)) :=
  source.aromaticCanonicalRerootChildren?
    { occurrence := occurrence, previous? := none }

theorem aromaticCanonicalOccurrenceLigandFrame?_sound
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence fuel)
    (frame : List (source.AromaticCanonicalRerootCursor fuel))
    (computed : source.aromaticCanonicalOccurrenceLigandFrame? occurrence = some frame) :
    source.DeclarativeAromaticCanonicalRerootChildren
      { occurrence := occurrence, previous? := none } frame :=
  source.aromaticCanonicalRerootChildren?_sound
    { occurrence := occurrence, previous? := none } frame computed

/-- The first molecule occurrence frame is exactly its independently specified ordered zipper
expansion.  In particular, no caller-supplied executable-success equation is needed to recover
the canonical ligand frame. -/
theorem aromaticCanonicalOccurrenceLigandFrame?_eq_some_iff
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence fuel)
    (frame : List (source.AromaticCanonicalRerootCursor fuel)) :
    source.aromaticCanonicalOccurrenceLigandFrame? occurrence = some frame ↔
      source.DeclarativeAromaticCanonicalRerootChildren
        { occurrence := occurrence, previous? := none } frame := by
  exact source.aromaticCanonicalRerootChildren?_eq_some_iff
    { occurrence := occurrence, previous? := none } frame

/-! ## Exact final-root ligand frames -/

/-- Every declarative subtree occurrence retains the address prefix at which its derivation
started. -/
theorem declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence) :
    path <+: occurrence.address := by
  induction derived with
  | subtreeRoot => exact ⟨[], by simp⟩
  | @subtreeDescendant path fuel node child slot occurrence
      childAtSlot descendant inductionHypothesis =>
      exact (List.prefix_append path [slot]).trans inductionHypothesis

/-- A subtree derivation that has not advanced its address is its root constructor. -/
theorem declarativeAromaticCanonicalOccurrenceSubtree_eq_root_of_address_eq
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence)
    (address : occurrence.address = path) :
    occurrence =
      { root := root, address := path, node := node, remaining := fuel } := by
  cases derived with
  | subtreeRoot => rfl
  | @subtreeDescendant _ _ _ child slot descendant childAtSlot below =>
      have addressPrefix :=
        declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix source below
      have lengthBound := addressPrefix.length_le
      rw [address] at lengthBound
      simp at lengthBound

/-- Every carrier frame one address step below the final center is exactly the official child at
that address slot, and every official child slot occurs there. -/
theorem mem_aromaticCanonicalCarrierOutwardChildFrames_final_iff
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (frame : source.AromaticCanonicalOccurrenceFrame) :
    frame ∈ source.aromaticCanonicalCarrierOutwardChildFrames
        (fuel := fuel) (source.aromaticCanonicalFinalOccurrence fuel center).1 ↔
      ∃ child slot,
        (child, slot) ∈
          (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
            source.molecule.atomCount (OfficialCIPNode.root center.1)).zipIdx ∧
        frame =
          { root := center.1
            address := [slot]
            node := child
            remaining := fuel } := by
  constructor
  · intro present
    rw [aromaticCanonicalCarrierOutwardChildFrames, List.mem_filter] at present
    rcases present with ⟨global, conditions⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at conditions
    have rootEq := conditions.1.1
    have addressLength := conditions.1.2
    have derived := (source.mem_aromaticCanonicalOccurrences_iff fuel frame).mp global
    have derivedAtCenter :
        source.DeclarativeAromaticCanonicalOccurrenceSubtree
          center.1 [] (fuel + 1) (OfficialCIPNode.root center.1) frame := by
      simpa [DeclarativeAromaticCanonicalOccurrence,
        DeclarativeAromaticCanonicalOccurrenceAtAtom, rootEq] using derived
    cases derivedAtCenter with
    | subtreeRoot => simp at addressLength
    | @subtreeDescendant _ _ _ child slot occurrence childAtSlot below =>
        have addressPrefix :=
          declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix source below
        have addressEq : frame.address = [slot] := by
          exact addressPrefix.eq_of_length (by
            simpa [aromaticCanonicalFinalOccurrence] using addressLength.symm) |>.symm
        have frameEq :=
          declarativeAromaticCanonicalOccurrenceSubtree_eq_root_of_address_eq
            source below addressEq
        exact ⟨child, slot, childAtSlot, frameEq⟩
  · rintro ⟨child, slot, childAtSlot, rfl⟩
    rw [aromaticCanonicalCarrierOutwardChildFrames, List.mem_filter]
    constructor
    · apply (source.mem_aromaticCanonicalOccurrences_iff fuel _).mpr
      change source.DeclarativeAromaticCanonicalOccurrenceSubtree
        center.1 [] (fuel + 1) (OfficialCIPNode.root center.1)
          { root := center.1
            address := [slot]
            node := child
            remaining := fuel }
      exact DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeDescendant childAtSlot
        (DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeRoot [slot] fuel child)
    · simp [aromaticCanonicalFinalOccurrence]

/-- The official direct-child frames, retaining the exact source slot in each address. -/
def aromaticCanonicalFinalDirectChildFrames
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    List source.AromaticCanonicalOccurrenceFrame :=
  (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
      source.molecule.atomCount (OfficialCIPNode.root center.1)).zipIdx.map fun child =>
    { root := center.1
      address := [child.2]
      node := child.1
      remaining := fuel }

theorem aromaticCanonicalFinalDirectChildFrames_nodup
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (aromaticCanonicalFinalDirectChildFrames source fuel center).Nodup := by
  let children := source.molecule.aromaticCanonicalOfficialCIPChildrenAt
    source.molecule.atomCount (OfficialCIPNode.root center.1)
  have slotNodup : (children.zipIdx.map Prod.snd).Nodup := by
    simp [List.nodup_range']
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at slotNodup
  unfold aromaticCanonicalFinalDirectChildFrames
  change (children.zipIdx.map _).Nodup
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact slotNodup.imp (by
    intro left right slotsDifferent framesEqual
    apply slotsDifferent
    simpa using congrArg
      (fun frame : source.AromaticCanonicalOccurrenceFrame => frame.address) framesEqual)

theorem mem_aromaticCanonicalFinalDirectChildFrames_iff
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (frame : source.AromaticCanonicalOccurrenceFrame) :
    frame ∈ aromaticCanonicalFinalDirectChildFrames source fuel center ↔
      ∃ child slot,
        (child, slot) ∈
          (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
            source.molecule.atomCount (OfficialCIPNode.root center.1)).zipIdx ∧
        frame =
          { root := center.1
            address := [slot]
            node := child
            remaining := fuel } := by
  unfold aromaticCanonicalFinalDirectChildFrames
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨child, slot⟩, present, rfl⟩
    exact ⟨child, slot, present, rfl⟩
  · rintro ⟨child, slot, present, rfl⟩
    exact ⟨(child, slot), present, rfl⟩

/-- The final occurrence's outward carrier layer is a permutation of the official direct-child
slot list.  This is intentionally order-agnostic: the carrier is globally deduplicated, while
the exact source slots determine the same finite set. -/
theorem aromaticCanonicalCarrierOutwardChildFrames_final_perm
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    List.Perm
      (source.aromaticCanonicalCarrierOutwardChildFrames
        (fuel := fuel) (source.aromaticCanonicalFinalOccurrence fuel center).1)
      (aromaticCanonicalFinalDirectChildFrames source fuel center) := by
  apply (List.perm_ext_iff_of_nodup
    ((source.aromaticCanonicalOccurrences_nodup fuel).filter _)
    (aromaticCanonicalFinalDirectChildFrames_nodup source fuel center)).mpr
  intro frame
  change frame ∈ source.aromaticCanonicalCarrierOutwardChildFrames
      (fuel := fuel) (source.aromaticCanonicalFinalOccurrence fuel center).1 ↔
    frame ∈ aromaticCanonicalFinalDirectChildFrames source fuel center
  exact (mem_aromaticCanonicalCarrierOutwardChildFrames_final_iff
    source fuel center frame).trans
      (mem_aromaticCanonicalFinalDirectChildFrames_iff source fuel center frame).symm

theorem aromaticCanonicalCarrierOutwardChildFrames_final_length
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (source.aromaticCanonicalCarrierOutwardChildFrames
      (fuel := fuel) (source.aromaticCanonicalFinalOccurrence fuel center).1).length =
        (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount (OfficialCIPNode.root center.1)).length := by
  have perm := aromaticCanonicalCarrierOutwardChildFrames_final_perm source fuel center
  rw [perm.length_eq]
  simp [aromaticCanonicalFinalDirectChildFrames]

theorem aromaticCanonicalFinalOccurrence_intendedChildren_eq_outward
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.intendedAromaticCanonicalRerootChildFrames
        { occurrence := source.aromaticCanonicalFinalOccurrence fuel center
          previous? := none } =
      source.aromaticCanonicalCarrierOutwardChildFrames
        (fuel := fuel) (source.aromaticCanonicalFinalOccurrence fuel center).1 := by
  simp [intendedAromaticCanonicalRerootChildFrames,
    aromaticCanonicalRerootNeighborFrames, aromaticCanonicalCarrierParentFrames,
    aromaticCanonicalFinalOccurrence, OfficialCIPNode.root, OfficialCIPNode.isDuplicateLeaf]

/-- The final center's optional ligand frame is total, and its length is exactly the number of
official source-canonical direct children. -/
theorem aromaticCanonicalOccurrenceLigandFrame_final_length
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    ∃ roots,
      source.aromaticCanonicalOccurrenceLigandFrame?
          (source.aromaticCanonicalFinalOccurrence fuel center) = some roots ∧
      roots.length =
        (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount (OfficialCIPNode.root center.1)).length := by
  let target := source.aromaticCanonicalFinalOccurrence fuel center
  let roots := source.aromaticCanonicalRerootChildren
    { occurrence := target, previous? := none }
  refine ⟨roots, ?_, ?_⟩
  · rfl
  · unfold roots aromaticCanonicalRerootChildren
    simp only [List.length_map, List.length_attach]
    rw [aromaticCanonicalFinalOccurrence_intendedChildren_eq_outward,
      aromaticCanonicalCarrierOutwardChildFrames_final_length]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
