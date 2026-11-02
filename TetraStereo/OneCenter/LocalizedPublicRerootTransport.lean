import TetraStereo.KernelOnly
import TetraStereo.OneCenter.LocalizedPublicOccurrenceTransport
import TetraStereo.OneCenter.LocalizedOccurrenceRerootFrame
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRerootFrame
import TetraStereo.OneCenter.LocalizedOccurrenceRule45Descriptor
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through5FixedPoint

set_option autoImplicit false

namespace TetraStereo.OneCenter




































namespace CertifiedLocalizedCIPInput

/-! ## Occurrence-carrier transport in the localized-to-public direction -/

/-- The sibling bounded-subtree transport read in the localized-to-public direction. -/
theorem localizedOccurrenceSubtree_map_eq_aromaticCanonical
    (input : CertifiedLocalizedCIPInput) (root : input.Atom) :
    ∀ (fuel : Nat) (path : List Nat) (node : OfficialCIPNode input.Atom),
      (input.localizedOccurrenceSubtree root fuel path node).map input.publicLocalizedFrame
        = input.certified.input.aromaticCanonicalOccurrenceSubtree root fuel path node :=
  input.map_publicLocalizedFrame_localizedOccurrenceSubtree root

/-- Atom-rooted occurrence enumeration transports exactly in the localized-to-public direction. -/
theorem localizedOccurrencesAtAtom_map_eq_aromaticCanonical
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.localizedOccurrencesAtAtom fuel atom).map input.publicLocalizedFrame
      = input.certified.input.aromaticCanonicalOccurrencesAtAtom fuel atom := by
  unfold CertifiedLocalizedCIPInput.localizedOccurrencesAtAtom
    AuthoritativeChemicalInput.aromaticCanonicalOccurrencesAtAtom
  exact input.localizedOccurrenceSubtree_map_eq_aromaticCanonical atom (fuel + 1) []
    (OfficialCIPNode.root atom)

/-- The whole deduplicated molecule-wide localized occurrence carrier maps exactly onto the
public source-canonical carrier, in order.  This is the sibling carrier equality composed with
the inverse frame map, not a new enumeration. -/
theorem localizedOccurrences_map_eq_aromaticCanonicalOccurrences
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedOccurrences fuel).map input.publicLocalizedFrame
      = input.certified.input.aromaticCanonicalOccurrences fuel := by
  have forward := input.map_localizedPublicFrame_aromaticCanonicalOccurrences fuel
  have mapped := congrArg (List.map input.publicLocalizedFrame) forward
  rw [List.map_map] at mapped
  have composition : input.publicLocalizedFrame ∘ input.localizedPublicFrame = id := by
    funext frame
    exact input.publicLocalizedFrame_localizedPublicFrame frame
  rw [composition, List.map_id] at mapped
  exact mapped.symm

/-- Membership transports in the localized-to-public direction across the frame map; this is
the sibling membership theorem in the opposite presentation. -/
theorem mem_localizedOccurrences_iff_mem_aromaticCanonicalOccurrences
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (frame : input.certified.input.AromaticCanonicalOccurrenceFrame) :
    input.localizedPublicFrame frame ∈ input.localizedOccurrences fuel ↔
      frame ∈ input.certified.input.aromaticCanonicalOccurrences fuel :=
  (input.mem_aromaticCanonicalOccurrences_iff_localizedPublicFrame_mem fuel frame).symm

/-! ## Cursor transport -/

/-- The public cursor with the same occurrence and the mapped incoming cut coordinate.  The
`previous?` field is preserved as data rather than discarded. -/
def localizedPublicCursorMap (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.certified.input.AromaticCanonicalRerootCursor fuel :=
  { occurrence := (input.localizedPublicOccurrenceEquiv fuel).symm cursor.occurrence
    previous? := cursor.previous?.map (input.localizedPublicOccurrenceEquiv fuel).symm }

@[simp] theorem localizedPublicCursorMap_occurrence
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.localizedPublicCursorMap cursor).occurrence =
      (input.localizedPublicOccurrenceEquiv fuel).symm cursor.occurrence := rfl

@[simp] theorem localizedPublicCursorMap_previous
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.localizedPublicCursorMap cursor).previous? =
      cursor.previous?.map (input.localizedPublicOccurrenceEquiv fuel).symm := rfl

@[simp] theorem localizedPublicCursorMap_occurrence_frame
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.localizedPublicCursorMap cursor).occurrence.1 =
      input.publicLocalizedFrame cursor.occurrence.1 := rfl

@[simp] theorem localizedPublicCursorMap_occurrence_root
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.localizedPublicCursorMap cursor).occurrence.1.root =
      cursor.occurrence.1.root := rfl

@[simp] theorem localizedPublicCursorMap_occurrence_address
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.localizedPublicCursorMap cursor).occurrence.1.address =
      cursor.occurrence.1.address := rfl

@[simp] theorem localizedPublicCursorMap_occurrence_node
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.localizedPublicCursorMap cursor).occurrence.1.node =
      cursor.occurrence.1.node := rfl

/-! ## Neighborhood transport -/

/-- Mapping an ordered filter is filtering the mapped list, provided the predicates agree through
the map.  This is the ordered (not merely set-theoretic) form used by the zipper. -/
private theorem map_filter_of_predicate_eq_f90
    {Alpha Beta : Type*} (f : Alpha → Beta) (l : List Alpha)
    (p : Alpha → Bool) (q : Beta → Bool)
    (h : ∀ a, p a = q (f a)) :
    (l.filter p).map f = (l.map f).filter q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      have conditionEq : q (f a) = p a := (h a).symm
      cases condition : p a with
      | false => simp [condition, conditionEq, ih]
      | true => simp [condition, conditionEq, ih]

/-- Carrier parent frames transport exactly, retaining carrier order. -/
theorem localizedCarrierParentFrames_map_eq_aromaticCanonical
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (input.localizedCarrierParentFrames (fuel := fuel) frame).map input.publicLocalizedFrame
      = input.certified.input.aromaticCanonicalCarrierParentFrames (fuel := fuel)
          (input.publicLocalizedFrame frame) := by
  unfold CertifiedLocalizedCIPInput.localizedCarrierParentFrames
    AuthoritativeChemicalInput.aromaticCanonicalCarrierParentFrames
  rw [map_filter_of_predicate_eq_f90 input.publicLocalizedFrame
    (input.localizedOccurrences fuel)
    (fun candidate =>
      candidate.root == frame.root &&
        candidate.address.length + 1 == frame.address.length &&
        candidate.address == frame.address.dropLast)
    (fun candidate =>
      candidate.root == (input.publicLocalizedFrame frame).root &&
        candidate.address.length + 1 == (input.publicLocalizedFrame frame).address.length &&
        candidate.address == (input.publicLocalizedFrame frame).address.dropLast)
    (by intro candidate; rfl)]
  rw [localizedOccurrences_map_eq_aromaticCanonicalOccurrences]

/-- Carrier outward child frames transport exactly, retaining official sibling order. -/
theorem localizedCarrierOutwardChildFrames_map_eq_aromaticCanonical
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (input.localizedCarrierOutwardChildFrames (fuel := fuel) frame).map
        input.publicLocalizedFrame
      = input.certified.input.aromaticCanonicalCarrierOutwardChildFrames (fuel := fuel)
          (input.publicLocalizedFrame frame) := by
  unfold CertifiedLocalizedCIPInput.localizedCarrierOutwardChildFrames
    AuthoritativeChemicalInput.aromaticCanonicalCarrierOutwardChildFrames
  rw [map_filter_of_predicate_eq_f90 input.publicLocalizedFrame
    (input.localizedOccurrences fuel)
    (fun candidate =>
      candidate.root == frame.root &&
        candidate.address.length == frame.address.length + 1 &&
        candidate.address.dropLast == frame.address)
    (fun candidate =>
      candidate.root == (input.publicLocalizedFrame frame).root &&
        candidate.address.length == (input.publicLocalizedFrame frame).address.length + 1 &&
        candidate.address.dropLast == (input.publicLocalizedFrame frame).address)
    (by intro candidate; rfl)]
  rw [localizedOccurrences_map_eq_aromaticCanonicalOccurrences]

/-- The uncut zipper neighborhood (parent first, then outward children) transports exactly. -/
theorem localizedRerootNeighborFrames_map_eq_aromaticCanonical
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (input.localizedRerootNeighborFrames (fuel := fuel) frame).map input.publicLocalizedFrame
      = input.certified.input.aromaticCanonicalRerootNeighborFrames (fuel := fuel)
          (input.publicLocalizedFrame frame) := by
  unfold CertifiedLocalizedCIPInput.localizedRerootNeighborFrames
    AuthoritativeChemicalInput.aromaticCanonicalRerootNeighborFrames
  rw [List.map_append, localizedCarrierParentFrames_map_eq_aromaticCanonical,
    localizedCarrierOutwardChildFrames_map_eq_aromaticCanonical]

/-! ## Intended child frames -/

/-- The exact cut neighborhood transports: duplicate-terminal behavior and the incoming-address
cut are both preserved. -/
theorem intendedLocalizedRerootChildFrames_map_eq_aromaticCanonical
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.intendedLocalizedRerootChildFrames cursor).map input.publicLocalizedFrame
      = input.certified.input.intendedAromaticCanonicalRerootChildFrames
          (input.localizedPublicCursorMap cursor) := by
  unfold CertifiedLocalizedCIPInput.intendedLocalizedRerootChildFrames
    AuthoritativeChemicalInput.intendedAromaticCanonicalRerootChildFrames
  rw [localizedPublicCursorMap_occurrence_node, localizedPublicCursorMap_previous]
  by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true
  · simp [duplicate]
  · rw [if_neg duplicate, if_neg duplicate]
    cases previous : cursor.previous? with
    | none =>
        simp only [Option.map_none]
        rw [localizedPublicCursorMap_occurrence_frame]
        exact localizedRerootNeighborFrames_map_eq_aromaticCanonical input cursor.occurrence.1
    | some incoming =>
        simp only [Option.map_some]
        rw [localizedPublicCursorMap_occurrence_frame]
        rw [map_filter_of_predicate_eq_f90 input.publicLocalizedFrame
          (input.localizedRerootNeighborFrames (fuel := fuel) cursor.occurrence.1)
          (fun candidate => candidate.address != incoming.1.address)
          (fun candidate => candidate.address !=
            ((input.localizedPublicOccurrenceEquiv fuel).symm incoming).1.address)
          (by intro candidate; rfl)]
        rw [localizedRerootNeighborFrames_map_eq_aromaticCanonical]

/-! ## Executable reroot children -/

/-- The independent declarative zipper relation transports along the cursor map. -/
theorem declarativeLocalizedRerootChildren_map
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (derived : input.DeclarativeLocalizedRerootChildren cursor children) :
    input.certified.input.DeclarativeAromaticCanonicalRerootChildren
      (input.localizedPublicCursorMap cursor)
      (children.map (input.localizedPublicCursorMap)) := by
  constructor
  · calc
      (children.map (input.localizedPublicCursorMap)).map
          (fun child => child.occurrence.1)
          = children.map (fun child =>
              (input.localizedPublicCursorMap child).occurrence.1) := by
            rw [List.map_map]
            rfl
      _ = children.map (fun child =>
            input.publicLocalizedFrame child.occurrence.1) := rfl
      _ = (children.map (fun child => child.occurrence.1)).map
            input.publicLocalizedFrame := by
            rw [List.map_map]
            rfl
      _ = (input.intendedLocalizedRerootChildFrames cursor).map
            input.publicLocalizedFrame := by
            rw [derived.1]
      _ = input.certified.input.intendedAromaticCanonicalRerootChildFrames
            (input.localizedPublicCursorMap cursor) :=
            intendedLocalizedRerootChildFrames_map_eq_aromaticCanonical input cursor
  · intro child childPresent
    rw [List.mem_map] at childPresent
    rcases childPresent with ⟨localizedChild, localizedPresent, rfl⟩
    rw [localizedPublicCursorMap_previous, derived.2 localizedChild localizedPresent]
    simp

/-- **Executable reroot transport.**  The localized fail-closed expansion succeeds at every
cursor (derived from `exists_localizedRerootChildren`, not assumed), the public total expansion
is exactly the map of that localized child list, and the public optional wrapper returns it. -/
theorem localizedRerootChildren?_transport
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    ∃ children,
      input.localizedRerootChildren? cursor = some children ∧
      children.map (input.localizedPublicCursorMap) =
        input.certified.input.aromaticCanonicalRerootChildren
          (input.localizedPublicCursorMap cursor) ∧
      input.certified.input.aromaticCanonicalRerootChildren?
          (input.localizedPublicCursorMap cursor) =
        some (children.map (input.localizedPublicCursorMap)) := by
  obtain ⟨children, computed⟩ := input.exists_localizedRerootChildren cursor
  have localizedDerived :=
    input.localizedRerootChildren?_sound cursor children computed
  have publicDerived :=
    input.declarativeLocalizedRerootChildren_map cursor children localizedDerived
  have publicComputed : input.certified.input.aromaticCanonicalRerootChildren?
      (input.localizedPublicCursorMap cursor) =
        some (children.map (input.localizedPublicCursorMap)) :=
    (input.certified.input.aromaticCanonicalRerootChildren?_eq_some_iff
      (input.localizedPublicCursorMap cursor) _).mpr publicDerived
  have total : input.certified.input.aromaticCanonicalRerootChildren?
      (input.localizedPublicCursorMap cursor) =
        some (input.certified.input.aromaticCanonicalRerootChildren
          (input.localizedPublicCursorMap cursor)) := rfl
  rw [total] at publicComputed
  exact ⟨children, computed, (Option.some.inj publicComputed).symm, publicComputed⟩

/-- The localized optional zipper expansion is total, as a direct corollary of the transport
theorem (itself derived from the actual carrier-membership theorem). -/
theorem localizedRerootChildren?_isSome
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.localizedRerootChildren? cursor).isSome = true := by
  obtain ⟨children, computed, _mapped, _public⟩ :=
    input.localizedRerootChildren?_transport cursor
  simp [computed]

/-! ## Occurrence ligand frames -/

/-- **Occurrence ligand-frame transport.**  The localized first zipper frame returns `some`
(derived, not assumed) and the public total ligand frame is exactly the map of its cursors. -/
theorem localizedOccurrenceLigandFrame?_transport
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    ∃ frame,
      input.localizedOccurrenceLigandFrame? occurrence = some frame ∧
      frame.map (input.localizedPublicCursorMap) =
        input.certified.input.aromaticCanonicalRerootChildren
          { occurrence := (input.localizedPublicOccurrenceEquiv fuel).symm occurrence
            previous? := none } ∧
      input.certified.input.aromaticCanonicalOccurrenceLigandFrame?
          ((input.localizedPublicOccurrenceEquiv fuel).symm occurrence) =
        some (frame.map (input.localizedPublicCursorMap)) := by
  unfold CertifiedLocalizedCIPInput.localizedOccurrenceLigandFrame?
  obtain ⟨frame, computed, mapped, publicComputed⟩ :=
    input.localizedRerootChildren?_transport
      ({ occurrence := occurrence, previous? := none } :
        input.LocalizedRerootCursor fuel)
  have cursorEq : input.localizedPublicCursorMap
        ({ occurrence := occurrence, previous? := none } :
          input.LocalizedRerootCursor fuel) =
      ({ occurrence := (input.localizedPublicOccurrenceEquiv fuel).symm occurrence
         previous? := none } :
        input.certified.input.AromaticCanonicalRerootCursor fuel) := by
    apply AuthoritativeChemicalInput.AromaticCanonicalRerootCursor.ext
    · rfl
    · rfl
  rw [cursorEq] at mapped publicComputed
  exact ⟨frame, computed, mapped, publicComputed⟩

/-! ## Four-ligand occurrence frames -/

/-- Map a successful localized four-ligand frame to the public four-ligand frame with the same
ordered cursors. -/
abbrev localizedPublicFourLigandFrameMap
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel) :
    input.certified.input.AromaticCanonicalOccurrenceFourLigandFrame fuel :=
  { roots := frame.cursors.map (input.localizedPublicCursorMap)
    rootsLength := by
      rw [List.length_map, frame.length_eq] }

/-- The independent four-ligand meaning transports to the public source-canonical meaning. -/
theorem declarativeLocalizedOccurrenceFourLigandFrame_map
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame) :
    input.certified.input.DeclarativeAromaticCanonicalOccurrenceFourLigandFrame
      ((input.localizedPublicOccurrenceEquiv fuel).symm target)
      (localizedPublicFourLigandFrameMap input frame) := by
  constructor
  · have cursorEq : input.localizedPublicCursorMap
          ({ occurrence := target, previous? := none } :
            input.LocalizedRerootCursor fuel) =
        ({ occurrence := (input.localizedPublicOccurrenceEquiv fuel).symm target
           previous? := none } :
          input.certified.input.AromaticCanonicalRerootCursor fuel) := by
      apply AuthoritativeChemicalInput.AromaticCanonicalRerootCursor.ext
      · rfl
      · rfl
    rw [← cursorEq]
    exact input.declarativeLocalizedRerootChildren_map _ frame.cursors derived.1
  · simp [derived.2]

/-- **Four-ligand frame transport.**  Every successfully constructed localized four-ligand frame
yields the public source-canonical four-ligand frame, with exactly the mapped ordered cursors. -/
theorem localizedOccurrenceFourLigandFrame?_transport
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    input.certified.input.aromaticCanonicalOccurrenceFourLigandFrame?
        ((input.localizedPublicOccurrenceEquiv fuel).symm target) =
      some (localizedPublicFourLigandFrameMap input frame) := by
  have derived :=
    input.localizedOccurrenceFourLigandFrame?_sound target frame computed
  have publicDerived :=
    input.declarativeLocalizedOccurrenceFourLigandFrame_map target frame derived
  have childrenComputed : input.certified.input.aromaticCanonicalRerootChildren?
      ({ occurrence := (input.localizedPublicOccurrenceEquiv fuel).symm target
         previous? := none } :
        input.certified.input.AromaticCanonicalRerootCursor fuel) =
      some (localizedPublicFourLigandFrameMap input frame).roots :=
    (input.certified.input.aromaticCanonicalRerootChildren?_eq_some_iff
      ({ occurrence := (input.localizedPublicOccurrenceEquiv fuel).symm target
         previous? := none } :
        input.certified.input.AromaticCanonicalRerootCursor fuel) _).mpr publicDerived.1
  unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame?
  unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrenceLigandFrame?
  rw [childrenComputed]
  change (if rootsLength :
      (localizedPublicFourLigandFrameMap input frame).roots.length = 4 then
        some { roots := (localizedPublicFourLigandFrameMap input frame).roots
               rootsLength := rootsLength }
      else none) = some (localizedPublicFourLigandFrameMap input frame)
  have lengthFour : (localizedPublicFourLigandFrameMap input frame).roots.length = 4 :=
    publicDerived.2
  rw [dif_pos lengthFour]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceSubtree_map_eq_aromaticCanonical
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrencesAtAtom_map_eq_aromaticCanonical
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrences_map_eq_aromaticCanonicalOccurrences
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedOccurrences_iff_mem_aromaticCanonicalOccurrences
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicCursorMap_occurrence
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicCursorMap_previous
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicCursorMap_occurrence_frame
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicCursorMap_occurrence_root
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicCursorMap_occurrence_address
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicCursorMap_occurrence_node
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCarrierParentFrames_map_eq_aromaticCanonical
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCarrierOutwardChildFrames_map_eq_aromaticCanonical
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootNeighborFrames_map_eq_aromaticCanonical
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.intendedLocalizedRerootChildFrames_map_eq_aromaticCanonical
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedRerootChildren_map
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_transport
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_isSome
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceLigandFrame?_transport
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedOccurrenceFourLigandFrame_map
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame?_transport
