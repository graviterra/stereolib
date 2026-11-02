import TetraStereo.OneCenter.LocalizedOccurrenceRule45Descriptor
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Child classification of an actual tetrahedral four-ligand frame

The occurrence descriptor evaluates the target-start four-ligand frame
`localizedOccurrenceFourLigandFrame? target`, whose cursors are the first cut-neighborhood
expansion of the target occurrence.  This module classifies each actual cursor of such a frame
*structurally*, without assuming any classification predicate:

* every cursor is an uncut carrier neighbor of the target, records the target as `previous?`, and
  is path-valid;
* consequently each cursor is either the parent cursor (address exactly
  `target.address.dropLast`) or a strict outward child cursor (address exactly
  `target.address ++ [slot]`); in the latter case it is an `OutwardRerootCursor` of the target;
* in the parent case the derived `LocalizedParentFrameHistory` certificate of the target exists
  and its actual parent occurrence is literally the cursor occurrence, so the cursor is the
  canonical parent cursor.  The activity-retaining certificate is obtained when the target itself
  is active;
* two parent cursors in one frame are equal (so parent-versus-parent cannot occur at distinct
  indices), while the frame cursor list is duplicate-free, so distinct indices carry distinct
  cursors;
* when the target sits at the root address, every cursor of the frame is an outward child.

All statements are about the object returned by the executable constructor
(`... = some frame`) or about its exact map.  No arbitrary cursor list is existentially
quantified, and no classification fact is hypothesized.  The outward read-agreement and eager
key-existence corollaries expose the bridge consumed by the downstream all-pairs descriptor
locality: only outward cursors are strict depth dependencies of the target, so only they inherit
the whole-state read agreement.  The parent cursor is deliberately left without such a read
claim, avoiding any parent-reference independence assumption.
-/

/-! ## Cursor classes -/

/-- Structural parent-cursor class: the cursor occurrence sits at the immediate carrier-parent
address of the target. -/
def IsLocalizedActualFrameParentCursor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  cursor.occurrence.1.address = target.1.address.dropLast

/-- Structural outward-child class: the cursor occurrence extends the target address by one
sibling slot. -/
def IsLocalizedActualFrameOutwardCursor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ slot : Nat, cursor.occurrence.1.address = target.1.address ++ [slot]

/-! ## The actual frame is exactly the executable expansion -/

/-- The cursor list of an actually computed four-ligand frame is definitionally the total
executable cut-neighborhood expansion of the target-start cursor.  This pins the construction
equality at the endpoint instead of leaving an arbitrary list. -/
theorem localizedOccurrenceFourLigandFrame_cursors_eq_executable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    frame.cursors = input.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) := by
  unfold localizedOccurrenceFourLigandFrame? at computed
  cases h : input.localizedOccurrenceLigandFrame? target with
  | none => simp [h] at computed
  | some cursors =>
      by_cases len : cursors.length = 4
      · simp [h, len] at computed
        subst frame
        have h' : input.localizedRerootChildren?
            ({ occurrence := target, previous? := none } :
              input.LocalizedRerootCursor carrierFuel) = some cursors := h
        rw [input.localizedRerootChildren?_eq_some_executable] at h'
        exact (Option.some.inj h').symm
      · simp [h, len] at computed

/-- An actual four-ligand frame forces the target node not to be a duplicate terminal: a
duplicate has an empty intended cut-neighborhood, which cannot have length four. -/
theorem localizedOccurrenceFourLigandFrame_target_not_duplicate
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    target.1.node.isDuplicateLeaf = false := by
  have derived :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mp computed
  have intendedLength :
      (input.intendedLocalizedRerootChildFrames
        ({ occurrence := target, previous? := none } :
          input.LocalizedRerootCursor carrierFuel)).length = 4 := by
    rw [← derived.1.1, List.length_map, frame.length_eq]
  by_cases duplicate : target.1.node.isDuplicateLeaf = true
  · simp [intendedLocalizedRerootChildFrames, duplicate] at intendedLength
  · exact Bool.eq_false_of_not_eq_true duplicate

/-- Exact ordered map of an actual frame: its four cursor occurrences are precisely the carrier
neighborhood of the target, in construction order. -/
theorem localizedOccurrenceFourLigandFrame_cursors_map_eq_neighborFrames
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    frame.cursors.map (fun cursor => cursor.occurrence.1) =
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 := by
  have derived :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mp computed
  have notDuplicate :=
    input.localizedOccurrenceFourLigandFrame_target_not_duplicate target frame computed
  rw [derived.1.1]
  simp [intendedLocalizedRerootChildFrames, notDuplicate]

/-! ## Membership, path validity, and the address dichotomy -/

/-- Every cursor of an actual frame is an uncut carrier neighbor of the target. -/
theorem localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors) :
    cursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 := by
  rw [← input.localizedOccurrenceFourLigandFrame_cursors_map_eq_neighborFrames
    target frame computed]
  exact List.mem_map.mpr ⟨cursor, present, rfl⟩

/-- Every cursor of an actual frame records the target occurrence as its incoming cut. -/
theorem localizedOccurrenceFourLigandFrame_cursor_previous
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors) :
    cursor.previous? = some target := by
  have derived :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mp computed
  exact derived.1.2 cursor present

/-- Every cursor of an actual frame keeps the target's final-center root. -/
theorem localizedOccurrenceFourLigandFrame_cursor_root
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors) :
    cursor.occurrence.1.root = target.1.root :=
  input.localizedRerootNeighborFrames_root_eq target.1 cursor.occurrence.1
    (input.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
      target frame computed cursor present)

/-- Every cursor of an actual frame is path-valid: its occurrence is the neighbor from which it
was reached. -/
theorem localizedOccurrenceFourLigandFrame_cursor_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors) :
    input.LocalizedRerootCursorValid cursor := by
  unfold LocalizedRerootCursorValid
  rw [input.localizedOccurrenceFourLigandFrame_cursor_previous
    target frame computed cursor present]
  exact input.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
    target frame computed cursor present

/-- **Address dichotomy for every actual frame cursor.**  Each cursor is either the parent
cursor or an outward child cursor with an explicit sibling slot. -/
theorem localizedOccurrenceFourLigandFrame_cursor_address_classification
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors) :
    (cursor.occurrence.1.address = target.1.address.dropLast ∧
        cursor.occurrence.1.address.length + 1 = target.1.address.length) ∨
      (∃ slot : Nat, cursor.occurrence.1.address = target.1.address ++ [slot]) := by
  have neighbor := input.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
    target frame computed cursor present
  have adjacent :=
    (input.mem_localizedRerootNeighborFrames_iff target.1 cursor.occurrence.1).mp neighbor
  rcases adjacent.2.2 with parent | child
  · exact Or.inl ⟨parent.2, parent.1⟩
  · right
    have nonempty : cursor.occurrence.1.address ≠ [] := by
      intro empty
      have zero : cursor.occurrence.1.address.length = 0 := by simp [empty]
      omega
    refine ⟨cursor.occurrence.1.address.getLast nonempty, ?_⟩
    calc
      cursor.occurrence.1.address
          = cursor.occurrence.1.address.dropLast ++
              [cursor.occurrence.1.address.getLast nonempty] :=
            (List.dropLast_append_getLast
              (l := cursor.occurrence.1.address) nonempty).symm
      _ = target.1.address ++
              [cursor.occurrence.1.address.getLast nonempty] := by
            rw [← child.2]

/-! ## The derived parent-frame history on the parent cursor -/

/-- A parent cursor forces a non-root target address, so the carrier parent-frame certificate
exists. -/
theorem localizedOccurrenceFourLigandFrame_parent_cursor_nonroot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors)
    (parentAddress : IsLocalizedActualFrameParentCursor input target cursor) :
    target.1.address ≠ [] := by
  have neighbor := input.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
    target frame computed cursor present
  intro root
  have parentAddress' : cursor.occurrence.1.address = target.1.address.dropLast :=
    parentAddress
  rw [root] at parentAddress'
  have cursorEmpty : cursor.occurrence.1.address = [] := by
    simpa using parentAddress'
  have adjacent :=
    (input.mem_localizedRerootNeighborFrames_iff target.1 cursor.occurrence.1).mp neighbor
  rcases adjacent.2.2 with parent | child
  · have parentStep : cursor.occurrence.1.address.length + 1 = 0 := by
      have step := parent.1
      rw [root] at step
      simp at step
    omega
  · have cursorLength : cursor.occurrence.1.address.length = 1 := by
      have step := child.1
      rw [root] at step
      simpa using step.symm
    have zero : cursor.occurrence.1.address.length = 0 := by simp [cursorEmpty]
    omega

/-- **Derived parent-frame history.**  A parent cursor of an actual frame is the actual carrier
parent occurrence of the target, together with the derived `LocalizedParentFrameHistory`
certificate. -/
theorem localizedOccurrenceFourLigandFrame_parent_cursor_history
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors)
    (parentAddress : IsLocalizedActualFrameParentCursor input target cursor) :
    ∃ certificate : input.LocalizedParentFrameHistory target,
      cursor.occurrence = certificate.parent := by
  have nonroot := input.localizedOccurrenceFourLigandFrame_parent_cursor_nonroot
    target frame computed cursor present parentAddress
  obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory target nonroot
  refine ⟨certificate, ?_⟩
  have cursorRoot := input.localizedOccurrenceFourLigandFrame_cursor_root
    target frame computed cursor present
  have sameRoot : certificate.parent.1.root = cursor.occurrence.1.root :=
    certificate.parent_root.trans cursorRoot.symm
  have parentAddress' : cursor.occurrence.1.address = target.1.address.dropLast :=
    parentAddress
  have sameAddress : certificate.parent.1.address = cursor.occurrence.1.address := by
    rw [certificate.parent_address, parentAddress']
  have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
    ((input.mem_localizedOccurrences_iff carrierFuel certificate.parent.1).mp
      certificate.parent.2)
    ((input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp
      cursor.occurrence.2)
    sameRoot sameAddress
  exact Subtype.ext frameEq.symm

/-- **Canonical parent cursor.**  The parent cursor of an actual frame is literally the canonical
cursor built from the derived parent-frame certificate. -/
theorem localizedOccurrenceFourLigandFrame_parent_cursor_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors)
    (parentAddress : IsLocalizedActualFrameParentCursor input target cursor) :
    ∃ certificate : input.LocalizedParentFrameHistory target,
      cursor = { occurrence := certificate.parent, previous? := some target } := by
  obtain ⟨certificate, occurrenceEq⟩ :=
    input.localizedOccurrenceFourLigandFrame_parent_cursor_history
      target frame computed cursor present parentAddress
  have previous := input.localizedOccurrenceFourLigandFrame_cursor_previous
    target frame computed cursor present
  exact ⟨certificate, LocalizedRerootCursor.ext input occurrenceEq previous⟩

/-- **Activity-retaining parent history.**  When the target itself is active, the parent cursor is
the canonical cursor of the derived activity-retaining parent-frame certificate. -/
theorem localizedOccurrenceFourLigandFrame_parent_cursor_activeHistory
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors)
    (parentAddress : IsLocalizedActualFrameParentCursor input target cursor)
    (active : target.1.node.ActiveSimple) :
    ∃ certificate : input.ActiveLocalizedParentFrameHistory target,
      cursor = { occurrence := certificate.toLocalizedParentFrameHistory.parent,
                  previous? := some target } := by
  have nonroot := input.localizedOccurrenceFourLigandFrame_parent_cursor_nonroot
    target frame computed cursor present parentAddress
  obtain ⟨certificate⟩ :=
    input.exists_activeLocalizedParentFrameHistory target active nonroot
  let plain := certificate.toLocalizedParentFrameHistory
  have cursorRoot := input.localizedOccurrenceFourLigandFrame_cursor_root
    target frame computed cursor present
  have sameRoot : plain.parent.1.root = cursor.occurrence.1.root :=
    plain.parent_root.trans cursorRoot.symm
  have parentAddress' : cursor.occurrence.1.address = target.1.address.dropLast :=
    parentAddress
  have sameAddress : plain.parent.1.address = cursor.occurrence.1.address := by
    rw [plain.parent_address, parentAddress']
  have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
    ((input.mem_localizedOccurrences_iff carrierFuel plain.parent.1).mp plain.parent.2)
    ((input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp
      cursor.occurrence.2)
    sameRoot sameAddress
  have occurrenceEq : cursor.occurrence = plain.parent := Subtype.ext frameEq.symm
  have previous := input.localizedOccurrenceFourLigandFrame_cursor_previous
    target frame computed cursor present
  refine ⟨certificate, ?_⟩
  change cursor = { occurrence := plain.parent, previous? := some target }
  exact LocalizedRerootCursor.ext input occurrenceEq previous

/-! ## Uniqueness of the parent cursor and distinctness of indexed cursors -/

/-- Two parent cursors of the same actual frame are the same cursor: the carrier parent
coordinate is a function of the target. -/
theorem localizedOccurrenceFourLigandFrame_parent_cursor_unique
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (left right : input.LocalizedRerootCursor carrierFuel)
    (leftPresent : left ∈ frame.cursors)
    (rightPresent : right ∈ frame.cursors)
    (leftParent : IsLocalizedActualFrameParentCursor input target left)
    (rightParent : IsLocalizedActualFrameParentCursor input target right) :
    left = right := by
  have leftRoot := input.localizedOccurrenceFourLigandFrame_cursor_root
    target frame computed left leftPresent
  have rightRoot := input.localizedOccurrenceFourLigandFrame_cursor_root
    target frame computed right rightPresent
  have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
    ((input.mem_localizedOccurrences_iff carrierFuel left.occurrence.1).mp
      left.occurrence.2)
    ((input.mem_localizedOccurrences_iff carrierFuel right.occurrence.1).mp
      right.occurrence.2)
    (leftRoot.trans rightRoot.symm)
    (leftParent.trans rightParent.symm)
  have occurrenceEq : left.occurrence = right.occurrence := Subtype.ext frameEq
  have leftPrevious := input.localizedOccurrenceFourLigandFrame_cursor_previous
    target frame computed left leftPresent
  have rightPrevious := input.localizedOccurrenceFourLigandFrame_cursor_previous
    target frame computed right rightPresent
  exact LocalizedRerootCursor.ext input occurrenceEq
    (leftPrevious.trans rightPrevious.symm)

/-- The cursor list of an actual frame is duplicate-free.  This is inherited from the
duplicate-freedom of the intended cut-neighborhood through the executable expansion. -/
theorem localizedOccurrenceFourLigandFrame_cursors_nodup
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    frame.cursors.Nodup := by
  have derived :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mp computed
  exact input.localizedRerootChildren_nodup
    ({ occurrence := target, previous? := none } :
      input.LocalizedRerootCursor carrierFuel)
    frame.cursors derived.1

/-- Indexed access to an actual frame is injective.  Distinct `Fin 4` indices therefore carry
distinct cursors; this is available because the actual frame is duplicate-free. -/
theorem localizedOccurrenceFourLigandFrame_cursorAt_injective
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    Function.Injective frame.cursorAt := by
  intro left right equal
  have nodup := input.localizedOccurrenceFourLigandFrame_cursors_nodup
    target frame computed
  have getEq : frame.cursors.get (Fin.cast frame.length_eq.symm left) =
      frame.cursors.get (Fin.cast frame.length_eq.symm right) := equal
  have indexEq : (Fin.cast frame.length_eq.symm left) =
      (Fin.cast frame.length_eq.symm right) :=
    (List.Nodup.get_inj_iff nodup).mp getEq
  apply Fin.ext
  simpa using congrArg Fin.val indexEq

/-- Distinct indices of an actual frame carry distinct cursors. -/
theorem localizedOccurrenceFourLigandFrame_cursorAt_ne
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    {left right : Fin 4} (distinct : left ≠ right) :
    frame.cursorAt left ≠ frame.cursorAt right :=
  fun equal =>
    distinct (input.localizedOccurrenceFourLigandFrame_cursorAt_injective
      target frame computed equal)

/-- Parent-versus-parent cannot occur at distinct indices of an actual frame. -/
theorem localizedOccurrenceFourLigandFrame_no_two_parent_cursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    {left right : Fin 4} (distinct : left ≠ right) :
    ¬ (IsLocalizedActualFrameParentCursor input target (frame.cursorAt left) ∧
        IsLocalizedActualFrameParentCursor input target (frame.cursorAt right)) := by
  rintro ⟨leftParent, rightParent⟩
  have leftPresent : frame.cursorAt left ∈ frame.cursors :=
    List.get_mem frame.cursors (Fin.cast frame.length_eq.symm left)
  have rightPresent : frame.cursorAt right ∈ frame.cursors :=
    List.get_mem frame.cursors (Fin.cast frame.length_eq.symm right)
  have cursorEq := input.localizedOccurrenceFourLigandFrame_parent_cursor_unique
    target frame computed (frame.cursorAt left) (frame.cursorAt right)
    leftPresent rightPresent leftParent rightParent
  exact distinct (input.localizedOccurrenceFourLigandFrame_cursorAt_injective
    target frame computed cursorEq)

/-! ## The indexed classification -/

/-- **Classification of every actual frame cursor.**  For an actually computed target-start
four-ligand frame, each indexed cursor is either the unique parent cursor, carrying the derived
parent-frame history certificate, or a path-valid strict outward child cursor with address
`target.address ++ [slot]`. -/
theorem localizedOccurrenceFourLigandFrame_cursorAt_classification
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    (∃ certificate : input.LocalizedParentFrameHistory target,
        frame.cursorAt index =
            { occurrence := certificate.parent, previous? := some target } ∧
          IsLocalizedActualFrameParentCursor input target (frame.cursorAt index)) ∨
      (IsLocalizedActualFrameOutwardCursor input target (frame.cursorAt index) ∧
        (frame.cursorAt index).occurrence.1.root = target.1.root ∧
        input.LocalizedRerootCursorValid (frame.cursorAt index) ∧
        OutwardRerootCursor input target (frame.cursorAt index)) := by
  have present : frame.cursorAt index ∈ frame.cursors :=
    List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)
  have structural :=
    input.localizedOccurrenceFourLigandFrame_cursor_address_classification
      target frame computed (frame.cursorAt index) present
  rcases structural with parent | child
  · obtain ⟨certificate, cursorEq⟩ :=
      input.localizedOccurrenceFourLigandFrame_parent_cursor_eq
        target frame computed (frame.cursorAt index) present parent.1
    exact Or.inl ⟨certificate, cursorEq, parent.1⟩
  · obtain ⟨slot, addressForm⟩ := child
    have valid := input.localizedOccurrenceFourLigandFrame_cursor_valid
      target frame computed (frame.cursorAt index) present
    have rootEq := input.localizedOccurrenceFourLigandFrame_cursor_root
      target frame computed (frame.cursorAt index) present
    have previous := input.localizedOccurrenceFourLigandFrame_cursor_previous
      target frame computed (frame.cursorAt index) present
    have strict : target.1.address.length <
        (frame.cursorAt index).occurrence.1.address.length := by
      rw [addressForm]
      simp
    have outward : OutwardRerootCursor input target (frame.cursorAt index) :=
      ⟨valid, ⟨rootEq, strict⟩, target, previous, strict⟩
    exact Or.inr ⟨⟨slot, addressForm⟩, rootEq, valid, outward⟩

/-! ## Root targets -/

/-- **Root case: all four cursors are outward.**  If the target address is empty, no cursor can
be a parent cursor, so every indexed cursor is a path-valid strict outward child with address
`target.address ++ [slot]`. -/
theorem localizedOccurrenceFourLigandFrame_root_all_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (rootAddress : target.1.address = []) :
    ∀ index : Fin 4,
      OutwardRerootCursor input target (frame.cursorAt index) ∧
        IsLocalizedActualFrameOutwardCursor input target (frame.cursorAt index) := by
  intro index
  have present : frame.cursorAt index ∈ frame.cursors :=
    List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)
  have structural :=
    input.localizedOccurrenceFourLigandFrame_cursor_address_classification
      target frame computed (frame.cursorAt index) present
  rcases structural with parent | child
  · exfalso
    have impossible : (frame.cursorAt index).occurrence.1.address.length + 1 = 0 := by
      simpa [rootAddress] using parent.2
    omega
  · obtain ⟨slot, addressForm⟩ := child
    have valid := input.localizedOccurrenceFourLigandFrame_cursor_valid
      target frame computed (frame.cursorAt index) present
    have rootEq := input.localizedOccurrenceFourLigandFrame_cursor_root
      target frame computed (frame.cursorAt index) present
    have previous := input.localizedOccurrenceFourLigandFrame_cursor_previous
      target frame computed (frame.cursorAt index) present
    have strict : target.1.address.length <
        (frame.cursorAt index).occurrence.1.address.length := by
      rw [addressForm]
      simp
    have outward : OutwardRerootCursor input target (frame.cursorAt index) :=
      ⟨valid, ⟨rootEq, strict⟩, target, previous, strict⟩
    exact ⟨outward, ⟨slot, addressForm⟩⟩

/-- In the root case no indexed cursor is a parent cursor. -/
theorem localizedOccurrenceFourLigandFrame_root_no_parent_cursor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (rootAddress : target.1.address = []) (index : Fin 4) :
    ¬ IsLocalizedActualFrameParentCursor input target (frame.cursorAt index) := by
  intro parentCursor
  have present : frame.cursorAt index ∈ frame.cursors :=
    List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)
  have structural :=
    input.localizedOccurrenceFourLigandFrame_cursor_address_classification
      target frame computed (frame.cursorAt index) present
  rcases structural with parent | child
  · have impossible : (frame.cursorAt index).occurrence.1.address.length + 1 = 0 := by
      simpa [rootAddress] using parent.2
    omega
  · obtain ⟨slot, addressForm⟩ := child
    have parentEmpty : (frame.cursorAt index).occurrence.1.address = [] := by
      have address : (frame.cursorAt index).occurrence.1.address =
          target.1.address.dropLast := parentCursor
      rw [rootAddress] at address
      simpa using address
    have nonempty : (frame.cursorAt index).occurrence.1.address ≠ [] := by
      rw [addressForm, rootAddress]
      simp
    exact nonempty parentEmpty

/-! ## Outward-only read and key bridges -/

/-- Only outward frame cursors are strict depth dependencies of the target, so their restricted
dependency-view read equals the unrestricted whole-state read.  No such claim is made for the
parent cursor. -/
theorem localizedOccurrenceFourLigandFrame_outward_read_agreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (_computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4)
    (outward : OutwardRerootCursor input target (frame.cursorAt index))
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    input.localizedDependencyLabel target
        (input.localizedDependencyView state target) (frame.cursorAt index) =
      state (frame.cursorAt index).occurrence :=
  input.localizedDependencyLabel_eq_state_of_dependency target state
    (frame.cursorAt index) outward.2.1

/-- Every outward frame cursor admits the eager compound Rules-4/5 key at the occurrence
evaluator's fuel. -/
theorem localizedOccurrenceFourLigandFrame_outward_evaluationFuel_key_exists
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (_computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4)
    (view : input.LocalizedDependencyView target)
    (outward : OutwardRerootCursor input target (frame.cursorAt index)) :
    ∃ key, input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt index) = some key := by
  obtain ⟨key, computedKey⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice target view
      (frame.cursorAt index) outward.1
  exact ⟨key, by
    simpa [localizedOccurrenceRerootEvaluationFuel] using computedKey⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority assertions

The exported classification, uniqueness, root, and bridge results are checked to depend only on
the permitted kernel axioms (`propext`, `Classical.choice`, `Quot.sound`). -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_cursors_eq_executable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_target_not_duplicate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_cursors_map_eq_neighborFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_cursor_previous
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_cursor_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_cursor_valid
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_cursor_address_classification
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_parent_cursor_nonroot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_parent_cursor_history
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_parent_cursor_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_parent_cursor_activeHistory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_parent_cursor_unique
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_cursors_nodup
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_cursorAt_injective
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_cursorAt_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_no_two_parent_cursors
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_cursorAt_classification
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_root_all_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_root_no_parent_cursor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_outward_read_agreement
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceFourLigandFrame_outward_evaluationFuel_key_exists
