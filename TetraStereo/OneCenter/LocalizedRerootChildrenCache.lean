import TetraStereo.OneCenter.LocalizedOccurrenceFiniteCarrier
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Runtime reader for the reroot children of a carrier

`localizedRerootChildrenFromCarrier?` expands a reroot cursor from a *runtime* occurrence list: it
filters the supplied carrier for the shorter-address parents and the longer-address outward
children, concatenates them, applies the incoming cut, and returns the resulting cursors.  It is
the executable-reader form of the declarative expansion, in which the carrier is an argument rather
than the module-wide enumeration `localizedOccurrences`.

This module proves that reading from the canonical executable carrier
`localizedOccurrenceCarrier fuel` reproduces the existing executable expansion exactly:
`localizedRerootChildrenFromCarrier?_eq_executable`.  The proof is by extensionality of the carrier
projection: because `localizedOccurrenceCarrier fuel` is precisely the attachment of
`localizedOccurrences fuel`, filtering it and projecting to frames commutes with filtering the raw
enumeration (`List.filter_map`), so the runtime reader's child frames coincide with
`intendedLocalizedRerootChildFrames`; the shared declarative meaning then forces the two cursor
lists to be equal.
-/

/-- Runtime reroot expansion: expand `cursor` from the supplied runtime carrier by collecting its
carrier parents and carrier outward children, cutting the incoming coordinate, and recording the
source occurrence as the incoming cut of every emitted child. -/
def localizedRerootChildrenFromCarrier?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (carrier : List (input.LocalizedCIPOccurrence fuel))
    (cursor : input.LocalizedRerootCursor fuel) :
    Option (List (input.LocalizedRerootCursor fuel)) :=
  let frame := cursor.occurrence.1
  let parents := carrier.filter fun candidate =>
    candidate.1.root == frame.root &&
      candidate.1.address.length + 1 == frame.address.length &&
      candidate.1.address == frame.address.dropLast
  let outward := carrier.filter fun candidate =>
    candidate.1.root == frame.root &&
      candidate.1.address.length == frame.address.length + 1 &&
      candidate.1.address.dropLast == frame.address
  let neighbors := parents ++ outward
  let children := if frame.node.isDuplicateLeaf then [] else
    match cursor.previous? with
    | none => neighbors
    | some previous => neighbors.filter fun child => child.1.address != previous.1.address
  some (children.map fun occurrence => { occurrence, previous? := some cursor.occurrence })

/-- Filtering an attached list by a predicate on the underlying value and then projecting back to
the underlying value is the same as filtering the original list.  This is the proof-irrelevance of
`List.attach` for `Bool`-valued predicates; it is the bridge that erases the carrier certificates
stored in `LocalizedCIPOccurrence`. -/
private theorem attach_filter_map_val {α : Type*} (l : List α) (p : α → Bool) :
    ((l.attach.filter fun x => p x.1 : List {x // x ∈ l}).map Subtype.val) = l.filter p := by
  simp [List.filter_attach, List.map_map, Subtype.map, Function.comp_def]

/-- The runtime reader's parent selection is exactly the declarative carrier parent list. -/
theorem localizedRerootChildrenFromCarrier?_parents_map
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (((input.localizedOccurrenceCarrier fuel).filter fun candidate =>
        candidate.1.root == frame.root &&
          candidate.1.address.length + 1 == frame.address.length &&
          candidate.1.address == frame.address.dropLast).map Subtype.val) =
      input.localizedCarrierParentFrames (fuel := fuel) frame := by
  show (((input.localizedOccurrences fuel).attach.filter fun candidate =>
      candidate.1.root == frame.root &&
        candidate.1.address.length + 1 == frame.address.length &&
        candidate.1.address == frame.address.dropLast).map Subtype.val) =
    (input.localizedOccurrences fuel).filter fun candidate =>
      candidate.root == frame.root &&
        candidate.address.length + 1 == frame.address.length &&
        candidate.address == frame.address.dropLast
  exact attach_filter_map_val (input.localizedOccurrences fuel) (fun candidate =>
    candidate.root == frame.root &&
      candidate.address.length + 1 == frame.address.length &&
      candidate.address == frame.address.dropLast)

/-- The runtime reader's outward selection is exactly the declarative carrier outward child list. -/
theorem localizedRerootChildrenFromCarrier?_outward_map
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (((input.localizedOccurrenceCarrier fuel).filter fun candidate =>
        candidate.1.root == frame.root &&
          candidate.1.address.length == frame.address.length + 1 &&
          candidate.1.address.dropLast == frame.address).map Subtype.val) =
      input.localizedCarrierOutwardChildFrames (fuel := fuel) frame := by
  show (((input.localizedOccurrences fuel).attach.filter fun candidate =>
      candidate.1.root == frame.root &&
        candidate.1.address.length == frame.address.length + 1 &&
        candidate.1.address.dropLast == frame.address).map Subtype.val) =
    (input.localizedOccurrences fuel).filter fun candidate =>
      candidate.root == frame.root &&
        candidate.address.length == frame.address.length + 1 &&
        candidate.address.dropLast == frame.address
  exact attach_filter_map_val (input.localizedOccurrences fuel) (fun candidate =>
    candidate.root == frame.root &&
      candidate.address.length == frame.address.length + 1 &&
      candidate.address.dropLast == frame.address)

/-- Reading the children of a cursor from the canonical executable carrier yields cursors whose
ordered occurrence frames are exactly the intended cut-neighborhood, with the source occurrence
recorded as incoming cut.  This is the frame-level meaning of the runtime reader. -/
theorem localizedRerootChildrenFromCarrier?_map_val
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (computed : localizedRerootChildrenFromCarrier? input
        (carrier := input.localizedOccurrenceCarrier fuel) cursor = some children) :
    children.map (fun child => child.occurrence.1) =
        input.intendedLocalizedRerootChildFrames cursor ∧
      ∀ child ∈ children, child.previous? = some cursor.occurrence := by
  let carrier := input.localizedOccurrenceCarrier fuel
  let frame := cursor.occurrence.1
  let parents : List (input.LocalizedCIPOccurrence fuel) := carrier.filter fun candidate =>
    candidate.1.root == frame.root &&
      candidate.1.address.length + 1 == frame.address.length &&
      candidate.1.address == frame.address.dropLast
  let outward : List (input.LocalizedCIPOccurrence fuel) := carrier.filter fun candidate =>
    candidate.1.root == frame.root &&
      candidate.1.address.length == frame.address.length + 1 &&
      candidate.1.address.dropLast == frame.address
  let neighbors : List (input.LocalizedCIPOccurrence fuel) := parents ++ outward
  let children' : List (input.LocalizedCIPOccurrence fuel) :=
    if frame.node.isDuplicateLeaf then [] else
      match cursor.previous? with
      | none => neighbors
      | some previous => neighbors.filter fun child => child.1.address != previous.1.address
  let built : List (input.LocalizedRerootCursor fuel) := children'.map fun occurrence =>
    { occurrence, previous? := some cursor.occurrence }
  have hparents : parents.map Subtype.val =
      input.localizedCarrierParentFrames (fuel := fuel) frame :=
    input.localizedRerootChildrenFromCarrier?_parents_map fuel frame
  have houtward : outward.map Subtype.val =
      input.localizedCarrierOutwardChildFrames (fuel := fuel) frame :=
    input.localizedRerootChildrenFromCarrier?_outward_map fuel frame
  have hneighbors : neighbors.map Subtype.val =
      input.localizedRerootNeighborFrames (fuel := fuel) frame := by
    show (parents ++ outward).map Subtype.val =
      (input.localizedCarrierParentFrames (fuel := fuel) frame ++
        input.localizedCarrierOutwardChildFrames (fuel := fuel) frame)
    rw [List.map_append, hparents, houtward]
  have hchildren : children'.map Subtype.val =
      input.intendedLocalizedRerootChildFrames cursor := by
    show (if frame.node.isDuplicateLeaf then [] else
        match cursor.previous? with
        | none => neighbors
        | some previous => neighbors.filter fun child => child.1.address != previous.1.address).map
          Subtype.val =
      (if cursor.occurrence.1.node.isDuplicateLeaf then [] else
        match cursor.previous? with
        | none => input.localizedRerootNeighborFrames (fuel := fuel) cursor.occurrence.1
        | some previous =>
            (input.localizedRerootNeighborFrames (fuel := fuel)
              cursor.occurrence.1).filter fun candidate =>
              candidate.address != previous.1.address)
    split
    · rfl
    · split
      · exact hneighbors
      · rename_i previous _previousIdentity
        rw [← hneighbors]
        exact (List.filter_map (f := Subtype.val)
          (p := fun candidate : input.LocalizedCIPOccurrenceFrame =>
            candidate.address != previous.1.address) (l := neighbors)).symm
  have hbuilt : built.map (fun child => child.occurrence.1) = children'.map Subtype.val := by
    show (children'.map _).map _ = children'.map Subtype.val
    rw [List.map_map]
    rfl
  have hbuiltPrevious : ∀ child ∈ built, child.previous? = some cursor.occurrence := by
    intro child present
    dsimp only [built] at present
    rw [List.mem_map] at present
    rcases present with ⟨occurrence, _occurrencePresent, rfl⟩
    rfl
  have hbuiltEq : built = children := by
    change some built = some children at computed
    exact Option.some.inj computed
  have hchildrenEq : children.map (fun child => child.occurrence.1) =
      children'.map Subtype.val := by
    rw [← hbuiltEq, hbuilt]
  exact ⟨hchildrenEq.trans hchildren,
    fun child present => hbuiltPrevious child (hbuiltEq.symm ▸ present)⟩

/-- Reading the reroot children from the canonical executable occurrence carrier reproduces the
executable expansion exactly.  The runtime reader never inspects the carrier certificates, so its
selection coincides with the frame-level intended cut-neighborhood; the shared declarative meaning
then identifies the two cursor lists. -/
theorem localizedRerootChildrenFromCarrier?_eq_executable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    localizedRerootChildrenFromCarrier? input
        (carrier := input.localizedOccurrenceCarrier fuel) cursor =
      some (input.executableLocalizedRerootChildren cursor) := by
  obtain ⟨children, computed⟩ : ∃ children,
      localizedRerootChildrenFromCarrier? input
        (carrier := input.localizedOccurrenceCarrier fuel) cursor = some children :=
    ⟨_, rfl⟩
  have mapped := input.localizedRerootChildrenFromCarrier?_map_val cursor children computed
  have declarative : input.DeclarativeLocalizedRerootChildren cursor children :=
    ⟨mapped.1, mapped.2⟩
  have optional : input.localizedRerootChildren? cursor = some children :=
    (input.localizedRerootChildren?_eq_some_iff cursor children).mpr declarative
  have executable : input.localizedRerootChildren? cursor =
      some (input.executableLocalizedRerootChildren cursor) :=
    input.localizedRerootChildren?_eq_some_executable cursor
  have childrenEq : children = input.executableLocalizedRerootChildren cursor :=
    Option.some.inj (optional.symm.trans executable)
  rw [computed, childrenEq]

/-- The runtime reader from the canonical carrier never fails. -/
theorem localizedRerootChildrenFromCarrier?_isSome
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (localizedRerootChildrenFromCarrier? input
        (carrier := input.localizedOccurrenceCarrier fuel) cursor).isSome = true := by
  rw [input.localizedRerootChildrenFromCarrier?_eq_executable cursor]
  rfl

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
