import TetraStereo.OneCenter.LocalizedOccurrenceRerootFrame

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Total executable local reroot children

`TetraStereo.OneCenter.LocalizedOccurrenceRerootFrame` defines the fail-closed optional expansion
`localizedRerootChildren?` of one occurrence-local reroot cursor.  That expansion collects the
intended cut-neighborhood `intendedLocalizedRerootChildFrames` and returns children only after
every intended coordinate has been certified to lie in the finite carrier `localizedOccurrences`;
otherwise it returns `none`.

The runtime certification is redundant.  The existing theorem
`mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames` already proves that *every*
intended coordinate is a carrier member, so attaching the carrier certificate to each intended
frame produces the expanded children directly and the expansion becomes total:

* `executableLocalizedRerootChildren` is that total list of child cursors;
* `executableLocalizedRerootChildren?` is its `some` twin, retained for the fail-closed
  interface;
* `localizedRerootChildren?_eq_some_executable` proves that the old optional expansion returns
  exactly the executable list, so no caller has to handle the unreachable `none` branch.

Both definitions are plain `def`s built from `List.attach` and `List.map`; no `classical` choice
and no runtime membership scan is used.  The carrier certificates stored in `LocalizedCIPOccurrence`
are propositions, are never inspected, and therefore never influence the emitted coordinates.

The executable list is pinned down independently of the optional expansion by
`executableLocalizedRerootChildren_map` (the exact intended frames, in order) and
`executableLocalizedRerootChildren_previous` (the source occurrence recorded as incoming cut),
i.e. by `executableLocalizedRerootChildren_declarative`.  `executableLocalizedRerootChildren_sound`
rederives the same statement through the old fail-closed soundness theorem
`localizedRerootChildren?_sound`, as a consistency check between the two routes.
-/

/-- Total executable children of one reroot cursor: the intended cut-neighborhood with the
carrier-membership certificates attached.  `List.attach` supplies the certificate that the frame
it carries is an intended frame, and
`mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames` turns it into the carrier
certificate demanded by `LocalizedCIPOccurrence`.  No membership test is performed and the
definition cannot fail. -/
def executableLocalizedRerootChildren
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    List (input.LocalizedRerootCursor fuel) :=
  (input.intendedLocalizedRerootChildFrames cursor).attach.map fun frame =>
    { occurrence :=
        ⟨frame.1,
          input.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames
            cursor frame.1 frame.2⟩
      previous? := some cursor.occurrence }

/-- Optional twin of `executableLocalizedRerootChildren`, kept for the fail-closed interface
`localizedRerootChildren?`.  Because the total list always exists, this option is always `some`. -/
def executableLocalizedRerootChildren?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    Option (List (input.LocalizedRerootCursor fuel)) :=
  some (input.executableLocalizedRerootChildren cursor)

/-- The optional twin is by definition the total executable list. -/
theorem executableLocalizedRerootChildren?_eq_some
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.executableLocalizedRerootChildren? cursor =
      some (input.executableLocalizedRerootChildren cursor) :=
  rfl

/-- The optional twin never fails: total expansion always succeeds. -/
theorem executableLocalizedRerootChildren?_isSome
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.executableLocalizedRerootChildren? cursor).isSome = true := by
  simp [executableLocalizedRerootChildren?]

/-- Projecting the executable children back to occurrence frames recovers the intended
cut-neighborhood exactly, in the same order.  The carrier certificates are erased by the
projection, so this is the independent frame-level meaning of the executable list. -/
theorem executableLocalizedRerootChildren_map
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.executableLocalizedRerootChildren cursor).map
        (fun child => child.occurrence.1) =
      input.intendedLocalizedRerootChildFrames cursor := by
  unfold executableLocalizedRerootChildren
  rw [List.map_map]
  conv_rhs =>
    rw [← List.attach_map_subtype_val (input.intendedLocalizedRerootChildFrames cursor)]
  apply List.map_congr_left
  intro frame _framePresent
  rfl

/-- Every executable child records the source occurrence as its incoming cut. -/
theorem executableLocalizedRerootChildren_previous
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (child : input.LocalizedRerootCursor fuel)
    (present : child ∈ input.executableLocalizedRerootChildren cursor) :
    child.previous? = some cursor.occurrence := by
  unfold executableLocalizedRerootChildren at present
  rw [List.mem_map] at present
  rcases present with ⟨frame, _framePresent, rfl⟩
  rfl

/-- The executable children are exactly the intended cut-neighborhood in order, each recording the
source occurrence as incoming cut.  This is `DeclarativeLocalizedRerootChildren` proved directly
from the two projections, without passing through the optional expansion. -/
theorem executableLocalizedRerootChildren_declarative
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.DeclarativeLocalizedRerootChildren cursor
      (input.executableLocalizedRerootChildren cursor) :=
  ⟨input.executableLocalizedRerootChildren_map cursor,
    fun child present =>
      input.executableLocalizedRerootChildren_previous cursor child present⟩

/-- The old fail-closed expansion returns exactly the executable list.  Its `none` branch is
unreachable, because every intended frame is already a member of the finite occurrence carrier,
so its runtime membership scan always succeeds; the two dependent record constructions differ only
in the (propositional, erased) carrier certificates. -/
theorem localizedRerootChildren?_eq_some_executable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.localizedRerootChildren? cursor =
      some (input.executableLocalizedRerootChildren cursor) := by
  classical
  have present : ∀ frame ∈ input.intendedLocalizedRerootChildFrames cursor,
      frame ∈ input.localizedOccurrences fuel := fun frame framePresent =>
    input.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames
      cursor frame framePresent
  unfold localizedRerootChildren?
  rw [dif_pos present]
  rw [Option.some.injEq]
  unfold executableLocalizedRerootChildren
  apply List.map_congr_left
  intro frame _framePresent
  apply LocalizedRerootCursor.ext input
  · exact Subtype.ext rfl
  · rfl

/-- The independent declarative meaning of the executable list, recovered from the old fail-closed
soundness theorem `localizedRerootChildren?_sound` applied to
`localizedRerootChildren?_eq_some_executable`.  It agrees with
`executableLocalizedRerootChildren_declarative`, which is proved directly. -/
theorem executableLocalizedRerootChildren_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.DeclarativeLocalizedRerootChildren cursor
      (input.executableLocalizedRerootChildren cursor) :=
  input.localizedRerootChildren?_sound cursor (input.executableLocalizedRerootChildren cursor)
    (input.localizedRerootChildren?_eq_some_executable cursor)

/-- Executable expansion never repeats a child cursor.  This is inherited from the coordinate
duplicate-freedom of the intended cut-neighborhood through the existing theorem
`localizedRerootChildren_nodup`. -/
theorem executableLocalizedRerootChildren_nodup
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.executableLocalizedRerootChildren cursor).Nodup :=
  input.localizedRerootChildren_nodup cursor (input.executableLocalizedRerootChildren cursor)
    (input.executableLocalizedRerootChildren_declarative cursor)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
