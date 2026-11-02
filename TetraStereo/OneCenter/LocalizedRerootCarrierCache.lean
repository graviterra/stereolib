import TetraStereo.OneCenter.LocalizedNoDoubleWithChildren
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Share the finite occurrence carrier across reroot expansions

The executable child wrapper still obtains its parent and outward frames by filtering the full
occurrence carrier. Rebuilding that carrier at every cursor repeats the all-root expansion and
deduplication. This module stores the exact carrier once and performs the original ordered filters
on that stored list. Both frame selection and certified cursor construction are unchanged.

The existing `WithChildren` compiler then gives exact equality of cumulative keys, compound keys
and descriptors, including refusals. No acyclicity, single-bond, reader, geometry or reference-count
hypothesis is needed for these implementation equalities. The initial carrier construction and
linear lookup cost remain; callers should bind one cache outside repeated stages or rounds.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- One materialized carrier, with a proof-erased certificate of its exact contents and order. -/
structure LocalizedRerootCarrierCache (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  frames : List input.LocalizedCIPOccurrenceFrame
  correct : frames = input.localizedOccurrences fuel

/-- Materialize once at the caller, then share the returned value across cursor and stage reads. -/
def localizedRerootCarrierCache (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedRerootCarrierCache fuel :=
  ⟨input.localizedOccurrences fuel, rfl⟩

namespace LocalizedRerootCarrierCache

variable {input : CertifiedLocalizedCIPInput} {fuel : Nat}

/-- Exactly the original parent-first neighborhood, filtering a retained carrier value. -/
def neighborFrames (cache : input.LocalizedRerootCarrierCache fuel)
    (frame : input.LocalizedCIPOccurrenceFrame) :
    List input.LocalizedCIPOccurrenceFrame :=
  (cache.frames.filter fun candidate =>
    candidate.root == frame.root &&
      candidate.address.length + 1 == frame.address.length &&
      candidate.address == frame.address.dropLast) ++
  (cache.frames.filter fun candidate =>
    candidate.root == frame.root &&
      candidate.address.length == frame.address.length + 1 &&
      candidate.address.dropLast == frame.address)

/-- Preserve duplicate leaves and the incoming-address cut exactly. -/
def intendedFrames (cache : input.LocalizedRerootCarrierCache fuel)
    (cursor : input.LocalizedRerootCursor fuel) :
    List input.LocalizedCIPOccurrenceFrame :=
  if cursor.occurrence.1.node.isDuplicateLeaf then []
  else
    match cursor.previous? with
    | none => cache.neighborFrames cursor.occurrence.1
    | some previous =>
        (cache.neighborFrames cursor.occurrence.1).filter fun frame =>
          frame.address != previous.1.address

theorem intendedFrames_eq (cache : input.LocalizedRerootCarrierCache fuel)
    (cursor : input.LocalizedRerootCursor fuel) :
    cache.intendedFrames cursor = input.intendedLocalizedRerootChildFrames cursor := by
  cases cache with
  | mk frames correct =>
      subst frames
      rfl

/-- Attach the existing carrier-membership proof without recomputing carrier membership. -/
def children (cache : input.LocalizedRerootCarrierCache fuel)
    (cursor : input.LocalizedRerootCursor fuel) :
    List (input.LocalizedRerootCursor fuel) :=
  (cache.intendedFrames cursor).attach.map fun frame =>
    { occurrence :=
        ⟨frame.1,
          input.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames
            cursor frame.1 (by rw [← cache.intendedFrames_eq cursor]; exact frame.2)⟩
      previous? := some cursor.occurrence }

def readChildren (cache : input.LocalizedRerootCarrierCache fuel)
    (cursor : input.LocalizedRerootCursor fuel) :
    Option (List (input.LocalizedRerootCursor fuel)) :=
  some (cache.children cursor)

theorem readChildren_eq (cache : input.LocalizedRerootCarrierCache fuel)
    (cursor : input.LocalizedRerootCursor fuel) :
    cache.readChildren cursor = input.executableLocalizedRerootChildren? cursor := by
  cases cache with
  | mk frames correct =>
      subst frames
      rfl

/-- Exact cumulative-key equality for every stage, dependency view and fuel, including failure. -/
theorem cumulative_eq (cache : input.LocalizedRerootCarrierCache fuel)
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (depth : Nat) (cursor : input.LocalizedRerootCursor fuel) :
    WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?
        input cache.readChildren stage target view depth cursor =
      input.buildLocalizedRerootCumulativeRule45KeyExec? stage target view depth cursor :=
  WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?_eq_original
    input cache.readChildren cache.readChildren_eq stage target view depth cursor

/-- The complete compound Rules-4b/4c/5 key is preserved, not only its comparison result. -/
theorem compound45_eq (cache : input.LocalizedRerootCarrierCache fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (depth : Nat) (cursor : input.LocalizedRerootCursor fuel) :
    WithChildren.buildLocalizedRerootCompoundRule45KeyExec?
        input cache.readChildren target view depth cursor =
      input.buildLocalizedRerootCompoundRule45KeyExec? target view depth cursor :=
  WithChildren.buildLocalizedRerootCompoundRule45KeyExec?_eq_original
    input cache.readChildren cache.readChildren_eq target view depth cursor

/-- The existing no-localized-double executable descriptor keeps its exact result. The equality
itself imposes no chemistry-domain restriction and makes no new chemical correctness claim. -/
theorem descriptor_eq (cache : input.LocalizedRerootCarrierCache fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    WithChildren.localizedNoDoubleDescriptorExec? input cache.readChildren target view =
      input.localizedNoDoubleDescriptorExec? target view :=
  WithChildren.localizedNoDoubleDescriptorExec?_eq_original
    input cache.readChildren cache.readChildren_eq target view

assert_kernel_only intendedFrames_eq
assert_kernel_only readChildren_eq
assert_kernel_only cumulative_eq
assert_kernel_only compound45_eq
assert_kernel_only descriptor_eq

end LocalizedRerootCarrierCache
end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
