import TetraStereo.OneCenter.LocalizedRerootCarrierCache
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Share an exact selected-root slice of an already materialized carrier. The caller
constructs the slice once. Child reads at that root filter the smaller list; every other
root falls back to the original cache. All filtering order, duplicate leaves, incoming
cuts and typed occurrence payloads are preserved. No valid-cursor or root-match premise
is needed for the resulting reader equality. -/
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- A child reader certified equal to the actual executable reader on every cursor. -/
structure LocalizedRerootChildReader (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel))
  readChildren_eq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor

instance {input : CertifiedLocalizedCIPInput} {fuel : Nat} :
    Coe (input.LocalizedRerootCarrierCache fuel) (input.LocalizedRerootChildReader fuel) where
  coe cache := ⟨cache.readChildren, cache.readChildren_eq⟩

/-- Both lists are materialized values; the full cache remains available for other roots. -/
structure LocalizedRerootRootSliceCache (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  full : input.LocalizedRerootCarrierCache fuel
  root : input.Atom
  frames : List input.LocalizedCIPOccurrenceFrame
  correct : frames = full.frames.filter (fun frame => frame.root == root)

/-- Call once outside repeated cursor/stage evaluation. -/
def localizedRerootRootSliceCache {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (full : input.LocalizedRerootCarrierCache fuel) (root : input.Atom) :
    input.LocalizedRerootRootSliceCache fuel :=
  ⟨full, root, full.frames.filter (fun frame => frame.root == root), rfl⟩

namespace LocalizedRerootRootSliceCache

variable {input : CertifiedLocalizedCIPInput} {fuel : Nat}

private theorem filter_root_redundant (frames : List input.LocalizedCIPOccurrenceFrame)
    (root : input.Atom) (p : input.LocalizedCIPOccurrenceFrame → Bool)
    (guard : ∀ frame, p frame = true → frame.root = root) :
    (frames.filter (fun frame => frame.root == root)).filter p = frames.filter p := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro frame _
  cases h : p frame with
  | false => simp
  | true => simp [guard frame h]

def neighborFrames (slice : input.LocalizedRerootRootSliceCache fuel)
    (frame : input.LocalizedCIPOccurrenceFrame) : List input.LocalizedCIPOccurrenceFrame :=
  if frame.root = slice.root then
    (slice.frames.filter fun candidate =>
      candidate.root == frame.root && candidate.address.length + 1 == frame.address.length &&
        candidate.address == frame.address.dropLast) ++
    (slice.frames.filter fun candidate =>
      candidate.root == frame.root && candidate.address.length == frame.address.length + 1 &&
        candidate.address.dropLast == frame.address)
  else slice.full.neighborFrames frame

theorem neighborFrames_eq (slice : input.LocalizedRerootRootSliceCache fuel)
    (frame : input.LocalizedCIPOccurrenceFrame) :
    slice.neighborFrames frame = slice.full.neighborFrames frame := by
  unfold neighborFrames
  split
  · rename_i sameRoot
    simp only [slice.correct]
    unfold LocalizedRerootCarrierCache.neighborFrames
    congr 1
    · apply filter_root_redundant
      intro candidate included
      simp only [Bool.and_eq_true, beq_iff_eq] at included
      exact included.1.1.trans sameRoot
    · apply filter_root_redundant
      intro candidate included
      simp only [Bool.and_eq_true, beq_iff_eq] at included
      exact included.1.1.trans sameRoot
  · rfl

def intendedFrames (slice : input.LocalizedRerootRootSliceCache fuel)
    (cursor : input.LocalizedRerootCursor fuel) : List input.LocalizedCIPOccurrenceFrame :=
  if cursor.occurrence.1.node.isDuplicateLeaf then []
  else
    match cursor.previous? with
    | none => slice.neighborFrames cursor.occurrence.1
    | some previous => (slice.neighborFrames cursor.occurrence.1).filter fun frame =>
        frame.address != previous.1.address

theorem intendedFrames_eq (slice : input.LocalizedRerootRootSliceCache fuel)
    (cursor : input.LocalizedRerootCursor fuel) :
    slice.intendedFrames cursor = input.intendedLocalizedRerootChildFrames cursor := by
  rw [← slice.full.intendedFrames_eq cursor]
  unfold intendedFrames LocalizedRerootCarrierCache.intendedFrames
  simp only [neighborFrames_eq]
  rfl

def readChildren (slice : input.LocalizedRerootRootSliceCache fuel)
    (cursor : input.LocalizedRerootCursor fuel) :
    Option (List (input.LocalizedRerootCursor fuel)) :=
  some ((slice.intendedFrames cursor).attach.map fun frame =>
    { occurrence :=
        ⟨frame.1, input.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames
          cursor frame.1 (by rw [← slice.intendedFrames_eq cursor]; exact frame.2)⟩
      previous? := some cursor.occurrence })

private theorem map_attach_congr {α β : Type} (xs ys : List α) (same : xs = ys)
    (f : {x // x ∈ xs} → β) (g : {x // x ∈ ys} → β)
    (pointwise : ∀ x hx hy, f ⟨x, hx⟩ = g ⟨x, hy⟩) : xs.attach.map f = ys.attach.map g := by
  subst ys
  apply List.map_congr_left
  intro entry _
  exact pointwise entry.1 entry.2 entry.2

theorem readChildren_eq (slice : input.LocalizedRerootRootSliceCache fuel)
    (cursor : input.LocalizedRerootCursor fuel) :
    slice.readChildren cursor = input.executableLocalizedRerootChildren? cursor := by
  unfold readChildren executableLocalizedRerootChildren? executableLocalizedRerootChildren
  congr 1
  apply map_attach_congr _ _ (slice.intendedFrames_eq cursor)
  intros
  rfl

def reader (slice : input.LocalizedRerootRootSliceCache fuel) : input.LocalizedRerootChildReader fuel :=
  ⟨slice.readChildren, slice.readChildren_eq⟩

instance : Coe (input.LocalizedRerootRootSliceCache fuel) (input.LocalizedRerootChildReader fuel) where
  coe := reader

end LocalizedRerootRootSliceCache
end TetraStereo.OneCenter.CertifiedLocalizedCIPInput

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootRootSliceCache.neighborFrames_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootRootSliceCache.intendedFrames_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootRootSliceCache.readChildren_eq
