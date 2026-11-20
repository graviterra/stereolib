import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCarrier
import TetraStereo.OneCenter.LocalizedNoDoubleWithChildren
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-! Certified lookup and reroot expansion using the exact finite carrier of the cyclic example.
These are computational replacements only: both equalities include every failure case. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleChildren

open CertifiedLocalizedCIPInput LocalizedChemicalRingCyclicExampleInput
open LocalizedChemicalRingCyclicExampleCarrier
open LocalizedMarkedCarrierLookup

abbrev Occ := certified.LocalizedCIPOccurrence 10
abbrev Cursor := certified.LocalizedRerootCursor 10
abbrev CyclicFrame := certified.LocalizedCIPOccurrenceFrame

private theorem map_attach_congr {α β : Type} (xs ys : List α) (same : xs = ys)
    (f : {x // x ∈ xs} → β) (g : {x // x ∈ ys} → β)
    (pointwise : ∀ x hx hy, f ⟨x, hx⟩ = g ⟨x, hy⟩) : xs.attach.map f = ys.attach.map g := by
  subst ys
  apply List.map_congr_left
  intro entry _
  exact pointwise entry.1 entry.2 entry.2

def rooted (atom : Atom) : List Occ :=
  (occurrencesAt 10 atom).attach.map fun entry =>
    ⟨entry.1, by
      unfold localizedOccurrences
      rw [List.mem_dedup, List.mem_flatMap]
      refine ⟨atom, by simp, ?_⟩
      rw [occurrencesAt_eq]
      exact entry.2⟩

theorem rooted_eq (atom : Atom) : rooted atom = rootedCarrier certified 10 atom := by
  unfold rooted rootedCarrier
  apply map_attach_congr _ _ (occurrencesAt_eq 10 atom).symm
  intros
  rfl

def lookupAt (atom : Atom) (node : RawMolecule.CanonicalBranchNode) : Option Occ :=
  (rooted atom).find? fun occurrence => nodeMatches certified occurrence.1.node node

def lookup (node : RawMolecule.CanonicalBranchNode) : Option Occ :=
  match node.history.getLast? with
  | none => none
  | some atom => if h : atom < 9 then lookupAt ⟨atom, h⟩ node else none

theorem lookup_eq (node : RawMolecule.CanonicalBranchNode) :
    lookup node = lookup? certified node := by
  unfold lookup lookup? lookupAt lookupAtRoot?
  simp only [rooted_eq]
  rfl

def neighborsOfFrame (frame : CyclicFrame) : List CyclicFrame :=
  ((carrier 10).filter fun candidate =>
    candidate.root == frame.root && candidate.address.length + 1 == frame.address.length &&
      candidate.address == frame.address.dropLast) ++
  ((carrier 10).filter fun candidate =>
    candidate.root == frame.root && candidate.address.length == frame.address.length + 1 &&
      candidate.address.dropLast == frame.address)

theorem neighborsOfFrame_eq (frame : CyclicFrame) :
    neighborsOfFrame frame = certified.localizedRerootNeighborFrames (fuel := 10) frame := by
  unfold neighborsOfFrame localizedRerootNeighborFrames localizedCarrierParentFrames
    localizedCarrierOutwardChildFrames
  rw [carrier_eq]

def intended (cursor : Cursor) : List CyclicFrame :=
  if cursor.occurrence.1.node.isDuplicateLeaf then [] else
    match cursor.previous? with
    | none => neighborsOfFrame cursor.occurrence.1
    | some previous => (neighborsOfFrame cursor.occurrence.1).filter fun frame =>
        frame.address != previous.1.address

theorem intended_eq (cursor : Cursor) :
    intended cursor = certified.intendedLocalizedRerootChildFrames cursor := by
  unfold intended intendedLocalizedRerootChildFrames
  cases cursor.occurrence.1.node.isDuplicateLeaf <;> cases cursor.previous? <;>
    simp [neighborsOfFrame_eq]

def readChildren (cursor : Cursor) : Option (List Cursor) :=
  some ((intended cursor).attach.map fun frame =>
    { occurrence := ⟨frame.1, certified.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames
        cursor frame.1 (by rw [← intended_eq]; exact frame.2)⟩
      previous? := some cursor.occurrence })

theorem readChildren_eq (cursor : Cursor) :
    readChildren cursor = certified.executableLocalizedRerootChildren? cursor := by
  unfold readChildren executableLocalizedRerootChildren? executableLocalizedRerootChildren
  congr 1
  apply map_attach_congr _ _ (intended_eq cursor)
  intros
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleChildren

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleChildren.lookup_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleChildren.readChildren_eq
