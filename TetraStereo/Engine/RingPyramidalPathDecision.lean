import TetraStereo.Engine.RingPyramidalPathRank
import TetraStereo.Engine.RingTerminalPyramid

/-! Pyramidal orientation from the input bonds, physical coordinates and
original path. The decision can run without expanding any ligand subtree. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPyramidalPathDecision
open OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Labels)
open RingPyramidalSource (Directions slots atomId)
open RingPyramidalPathRank (atSite)
open RingAtomicNeighborOrder (neighbors)
open RingStereoSiblingPass (order legal_order)
attribute [local instance] lexOrd
open private nodup_injective from TetraStereo.Engine.RingPyramidalSource

def row (i : Input) (q : Site i) (a : i.certified.Atom) : List Nat :=
  order (atSite i q a) (neighbors i.molecule a.val)

def reading (i : Input) (q : Site i) (a : i.certified.Atom) : Option Labels :=
  (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
    (row i q a ++ [a.val])).map fun h => (.chiral h,.chiral h.swap)

/-- A tie defers to the recursive evaluator. A flat frame has a determined
absent descriptor, so it is a successful decision. -/
def direct? (i : Input) (q : Site i) : Option (Option Labels) := do
  let a ← RingPyramidalPublication.focusP i q
  guard (((neighbors i.molecule a.val).map (atSite i q a)).Nodup)
  return reading i q a

private theorem weights {i : Input} {q : Site i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) (d : Directions i q) :
    RingTerminalPyramid.weight d = atSite i q a ∘ atomId d := by
  unfold RingPyramidalPublication.focusP at selected
  split at selected <;> try contradiction
  rename_i real
  have current := (Option.filter_eq_some_iff.mp selected).1
  funext s
  exact (RingPyramidalPathRank.rank_direction real current d s).symm

theorem ranks_perm {i : Input} {q : Site i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) (d : Directions i q) :
    (slots.map (RingTerminalPyramid.weight d)).Perm
      ((neighbors i.molecule a.val).map (atSite i q a)) := by
  have p := (RingPyramidalPathRank.neighbors_perm d selected).map (atSite i q a)
  rwa [List.map_map,← weights selected d] at p

theorem direct_of_strict {i : Input} {q : Site i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) (d : Directions i q)
    (strict : Function.Injective (RingTerminalPyramid.weight d)) :
    direct? i q = some (reading i q a) := by
  have nd : (slots.map (RingTerminalPyramid.weight d)).Nodup := (nodup_injective _).mpr strict
  have raw := (ranks_perm selected d).nodup_iff.mp nd
  simp [direct?,selected,raw,guard]

theorem local_exact {i : Input} {q : Site i} {r : RingNestedActivePair.Reader i}
    (ready : RingGroupedStereo.Ready q r) {v : Option Labels}
    (hit : direct? i q = some v) : RingPyramidalPublication.publish i q r = some v := by
  cases selected : RingPyramidalPublication.focusP i q with
  | none => simp [direct?,selected] at hit
  | some a =>
    obtain ⟨d⟩ := RingPyramidalSource.selected_framed selected
    let key := atSite i q a
    by_cases nd : ((neighbors i.molecule a.val).map key).Nodup
    · have dinj := (nodup_injective (RingTerminalPyramid.weight d)).mp ((ranks_perm selected d).nodup_iff.mpr nd)
      have native := RingTerminalPyramid.local_exact ready (RingTerminalPyramid.hit_of_injective selected d dinj)
      let ds := order (RingTerminalPyramid.weight d) slots
      have dlegal := legal_order (RingTerminalPyramid.weight d) slots
      have rawLegal := legal_order key (neighbors i.molecule a.val)
      have p : (ds.map (atomId d)).Perm (row i q a) :=
        ((dlegal.perm.map _).trans (RingPyramidalPathRank.neighbors_perm d selected)).trans rawLegal.perm.symm
      have strictRows (xs : List Nat) (p' : xs.Perm (neighbors i.molecule a.val))
          (desc : (xs.map key).Pairwise (· ≥ ·)) : xs.Pairwise (fun x y => key y < key x) :=
        List.pairwise_map.mp ((desc.and ((p'.map key).nodup_iff.mpr nd)).imp
          fun h => lt_of_le_of_ne h.1 h.2.symm)
      have left : ((ds.map (atomId d)).map key).Pairwise (· ≥ ·) := by
        change ((ds.map (atomId d)).map (atSite i q a)).Pairwise _
        rw [List.map_map,← weights selected d]
        exact dlegal.descending
      have eqrow : ds.map (atomId d) = row i q a := List.Perm.eq_of_pairwise
        (le := fun x y => key y < key x) (fun _ _ _ _ ab ba => (lt_asymm ab ba).elim)
        (strictRows _ (p.trans rawLegal.perm) left) (strictRows _ rawLegal.perm rawLegal.descending) p
      have eqv : reading i q a = v := by
        simpa [direct?,selected,guard,show ((neighbors i.molecule a.val).map (atSite i q a)).Nodup from nd] using hit
      rw [← eqv]
      simpa only [RingTerminalPyramid.reading,reading,show (order (RingTerminalPyramid.weight d) slots).map (atomId d) = row i q a from eqrow] using native
    · simp [direct?,selected,guard,show ¬ ((neighbors i.molecule a.val).map (atSite i q a)).Nodup from nd] at hit

theorem sound {i : Input} {q : Site i} {v : Option Labels}
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (hit : direct? i q = some v) :
    RingChemicalGraphProof.state i q = some v := by
  rw [RingChemicalGraphProof.state_eq]
  exact local_exact (RingChemicalGraphProof.ready ok q) hit
end TetraStereo.Engine.RingPyramidalPathDecision
assert_kernel_only TetraStereo.Engine.RingPyramidalPathDecision.local_exact
assert_kernel_only TetraStereo.Engine.RingPyramidalPathDecision.sound
