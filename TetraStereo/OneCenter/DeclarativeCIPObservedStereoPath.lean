import TetraStereo.OneCenter.DeclarativeCIPObservedOrdinaryKey
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section
open scoped Classical
universe u

open Certificate.CanonicalSphereKey
  (pathObservationOf keyObservation assemble slotOf pad)

section ObservedStereoPath

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)
  (evidence : StereochemicalEvidence graph)

local instance observedStereoPathNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Stereochemical component observations in the ordinary key whose constitutional columns
use an independently supplied observer. -/
def observedStereoNodePathObservation (W D : ℕ) (rule : StereochemicalRule)
    (node : graph.Node) (path : List ℕ) : WithBot StereoLabel :=
  pathObservationOf W D
    ((ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD
      (stereoIndex rule) []) path

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedStereoNodePathObservation_nil (W D : ℕ) (rule : StereochemicalRule)
    (node : graph.Node) :
    observedStereoNodePathObservation graph observe evidence W D rule node [] =
      (stereoLabel graph evidence rule node : WithBot StereoLabel) := by
  unfold observedStereoNodePathObservation pathObservationOf
  rw [if_pos ⟨by simp, by simp⟩, ordinaryKeyWithObservations_stereo_getD]
  simp [keyObservation, stereoComponent, assemble, slotOf]

omit [Fintype Atom] [DecidableEq Atom] in
/-- One sphere further out is read from the sorted child at that slot. -/
theorem observedStereoNodePathObservation_cons (W D : ℕ)
    (rule : StereochemicalRule) (node : graph.Node) {ranked : List graph.Node}
    (hperm : ranked.Perm (graph.childList node))
    (hsorted : (ranked.map (ordinaryKeyWithObservations graph observe evidence W D)).Pairwise
      fun x y => y ≤ x) (digit : ℕ) (path : List ℕ) :
    observedStereoNodePathObservation graph observe evidence W D rule node
        (digit :: path) =
      if digit < W ∧ path.length < D then
        ((ranked[digit]?).map fun child =>
          observedStereoNodePathObservation graph observe evidence W D rule child path).getD ⊥
      else ⊥ := by
  have hrank : rankedOrdinaryKeysWithObservations graph observe evidence W D node =
      ranked.map (ordinaryKeyWithObservations graph observe evidence W D) := by
    unfold rankedOrdinaryKeysWithObservations
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
      (hperm.symm.map (ordinaryKeyWithObservations graph observe evidence W D))]
    exact Certificate.CanonicalSphereKey.sortDesc_of_pairwise hsorted
  have hkeys : ∀ key ∈ (ranked.map
      (ordinaryKeyWithObservations graph observe evidence W D)).map
      (fun key => (ofLex key).2.getD (stereoIndex rule) []),
      Certificate.CanonicalSphereKey.WellShaped W D key := by
    intro key hkey
    obtain ⟨vector, hvector, rfl⟩ := List.mem_map.1 hkey
    obtain ⟨child, _, rfl⟩ := List.mem_map.1 hvector
    exact ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D rule child
  by_cases hguard : digit < W ∧ path.length < D
  · rw [if_pos hguard]
    obtain ⟨hs, hpl⟩ := hguard
    by_cases hpath : ∀ i ∈ path, i < W
    · have hbound := Certificate.CanonicalSphereKey.slotOf_lt hpath
      have houter : (∀ i ∈ digit :: path, i < W) ∧ (digit :: path).length ≤ D :=
        ⟨by simpa [hs] using hpath, by simp; omega⟩
      unfold observedStereoNodePathObservation pathObservationOf
      rw [if_pos houter, ordinaryKeyWithObservations_stereo_getD, hrank]
      simp only [keyObservation, stereoComponent, assemble, List.length_cons, slotOf,
        List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
        List.getElem?_range hpl, Option.map_some, Option.getD_some,
        Certificate.CanonicalSphereKey.getD_flatMap_range _ _ W
          (fun i _ => Certificate.CanonicalSphereKey.slotLevel_length hkeys hpl i) hs hbound]
      cases hchild : ranked[digit]? with
      | none =>
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hchild,
            Option.map_none, Option.getD_none, List.getElem?_nil, pad,
            List.getElem?_replicate]
          split <;> rfl
      | some child =>
          simp only [Option.map_some, Option.getD_some]
          rw [if_pos ⟨hpath, by omega⟩]
          have hk : path.length < ((ofLex
              (ordinaryKeyWithObservations graph observe evidence W D child)).2.getD
                (stereoIndex rule) []).length := by
            have h := (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence
              W D rule child).1
            rw [h]
            omega
          rw [List.getD_eq_getElem?_getD] at hk
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hchild,
            Option.map_some, Option.getD_some, List.getElem?_eq_getElem hk, Option.getD_some]
    · have houter : ¬ ((∀ i ∈ digit :: path, i < W) ∧ (digit :: path).length ≤ D) :=
        fun h => hpath fun i hi => h.1 i (by simp [hi])
      unfold observedStereoNodePathObservation pathObservationOf
      rw [if_neg houter]
      cases ranked[digit]? with
      | none => rfl
      | some child =>
          simp only [Option.map_some, Option.getD_some]
          rw [if_neg fun h => hpath h.1]
  · rw [if_neg hguard]
    unfold observedStereoNodePathObservation pathObservationOf
    rw [if_neg]
    rintro ⟨hdigits, hlength⟩
    exact hguard ⟨hdigits digit (by simp), by simp at hlength; omega⟩

end ObservedStereoPath

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedStereoNodePathObservation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedStereoNodePathObservation_nil
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedStereoNodePathObservation_cons
