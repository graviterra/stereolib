import TetraStereo.OneCenter.DeclarativeCIPOrdinaryCanonicalAddressing
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

open scoped Classical

universe u

open Certificate.CanonicalSphereKey (Key assemble sortDesc keyObservation slotOf WellShaped pad
  pathObservationOf)
open RootedDigraph



















section

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (graph : RootedDigraph Atom) (evidence : StereochemicalEvidence graph)

local instance stereoPathNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Observation of the stereochemical component of `rule` at relative address `path` below
`node`. -/
def stereoNodePathObservation (W D : ℕ) (rule : StereochemicalRule) (node : graph.Node)
    (path : List ℕ) : WithBot StereoLabel :=
  pathObservationOf W D
    ((ofLex (ordinaryKey molecule graph evidence W D node)).2.getD (stereoIndex rule) []) path

theorem stereoNodePathObservation_nil (W D : ℕ) (rule : StereochemicalRule) (node : graph.Node) :
    stereoNodePathObservation molecule graph evidence W D rule node [] =
      (stereoLabel graph evidence rule node : WithBot StereoLabel) := by
  unfold stereoNodePathObservation pathObservationOf
  rw [if_pos ⟨by simp, by simp⟩, ordinaryKey_stereo_getD]
  simp [keyObservation, stereoComponent, assemble, slotOf]

/-- The observation one sphere further out is read from the ranked child in that slot. -/
theorem stereoNodePathObservation_cons (W D : ℕ) (rule : StereochemicalRule) (node : graph.Node)
    {ranked : List graph.Node} (hperm : ranked.Perm (graph.childList node))
    (hsorted : (ranked.map (ordinaryKey molecule graph evidence W D)).Pairwise fun x y => y ≤ x)
    (digit : ℕ) (path : List ℕ) :
    stereoNodePathObservation molecule graph evidence W D rule node (digit :: path) =
      if digit < W ∧ path.length < D then
        ((ranked[digit]?).map fun child =>
          stereoNodePathObservation molecule graph evidence W D rule child path).getD ⊥
      else ⊥ := by
  have hrank : rankedOrdinaryKeys molecule graph evidence W D node =
      ranked.map (ordinaryKey molecule graph evidence W D) := by
    unfold rankedOrdinaryKeys
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
      (hperm.symm.map (ordinaryKey molecule graph evidence W D))]
    exact Certificate.CanonicalSphereKey.sortDesc_of_pairwise hsorted
  have hkeys : ∀ key ∈ (ranked.map (ordinaryKey molecule graph evidence W D)).map
      (fun key => (ofLex key).2.getD (stereoIndex rule) []), WellShaped W D key := by
    intro key hkey
    obtain ⟨vector, hvector, rfl⟩ := List.mem_map.1 hkey
    obtain ⟨child, _, rfl⟩ := List.mem_map.1 hvector
    exact ordinaryKey_stereo_wellShaped molecule graph evidence W D rule child
  by_cases hguard : digit < W ∧ path.length < D
  · rw [if_pos hguard]
    obtain ⟨hs, hpl⟩ := hguard
    by_cases hpath : ∀ i ∈ path, i < W
    · have hbound := Certificate.CanonicalSphereKey.slotOf_lt hpath
      have houter : (∀ i ∈ digit :: path, i < W) ∧ (digit :: path).length ≤ D :=
        ⟨by simpa [hs] using hpath, by simp; omega⟩
      unfold stereoNodePathObservation pathObservationOf
      rw [if_pos houter, ordinaryKey_stereo_getD, hrank]
      simp only [keyObservation, stereoComponent, assemble, List.length_cons, slotOf,
        List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
        List.getElem?_range hpl, Option.map_some, Option.getD_some,
        Certificate.CanonicalSphereKey.getD_flatMap_range _ _ W
          (fun i _ => Certificate.CanonicalSphereKey.slotLevel_length hkeys hpl i) hs hbound]
      cases hchild : ranked[digit]? with
      | none =>
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hchild, Option.map_none,
            Option.getD_none, List.getElem?_nil, pad, List.getElem?_replicate]
          split <;> rfl
      | some child =>
          simp only [Option.map_some, Option.getD_some]
          rw [if_pos ⟨hpath, by omega⟩]
          have hk : path.length <
              ((ofLex (ordinaryKey molecule graph evidence W D child)).2.getD
                (stereoIndex rule) []).length := by
            have h := (ordinaryKey_stereo_wellShaped molecule graph evidence W D rule child).1
            rw [h]
            omega
          rw [List.getD_eq_getElem?_getD] at hk
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hchild, Option.map_some,
            Option.getD_some, List.getElem?_eq_getElem hk, Option.getD_some]
    · have houter : ¬ ((∀ i ∈ digit :: path, i < W) ∧ (digit :: path).length ≤ D) :=
        fun h => hpath fun i hi => h.1 i (by simp [hi])
      unfold stereoNodePathObservation pathObservationOf
      rw [if_neg houter]
      cases ranked[digit]? with
      | none => rfl
      | some child =>
          simp only [Option.map_some, Option.getD_some]
          rw [if_neg fun h => hpath h.1]
  · rw [if_neg hguard]
    unfold stereoNodePathObservation pathObservationOf
    rw [if_neg]
    rintro ⟨hdigits, hlength⟩
    exact hguard ⟨hdigits digit (by simp), by simp at hlength; omega⟩

end

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoNodePathObservation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoNodePathObservation_nil
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoNodePathObservation_cons
