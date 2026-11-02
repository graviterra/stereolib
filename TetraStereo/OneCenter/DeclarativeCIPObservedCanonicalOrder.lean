import TetraStereo.OneCenter.DeclarativeCIPContextualConstitutional
import TetraStereo.OneCenter.DeclarativeCIPCanonicalOrder
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

open Certificate.CanonicalSphereKey
  (Key assemble keyObservation slotOf WellShaped pad pathObservationOf AddressBefore
    VectorWellShaped sortDesc)

noncomputable section
open scoped Classical

universe u
variable {Atom : Type u}

section ObservedOrder

variable [Fintype Atom] [DecidableEq Atom]
  (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)

local instance observedOrderNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- A generic observation path through the observer-parametric rule-major vector key. -/
def nodePathObservationWithObservations (W D r : ℕ) (node : graph.Node)
    (path : List ℕ) : WithBot ℤ :=
  pathObservationOf W D
    ((ruleKeyWithObservations graph W D observe node).getD r []) path

omit [Fintype Atom] [DecidableEq Atom] in
theorem ruleKeyWithObservations_length (W D : ℕ) (node : graph.Node) :
    (ruleKeyWithObservations graph W D observe node).length = 3 := by
  rw [ruleKeyWithObservations_eq]
  rfl

omit [Fintype Atom] [DecidableEq Atom] in
theorem ruleKeyWithObservations_getD_of_index {W D r : ℕ} (hr : r < 3)
    (node : graph.Node) :
    (ruleKeyWithObservations graph W D observe node).getD r [] =
      ruleComponentWithObservations graph W D observe (ruleOfIndex r) node
        (sortDesc ((graph.childList node).map
          (ruleKeyWithObservations graph W D observe))) := by
  rw [← ruleKeyWithObservations_getD, ruleIndex_ruleOfIndex hr]

omit [Fintype Atom] [DecidableEq Atom] in
theorem ruleKeyWithObservations_getD_of_three_le {W D r : ℕ} (hr : 3 ≤ r)
    (node : graph.Node) :
    (ruleKeyWithObservations graph W D observe node).getD r [] = [] := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [ruleKeyWithObservations_length]; exact hr)]
  rfl

omit [Fintype Atom] [DecidableEq Atom] in
theorem ruleKeyWithObservations_vectorWellShaped (W D : ℕ) (node : graph.Node) :
    VectorWellShaped 3 W D (ruleKeyWithObservations graph W D observe node) := by
  refine ⟨ruleKeyWithObservations_length graph observe W D node, fun r hr => ?_⟩
  have h := ruleKeyWithObservations_wellShaped graph W D observe (ruleOfIndex r) node
  rwa [ruleIndex_ruleOfIndex hr] at h

omit [Fintype Atom] [DecidableEq Atom] in
theorem nodePathObservationWithObservations_of_three_le {W D r : ℕ}
    (hr : 3 ≤ r) (node : graph.Node) (path : List ℕ) :
    nodePathObservationWithObservations graph observe W D r node path = ⊥ := by
  unfold nodePathObservationWithObservations pathObservationOf
  rw [ruleKeyWithObservations_getD_of_three_le graph observe hr]
  split <;> simp [keyObservation]

omit [Fintype Atom] [DecidableEq Atom] in
theorem nodePathObservationWithObservations_nil {W D r : ℕ} (hr : r < 3)
    (node : graph.Node) :
    nodePathObservationWithObservations graph observe W D r node [] =
      (observe (ruleOfIndex r) node : WithBot ℤ) := by
  unfold nodePathObservationWithObservations pathObservationOf
  rw [if_pos ⟨by simp, by simp⟩,
    ruleKeyWithObservations_getD_of_index graph observe hr]
  simp [keyObservation, ruleComponentWithObservations, assemble, slotOf]

/-- Children sorted by the generic vector key. -/
def sortedChildrenWithObservations (W D : ℕ) (node : graph.Node) : List graph.Node :=
  (graph.childList node).insertionSort
    (KeyDesc (ruleKeyWithObservations graph W D observe))

omit [Fintype Atom] [DecidableEq Atom] in
theorem sortedChildrenWithObservations_perm (W D : ℕ) (node : graph.Node) :
    (sortedChildrenWithObservations graph observe W D node).Perm (graph.childList node) :=
  List.perm_insertionSort _ _

omit [Fintype Atom] [DecidableEq Atom] in
theorem sortedChildrenWithObservations_pairwise (W D : ℕ) (node : graph.Node) :
    ((sortedChildrenWithObservations graph observe W D node).map
      (ruleKeyWithObservations graph W D observe)).Pairwise fun x y => y ≤ x := by
  rw [List.pairwise_map]
  exact List.pairwise_insertionSort
    (KeyDesc (ruleKeyWithObservations graph W D observe)) _

omit [Fintype Atom] [DecidableEq Atom] in
/-- One generic observation sphere further out is read from the ranked child in that slot. -/
theorem nodePathObservationWithObservations_cons {W D r : ℕ} (hr : r < 3)
    (node : graph.Node) {ranked : List graph.Node}
    (hperm : ranked.Perm (graph.childList node))
    (hsorted : (ranked.map (ruleKeyWithObservations graph W D observe)).Pairwise
      fun x y => y ≤ x) (digit : ℕ) (path : List ℕ) :
    nodePathObservationWithObservations graph observe W D r node (digit :: path) =
      if digit < W ∧ path.length < D then
        ((ranked[digit]?).map fun child =>
          nodePathObservationWithObservations graph observe W D r child path).getD ⊥
      else ⊥ := by
  have hrank : sortDesc ((graph.childList node).map
      (ruleKeyWithObservations graph W D observe)) =
      ranked.map (ruleKeyWithObservations graph W D observe) := by
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
      (hperm.symm.map (ruleKeyWithObservations graph W D observe))]
    exact Certificate.CanonicalSphereKey.sortDesc_of_pairwise hsorted
  have hkeys : ∀ key ∈ (ranked.map (ruleKeyWithObservations graph W D observe)).map
      (fun key => key.getD (ruleIndex (ruleOfIndex r)) []), WellShaped W D key := by
    intro key hkey
    obtain ⟨vector, hvector, rfl⟩ := List.mem_map.1 hkey
    obtain ⟨child, _, rfl⟩ := List.mem_map.1 hvector
    exact ruleKeyWithObservations_wellShaped graph W D observe _ child
  by_cases hguard : digit < W ∧ path.length < D
  · rw [if_pos hguard]
    obtain ⟨hs, hpl⟩ := hguard
    by_cases hpath : ∀ i ∈ path, i < W
    · have hbound := Certificate.CanonicalSphereKey.slotOf_lt hpath
      have houter : (∀ i ∈ digit :: path, i < W) ∧ (digit :: path).length ≤ D :=
        ⟨by simpa [hs] using hpath, by simp; omega⟩
      unfold nodePathObservationWithObservations pathObservationOf
      rw [if_pos houter, ruleKeyWithObservations_getD_of_index graph observe hr, hrank]
      simp only [keyObservation, ruleComponentWithObservations, assemble,
        List.length_cons, slotOf, List.getD_cons_succ]
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
          rw [if_pos ⟨hpath, by omega⟩,
            ruleKeyWithObservations_getD_of_index graph observe hr]
          have hk : path.length <
              (ruleComponentWithObservations graph W D observe (ruleOfIndex r) child
                (sortDesc ((graph.childList child).map
                  (ruleKeyWithObservations graph W D observe)))).length := by
            have h := (ruleKeyWithObservations_wellShaped graph W D observe
              (ruleOfIndex r) child).1
            rw [ruleKeyWithObservations_getD] at h
            rw [h]
            omega
          have hcomp :
              (ruleKeyWithObservations graph W D observe child)[ruleIndex (ruleOfIndex r)]?.getD [] =
                ruleComponentWithObservations graph W D observe (ruleOfIndex r) child
                  (sortDesc ((graph.childList child).map
                    (ruleKeyWithObservations graph W D observe))) := by
            rw [← List.getD_eq_getElem?_getD]
            exact ruleKeyWithObservations_getD graph W D observe _ child
          simp [List.getD_eq_getElem?_getD, List.getElem?_map, hchild, hcomp,
            List.getElem?_eq_getElem hk]
    · have houter : ¬ ((∀ i ∈ digit :: path, i < W) ∧ (digit :: path).length ≤ D) :=
        fun h => hpath fun i hi => h.1 i (by simp [hi])
      unfold nodePathObservationWithObservations pathObservationOf
      rw [if_neg houter]
      cases ranked[digit]? with
      | none => rfl
      | some child =>
          simp only [Option.map_some, Option.getD_some]
          rw [if_neg fun h => hpath h.1]
  · rw [if_neg hguard]
    unfold nodePathObservationWithObservations pathObservationOf
    rw [if_neg]
    rintro ⟨hdigits, hlength⟩
    exact hguard ⟨hdigits digit (by simp), by simp at hlength; omega⟩

omit [Fintype Atom] [DecidableEq Atom] in
/-- A non-bottom generic observation lies inside the hierarchy. -/
theorem depth_add_length_le_of_nodePathObservationWithObservations {W D r : ℕ}
    (hr : r < 3) :
    ∀ (path : List ℕ) (node : graph.Node),
      nodePathObservationWithObservations graph observe W D r node path ≠ ⊥ →
        graph.depth node + path.length ≤ graph.height
  | [], node, _ => by simpa using graph.depth_le_height node
  | digit :: path, node, hne => by
      rw [nodePathObservationWithObservations_cons graph observe hr node
        (sortedChildrenWithObservations_perm graph observe W D node)
        (sortedChildrenWithObservations_pairwise graph observe W D node)] at hne
      split at hne
      · cases hchild : (sortedChildrenWithObservations graph observe W D node)[digit]? with
        | none => simp [hchild] at hne
        | some child =>
            simp only [hchild, Option.map_some, Option.getD_some] at hne
            have hmem : child ∈ graph.childList node :=
              (sortedChildrenWithObservations_perm graph observe W D node).subset
                (List.mem_of_getElem? hchild)
            have hdepth := graph.child_depth ((graph.mem_childList).1 hmem)
            have ih := depth_add_length_le_of_nodePathObservationWithObservations
              hr path child hne
            simp only [List.length_cons]
            omega
      · exact (hne rfl).elim

end ObservedOrder

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKeyWithObservations_vectorWellShaped
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.nodePathObservationWithObservations_nil
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.nodePathObservationWithObservations_cons
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.depth_add_length_le_of_nodePathObservationWithObservations
