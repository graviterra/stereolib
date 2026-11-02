import TetraStereo.OneCenter.DeclarativeCIPCanonicalAddressing

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

open Certificate.CanonicalSphereKey (Key assemble sortDesc keyObservation slotOf WellShaped pad
  pathObservationOf AddressBefore VectorWellShaped)

noncomputable section

open scoped Classical

universe u

/-!
# Width independence of the canonical sibling order

`CanonicalAddressing` ranks siblings by `ruleKey W D` with the graph's own width and height as
layout parameters.  This module proves that the induced order does not depend on those parameters:
for all `W, W' ≥ width` and `D, D' ≥ height`, the path observations of `ruleKey W D` and
`ruleKey W' D'` coincide (`nodePathObservation_width_independent`).  Consequently the two keys order
every pair of nodes identically (`ruleKey_le_iff_of_bounds`), and canonicality may be checked with
any sufficiently large layout (`canonicalAddressing_iff_of_bounds`).

The key order is characterized without slots: first by rule component, then by the first
differing observation in shortlex address order (`ruleKey_lt_iff`, `ruleKey_eq_iff`).
-/

variable {Atom : Type u}

/-- The constitutional rule stored at a vector-key component index. -/
def ruleOfIndex : ℕ → ConstitutionalRule
  | 0 => .rule1aAtomicNumber
  | 1 => .rule1bDuplicateNodeProximity
  | _ => .rule2AtomicMass

theorem ruleIndex_ruleOfIndex {r : ℕ} (hr : r < 3) : ruleIndex (ruleOfIndex r) = r := by
  rcases r with _ | _ | _ | r
  · rfl
  · rfl
  · rfl
  · omega

section Order

variable [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (graph : RootedDigraph Atom)

local instance : Fintype graph.Node := graph.nodeFintype

theorem ruleKey_length (W D : ℕ) (node : graph.Node) :
    (ruleKey molecule graph W D node).length = 3 := by
  rw [ruleKey_eq]
  rfl

theorem ruleKey_getD_of_index {W D r : ℕ} (hr : r < 3) (node : graph.Node) :
    (ruleKey molecule graph W D node).getD r [] =
      ruleComponent molecule graph W D (ruleOfIndex r) node
        (sortDesc ((graph.childList node).map (ruleKey molecule graph W D))) := by
  rw [← ruleKey_getD, ruleIndex_ruleOfIndex hr]

theorem ruleKey_getD_of_three_le {W D r : ℕ} (hr : 3 ≤ r) (node : graph.Node) :
    (ruleKey molecule graph W D node).getD r [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [ruleKey_length]; exact hr)]
  rfl

theorem ruleKey_vectorWellShaped (W D : ℕ) (node : graph.Node) :
    VectorWellShaped 3 W D (ruleKey molecule graph W D node) := by
  refine ⟨ruleKey_length molecule graph W D node, fun r hr => ?_⟩
  have h := ruleKey_wellShaped molecule graph W D (ruleOfIndex r) node
  rwa [ruleIndex_ruleOfIndex hr] at h

/-- Observation of vector-key component `r` at relative address `path` below `node`. -/
def nodePathObservation (W D r : ℕ) (node : graph.Node) (path : List ℕ) : WithBot ℤ :=
  pathObservationOf W D ((ruleKey molecule graph W D node).getD r []) path

theorem nodePathObservation_of_three_le {W D r : ℕ} (hr : 3 ≤ r) (node : graph.Node)
    (path : List ℕ) : nodePathObservation molecule graph W D r node path = ⊥ := by
  unfold nodePathObservation pathObservationOf
  rw [ruleKey_getD_of_three_le molecule graph hr]
  split <;> simp [keyObservation]

theorem nodePathObservation_nil {W D r : ℕ} (hr : r < 3) (node : graph.Node) :
    nodePathObservation molecule graph W D r node [] =
      (nodeObservation molecule graph (ruleOfIndex r) node : WithBot ℤ) := by
  unfold nodePathObservation pathObservationOf
  rw [if_pos ⟨by simp, by simp⟩, ruleKey_getD_of_index molecule graph hr]
  simp [keyObservation, ruleComponent, assemble, slotOf]

/-- Children ranked by a layout's vector key. -/
def sortedChildren (W D : ℕ) (node : graph.Node) : List graph.Node :=
  (graph.childList node).insertionSort (KeyDesc (ruleKey molecule graph W D))

theorem sortedChildren_perm (W D : ℕ) (node : graph.Node) :
    (sortedChildren molecule graph W D node).Perm (graph.childList node) :=
  List.perm_insertionSort _ _

theorem sortedChildren_pairwise (W D : ℕ) (node : graph.Node) :
    ((sortedChildren molecule graph W D node).map (ruleKey molecule graph W D)).Pairwise
      fun x y => y ≤ x := by
  rw [List.pairwise_map]
  exact List.pairwise_insertionSort (KeyDesc (ruleKey molecule graph W D)) _

/-- The observation one sphere further out is read from the ranked child in that slot. -/
theorem nodePathObservation_cons {W D r : ℕ} (hr : r < 3) (node : graph.Node)
    {ranked : List graph.Node} (hperm : ranked.Perm (graph.childList node))
    (hsorted : (ranked.map (ruleKey molecule graph W D)).Pairwise fun x y => y ≤ x)
    (digit : ℕ) (path : List ℕ) :
    nodePathObservation molecule graph W D r node (digit :: path) =
      if digit < W ∧ path.length < D then
        ((ranked[digit]?).map fun child =>
          nodePathObservation molecule graph W D r child path).getD ⊥
      else ⊥ := by
  have hrank : sortDesc ((graph.childList node).map (ruleKey molecule graph W D)) =
      ranked.map (ruleKey molecule graph W D) := by
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
      (hperm.symm.map (ruleKey molecule graph W D))]
    exact Certificate.CanonicalSphereKey.sortDesc_of_pairwise hsorted
  have hkeys : ∀ key ∈ (ranked.map (ruleKey molecule graph W D)).map
      (fun key => key.getD (ruleIndex (ruleOfIndex r)) []), WellShaped W D key := by
    intro key hkey
    obtain ⟨vector, hvector, rfl⟩ := List.mem_map.1 hkey
    obtain ⟨child, _, rfl⟩ := List.mem_map.1 hvector
    exact ruleKey_wellShaped molecule graph W D _ child
  by_cases hguard : digit < W ∧ path.length < D
  · rw [if_pos hguard]
    obtain ⟨hs, hpl⟩ := hguard
    by_cases hpath : ∀ i ∈ path, i < W
    · have hbound := Certificate.CanonicalSphereKey.slotOf_lt hpath
      have houter : (∀ i ∈ digit :: path, i < W) ∧ (digit :: path).length ≤ D :=
        ⟨by simpa [hs] using hpath, by simp; omega⟩
      unfold nodePathObservation pathObservationOf
      rw [if_pos houter, ruleKey_getD_of_index molecule graph hr, hrank]
      simp only [keyObservation, ruleComponent, assemble, List.length_cons, slotOf,
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
          rw [if_pos ⟨hpath, by omega⟩, ruleKey_getD_of_index molecule graph hr]
          have hk : path.length < (ruleComponent molecule graph W D (ruleOfIndex r) child
              (sortDesc ((graph.childList child).map (ruleKey molecule graph W D)))).length := by
            have h := (ruleKey_wellShaped molecule graph W D (ruleOfIndex r) child).1
            rw [ruleKey_getD] at h
            rw [h]
            omega
          have hcomp : (ruleKey molecule graph W D child)[ruleIndex (ruleOfIndex r)]?.getD [] =
              ruleComponent molecule graph W D (ruleOfIndex r) child
                (sortDesc ((graph.childList child).map (ruleKey molecule graph W D))) := by
            rw [← List.getD_eq_getElem?_getD]
            exact ruleKey_getD molecule graph W D _ child
          simp [List.getD_eq_getElem?_getD, List.getElem?_map, hchild, hcomp,
            List.getElem?_eq_getElem hk]
    · have houter : ¬ ((∀ i ∈ digit :: path, i < W) ∧ (digit :: path).length ≤ D) :=
        fun h => hpath fun i hi => h.1 i (by simp [hi])
      unfold nodePathObservation pathObservationOf
      rw [if_neg houter]
      cases ranked[digit]? with
      | none => rfl
      | some child =>
          simp only [Option.map_some, Option.getD_some]
          rw [if_neg fun h => hpath h.1]
  · rw [if_neg hguard]
    unfold nodePathObservation pathObservationOf
    rw [if_neg]
    rintro ⟨hdigits, hlength⟩
    exact hguard ⟨hdigits digit (by simp), by simp at hlength; omega⟩

/-- A non-`⊥` observation lies inside the hierarchy. -/
theorem depth_add_length_le_of_nodePathObservation {W D r : ℕ} (hr : r < 3) :
    ∀ (path : List ℕ) (node : graph.Node),
      nodePathObservation molecule graph W D r node path ≠ ⊥ →
        graph.depth node + path.length ≤ graph.height
  | [], node, _ => by simpa using graph.depth_le_height node
  | digit :: path, node, hne => by
      rw [nodePathObservation_cons molecule graph hr node (sortedChildren_perm molecule graph W D node)
        (sortedChildren_pairwise molecule graph W D node)] at hne
      split at hne
      · cases hchild : (sortedChildren molecule graph W D node)[digit]? with
        | none => simp [hchild] at hne
        | some child =>
            simp only [hchild, Option.map_some, Option.getD_some] at hne
            have hmem : child ∈ graph.childList node :=
              (sortedChildren_perm molecule graph W D node).subset (List.mem_of_getElem? hchild)
            have hdepth := graph.child_depth ((graph.mem_childList).1 hmem)
            have ih := depth_add_length_le_of_nodePathObservation hr path child hne
            simp only [List.length_cons]
            omega
      · exact (hne rfl).elim

/-- Vector-key order is the first difference of path observations: by rule component, then by
shortlex address order. -/
theorem ruleKey_lt_iff (W D : ℕ) (left right : graph.Node) :
    ruleKey molecule graph W D left < ruleKey molecule graph W D right ↔ ∃ r < 3, ∃ path,
      nodePathObservation molecule graph W D r left path <
          nodePathObservation molecule graph W D r right path ∧
        (∀ r' < r, ∀ path', nodePathObservation molecule graph W D r' left path' =
          nodePathObservation molecule graph W D r' right path') ∧
        ∀ earlier, AddressBefore earlier path →
          nodePathObservation molecule graph W D r left earlier =
            nodePathObservation molecule graph W D r right earlier :=
  Certificate.CanonicalSphereKey.vector_lt_iff_pathObservation
    (ruleKey_vectorWellShaped molecule graph W D left)
    (ruleKey_vectorWellShaped molecule graph W D right)

theorem ruleKey_eq_iff (W D : ℕ) (left right : graph.Node) :
    ruleKey molecule graph W D left = ruleKey molecule graph W D right ↔ ∀ r < 3, ∀ path,
      nodePathObservation molecule graph W D r left path =
        nodePathObservation molecule graph W D r right path :=
  Certificate.CanonicalSphereKey.vector_eq_iff_pathObservation
    (ruleKey_vectorWellShaped molecule graph W D left)
    (ruleKey_vectorWellShaped molecule graph W D right)

/-- Two layouts with identical path observations order nodes identically. -/
theorem ruleKey_le_iff_of_observations {W D W' D' : ℕ} {left right : graph.Node}
    (hleft : ∀ r path, nodePathObservation molecule graph W D r left path =
      nodePathObservation molecule graph W' D' r left path)
    (hright : ∀ r path, nodePathObservation molecule graph W D r right path =
      nodePathObservation molecule graph W' D' r right path) :
    ruleKey molecule graph W D left ≤ ruleKey molecule graph W D right ↔
      ruleKey molecule graph W' D' left ≤ ruleKey molecule graph W' D' right := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, ruleKey_lt_iff, ruleKey_lt_iff, ruleKey_eq_iff,
    ruleKey_eq_iff]
  simp only [hleft, hright]

/-- **Width independence.**  Path observations do not depend on the layout parameters, provided
they bound the hierarchy's width and height. -/
theorem nodePathObservation_width_independent {W D W' D' : ℕ}
    (hW : graph.width ≤ W) (hW' : graph.width ≤ W') (hD : graph.height ≤ D)
    (hD' : graph.height ≤ D') :
    ∀ node r path, nodePathObservation molecule graph W D r node path =
      nodePathObservation molecule graph W' D' r node path := by
  intro node
  refine node_induction graph (motive := fun node => ∀ r path,
    nodePathObservation molecule graph W D r node path =
      nodePathObservation molecule graph W' D' r node path) ?_ node
  intro node ih r path
  by_cases hr : r < 3
  · cases path with
    | nil => rw [nodePathObservation_nil molecule graph hr, nodePathObservation_nil molecule graph hr]
    | cons digit path =>
        have horder : ∀ a ∈ graph.childList node, ∀ b ∈ graph.childList node,
            (ruleKey molecule graph W D a ≤ ruleKey molecule graph W D b ↔
              ruleKey molecule graph W' D' a ≤ ruleKey molecule graph W' D' b) :=
          fun a ha b hb => ruleKey_le_iff_of_observations molecule graph
            (ih a ((graph.mem_childList).1 ha)) (ih b ((graph.mem_childList).1 hb))
        let ranked := sortedChildren molecule graph W D node
        have hperm := sortedChildren_perm molecule graph W D node
        have hsorted := sortedChildren_pairwise molecule graph W D node
        have hsorted' : (ranked.map (ruleKey molecule graph W' D')).Pairwise
            fun x y => y ≤ x := by
          rw [List.pairwise_map] at hsorted ⊢
          exact hsorted.imp_of_mem fun ha hb h =>
            (horder _ (hperm.subset hb) _ (hperm.subset ha)).1 h
        rw [nodePathObservation_cons molecule graph hr node hperm hsorted,
          nodePathObservation_cons molecule graph hr node hperm hsorted']
        cases hchild : ranked[digit]? with
        | none => simp
        | some child =>
            have hlt : digit < ranked.length := (List.getElem?_eq_some_iff.1 hchild).1
            have hlen : ranked.length ≤ graph.width := by
              rw [hperm.length_eq]
              exact (graph.childList_nodup node).length_le_card
            have hmem : child ∈ graph.childList node := hperm.subset (List.mem_of_getElem? hchild)
            have hedge := (graph.mem_childList).1 hmem
            have hdepth := graph.child_depth hedge
            have hbound : ∀ {W₀ D₀ : ℕ}, nodePathObservation molecule graph W₀ D₀ r child path ≠ ⊥ →
                path.length < graph.height := by
              intro W₀ D₀ hne
              have := depth_add_length_le_of_nodePathObservation molecule graph hr path child hne
              omega
            simp only [Option.map_some, Option.getD_some]
            by_cases hl : path.length < D <;> by_cases hl' : path.length < D'
            · rw [if_pos ⟨by omega, hl⟩, if_pos ⟨by omega, hl'⟩]
              exact ih child hedge r path
            · rw [if_pos ⟨by omega, hl⟩, if_neg (fun h => hl' h.2)]
              by_contra hne
              have := hbound hne
              omega
            · rw [if_neg (fun h => hl h.2), if_pos ⟨by omega, hl'⟩]
              by_contra hne
              have := hbound (Ne.symm hne)
              omega
            · rw [if_neg (fun h => hl h.2), if_neg (fun h => hl' h.2)]
  · rw [nodePathObservation_of_three_le molecule graph (by omega),
      nodePathObservation_of_three_le molecule graph (by omega)]

/-- Sufficiently large layouts order every pair of nodes identically. -/
theorem ruleKey_le_iff_of_bounds {W D W' D' : ℕ}
    (hW : graph.width ≤ W) (hW' : graph.width ≤ W') (hD : graph.height ≤ D)
    (hD' : graph.height ≤ D') (left right : graph.Node) :
    ruleKey molecule graph W D left ≤ ruleKey molecule graph W D right ↔
      ruleKey molecule graph W' D' left ≤ ruleKey molecule graph W' D' right :=
  ruleKey_le_iff_of_observations molecule graph
    (nodePathObservation_width_independent molecule graph hW hW' hD hD' left)
    (nodePathObservation_width_independent molecule graph hW hW' hD hD' right)

/-- Canonicality may be checked with any layout bounding the hierarchy. -/
theorem canonicalAddressing_iff_of_bounds {W D : ℕ} (hW : graph.width ≤ W)
    (hD : graph.height ≤ D) (addressing : graph.Addressing) :
    CanonicalAddressing molecule addressing ↔
      Dense addressing ∧ KeySorted (ruleKey molecule graph W D) addressing := by
  unfold CanonicalAddressing KeySorted
  apply and_congr Iff.rfl
  apply forall_congr'; intro parent
  apply forall_congr'; intro first
  apply forall_congr'; intro second
  apply forall_congr'; intro firstSlot
  apply forall_congr'; intro secondSlot
  rw [ruleKey_le_iff_of_bounds molecule graph le_rfl hW le_rfl hD]

end Order

end
end DeclarativeCIP
end OneCenter
end TetraStereo
