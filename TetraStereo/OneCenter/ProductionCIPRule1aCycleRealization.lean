import TetraStereo.OneCenter.ProductionCIPRule1aCycleClassification

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace RawMolecule

/-- Directed consecutive edges of a vertex-simple path contain no repeated record. -/
theorem orderedPathEdges_nodup : ∀ {vertices : List ℕ},
    vertices.Nodup → (orderedPathEdges vertices).Nodup
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: rest, hnodup => by
      rw [orderedPathEdges_cons_cons, List.nodup_cons]
      have hparts := List.nodup_cons.mp hnodup
      constructor
      · intro hmem
        have hendpoints := endpoints_mem_of_mem_orderedPathEdges hmem
        exact hparts.1 (by simpa using hendpoints.1)
      · exact orderedPathEdges_nodup (List.nodup_cons.mp hnodup).2
termination_by vertices => vertices.length

/-- A vertex-simple directed path never contains the reverse of one of its own edges. -/
theorem reverse_not_mem_orderedPathEdges : ∀ {vertices : List ℕ} {edge : ℕ × ℕ},
    vertices.Nodup → edge ∈ orderedPathEdges vertices →
      (edge.2, edge.1) ∉ orderedPathEdges vertices
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | a :: b :: rest, edge, hnodup, hedge => by
      have hparts := List.nodup_cons.mp hnodup
      simp only [orderedPathEdges_cons_cons, List.mem_cons] at hedge ⊢
      rcases hedge with rfl | htail
      · rintro (hreverse | hreverse)
        ·
          have hab : a ≠ b := fun h => hparts.1 (by simp [h])
          exact hab (congrArg Prod.fst hreverse).symm
        ·
          have hendpoints := endpoints_mem_of_mem_orderedPathEdges hreverse
          exact hparts.1 (by simpa using hendpoints.2)
      · rintro (hreverse | hreverse)
        ·
          have hendpoints := endpoints_mem_of_mem_orderedPathEdges htail
          have ha : edge.2 = a := congrArg Prod.fst hreverse
          exact hparts.1 (by simpa [ha] using hendpoints.2)
        · exact reverse_not_mem_orderedPathEdges hparts.2 htail hreverse
termination_by vertices => vertices.length

/-- Every directed path edge has distinct endpoints when the vertex list is duplicate-free. -/
theorem orderedPathEdges_noSelf : ∀ {vertices : List ℕ},
    vertices.Nodup → ∀ edge ∈ orderedPathEdges vertices, edge.1 ≠ edge.2
  | [], _, edge, h => by simp at h
  | [_], _, edge, h => by simp at h
  | a :: b :: rest, hnodup, edge, hedge => by
      have hparts := List.nodup_cons.mp hnodup
      simp only [orderedPathEdges_cons_cons, List.mem_cons] at hedge
      rcases hedge with rfl | htail
      · intro hab
        change a = b at hab
        exact hparts.1 (by simp only [List.mem_cons]; exact Or.inl hab)
      · exact orderedPathEdges_noSelf hparts.2 edge htail
termination_by vertices => vertices.length

/-- Undirected edge identity is functional in a vertex-simple directed path. -/
theorem orderedPathEdges_undirectedUnique {vertices : List ℕ}
    (hnodup : vertices.Nodup) : ∀ first ∈ orderedPathEdges vertices,
      ∀ second ∈ orderedPathEdges vertices,
      (first = second ∨ first = (second.2, second.1)) → first = second := by
  intro first hfirst second hsecond heq
  rcases heq with heq | hreverse
  · exact heq
  · exfalso
    exact reverse_not_mem_orderedPathEdges hnodup hsecond (by simpa [hreverse] using hfirst)

private theorem zip_path_append_closing (close a b z : ℕ) : ∀ rest : List ℕ,
    (a :: b :: (rest ++ [z])).zip (b :: (rest ++ [z, close])) =
      orderedPathEdges (a :: b :: (rest ++ [z])) ++ [(z, close)]
  | [] => by simp [orderedPathEdges]
  | c :: rest => by
      rw [List.zip_cons_cons, orderedPathEdges_cons_cons]
      congr 1
      exact zip_path_append_closing close b c z rest

/-- The production `cycleEdges` list is the directed path plus its final closing edge. -/
theorem cycleEdges_eq_orderedPathEdges_append_closing
    (a b z : ℕ) (rest : List ℕ) :
    cycleEdges (a :: b :: (rest ++ [z])) =
      orderedPathEdges (a :: b :: (rest ++ [z])) ++ [(z, a)] := by
  unfold cycleEdges
  simp only [List.drop]
  simpa [List.append_assoc] using zip_path_append_closing a a b z rest

/-- Moving the closing edge to the front and reversing its orientation preserves undirected
membership exactly. -/
theorem containsUndirectedEdge_closingFirstCycleEdges_iff
    (a b z : ℕ) (rest : List ℕ) (left right : ℕ) :
    containsUndirectedEdge (closingFirstCycleEdges a (b :: rest) z) left right = true ↔
      containsUndirectedEdge (cycleEdges (a :: b :: (rest ++ [z]))) left right = true := by
  rw [cycleEdges_eq_orderedPathEdges_append_closing]
  simp only [closingFirstCycleEdges, containsUndirectedEdge, List.any_cons,
    List.any_append]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  tauto

/-- The closing edge is absent, in either orientation, from the open path around a simple cycle. -/
theorem closing_edge_not_mem_orderedPathEdges
    (a b z : ℕ) (rest : List ℕ)
    (hnodup : (a :: b :: (rest ++ [z])).Nodup) :
    (a, z) ∉ orderedPathEdges (a :: b :: (rest ++ [z])) ∧
      (z, a) ∉ orderedPathEdges (a :: b :: (rest ++ [z])) := by
  have hparts := List.nodup_cons.mp hnodup
  simp only [orderedPathEdges_cons_cons, List.mem_cons]
  constructor
  · rintro (heq | htail)
    · have hbz : b = z := (congrArg Prod.snd heq).symm
      exact (List.nodup_cons.mp hparts.2).1 (by simp [hbz])
    · have hendpoints := endpoints_mem_of_mem_orderedPathEdges htail
      exact hparts.1 (by simpa using hendpoints.1)
  · rintro (heq | htail)
    · have hza : z = a := congrArg Prod.fst heq
      exact hparts.1 (by simp [hza])
    · have hendpoints := endpoints_mem_of_mem_orderedPathEdges htail
      exact hparts.1 (by simpa using hendpoints.2)

/-- The reordered closing-first cycle list has all occurrence and orientation uniqueness required
by the independent matching bridge. -/
theorem closingFirstCycleEdges_nodup
    (a b z : ℕ) (rest : List ℕ)
    (hnodup : (a :: b :: (rest ++ [z])).Nodup) :
    (closingFirstCycleEdges a (b :: rest) z).Nodup := by
  rw [closingFirstCycleEdges, List.nodup_cons]
  exact ⟨(closing_edge_not_mem_orderedPathEdges a b z rest hnodup).1,
    orderedPathEdges_nodup hnodup⟩

theorem closingFirstCycleEdges_noSelf
    (a b z : ℕ) (rest : List ℕ)
    (hnodup : (a :: b :: (rest ++ [z])).Nodup) :
    ∀ edge ∈ closingFirstCycleEdges a (b :: rest) z, edge.1 ≠ edge.2 := by
  intro edge hedge
  simp only [closingFirstCycleEdges, List.mem_cons] at hedge
  rcases hedge with rfl | hpath
  · intro haz
    have haza : a = z := haz
    exact (List.nodup_cons.mp hnodup).1 (by simp [haza])
  · exact orderedPathEdges_noSelf hnodup edge hpath

theorem closingFirstCycleEdges_undirectedUnique
    (a b z : ℕ) (rest : List ℕ)
    (hnodup : (a :: b :: (rest ++ [z])).Nodup) :
    ∀ first ∈ closingFirstCycleEdges a (b :: rest) z,
      ∀ second ∈ closingFirstCycleEdges a (b :: rest) z,
      (first = second ∨ first = (second.2, second.1)) → first = second := by
  intro first hfirst second hsecond heq
  simp only [closingFirstCycleEdges, List.mem_cons] at hfirst hsecond
  rcases hfirst with rfl | hfirst <;> rcases hsecond with rfl | hsecond
  · rfl
  · rcases heq with heq | heq
    · rw [← heq] at hsecond
      exact ((closing_edge_not_mem_orderedPathEdges a b z rest hnodup).1 hsecond).elim
    · have hreverse : (z, a) = second := by
        apply Prod.ext
        · exact congrArg Prod.snd heq
        · exact congrArg Prod.fst heq
      rw [← hreverse] at hsecond
      exact ((closing_edge_not_mem_orderedPathEdges a b z rest hnodup).2 hsecond).elim
  · rcases heq with heq | heq
    · rw [heq] at hfirst
      exact ((closing_edge_not_mem_orderedPathEdges a b z rest hnodup).1 hfirst).elim
    · have hreverse : first = (z, a) := heq
      rw [hreverse] at hfirst
      exact ((closing_edge_not_mem_orderedPathEdges a b z rest hnodup).2 hfirst).elim
  · exact orderedPathEdges_undirectedUnique hnodup first hfirst second hsecond heq

private theorem natEdgeMatchedBy_iff_containsUndirectedEdge
    {atomCount : ℕ} (edges : List (ℕ × ℕ)) (left right : Fin atomCount) :
    NatEdgeMatchedBy edges left right ↔
      containsUndirectedEdge edges left.val right.val = true := by
  simp only [NatEdgeMatchedBy, NatEdgeIncident, containsUndirectedEdge,
    List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨edge, hedge, hforward | hreverse⟩
    · exact ⟨edge, hedge, Or.inl ⟨congrArg Prod.fst hforward, congrArg Prod.snd hforward⟩⟩
    · exact ⟨edge, hedge, Or.inr ⟨congrArg Prod.fst hreverse, congrArg Prod.snd hreverse⟩⟩
  · rintro ⟨edge, hedge, hforward | hreverse⟩
    · exact ⟨edge, hedge, Or.inl (Prod.ext hforward.1 hforward.2)⟩
    · exact ⟨edge, hedge, Or.inr (Prod.ext hreverse.1 hreverse.2)⟩

private theorem containsUndirectedEdge_of_mem
    (edges : List (ℕ × ℕ)) (edge : ℕ × ℕ) (hmem : edge ∈ edges) :
    containsUndirectedEdge edges edge.1 edge.2 = true := by
  simp only [containsUndirectedEdge, List.any_eq_true, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  exact ⟨edge, hmem, Or.inl ⟨rfl, rfl⟩⟩

/-- The closed edge list used by the parity recurrence realizes exactly the independent localized
component certified by the recognizer.  This is the occurrence-sensitive bridge: it establishes
bounds, absence of self-edges, unordered uniqueness, and exact semantic membership rather than
merely comparing the final rational output. -/
theorem closingFirstCycleEdges_realization
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (attached duplicated alternate : Fin mol.atomCount) (rest : List ℕ)
    (hexact : mol.SimpleCycleExactComponent attached.val
      (attached.val :: duplicated.val :: (rest ++ [alternate.val])))
    (hnodup : (attached.val :: duplicated.val :: (rest ++ [alternate.val])).Nodup) :
    LocalizedMancudeEdgeListRealization mol attached
      (closingFirstCycleEdges attached.val (duplicated.val :: rest) alternate.val) := by
  let cycle := attached.val :: duplicated.val :: (rest ++ [alternate.val])
  let edges := closingFirstCycleEdges attached.val (duplicated.val :: rest) alternate.val
  let actual := mol.localizedMancudeComponentEdges attached.val
  have hactual := mol.localizedMancudeComponentEdges_realization
    hwellFormed hunique attached
  have hcontainsIff (left right : ℕ) :
      containsUndirectedEdge edges left right = true ↔
        containsUndirectedEdge actual left right = true := by
    calc
      containsUndirectedEdge edges left right = true ↔
          containsUndirectedEdge (cycleEdges cycle) left right = true := by
            exact containsUndirectedEdge_closingFirstCycleEdges_iff
              attached.val duplicated.val alternate.val rest left right
      _ ↔ containsUndirectedEdge actual left right = true := by
        exact hexact.edge_mem_iff left right
  refine
    { nodup := closingFirstCycleEdges_nodup attached.val duplicated.val
        alternate.val rest hnodup
      endpointsInBounds := ?_
      noSelfEdges := closingFirstCycleEdges_noSelf attached.val duplicated.val
        alternate.val rest hnodup
      undirectedUnique := closingFirstCycleEdges_undirectedUnique attached.val
        duplicated.val alternate.val rest hnodup
      localizedComponent_iff := ?_ }
  · intro edge hedge
    have hcontains : containsUndirectedEdge actual edge.1 edge.2 = true :=
      (hcontainsIff edge.1 edge.2).1 (containsUndirectedEdge_of_mem edges edge hedge)
    simp only [containsUndirectedEdge, List.any_eq_true, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq] at hcontains
    rcases hcontains with ⟨record, hrecord, hforward | hreverse⟩
    · have hbounds := hactual.endpointsInBounds record hrecord
      exact ⟨by simpa [hforward.1] using hbounds.1,
        by simpa [hforward.2] using hbounds.2⟩
    · have hbounds := hactual.endpointsInBounds record hrecord
      exact ⟨by simpa [hreverse.2] using hbounds.2,
        by simpa [hreverse.1] using hbounds.1⟩
  · intro left right
    rw [natEdgeMatchedBy_iff_containsUndirectedEdge, hcontainsIff]
    exact (natEdgeMatchedBy_iff_containsUndirectedEdge actual left right).symm.trans
      (hactual.localizedComponent_iff left right)

end RawMolecule

end
end OneCenter
end TetraStereo
