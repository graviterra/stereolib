import TetraStereo.OneCenter.ProductionCIPRule1aAssembly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace RawMolecule

/-- The four finite-set equalities checked by the production simple-cycle recognizer. -/
structure SimpleCycleExactComponent (mol : RawMolecule) (attached : ℕ)
    (cycle : List ℕ) : Prop where
  cycleVerticesPresent : cycle.all (mol.localizedMancudeComponentVertices attached).contains = true
  noOtherComponentVertices :
    (mol.localizedMancudeComponentVertices attached).all cycle.contains = true
  cycleEdgesPresent : (cycleEdges cycle).all (fun edge =>
    containsUndirectedEdge (mol.localizedMancudeComponentEdges attached) edge.1 edge.2) = true
  noOtherComponentEdges : (mol.localizedMancudeComponentEdges attached).all (fun edge =>
    containsUndirectedEdge (cycleEdges cycle) edge.1 edge.2) = true

theorem SimpleCycleExactComponent.vertex_mem_iff
    {mol : RawMolecule} {attached : ℕ} {cycle : List ℕ}
    (hexact : mol.SimpleCycleExactComponent attached cycle) (atom : ℕ) :
    atom ∈ cycle ↔ atom ∈ mol.localizedMancudeComponentVertices attached := by
  constructor
  · intro hmem
    exact List.contains_iff_mem.mp
      ((List.all_eq_true.mp hexact.cycleVerticesPresent) atom hmem)
  · intro hmem
    exact List.contains_iff_mem.mp
      ((List.all_eq_true.mp hexact.noOtherComponentVertices) atom hmem)

private theorem containsUndirectedEdge_iff_pair_mem
    (edges : List (ℕ × ℕ)) (left right : ℕ) :
    containsUndirectedEdge edges left right = true ↔
      (left, right) ∈ edges ∨ (right, left) ∈ edges := by
  simp only [containsUndirectedEdge, List.any_eq_true, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨edge, hedge, hforward | hreverse⟩
    · left
      have : edge = (left, right) := Prod.ext hforward.1 hforward.2
      simpa [this] using hedge
    · right
      have : edge = (right, left) := Prod.ext hreverse.1 hreverse.2
      simpa [this] using hedge
  · rintro (hforward | hreverse)
    · exact ⟨(left, right), hforward, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(right, left), hreverse, Or.inr ⟨rfl, rfl⟩⟩

theorem SimpleCycleExactComponent.edge_mem_iff
    {mol : RawMolecule} {attached : ℕ} {cycle : List ℕ}
    (hexact : mol.SimpleCycleExactComponent attached cycle) (left right : ℕ) :
    containsUndirectedEdge (cycleEdges cycle) left right = true ↔
      containsUndirectedEdge (mol.localizedMancudeComponentEdges attached) left right = true := by
  rw [containsUndirectedEdge_iff_pair_mem, containsUndirectedEdge_iff_pair_mem]
  constructor
  · rintro (hforward | hreverse)
    · exact (containsUndirectedEdge_iff_pair_mem _ _ _).mp
        ((List.all_eq_true.mp hexact.cycleEdgesPresent) (left, right) hforward)
    · have hcontains := (containsUndirectedEdge_iff_pair_mem _ right left).mp
          ((List.all_eq_true.mp hexact.cycleEdgesPresent) (right, left) hreverse)
      rcases hcontains with hforward | hreverse
      · exact Or.inr hforward
      · exact Or.inl hreverse
  · rintro (hforward | hreverse)
    · exact (containsUndirectedEdge_iff_pair_mem _ _ _).mp
        ((List.all_eq_true.mp hexact.noOtherComponentEdges) (left, right) hforward)
    · have hcontains := (containsUndirectedEdge_iff_pair_mem _ right left).mp
          ((List.all_eq_true.mp hexact.noOtherComponentEdges) (right, left) hreverse)
      rcases hcontains with hforward | hreverse
      · exact Or.inr hforward
      · exact Or.inl hreverse

/-- A successful shortcut result carries an exact equality check against the localized component;
it cannot describe a chord, a fused component, or a second cycle sharing an articulation atom. -/
theorem simpleMancudeCycle?_exactComponent (mol : RawMolecule)
    (attached duplicated : ℕ) (cycle : List ℕ) (alternate : ℕ)
    (hresult : mol.simpleMancudeCycle? attached duplicated = some (cycle, alternate)) :
    mol.SimpleCycleExactComponent attached cycle := by
  unfold simpleMancudeCycle? at hresult
  split at hresult
  · contradiction
  · rename_i hdouble
    let alternatives :=
      (mol.incidentAtoms attached).filterMap fun candidate =>
        if candidate != duplicated && mol.bondOrder attached candidate == 1 then
          (mol.alternatingPath? attached candidate 1 (mol.atomCount + 1) duplicated
            [attached, duplicated]).map fun path => (path, candidate)
        else none
    change (match alternatives with
      | [(path, candidate)] =>
          let foundCycle := attached :: path
          let reportedEdges := cycleEdges foundCycle
          let localizedVertices := mol.localizedMancudeComponentVertices attached
          let localizedEdges := mol.localizedMancudeComponentEdges attached
          let exactComponent :=
            foundCycle.all localizedVertices.contains &&
              localizedVertices.all foundCycle.contains &&
              reportedEdges.all (fun edge =>
                containsUndirectedEdge localizedEdges edge.1 edge.2) &&
              localizedEdges.all (fun edge =>
                containsUndirectedEdge reportedEdges edge.1 edge.2)
          if 3 ≤ foundCycle.length &&
              foundCycle.eraseDups.length == foundCycle.length &&
              mol.cycleIsMancude foundCycle && exactComponent then
            some (foundCycle, candidate)
          else none
      | _ => none) = some (cycle, alternate) at hresult
    cases halternatives : alternatives with
    | nil => simp [halternatives] at hresult
    | cons first rest =>
        cases rest with
        | nil =>
            rcases first with ⟨path, candidate⟩
            simp only [halternatives] at hresult
            split at hresult
            · rename_i haccepted
              have hpairs : attached :: path = cycle ∧ candidate = alternate := by
                exact Prod.mk.inj (Option.some.inj hresult)
              rw [← hpairs.1]
              simp only [Bool.and_eq_true] at haccepted
              have hvertices : (attached :: path).all
                  (mol.localizedMancudeComponentVertices attached).contains = true := by
                tauto
              have hnoVertices : (mol.localizedMancudeComponentVertices attached).all
                  (attached :: path).contains = true := by
                tauto
              have hedges : (cycleEdges (attached :: path)).all (fun edge =>
                  containsUndirectedEdge (mol.localizedMancudeComponentEdges attached)
                    edge.1 edge.2) = true := by
                tauto
              have hnoEdges : (mol.localizedMancudeComponentEdges attached).all (fun edge =>
                  containsUndirectedEdge (cycleEdges (attached :: path))
                    edge.1 edge.2) = true := by
                tauto
              exact
                { cycleVerticesPresent := hvertices
                  noOtherComponentVertices := hnoVertices
                  cycleEdgesPresent := hedges
                  noOtherComponentEdges := hnoEdges }
            · contradiction
        | cons second tail => simp [halternatives] at hresult

end RawMolecule

end
end OneCenter
end TetraStereo
