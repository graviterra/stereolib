import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization
import TetraStereo.OneCenter.ProductionCIPRule1aMatchingRealization

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

private theorem containsUndirectedEdge_iff_membership
    (edges : List (ℕ × ℕ)) (left right : ℕ) :
    containsUndirectedEdge edges left right = true ↔
      (left, right) ∈ edges ∨ (right, left) ∈ edges := by
  simp only [containsUndirectedEdge, List.any_eq_true, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨edge, hedge, hforward | hreverse⟩
    · left
      have hedgeEq : edge = (left, right) := Prod.ext hforward.1 hforward.2
      simpa [hedgeEq] using hedge
    · right
      have hedgeEq : edge = (right, left) := Prod.ext hreverse.1 hreverse.2
      simpa [hedgeEq] using hedge
  · rintro (hforward | hreverse)
    · exact ⟨(left, right), hforward, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(right, left), hreverse, Or.inr ⟨rfl, rfl⟩⟩

/-- The exact production traversal of the localized component containing `attached`. -/
def localizedMancudeComponentVertices (mol : RawMolecule) (attached : ℕ) : List ℕ :=
  edgeComponent mol.localizedMancudeEdges (mol.localizedMancudeEdges.length + 1)
    [attached] [attached]

/-- The exact component-filtered edge list passed to the production matching search. -/
def localizedMancudeComponentEdges (mol : RawMolecule) (attached : ℕ) :
    List (ℕ × ℕ) :=
  mol.localizedMancudeEdges.filter fun edge =>
    (mol.localizedMancudeComponentVertices attached).contains edge.1 &&
      (mol.localizedMancudeComponentVertices attached).contains edge.2

private theorem natEdgeMatchedBy_iff_containsUndirectedEdge
    {atomCount : ℕ} (edges : List (ℕ × ℕ)) (left right : Fin atomCount) :
    NatEdgeMatchedBy edges left right ↔
      containsUndirectedEdge edges left.val right.val = true := by
  rw [containsUndirectedEdge_iff_membership]
  constructor
  · rintro ⟨edge, hedge, hincident⟩
    simp only [NatEdgeIncident] at hincident
    rcases hincident with rfl | rfl
    · exact Or.inl hedge
    · exact Or.inr hedge
  · rintro (hforward | hreverse)
    · exact ⟨(left.val, right.val), hforward, Or.inl rfl⟩
    · exact ⟨(right.val, left.val), hreverse, Or.inr rfl⟩

private theorem mem_localizedMancudeComponentVertices_iff
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached atom : Fin mol.atomCount) :
    atom.val ∈ mol.localizedMancudeComponentVertices attached.val ↔
      mol.toMoleculeGraph.InMancudeComponent attached atom := by
  exact mol.mem_edgeComponent_localizedMancudeEdges_iff
    hwellFormed hunique attached atom

/-- The component-filtered list used by `generalMancudeRule1aLabel?` realizes exactly the
independent localized component at `attached`. -/
theorem localizedMancudeComponentEdges_realization
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached : Fin mol.atomCount) :
    LocalizedMancudeEdgeListRealization mol attached
      (mol.localizedMancudeComponentEdges attached.val) := by
  let vertices := mol.localizedMancudeComponentVertices attached.val
  let edges := mol.localizedMancudeComponentEdges attached.val
  have hedgesSublist : List.Sublist edges mol.localizedMancudeEdges := by
    exact List.filter_sublist
  refine
    { nodup := (mol.localizedMancudeEdges_nodup hunique).sublist hedgesSublist
      endpointsInBounds := ?_
      noSelfEdges := ?_
      undirectedUnique := ?_
      localizedComponent_iff := ?_ }
  · intro edge hedge
    exact mol.endpoints_lt_of_mem_localizedMancudeEdges hwellFormed
      (hedgesSublist.subset hedge)
  · intro edge hedge
    exact mol.localizedMancudeEdges_noSelf hwellFormed hunique edge
      (hedgesSublist.subset hedge)
  · intro first hfirst second hsecond hsame
    exact mol.localizedMancudeEdges_undirectedUnique hwellFormed hunique
      first (hedgesSublist.subset hfirst) second (hedgesSublist.subset hsecond) hsame
  · intro left right
    rw [natEdgeMatchedBy_iff_containsUndirectedEdge]
    rw [containsUndirectedEdge_iff_membership]
    constructor
    · intro hcontains
      have hfullContains :
          containsUndirectedEdge mol.localizedMancudeEdges left.val right.val = true := by
        rw [containsUndirectedEdge_iff_membership]
        rcases hcontains with hforward | hreverse
        · exact Or.inl (hedgesSublist.subset hforward)
        · exact Or.inr (hedgesSublist.subset hreverse)
      have hlocalized :=
        (mol.containsUndirectedEdge_localizedMancudeEdges_iff
          hwellFormed hunique left right).1 hfullContains
      refine ⟨hlocalized, ?_⟩
      rcases hcontains with hforward | hreverse
      · have hfilter := (List.mem_filter.1 hforward).2
        simp only [Bool.and_eq_true,
          List.contains_iff_mem] at hfilter
        exact (mol.mem_localizedMancudeComponentVertices_iff
          hwellFormed hunique attached left).1 hfilter.1
      · have hfilter := (List.mem_filter.1 hreverse).2
        simp only [Bool.and_eq_true,
          List.contains_iff_mem] at hfilter
        exact (mol.mem_localizedMancudeComponentVertices_iff
          hwellFormed hunique attached left).1 hfilter.2
    · rintro ⟨hlocalized, hcomponent⟩
      have hrightComponent :
          mol.toMoleculeGraph.InMancudeComponent attached right :=
        hcomponent.tail hlocalized
      have hleftMem : left.val ∈ vertices :=
        (mol.mem_localizedMancudeComponentVertices_iff
          hwellFormed hunique attached left).2 hcomponent
      have hrightMem : right.val ∈ vertices :=
        (mol.mem_localizedMancudeComponentVertices_iff
          hwellFormed hunique attached right).2 hrightComponent
      have hfullContains :
          containsUndirectedEdge mol.localizedMancudeEdges left.val right.val = true :=
        (mol.containsUndirectedEdge_localizedMancudeEdges_iff
          hwellFormed hunique left right).2 hlocalized
      rw [containsUndirectedEdge_iff_membership] at hfullContains
      rcases hfullContains with hforward | hreverse
      · left
        apply List.mem_filter.2
        refine ⟨hforward, ?_⟩
        simpa [edges, localizedMancudeComponentEdges, vertices,
          Bool.and_eq_true, List.contains_iff_mem] using And.intro hleftMem hrightMem
      · right
        apply List.mem_filter.2
        refine ⟨hreverse, ?_⟩
        simpa [edges, localizedMancudeComponentEdges, vertices,
          Bool.and_eq_true, List.contains_iff_mem] using And.intro hrightMem hleftMem

/-- Production component matching count equals the independent maximum-family cardinality. -/
theorem componentExhaustiveStats_count_eq_independent_card
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached : Fin mol.atomCount) :
    (mol.exhaustiveMancudeMatchingStats attached.val
      (mol.localizedMancudeComponentEdges attached.val)).count =
        (mol.toMoleculeGraph.maximumMancudeMatchings attached).card := by
  exact mol.exhaustiveMancudeMatchingStats_count_eq_independent_card attached
    (mol.localizedMancudeComponentEdges attached.val)
    (mol.localizedMancudeComponentEdges_realization hwellFormed hunique attached)

/-- Production component partner sum equals the independent maximum-family partner sum. -/
theorem componentExhaustiveStats_partnerZSum_eq_independent_sum
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached : Fin mol.atomCount) :
    (mol.exhaustiveMancudeMatchingStats attached.val
      (mol.localizedMancudeComponentEdges attached.val)).partnerZSum =
        (mol.toMoleculeGraph.maximumMancudeMatchings attached).sum
          (mol.toMoleculeGraph.mancudePartnerAtomicNumber attached) := by
  exact mol.exhaustiveMancudeMatchingStats_partnerZSum_eq_independent_sum attached
    (mol.localizedMancudeComponentEdges attached.val)
    (mol.localizedMancudeComponentEdges_realization hwellFormed hunique attached)

/-- Every independent maximum matching saturates twice the production component summary size. -/
theorem componentMaximum_saturation_eq_two_mul_exhaustiveStats_size
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached : Fin mol.atomCount)
    (partner : Fin mol.atomCount → Option (Fin mol.atomCount))
    (hmaximum : partner ∈ mol.toMoleculeGraph.maximumMancudeMatchings attached) :
    MoleculeGraph.mancudeSaturation partner =
      2 * (mol.exhaustiveMancudeMatchingStats attached.val
        (mol.localizedMancudeComponentEdges attached.val)).size := by
  exact mol.mancudeSaturation_eq_two_mul_exhaustiveStats_size attached
    (mol.localizedMancudeComponentEdges attached.val)
    (mol.localizedMancudeComponentEdges_realization hwellFormed hunique attached)
    partner hmaximum

/-- Every label returned by the general maximum-matching path has exactly the independent
maximum-matching rational value. -/
theorem generalMancudeRule1aLabel_exactAverage
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached duplicated : Fin mol.atomCount)
    (label : CIPAtomicLabel)
    (hlabel : mol.generalMancudeRule1aLabel? attached.val duplicated.val = some label) :
    label.toExactAtomicNumber.value =
      (mol.toMoleculeGraph.exactMancudeAverage attached).value := by
  let vertices := mol.localizedMancudeComponentVertices attached.val
  let edges := mol.localizedMancudeComponentEdges attached.val
  have hedges : edges = mol.localizedMancudeEdges.filter fun edge =>
      vertices.contains edge.1 && vertices.contains edge.2 := rfl
  unfold generalMancudeRule1aLabel? at hlabel
  change (if !(vertices.contains duplicated.val) || edges.isEmpty then
      none
    else do
      let stats ← mol.mancudeMatchingStats attached.val (edges.length + 1) edges
      let writtenDoubleCount :=
        (edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2).length
      if stats.size != writtenDoubleCount || stats.count == 0 then none
      else some { numerator := stats.partnerZSum, denominator := stats.count }) =
        some label at hlabel
  split at hlabel <;> rename_i hguard
  · contradiction
  · have hstatsCall := mol.mancudeMatchingStats_length_succ attached.val edges
    rw [hstatsCall] at hlabel
    simp only [instMonadOption, Option.bind_some] at hlabel
    split at hlabel <;> rename_i hsupport
    · contradiction
    · have hlabelEq : label =
          { numerator :=
              (mol.exhaustiveMancudeMatchingStats attached.val edges).partnerZSum
            denominator :=
              (mol.exhaustiveMancudeMatchingStats attached.val edges).count } := by
          exact Option.some.inj hlabel.symm
      subst label
      have hcount := mol.componentExhaustiveStats_count_eq_independent_card
        hwellFormed hunique attached
      have hsum := mol.componentExhaustiveStats_partnerZSum_eq_independent_sum
        hwellFormed hunique attached
      have hcountPositive :
          0 < (mol.exhaustiveMancudeMatchingStats attached.val edges).count := by
        rw [hcount]
        exact Finset.card_pos.mpr
          (mol.toMoleculeGraph.maximumMancudeMatchings_nonempty attached)
      unfold CIPAtomicLabel.toExactAtomicNumber ExactAtomicNumber.value
        MoleculeGraph.exactMancudeAverage
      simp only [CIPAtomicLabel.effectiveDenominator]
      rw [hsum, hcount]
      have hindependentPositive :
          0 < (mol.toMoleculeGraph.maximumMancudeMatchings attached).card :=
        Finset.card_pos.mpr
          (mol.toMoleculeGraph.maximumMancudeMatchings_nonempty attached)
      have hone : 1 ≤ (mol.toMoleculeGraph.maximumMancudeMatchings attached).card :=
        hindependentPositive
      rw [max_eq_left hone]

end RawMolecule

end
end OneCenter
end TetraStereo
