import TetraStereo.OneCenter.ProductionCIPRule1aSoundness

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace RawMolecule

/-- Two raw edge occurrences can coexist in an undirected matching exactly when they share no
endpoint.  This predicate deliberately does not inspect molecular semantics. -/
def MancudeEdgesDisjoint (left right : ℕ × ℕ) : Bool :=
  right.1 != left.1 && right.2 != left.1 && right.1 != left.2 && right.2 != left.2

/-- The tail retained by the production include branch. -/
def remainingMancudeEdges (edge : ℕ × ℕ) (edges : List (ℕ × ℕ)) :
    List (ℕ × ℕ) :=
  edges.filter (MancudeEdgesDisjoint edge)

/-- All edge-occurrence matchings explored by the production exclude/include recursion.  Unlike
`exhaustiveMancudeMatchingStats`, this definition retains the witnesses, so its cardinality and
partner sum have an independent finite-family meaning. -/
def exhaustiveMancudeEdgeMatchings : List (ℕ × ℕ) → List (List (ℕ × ℕ))
  | [] => [[]]
  | edge :: edges =>
      exhaustiveMancudeEdgeMatchings edges ++
        (exhaustiveMancudeEdgeMatchings (remainingMancudeEdges edge edges)).map
          (fun matching => edge :: matching)
termination_by edges => edges.length
decreasing_by
  simp_wf
  exact (List.length_filter_le _ _).trans_lt (Nat.lt_succ_self _)

/-- An ordinary undirected edge matching, stated independently of the production search: it is
an order-preserving sublist whose selected edges are pairwise endpoint-disjoint. -/
def IsMancudeEdgeMatching (matching edges : List (ℕ × ℕ)) : Prop :=
  List.Sublist matching edges ∧ matching.Pairwise
    (fun left right => MancudeEdgesDisjoint left right = true)

/-- Contribution of one selected edge to the partner atomic number of `attached`. -/
def mancudeEdgePartnerZ (mol : RawMolecule) (attached : ℕ) (edge : ℕ × ℕ) : ℕ :=
  if edge.1 = attached then mol.atomZAt edge.2
  else if edge.2 = attached then mol.atomZAt edge.1
  else 0

/-- Partner contribution of an edge-occurrence matching.  For genuine matchings at most one term
is nonzero, but summation makes the definition total on the enumerated finite family. -/
def mancudeEdgeMatchingPartnerZ (mol : RawMolecule) (attached : ℕ)
    (matching : List (ℕ × ℕ)) : ℕ :=
  (matching.map (mol.mancudeEdgePartnerZ attached)).sum

/-- Maximum selected-edge cardinality in an explicit finite family. -/
def mancudeFamilyMaximumSize : List (List (ℕ × ℕ)) → ℕ
  | [] => 0
  | matching :: family => max matching.length (mancudeFamilyMaximumSize family)

/-- All occurrences in the family attaining its maximum selected-edge cardinality. -/
def maximumMancudeEdgeMatchings (family : List (List (ℕ × ℕ))) :
    List (List (ℕ × ℕ)) :=
  family.filter (fun matching => matching.length = mancudeFamilyMaximumSize family)

/-- Declarative summary of an explicit edge-matching family. -/
def mancudeEdgeMatchingFamilyStats (mol : RawMolecule) (attached : ℕ)
    (family : List (List (ℕ × ℕ))) : MancudeMatchingStats :=
  let maximum := maximumMancudeEdgeMatchings family
  { size := mancudeFamilyMaximumSize family
    count := maximum.length
    partnerZSum := (maximum.map (mol.mancudeEdgeMatchingPartnerZ attached)).sum }

@[simp] theorem remainingMancudeEdges_eq_filter (edge : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) :
    remainingMancudeEdges edge edges = edges.filter (MancudeEdgesDisjoint edge) := rfl

@[simp] theorem exhaustiveMancudeEdgeMatchings_nil :
    exhaustiveMancudeEdgeMatchings [] = [[]] := by
  rw [exhaustiveMancudeEdgeMatchings.eq_1]

@[simp] theorem exhaustiveMancudeEdgeMatchings_cons (edge : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) :
    exhaustiveMancudeEdgeMatchings (edge :: edges) =
      exhaustiveMancudeEdgeMatchings edges ++
        (exhaustiveMancudeEdgeMatchings (remainingMancudeEdges edge edges)).map
          (fun matching => edge :: matching) := by
  rw [exhaustiveMancudeEdgeMatchings.eq_2]

theorem nil_mem_exhaustiveMancudeEdgeMatchings
    (edges : List (ℕ × ℕ)) :
    [] ∈ exhaustiveMancudeEdgeMatchings edges := by
  induction edges with
  | nil => simp
  | cons edge tail inductionHypothesis =>
      simp only [exhaustiveMancudeEdgeMatchings_cons, List.mem_append]
      exact Or.inl inductionHypothesis

theorem exhaustiveMancudeEdgeMatchings_ne_nil
    (edges : List (ℕ × ℕ)) :
    exhaustiveMancudeEdgeMatchings edges ≠ [] := by
  intro hempty
  have := nil_mem_exhaustiveMancudeEdgeMatchings edges
  rw [hempty] at this
  simp at this

/-- Every witness retained by the exhaustive family is an ordinary pairwise endpoint-disjoint
sublist.  This direction needs no `Nodup` or molecular hypothesis. -/
theorem isMancudeEdgeMatching_of_mem_exhaustive : ∀
    (edges matching : List (ℕ × ℕ)),
    matching ∈ exhaustiveMancudeEdgeMatchings edges →
      IsMancudeEdgeMatching matching edges
  | [], matching, hmatching => by
      simp only [exhaustiveMancudeEdgeMatchings_nil, List.mem_singleton] at hmatching
      subst matching
      exact ⟨List.Sublist.slnil, by simp⟩
  | edge :: edges, matching, hmatching => by
      simp only [exhaustiveMancudeEdgeMatchings_cons, List.mem_append,
        List.mem_map] at hmatching
      rcases hmatching with hexcluded | ⟨tail, htail, rfl⟩
      · obtain ⟨hsublist, hpairwise⟩ :=
          isMancudeEdgeMatching_of_mem_exhaustive edges matching hexcluded
        exact ⟨List.sublist_cons_of_sublist edge hsublist, hpairwise⟩
      · obtain ⟨hsublist, hpairwise⟩ :=
          isMancudeEdgeMatching_of_mem_exhaustive
            (remainingMancudeEdges edge edges) tail htail
        refine ⟨?_, ?_⟩
        · exact (hsublist.trans List.filter_sublist).cons_cons edge
        · simp only [List.pairwise_cons]
          refine ⟨?_, hpairwise⟩
          intro candidate hcandidate
          have hfiltered : candidate ∈ remainingMancudeEdges edge edges :=
            hsublist.subset hcandidate
          exact (List.mem_filter.1 hfiltered).2
termination_by edges _ => edges.length
decreasing_by
  · simp_wf
  · simp_wf
    exact List.length_filter_le _ _

private theorem sublist_filter_of_forall {α : Type*} {p : α → Bool}
    {selected source : List α}
    (hsublist : List.Sublist selected source)
    (hselected : ∀ item ∈ selected, p item = true) :
    List.Sublist selected (source.filter p) := by
  induction hsublist with
  | slnil => simp
  | cons item hsublist inductionHypothesis =>
      simp only [List.filter_cons]
      split
      · exact List.Sublist.cons item (inductionHypothesis hselected)
      · exact inductionHypothesis hselected
  | cons₂ item hsublist inductionHypothesis =>
      have hitem : p item = true := hselected item (by simp)
      simp only [List.filter_cons, hitem, ↓reduceIte]
      apply List.Sublist.cons₂ item
      apply inductionHypothesis
      intro candidate hcandidate
      exact hselected candidate (by simp [hcandidate])

/-- Conversely, every ordinary pairwise endpoint-disjoint sublist occurs in the exhaustive
family.  Together with `isMancudeEdgeMatching_of_mem_exhaustive`, this removes the recursive
search architecture from the meaning of the enumerated witnesses. -/
theorem mem_exhaustiveMancudeEdgeMatchings_of_isMatching : ∀
    (edges matching : List (ℕ × ℕ)),
    IsMancudeEdgeMatching matching edges →
      matching ∈ exhaustiveMancudeEdgeMatchings edges
  | [], matching, hmatching => by
      obtain ⟨hsublist, _⟩ := hmatching
      cases hsublist
      simp
  | edge :: edges, [], _ => nil_mem_exhaustiveMancudeEdgeMatchings (edge :: edges)
  | edge :: edges, first :: tail, hmatching => by
      obtain ⟨hsublist, hpairwise⟩ := hmatching
      rw [List.cons_sublist_cons'] at hsublist
      rcases hsublist with hskipped | ⟨hfirst, htail⟩
      · rw [exhaustiveMancudeEdgeMatchings_cons, List.mem_append]
        exact Or.inl (mem_exhaustiveMancudeEdgeMatchings_of_isMatching
          edges (first :: tail) ⟨hskipped, hpairwise⟩)
      · subst first
        have hpairwiseParts := List.pairwise_cons.1 hpairwise
        have hfiltered : List.Sublist tail (remainingMancudeEdges edge edges) := by
          apply sublist_filter_of_forall htail
          intro candidate hcandidate
          exact hpairwiseParts.1 candidate hcandidate
        have htailMem := mem_exhaustiveMancudeEdgeMatchings_of_isMatching
          (remainingMancudeEdges edge edges) tail ⟨hfiltered, hpairwiseParts.2⟩
        rw [exhaustiveMancudeEdgeMatchings_cons, List.mem_append]
        exact Or.inr (List.mem_map.2 ⟨tail, htailMem, rfl⟩)
termination_by edges _ => edges.length
decreasing_by
  simp_wf
  exact (List.length_filter_le _ _).trans_lt (Nat.lt_succ_self _)

/-- Exact nonrecursive membership characterization of the witness family. -/
theorem mem_exhaustiveMancudeEdgeMatchings_iff
    (edges matching : List (ℕ × ℕ)) :
    matching ∈ exhaustiveMancudeEdgeMatchings edges ↔
      IsMancudeEdgeMatching matching edges :=
  ⟨isMancudeEdgeMatching_of_mem_exhaustive edges matching,
    mem_exhaustiveMancudeEdgeMatchings_of_isMatching edges matching⟩

/-- A duplicate-free input edge list yields a duplicate-free witness family.  Thus the list
length used by the exact stats theorem is a genuine family cardinality, not a count of repeated
search paths. -/
theorem exhaustiveMancudeEdgeMatchings_nodup : ∀ (edges : List (ℕ × ℕ)),
    edges.Nodup → (exhaustiveMancudeEdgeMatchings edges).Nodup
  | [], _ => by simp
  | edge :: edges, hnodup => by
      rw [exhaustiveMancudeEdgeMatchings_cons, List.nodup_append]
      have htailNodup : edges.Nodup := (List.nodup_cons.1 hnodup).2
      have hremainingNodup : (remainingMancudeEdges edge edges).Nodup :=
        List.filter_sublist.nodup htailNodup
      refine ⟨exhaustiveMancudeEdgeMatchings_nodup edges htailNodup,
        (exhaustiveMancudeEdgeMatchings_nodup
          (remainingMancudeEdges edge edges) hremainingNodup).map ?_, ?_⟩
      · intro left right heq
        exact List.cons.inj heq |>.2
      · intro excluded hexcluded included hincluded heq
        obtain ⟨tail, _, rfl⟩ := List.mem_map.1 hincluded
        have hexcludedMatching :=
          isMancudeEdgeMatching_of_mem_exhaustive edges excluded hexcluded
        have hedgeExcluded : edge ∈ excluded := by rw [heq]; simp
        have hedgeTail : edge ∈ edges := hexcludedMatching.1.subset hedgeExcluded
        exact (List.nodup_cons.1 hnodup).1 hedgeTail
termination_by edges => edges.length
decreasing_by
  simp_wf
  exact (List.length_filter_le _ _).trans_lt (Nat.lt_succ_self _)

/-! ## Temporary exact-list interface and partner construction -/

/-- One raw edge occurrence has the stated two endpoints, in either orientation. -/
def NatEdgeIncident {atomCount : ℕ} (edge : ℕ × ℕ)
    (left right : Fin atomCount) : Prop :=
  edge = (left.val, right.val) ∨ edge = (right.val, left.val)

/-- Symmetric incidence relation represented by a selected raw edge list. -/
def NatEdgeMatchedBy {atomCount : ℕ} (matching : List (ℕ × ℕ))
    (left right : Fin atomCount) : Prop :=
  ∃ edge ∈ matching, NatEdgeIncident edge left right

theorem natEdgeMatchedBy_symm {atomCount : ℕ} (matching : List (ℕ × ℕ))
    (left right : Fin atomCount) :
    NatEdgeMatchedBy matching left right ↔ NatEdgeMatchedBy matching right left := by
  simp only [NatEdgeMatchedBy, NatEdgeIncident, or_comm]

private theorem mancudeEdgesDisjoint_symm (left right : ℕ × ℕ) :
    MancudeEdgesDisjoint left right = true ↔
      MancudeEdgesDisjoint right left = true := by
  rcases left with ⟨leftFirst, leftSecond⟩
  rcases right with ⟨rightFirst, rightSecond⟩
  simp only [MancudeEdgesDisjoint, Bool.and_eq_true, bne_iff_ne]
  aesop

private theorem mancudeEdgesDisjoint_of_mem_of_ne {matching : List (ℕ × ℕ)}
    (hpairwise : matching.Pairwise
      (fun left right => MancudeEdgesDisjoint left right = true))
    {left right : ℕ × ℕ} (hleft : left ∈ matching) (hright : right ∈ matching)
    (hne : left ≠ right) : MancudeEdgesDisjoint left right = true := by
  induction matching generalizing left right with
  | nil => simp at hleft
  | cons head tail inductionHypothesis =>
      have hparts := List.pairwise_cons.1 hpairwise
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft <;> rcases hright with rfl | hright
      · exact (hne rfl).elim
      · exact hparts.1 right hright
      · exact (mancudeEdgesDisjoint_symm _ _).2 (hparts.1 left hleft)
      · exact inductionHypothesis hparts.2 hleft hright hne

private theorem natEdgeMatchedBy_functional {atomCount : ℕ}
    (matching : List (ℕ × ℕ)) :
    (matching.Pairwise (fun left right => MancudeEdgesDisjoint left right = true)) →
    (∀ edge ∈ matching, edge.1 ≠ edge.2) →
    ∀ left right other : Fin atomCount,
      NatEdgeMatchedBy matching left right →
      NatEdgeMatchedBy matching left other → right = other := by
  intro hpairwise hloop left right other hright hother
  obtain ⟨rightEdge, hrightMem, hrightIncident⟩ := hright
  obtain ⟨otherEdge, hotherMem, hotherIncident⟩ := hother
  simp only [NatEdgeIncident] at hrightIncident hotherIncident
  by_cases hedge : rightEdge = otherEdge
  · subst otherEdge
    rcases hrightIncident with hrightIncident | hrightIncident <;>
      rcases hotherIncident with hotherIncident | hotherIncident
    · apply Fin.ext
      rw [hrightIncident] at hotherIncident
      have hpairs : left.val = left.val ∧ right.val = other.val := by
        simpa using hotherIncident
      exact hpairs.2
    · have hne := hloop rightEdge hrightMem
      rw [hrightIncident] at hotherIncident hne
      have hpairs : left.val = other.val ∧ right.val = left.val := by
        simpa using hotherIncident
      apply Fin.ext
      omega
    · have hne := hloop rightEdge hrightMem
      rw [hrightIncident] at hotherIncident hne
      have hpairs : right.val = left.val ∧ left.val = other.val := by
        simpa using hotherIncident
      apply Fin.ext
      omega
    · apply Fin.ext
      rw [hrightIncident] at hotherIncident
      have hpairs : right.val = other.val ∧ left.val = left.val := by
        simpa using hotherIncident
      exact hpairs.1
  · have hdisjoint := mancudeEdgesDisjoint_of_mem_of_ne hpairwise
        hrightMem hotherMem hedge
    rcases hrightIncident with hrightIncident | hrightIncident <;>
      rcases hotherIncident with hotherIncident | hotherIncident <;>
      subst rightEdge <;> subst otherEdge <;>
      simp [MancudeEdgesDisjoint] at hdisjoint

/-- Canonical partner assignment induced by a functional symmetric edge-incidence relation. -/
noncomputable def partnerOfMancudeEdgeMatching {atomCount : ℕ}
    (matching : List (ℕ × ℕ)) (atom : Fin atomCount) : Option (Fin atomCount) := by
  classical
  exact if hpartner : ∃ partner, NatEdgeMatchedBy matching atom partner then
      some (Classical.choose hpartner)
    else none

theorem partnerOfMancudeEdgeMatching_eq_some_iff {atomCount : ℕ}
    (matching : List (ℕ × ℕ))
    (hpairwise : matching.Pairwise
      (fun left right => MancudeEdgesDisjoint left right = true))
    (hloop : ∀ edge ∈ matching, edge.1 ≠ edge.2)
    (left right : Fin atomCount) :
    partnerOfMancudeEdgeMatching matching left = some right ↔
      NatEdgeMatchedBy matching left right := by
  unfold partnerOfMancudeEdgeMatching
  split <;> rename_i hexists
  · constructor
    · intro heq
      have hchosen : Classical.choose hexists = right := Option.some.inj heq
      rw [← hchosen]
      exact Classical.choose_spec hexists
    · intro hmatched
      congr 1
      exact natEdgeMatchedBy_functional matching hpairwise hloop left
        (Classical.choose hexists) right (Classical.choose_spec hexists) hmatched
  · constructor
    · simp
    · intro hmatched
      exact (hexists ⟨right, hmatched⟩).elim

/-- Temporary, transparent interface between a production natural-number edge list and the
independent localized component.  This is intentionally not the final realization theorem: every
field is an obligation for `localizedMancudeEdges`, including orientation-free uniqueness. -/
structure LocalizedMancudeEdgeListRealization (mol : RawMolecule)
    (attached : Fin mol.atomCount) (edges : List (ℕ × ℕ)) : Prop where
  nodup : edges.Nodup
  endpointsInBounds : ∀ edge ∈ edges,
    edge.1 < mol.atomCount ∧ edge.2 < mol.atomCount
  noSelfEdges : ∀ edge ∈ edges, edge.1 ≠ edge.2
  undirectedUnique : ∀ first ∈ edges, ∀ second ∈ edges,
    (first = second ∨ first = (second.2, second.1)) → first = second
  localizedComponent_iff : ∀ left right : Fin mol.atomCount,
    NatEdgeMatchedBy edges left right ↔
      mol.toMoleculeGraph.LocalizedMancudeEdge left right ∧
        mol.toMoleculeGraph.InMancudeComponent attached left

private theorem natEdgeMatchedBy_mono {atomCount : ℕ}
    {selected edges : List (ℕ × ℕ)} (hsublist : List.Sublist selected edges)
    {left right : Fin atomCount} :
    NatEdgeMatchedBy selected left right → NatEdgeMatchedBy edges left right := by
  rintro ⟨edge, hedge, hincident⟩
  exact ⟨edge, hsublist.subset hedge, hincident⟩

/-- Every ordinary selected-edge matching in an exact realized localized-component list induces
an independent partner-function matching. -/
theorem partnerOfMancudeEdgeMatching_isMancudeMatching
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges matching : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges)
    (hmatching : IsMancudeEdgeMatching matching edges) :
    mol.toMoleculeGraph.IsMancudeMatching attached
      (partnerOfMancudeEdgeMatching matching) := by
  have hloop : ∀ edge ∈ matching, edge.1 ≠ edge.2 := by
    intro edge hedge
    exact hrealizes.noSelfEdges edge (hmatching.1.subset hedge)
  have hpartnerIff (left right : Fin mol.atomCount) :=
    partnerOfMancudeEdgeMatching_eq_some_iff (atomCount := mol.atomCount)
      matching hmatching.2 hloop left right
  constructor
  · intro atom houtside
    cases hvalue : partnerOfMancudeEdgeMatching matching atom with
    | none => rfl
    | some other =>
        have hselected : NatEdgeMatchedBy matching atom other :=
          (hpartnerIff atom other).1 hvalue
        have hall := natEdgeMatchedBy_mono hmatching.1 hselected
        exact (houtside ((hrealizes.localizedComponent_iff atom other).1 hall).2).elim
  · intro left right
    rw [hpartnerIff left right, hpartnerIff right left]
    constructor
    · intro hselected
      refine ⟨(natEdgeMatchedBy_symm matching left right).1 hselected, ?_⟩
      have hall := natEdgeMatchedBy_mono hmatching.1 hselected
      exact ((hrealizes.localizedComponent_iff left right).1 hall).1
    · exact fun h => (natEdgeMatchedBy_symm matching left right).2 h.1

/-- Vertices saturated by an explicit selected-edge matching. -/
def mancudeEdgeMatchingVertices {atomCount : ℕ} (matching : List (ℕ × ℕ)) :
    Finset (Fin atomCount) := by
  classical
  exact Finset.univ.filter (fun atom => ∃ other, NatEdgeMatchedBy matching atom other)

private theorem mancudeEdgeMatchingVertices_cons {atomCount : ℕ}
    (edge : ℕ × ℕ) (matching : List (ℕ × ℕ))
    (hfirst : edge.1 < atomCount) (hsecond : edge.2 < atomCount) :
    mancudeEdgeMatchingVertices (atomCount := atomCount) (edge :: matching) =
      insert ⟨edge.1, hfirst⟩
        (insert ⟨edge.2, hsecond⟩ (mancudeEdgeMatchingVertices matching)) := by
  classical
  ext atom
  simp only [mancudeEdgeMatchingVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨other, chosen, hchosen, hincident⟩
    simp only [List.mem_cons] at hchosen
    rcases hchosen with rfl | htail
    · simp only [NatEdgeIncident] at hincident
      rcases hincident with hincident | hincident
      · left
        apply Fin.ext
        exact (congrArg Prod.fst hincident).symm
      · right
        left
        apply Fin.ext
        exact (congrArg Prod.snd hincident).symm
    · right
      right
      exact ⟨other, chosen, htail, hincident⟩
  · rintro (hatom | hatom | ⟨other, chosen, hchosen, hincident⟩)
    · refine ⟨⟨edge.2, hsecond⟩, edge, by simp, ?_⟩
      left
      apply Prod.ext
      · exact (congrArg Fin.val hatom).symm
      · rfl
    · refine ⟨⟨edge.1, hfirst⟩, edge, by simp, ?_⟩
      right
      apply Prod.ext
      · rfl
      · exact (congrArg Fin.val hatom).symm
    · exact ⟨other, chosen, by simp [hchosen], hincident⟩

private theorem mancudeEdgeMatchingVertices_card {atomCount : ℕ} : ∀
    (matching : List (ℕ × ℕ)),
    matching.Pairwise (fun left right => MancudeEdgesDisjoint left right = true) →
    (∀ edge ∈ matching, edge.1 < atomCount ∧ edge.2 < atomCount) →
    (∀ edge ∈ matching, edge.1 ≠ edge.2) →
    (mancudeEdgeMatchingVertices (atomCount := atomCount) matching).card =
      2 * matching.length
  | [], _, _, _ => by simp [mancudeEdgeMatchingVertices, NatEdgeMatchedBy]
  | edge :: matching, hpairwise, hbounds, hloop => by
      have hparts := List.pairwise_cons.1 hpairwise
      have hedgeBounds := hbounds edge (by simp)
      have hedgeLoop := hloop edge (by simp)
      rw [mancudeEdgeMatchingVertices_cons edge matching hedgeBounds.1 hedgeBounds.2]
      have hfirstNotMem : (⟨edge.1, hedgeBounds.1⟩ : Fin atomCount) ∉
          mancudeEdgeMatchingVertices matching := by
        intro hmem
        simp only [mancudeEdgeMatchingVertices, Finset.mem_filter, Finset.mem_univ,
          true_and] at hmem
        obtain ⟨other, candidate, hcandidate, hcandidateIncident⟩ := hmem
        have hdisjoint := hparts.1 candidate hcandidate
        simp only [NatEdgeIncident] at hcandidateIncident
        rcases hcandidateIncident with hcandidateIncident | hcandidateIncident <;>
          subst candidate <;> simp [MancudeEdgesDisjoint] at hdisjoint
      have hsecondNotMem : (⟨edge.2, hedgeBounds.2⟩ : Fin atomCount) ∉
          mancudeEdgeMatchingVertices matching := by
        intro hmem
        simp only [mancudeEdgeMatchingVertices, Finset.mem_filter, Finset.mem_univ,
          true_and] at hmem
        obtain ⟨other, candidate, hcandidate, hcandidateIncident⟩ := hmem
        have hdisjoint := hparts.1 candidate hcandidate
        simp only [NatEdgeIncident] at hcandidateIncident
        rcases hcandidateIncident with hcandidateIncident | hcandidateIncident <;>
          subst candidate <;> simp [MancudeEdgesDisjoint] at hdisjoint
      have hfinNe : (⟨edge.1, hedgeBounds.1⟩ : Fin atomCount) ≠
          ⟨edge.2, hedgeBounds.2⟩ := by
        exact fun heq => hedgeLoop (congrArg Fin.val heq)
      have hfirstNotInsert : (⟨edge.1, hedgeBounds.1⟩ : Fin atomCount) ∉
          insert ⟨edge.2, hedgeBounds.2⟩ (mancudeEdgeMatchingVertices matching) := by
        simpa [hfinNe] using hfirstNotMem
      rw [Finset.card_insert_of_notMem hfirstNotInsert,
        Finset.card_insert_of_notMem hsecondNotMem,
        mancudeEdgeMatchingVertices_card matching hparts.2
          (fun candidate hcandidate => hbounds candidate (by simp [hcandidate]))
          (fun candidate hcandidate => hloop candidate (by simp [hcandidate]))]
      simp only [List.length_cons]
      omega

/-- The induced independent partner function saturates exactly two vertices per selected edge. -/
theorem mancudeSaturation_partnerOfMancudeEdgeMatching
    {atomCount : ℕ} (matching : List (ℕ × ℕ))
    (hpairwise : matching.Pairwise
      (fun left right => MancudeEdgesDisjoint left right = true))
    (hbounds : ∀ edge ∈ matching, edge.1 < atomCount ∧ edge.2 < atomCount)
    (hloop : ∀ edge ∈ matching, edge.1 ≠ edge.2) :
    MoleculeGraph.mancudeSaturation
        (partnerOfMancudeEdgeMatching (atomCount := atomCount) matching) =
      2 * matching.length := by
  have hpartnerIff (left right : Fin atomCount) :=
    partnerOfMancudeEdgeMatching_eq_some_iff matching hpairwise hloop left right
  rw [← mancudeEdgeMatchingVertices_card matching hpairwise hbounds hloop]
  unfold MoleculeGraph.mancudeSaturation mancudeEdgeMatchingVertices
  congr 1
  ext atom
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hsome
    obtain ⟨other, hother⟩ := Option.isSome_iff_exists.1 hsome
    exact ⟨other, (hpartnerIff atom other).1 hother⟩
  · rintro ⟨other, hmatched⟩
    exact Option.isSome_iff_exists.2 ⟨other, (hpartnerIff atom other).2 hmatched⟩

/-- An oriented list occurrence is selected by a partner function when its written orientation is
one of the reciprocal partner pairs. -/
def PartnerSelectsMancudeEdge {atomCount : ℕ}
    (partner : Fin atomCount → Option (Fin atomCount)) (edge : ℕ × ℕ) : Prop :=
  ∃ left right : Fin atomCount,
    edge = (left.val, right.val) ∧ partner left = some right

/-- Inverse extraction of the selected occurrences from an exact full edge list. -/
noncomputable def mancudeEdgeMatchingOfPartner {atomCount : ℕ}
    (edges : List (ℕ × ℕ)) (partner : Fin atomCount → Option (Fin atomCount)) :
    List (ℕ × ℕ) := by
  classical
  exact edges.filter (fun edge => decide (PartnerSelectsMancudeEdge partner edge))

@[simp] theorem mem_mancudeEdgeMatchingOfPartner_iff {atomCount : ℕ}
    (edges : List (ℕ × ℕ)) (partner : Fin atomCount → Option (Fin atomCount))
    (edge : ℕ × ℕ) :
    edge ∈ mancudeEdgeMatchingOfPartner edges partner ↔
      edge ∈ edges ∧ PartnerSelectsMancudeEdge partner edge := by
  classical
  simp [mancudeEdgeMatchingOfPartner]

private theorem partner_reciprocal_of_isMancudeMatching
    {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (attached : Atom)
    (partner : Atom → Option Atom) (hmatching : molecule.IsMancudeMatching attached partner)
    {left right : Atom} (hpartner : partner left = some right) :
    partner right = some left :=
  ((hmatching.2 left right).1 hpartner).1

/-- Inverse extraction from any independent partner-function matching is an ordinary selected-edge
matching of the realized list. -/
theorem mancudeEdgeMatchingOfPartner_isMatching
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges : List (ℕ × ℕ)) (partner : Fin mol.atomCount → Option (Fin mol.atomCount))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges)
    (hpartnerMatching : mol.toMoleculeGraph.IsMancudeMatching attached partner) :
    IsMancudeEdgeMatching (mancudeEdgeMatchingOfPartner edges partner) edges := by
  classical
  refine ⟨List.filter_sublist, ?_⟩
  apply (hrealizes.nodup.sublist List.filter_sublist).pairwise_of_forall_ne
  intro first hfirst second hsecond hne
  simp only [List.mem_filter, decide_eq_true_eq] at hfirst hsecond
  obtain ⟨firstLeft, firstRight, hfirstEdge, hfirstPartner⟩ := hfirst.2
  obtain ⟨secondLeft, secondRight, hsecondEdge, hsecondPartner⟩ := hsecond.2
  have hfirstReciprocal := partner_reciprocal_of_isMancudeMatching
    mol.toMoleculeGraph attached partner hpartnerMatching hfirstPartner
  have hsecondReciprocal := partner_reciprocal_of_isMancudeMatching
    mol.toMoleculeGraph attached partner hpartnerMatching hsecondPartner
  have hleftLeft : secondLeft ≠ firstLeft := by
    intro heq
    subst secondLeft
    have hright : secondRight = firstRight := Option.some.inj
      (hsecondPartner.symm.trans hfirstPartner)
    subst secondRight
    exact hne (hfirstEdge.trans hsecondEdge.symm)
  have hrightLeft : secondRight ≠ firstLeft := by
    intro heq
    subst secondRight
    have hright : secondLeft = firstRight := Option.some.inj
      (hsecondReciprocal.symm.trans hfirstPartner)
    subst secondLeft
    apply hne
    apply hrealizes.undirectedUnique first hfirst.1 second hsecond.1
    right
    rw [hfirstEdge, hsecondEdge]
  have hleftRight : secondLeft ≠ firstRight := by
    intro heq
    subst secondLeft
    have hright : secondRight = firstLeft := Option.some.inj
      (hsecondPartner.symm.trans hfirstReciprocal)
    subst secondRight
    apply hne
    apply hrealizes.undirectedUnique first hfirst.1 second hsecond.1
    right
    rw [hfirstEdge, hsecondEdge]
  have hrightRight : secondRight ≠ firstRight := by
    intro heq
    subst secondRight
    have hleft : secondLeft = firstLeft := Option.some.inj
      (hsecondReciprocal.symm.trans hfirstReciprocal)
    subst secondLeft
    exact hne (hfirstEdge.trans hsecondEdge.symm)
  rw [hfirstEdge, hsecondEdge]
  simp only [MancudeEdgesDisjoint, Bool.and_eq_true, bne_iff_ne]
  exact ⟨⟨⟨fun heq => hleftLeft (Fin.ext heq),
      fun heq => hrightLeft (Fin.ext heq)⟩,
    fun heq => hleftRight (Fin.ext heq)⟩,
    fun heq => hrightRight (Fin.ext heq)⟩

private theorem natEdgeMatchedBy_matchingOfPartner_iff
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges : List (ℕ × ℕ)) (partner : Fin mol.atomCount → Option (Fin mol.atomCount))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges)
    (hpartnerMatching : mol.toMoleculeGraph.IsMancudeMatching attached partner)
    (left right : Fin mol.atomCount) :
    NatEdgeMatchedBy (mancudeEdgeMatchingOfPartner edges partner) left right ↔
      partner left = some right := by
  classical
  constructor
  · rintro ⟨edge, hedge, hincident⟩
    rw [mem_mancudeEdgeMatchingOfPartner_iff] at hedge
    obtain ⟨selectedLeft, selectedRight, hselectedEdge, hselectedPartner⟩ := hedge.2
    simp only [NatEdgeIncident] at hincident
    rcases hincident with hincident | hincident
    · rw [hselectedEdge] at hincident
      have hpairs : selectedLeft.val = left.val ∧ selectedRight.val = right.val := by
        simpa using hincident
      rw [Fin.ext hpairs.1, Fin.ext hpairs.2] at hselectedPartner
      exact hselectedPartner
    · rw [hselectedEdge] at hincident
      have hpairs : selectedLeft.val = right.val ∧ selectedRight.val = left.val := by
        simpa using hincident
      rw [Fin.ext hpairs.1, Fin.ext hpairs.2] at hselectedPartner
      exact partner_reciprocal_of_isMancudeMatching
        mol.toMoleculeGraph attached partner hpartnerMatching hselectedPartner
  · intro hpartner
    have hlocalized := ((hpartnerMatching.2 left right).1 hpartner).2
    have hcomponent : mol.toMoleculeGraph.InMancudeComponent attached left := by
      by_contra houtside
      have hnone := hpartnerMatching.1 left houtside
      rw [hpartner] at hnone
      contradiction
    have hall : NatEdgeMatchedBy edges left right :=
      (hrealizes.localizedComponent_iff left right).2 ⟨hlocalized, hcomponent⟩
    obtain ⟨edge, hedge, hincident⟩ := hall
    refine ⟨edge, (mem_mancudeEdgeMatchingOfPartner_iff edges partner edge).2
      ⟨hedge, ?_⟩, hincident⟩
    simp only [NatEdgeIncident] at hincident
    rcases hincident with hincident | hincident
    · exact ⟨left, right, hincident, hpartner⟩
    · exact ⟨right, left, hincident,
        partner_reciprocal_of_isMancudeMatching
          mol.toMoleculeGraph attached partner hpartnerMatching hpartner⟩

/-- Extracting and then reconstructing an independent matching returns the same partner
function. -/
theorem partnerOf_matchingOfPartner
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges : List (ℕ × ℕ)) (partner : Fin mol.atomCount → Option (Fin mol.atomCount))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges)
    (hpartnerMatching : mol.toMoleculeGraph.IsMancudeMatching attached partner) :
    partnerOfMancudeEdgeMatching (mancudeEdgeMatchingOfPartner edges partner) = partner := by
  funext atom
  have hextracted := mancudeEdgeMatchingOfPartner_isMatching mol attached edges partner
    hrealizes hpartnerMatching
  have hloop : ∀ edge ∈ mancudeEdgeMatchingOfPartner edges partner,
      edge.1 ≠ edge.2 := by
    intro edge hedge
    exact hrealizes.noSelfEdges edge
      ((mem_mancudeEdgeMatchingOfPartner_iff edges partner edge).1 hedge).1
  cases hvalue : partner atom with
  | none =>
      cases hconstructed : partnerOfMancudeEdgeMatching
          (mancudeEdgeMatchingOfPartner edges partner) atom with
      | none => rfl
      | some other =>
          have hmatched := (partnerOfMancudeEdgeMatching_eq_some_iff
            (mancudeEdgeMatchingOfPartner edges partner) hextracted.2 hloop atom other).1
              hconstructed
          have := (natEdgeMatchedBy_matchingOfPartner_iff mol attached edges partner
            hrealizes hpartnerMatching atom other).1 hmatched
          rw [hvalue] at this
          contradiction
  | some other =>
      have hmatched := (natEdgeMatchedBy_matchingOfPartner_iff mol attached edges partner
        hrealizes hpartnerMatching atom other).2 hvalue
      exact (partnerOfMancudeEdgeMatching_eq_some_iff
        (mancudeEdgeMatchingOfPartner edges partner) hextracted.2 hloop atom other).2 hmatched

private theorem filter_eq_sublist_of_mem_iff {α : Type*} [DecidableEq α]
    (p : α → Bool) {selected source : List α}
    (hsublist : List.Sublist selected source) (hnodup : source.Nodup)
    (hiff : ∀ item ∈ source, p item = true ↔ item ∈ selected) :
    source.filter p = selected := by
  induction hsublist with
  | slnil => simp
  | cons item hsublist inductionHypothesis =>
      have hparts := List.nodup_cons.1 hnodup
      have hfalse : p item = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        have hmem : item ∈ _ := (hiff item (by simp)).1 htrue
        exact hparts.1 (hsublist.subset hmem)
      simp only [List.filter_cons, hfalse, Bool.false_eq_true, ↓reduceIte]
      apply inductionHypothesis hparts.2
      intro candidate hcandidate
      exact hiff candidate (by simp [hcandidate])
  | cons₂ item hsublist inductionHypothesis =>
      have hparts := List.nodup_cons.1 hnodup
      have htrue : p item = true := (hiff item (by simp)).2 (by simp)
      simp only [List.filter_cons, htrue, ↓reduceIte, List.cons.injEq, true_and]
      apply inductionHypothesis hparts.2
      intro candidate hcandidate
      rw [hiff candidate (by simp [hcandidate])]
      simp only [List.mem_cons]
      constructor
      · intro hmem
        exact hmem.resolve_left (fun heq => hparts.1 (heq.symm ▸ hcandidate))
      · exact Or.inr

private theorem partnerSelects_partnerOf_iff_mem
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges matching : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges)
    (hmatching : IsMancudeEdgeMatching matching edges)
    (edge : ℕ × ℕ) (hedge : edge ∈ edges) :
    PartnerSelectsMancudeEdge
        (partnerOfMancudeEdgeMatching (atomCount := mol.atomCount) matching) edge ↔
      edge ∈ matching := by
  have hloop : ∀ candidate ∈ matching, candidate.1 ≠ candidate.2 := by
    intro candidate hcandidate
    exact hrealizes.noSelfEdges candidate (hmatching.1.subset hcandidate)
  have hpartnerIff (left right : Fin mol.atomCount) :=
    partnerOfMancudeEdgeMatching_eq_some_iff matching hmatching.2 hloop left right
  constructor
  · rintro ⟨left, right, hedgeWritten, hpartner⟩
    have hmatched := (hpartnerIff left right).1 hpartner
    obtain ⟨selected, hselected, hselectedIncident⟩ := hmatched
    have heq : edge = selected := by
      apply hrealizes.undirectedUnique edge hedge selected (hmatching.1.subset hselected)
      simp only [NatEdgeIncident] at hselectedIncident
      rcases hselectedIncident with hselectedIncident | hselectedIncident
      · left
        exact hedgeWritten.trans hselectedIncident.symm
      · right
        rw [hedgeWritten, hselectedIncident]
    rwa [heq]
  · intro hselected
    have hbounds := hrealizes.endpointsInBounds edge hedge
    let left : Fin mol.atomCount := ⟨edge.1, hbounds.1⟩
    let right : Fin mol.atomCount := ⟨edge.2, hbounds.2⟩
    refine ⟨left, right, by rfl, ?_⟩
    apply (hpartnerIff left right).2
    exact ⟨edge, hselected, Or.inl rfl⟩

/-- Reconstructing and then extracting an ordinary selected-edge matching returns the same
ordered sublist, not merely a permutation. -/
theorem matchingOfPartner_partnerOf
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges matching : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges)
    (hmatching : IsMancudeEdgeMatching matching edges) :
    mancudeEdgeMatchingOfPartner edges
      (partnerOfMancudeEdgeMatching (atomCount := mol.atomCount) matching) = matching := by
  classical
  apply filter_eq_sublist_of_mem_iff
    (fun edge => decide (PartnerSelectsMancudeEdge
      (partnerOfMancudeEdgeMatching (atomCount := mol.atomCount) matching) edge))
    hmatching.1 hrealizes.nodup
  intro edge hedge
  simp only [decide_eq_true_eq]
  exact partnerSelects_partnerOf_iff_mem mol attached edges matching
    hrealizes hmatching edge hedge

/-- Bijection between ordinary selected-edge matchings and independent partner functions under
the transparent exact-list interface. -/
noncomputable def mancudeEdgeMatchingEquiv
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges) :
    {matching // IsMancudeEdgeMatching matching edges} ≃
      {partner // mol.toMoleculeGraph.IsMancudeMatching attached partner} where
  toFun matching := ⟨partnerOfMancudeEdgeMatching matching.1,
    partnerOfMancudeEdgeMatching_isMancudeMatching mol attached edges matching.1
      hrealizes matching.2⟩
  invFun partner := ⟨mancudeEdgeMatchingOfPartner edges partner.1,
    mancudeEdgeMatchingOfPartner_isMatching mol attached edges partner.1
      hrealizes partner.2⟩
  left_inv matching := by
    apply Subtype.ext
    exact matchingOfPartner_partnerOf mol attached edges matching.1 hrealizes matching.2
  right_inv partner := by
    apply Subtype.ext
    exact partnerOf_matchingOfPartner mol attached edges partner.1 hrealizes partner.2

/-- Maximum-cardinality formulation on the ordinary edge side. -/
def IsMaximumMancudeEdgeMatching (matching edges : List (ℕ × ℕ)) : Prop :=
  IsMancudeEdgeMatching matching edges ∧
    ∀ other, IsMancudeEdgeMatching other edges → other.length ≤ matching.length

/-- The edge/partner bijection preserves and reflects maximum matchings; the factor of two is
discharged by the saturation theorem rather than assumed. -/
theorem partnerOfMancudeEdgeMatching_isMaximum_iff
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges matching : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges)
    (hmatching : IsMancudeEdgeMatching matching edges) :
    mol.toMoleculeGraph.IsMaximumMancudeMatching attached
        (partnerOfMancudeEdgeMatching matching) ↔
      IsMaximumMancudeEdgeMatching matching edges := by
  have hbounds : ∀ edge ∈ matching,
      edge.1 < mol.atomCount ∧ edge.2 < mol.atomCount := by
    intro edge hedge
    exact hrealizes.endpointsInBounds edge (hmatching.1.subset hedge)
  have hloop : ∀ edge ∈ matching, edge.1 ≠ edge.2 := by
    intro edge hedge
    exact hrealizes.noSelfEdges edge (hmatching.1.subset hedge)
  have hsaturation := mancudeSaturation_partnerOfMancudeEdgeMatching matching
    hmatching.2 hbounds hloop
  constructor
  · intro hmaximum
    refine ⟨hmatching, ?_⟩
    intro other hother
    have hotherBounds : ∀ edge ∈ other,
        edge.1 < mol.atomCount ∧ edge.2 < mol.atomCount := by
      intro edge hedge
      exact hrealizes.endpointsInBounds edge (hother.1.subset hedge)
    have hotherLoop : ∀ edge ∈ other, edge.1 ≠ edge.2 := by
      intro edge hedge
      exact hrealizes.noSelfEdges edge (hother.1.subset hedge)
    have hotherSaturation := mancudeSaturation_partnerOfMancudeEdgeMatching other
      hother.2 hotherBounds hotherLoop
    have hle := hmaximum.2 (partnerOfMancudeEdgeMatching other)
      (partnerOfMancudeEdgeMatching_isMancudeMatching
        mol attached edges other hrealizes hother)
    rw [hotherSaturation, hsaturation] at hle
    omega
  · intro hmaximum
    refine ⟨partnerOfMancudeEdgeMatching_isMancudeMatching
      mol attached edges matching hrealizes hmatching, ?_⟩
    intro other hother
    let extracted := mancudeEdgeMatchingOfPartner edges other
    have hextracted : IsMancudeEdgeMatching extracted edges :=
      mancudeEdgeMatchingOfPartner_isMatching mol attached edges other hrealizes hother
    have hextractedBounds : ∀ edge ∈ extracted,
        edge.1 < mol.atomCount ∧ edge.2 < mol.atomCount := by
      intro edge hedge
      exact hrealizes.endpointsInBounds edge (hextracted.1.subset hedge)
    have hextractedLoop : ∀ edge ∈ extracted, edge.1 ≠ edge.2 := by
      intro edge hedge
      exact hrealizes.noSelfEdges edge (hextracted.1.subset hedge)
    have hextractedSaturation := mancudeSaturation_partnerOfMancudeEdgeMatching extracted
      hextracted.2 hextractedBounds hextractedLoop
    have hinverse := partnerOf_matchingOfPartner mol attached edges other hrealizes hother
    have hle := hmaximum.2 extracted hextracted
    rw [← hinverse, hextractedSaturation, hsaturation]
    omega

private theorem mancudeEdgeMatchingPartnerZ_cons_early
    (mol : RawMolecule) (attached : ℕ) (edge : ℕ × ℕ)
    (matching : List (ℕ × ℕ)) :
    mol.mancudeEdgeMatchingPartnerZ attached (edge :: matching) =
      mol.mancudeEdgeMatchingPartnerZ attached matching +
        mol.mancudeEdgePartnerZ attached edge := by
  simp [mancudeEdgeMatchingPartnerZ, Nat.add_comm]

private theorem mancudeEdgeMatchingPartnerZ_eq_zero
    (mol : RawMolecule) (attached : ℕ) : ∀ (matching : List (ℕ × ℕ)),
    (∀ edge ∈ matching, edge.1 ≠ attached ∧ edge.2 ≠ attached) →
      mol.mancudeEdgeMatchingPartnerZ attached matching = 0
  | [], _ => rfl
  | edge :: matching, hnone => by
      rw [mancudeEdgeMatchingPartnerZ_cons_early,
        mancudeEdgeMatchingPartnerZ_eq_zero mol attached matching
          (fun candidate hcandidate => hnone candidate (by simp [hcandidate]))]
      have hedge := hnone edge (by simp)
      simp [mancudeEdgePartnerZ, hedge.1, hedge.2]

private theorem partnerOf_cons_eq_tail_at
    {atomCount : ℕ} (edge : ℕ × ℕ) (matching : List (ℕ × ℕ))
    (atom : Fin atomCount)
    (hpairwise : (edge :: matching).Pairwise
      (fun left right => MancudeEdgesDisjoint left right = true))
    (hloop : ∀ candidate ∈ edge :: matching, candidate.1 ≠ candidate.2)
    (hfirst : edge.1 ≠ atom.val) (hsecond : edge.2 ≠ atom.val) :
    partnerOfMancudeEdgeMatching (edge :: matching) atom =
      partnerOfMancudeEdgeMatching matching atom := by
  have hparts := List.pairwise_cons.1 hpairwise
  have htailLoop : ∀ candidate ∈ matching, candidate.1 ≠ candidate.2 :=
    fun candidate hcandidate => hloop candidate (by simp [hcandidate])
  apply Option.ext
  intro other
  rw [partnerOfMancudeEdgeMatching_eq_some_iff
      (edge :: matching) hpairwise hloop atom other,
    partnerOfMancudeEdgeMatching_eq_some_iff
      matching hparts.2 htailLoop atom other]
  constructor
  · rintro ⟨candidate, hcandidate, hincident⟩
    simp only [List.mem_cons] at hcandidate
    rcases hcandidate with rfl | htail
    · simp only [NatEdgeIncident] at hincident
      rcases hincident with hincident | hincident
      · exact (hfirst ((congrArg Prod.fst hincident).trans rfl)).elim
      · exact (hsecond ((congrArg Prod.snd hincident).trans rfl)).elim
    · exact ⟨candidate, htail, hincident⟩
  · rintro ⟨candidate, hcandidate, hincident⟩
    exact ⟨candidate, by simp [hcandidate], hincident⟩

/-- The edge/partner bijection preserves the attached-atom atomic-number contribution exactly. -/
theorem mancudePartnerAtomicNumber_partnerOfMancudeEdgeMatching
    (mol : RawMolecule) (attached : Fin mol.atomCount) : ∀
    (matching : List (ℕ × ℕ)),
    matching.Pairwise (fun left right => MancudeEdgesDisjoint left right = true) →
    (∀ edge ∈ matching, edge.1 < mol.atomCount ∧ edge.2 < mol.atomCount) →
    (∀ edge ∈ matching, edge.1 ≠ edge.2) →
    mol.toMoleculeGraph.mancudePartnerAtomicNumber attached
        (partnerOfMancudeEdgeMatching matching) =
      mol.mancudeEdgeMatchingPartnerZ attached.val matching
  | [], _, _, _ => by
      simp [MoleculeGraph.mancudePartnerAtomicNumber,
        partnerOfMancudeEdgeMatching, mancudeEdgeMatchingPartnerZ,
        NatEdgeMatchedBy]
  | edge :: matching, hpairwise, hbounds, hloop => by
      have hparts := List.pairwise_cons.1 hpairwise
      have hedgeBounds := hbounds edge (by simp)
      have hedgeLoop := hloop edge (by simp)
      have htailBounds : ∀ candidate ∈ matching,
          candidate.1 < mol.atomCount ∧ candidate.2 < mol.atomCount :=
        fun candidate hcandidate => hbounds candidate (by simp [hcandidate])
      have htailLoop : ∀ candidate ∈ matching, candidate.1 ≠ candidate.2 :=
        fun candidate hcandidate => hloop candidate (by simp [hcandidate])
      by_cases hfirst : edge.1 = attached.val
      · have hsecond : edge.2 ≠ attached.val := by
          intro heq
          exact hedgeLoop (hfirst.trans heq.symm)
        let other : Fin mol.atomCount := ⟨edge.2, hedgeBounds.2⟩
        have hpartner : partnerOfMancudeEdgeMatching (edge :: matching) attached =
            some other := by
          apply (partnerOfMancudeEdgeMatching_eq_some_iff
            (edge :: matching) hpairwise hloop attached other).2
          refine ⟨edge, by simp, Or.inl ?_⟩
          apply Prod.ext
          · exact hfirst
          · rfl
        have htailNone : ∀ candidate ∈ matching,
            candidate.1 ≠ attached.val ∧ candidate.2 ≠ attached.val := by
          intro candidate hcandidate
          have hdisjoint := hparts.1 candidate hcandidate
          simp only [MancudeEdgesDisjoint, Bool.and_eq_true, bne_iff_ne] at hdisjoint
          exact ⟨fun heq => hdisjoint.1.1.1 (heq.trans hfirst.symm),
            fun heq => hdisjoint.1.1.2 (heq.trans hfirst.symm)⟩
        rw [mancudeEdgeMatchingPartnerZ_cons_early,
          mancudeEdgeMatchingPartnerZ_eq_zero mol attached.val matching htailNone]
        simp only [MoleculeGraph.mancudePartnerAtomicNumber, hpartner]
        simp [mancudeEdgePartnerZ, hfirst,
          mol.atomZAt_eq_toMoleculeGraph_atomZ edge.2 hedgeBounds.2, other]
      · by_cases hsecond : edge.2 = attached.val
        · let other : Fin mol.atomCount := ⟨edge.1, hedgeBounds.1⟩
          have hpartner : partnerOfMancudeEdgeMatching (edge :: matching) attached =
              some other := by
            apply (partnerOfMancudeEdgeMatching_eq_some_iff
              (edge :: matching) hpairwise hloop attached other).2
            refine ⟨edge, by simp, Or.inr ?_⟩
            apply Prod.ext
            · rfl
            · exact hsecond
          have htailNone : ∀ candidate ∈ matching,
              candidate.1 ≠ attached.val ∧ candidate.2 ≠ attached.val := by
            intro candidate hcandidate
            have hdisjoint := hparts.1 candidate hcandidate
            simp only [MancudeEdgesDisjoint, Bool.and_eq_true, bne_iff_ne] at hdisjoint
            exact ⟨fun heq => hdisjoint.1.2 (heq.trans hsecond.symm),
              fun heq => hdisjoint.2 (heq.trans hsecond.symm)⟩
          rw [mancudeEdgeMatchingPartnerZ_cons_early,
            mancudeEdgeMatchingPartnerZ_eq_zero mol attached.val matching htailNone]
          simp only [MoleculeGraph.mancudePartnerAtomicNumber, hpartner]
          simp [mancudeEdgePartnerZ, hfirst, hsecond,
            mol.atomZAt_eq_toMoleculeGraph_atomZ edge.1 hedgeBounds.1, other]
        · unfold MoleculeGraph.mancudePartnerAtomicNumber
          rw [partnerOf_cons_eq_tail_at edge matching attached hpairwise hloop
              hfirst hsecond,
            mancudeEdgeMatchingPartnerZ_cons_early]
          simpa [MoleculeGraph.mancudePartnerAtomicNumber, mancudeEdgePartnerZ,
            hfirst, hsecond] using
              (mancudePartnerAtomicNumber_partnerOfMancudeEdgeMatching
                mol attached matching hparts.2 htailBounds htailLoop)

private theorem exists_matching_length_eq_familyMaximumSize
    {family : List (List (ℕ × ℕ))} (hfamily : family ≠ []) :
    ∃ matching ∈ family, matching.length = mancudeFamilyMaximumSize family := by
  induction family with
  | nil => exact (hfamily rfl).elim
  | cons matching family inductionHypothesis =>
      by_cases hle : mancudeFamilyMaximumSize family ≤ matching.length
      · exact ⟨matching, by simp, by simp [mancudeFamilyMaximumSize, max_eq_left hle]⟩
      · have htail : family ≠ [] := by
          intro hempty
          subst family
          simp [mancudeFamilyMaximumSize] at hle
        obtain ⟨maximum, hmaximum, hlength⟩ := inductionHypothesis htail
        refine ⟨maximum, by simp [hmaximum], ?_⟩
        simp only [mancudeFamilyMaximumSize]
        rw [hlength, max_eq_right (Nat.le_of_not_ge hle)]

private theorem matching_length_le_familyMaximumSize_early
    {family : List (List (ℕ × ℕ))} {matching : List (ℕ × ℕ)}
    (hmatching : matching ∈ family) :
    matching.length ≤ mancudeFamilyMaximumSize family := by
  induction family with
  | nil => simp at hmatching
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hmatching
      simp only [mancudeFamilyMaximumSize]
      rcases hmatching with rfl | hmatching
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmatching).trans (Nat.le_max_right _ _)

/-- Membership in the explicit maximum witness list is exactly the nonrecursive maximum-edge
predicate. -/
theorem mem_maximum_exhaustiveMancudeEdgeMatchings_iff
    (edges matching : List (ℕ × ℕ)) :
    matching ∈ maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges) ↔
      IsMaximumMancudeEdgeMatching matching edges := by
  unfold maximumMancudeEdgeMatchings IsMaximumMancudeEdgeMatching
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hmem, hlength⟩
    refine ⟨(mem_exhaustiveMancudeEdgeMatchings_iff edges matching).1 hmem, ?_⟩
    intro other hother
    have hotherMem := (mem_exhaustiveMancudeEdgeMatchings_iff edges other).2 hother
    have hle := matching_length_le_familyMaximumSize_early hotherMem
    omega
  · rintro ⟨hmatching, hmaximum⟩
    have hmem := (mem_exhaustiveMancudeEdgeMatchings_iff edges matching).2 hmatching
    refine ⟨hmem, ?_⟩
    obtain ⟨witness, hwitness, hwitnessLength⟩ :=
      exists_matching_length_eq_familyMaximumSize
        (exhaustiveMancudeEdgeMatchings_ne_nil edges)
    have hwitnessMatching :=
      (mem_exhaustiveMancudeEdgeMatchings_iff edges witness).1 hwitness
    have hle := hmaximum witness hwitnessMatching
    have hmatchingLe := matching_length_le_familyMaximumSize_early hmem
    omega

/-- Bijection of the two finite maximum families. -/
noncomputable def maximumMancudeEdgeMatchingEquiv
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges) :
    {matching // matching ∈
      (maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges)).toFinset} ≃
      {partner // partner ∈ mol.toMoleculeGraph.maximumMancudeMatchings attached} where
  toFun matching := by
    let partner := partnerOfMancudeEdgeMatching (atomCount := mol.atomCount) matching.1
    refine ⟨partner, ?_⟩
    simp only [MoleculeGraph.maximumMancudeMatchings, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hmaximum := (mem_maximum_exhaustiveMancudeEdgeMatchings_iff edges matching.1).1
      (List.mem_toFinset.1 matching.2)
    exact (partnerOfMancudeEdgeMatching_isMaximum_iff mol attached edges matching.1
      hrealizes hmaximum.1).2 hmaximum
  invFun partner := by
    classical
    let matching := mancudeEdgeMatchingOfPartner edges partner.1
    refine ⟨matching, ?_⟩
    have hpartnerMaximum : mol.toMoleculeGraph.IsMaximumMancudeMatching attached partner.1 := by
      exact (Finset.mem_filter.1 partner.2).2
    have hmatching := mancudeEdgeMatchingOfPartner_isMatching
      mol attached edges partner.1 hrealizes hpartnerMaximum.1
    have hinverse := partnerOf_matchingOfPartner
      mol attached edges partner.1 hrealizes hpartnerMaximum.1
    have hmaximum : IsMaximumMancudeEdgeMatching matching edges :=
      (partnerOfMancudeEdgeMatching_isMaximum_iff mol attached edges matching
        hrealizes hmatching).1 (by simpa [matching, hinverse] using hpartnerMaximum)
    exact List.mem_toFinset.2
      ((mem_maximum_exhaustiveMancudeEdgeMatchings_iff edges matching).2 hmaximum)
  left_inv matching := by
    apply Subtype.ext
    exact matchingOfPartner_partnerOf mol attached edges matching.1 hrealizes
      ((mem_maximum_exhaustiveMancudeEdgeMatchings_iff edges matching.1).1
        (List.mem_toFinset.1 matching.2)).1
  right_inv partner := by
    classical
    apply Subtype.ext
    have hpartnerMatching : mol.toMoleculeGraph.IsMancudeMatching attached partner.1 := by
      have hmaximum : mol.toMoleculeGraph.IsMaximumMancudeMatching attached partner.1 := by
        exact (Finset.mem_filter.1 partner.2).2
      exact hmaximum.1
    exact partnerOf_matchingOfPartner mol attached edges partner.1 hrealizes hpartnerMatching

/-- The production-side explicit maximum witness count equals the independent maximum partner
family cardinality. -/
theorem maximumMancudeEdgeMatchings_length_eq_independent_card
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges) :
    (maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges)).length =
      (mol.toMoleculeGraph.maximumMancudeMatchings attached).card := by
  classical
  let maximumEdges := maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges)
  have hmaximumNodup : maximumEdges.Nodup := by
    exact (exhaustiveMancudeEdgeMatchings_nodup edges hrealizes.nodup).sublist
      List.filter_sublist
  rw [← List.toFinset_card_of_nodup hmaximumNodup]
  rw [← Fintype.card_coe maximumEdges.toFinset,
    ← Fintype.card_coe (mol.toMoleculeGraph.maximumMancudeMatchings attached)]
  simpa [maximumEdges] using Fintype.card_congr
    (maximumMancudeEdgeMatchingEquiv mol attached edges hrealizes)

private theorem list_map_sum_eq_toFinset_sum {α : Type*} [DecidableEq α]
    (f : α → ℕ) : ∀ (items : List α), items.Nodup →
    (items.map f).sum = items.toFinset.sum f
  | [], _ => by simp
  | item :: items, hnodup => by
      have hparts := List.nodup_cons.1 hnodup
      simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
      rw [Finset.sum_insert (by simpa using hparts.1)]
      rw [list_map_sum_eq_toFinset_sum f items hparts.2]

/-- Sum of attached partner atomic numbers agrees across the finite maximum-family bijection. -/
theorem maximumMancudeEdgeMatchings_partnerZSum_eq_independent_sum
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges) :
    ((maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges)).map
        (mol.mancudeEdgeMatchingPartnerZ attached.val)).sum =
      (mol.toMoleculeGraph.maximumMancudeMatchings attached).sum
        (mol.toMoleculeGraph.mancudePartnerAtomicNumber attached) := by
  classical
  let maximumEdges := maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges)
  have hmaximumNodup : maximumEdges.Nodup := by
    exact (exhaustiveMancudeEdgeMatchings_nodup edges hrealizes.nodup).sublist
      List.filter_sublist
  rw [list_map_sum_eq_toFinset_sum
    (mol.mancudeEdgeMatchingPartnerZ attached.val) maximumEdges hmaximumNodup]
  let equivalence := maximumMancudeEdgeMatchingEquiv mol attached edges hrealizes
  have hsum := Fintype.sum_equiv equivalence
    (fun matching => mol.mancudeEdgeMatchingPartnerZ attached.val matching.1)
    (fun partner => mol.toMoleculeGraph.mancudePartnerAtomicNumber attached partner.1)
    (fun matching => by
      exact (mancudePartnerAtomicNumber_partnerOfMancudeEdgeMatching
        mol attached matching.1
        (((mem_maximum_exhaustiveMancudeEdgeMatchings_iff edges matching.1).1
          (List.mem_toFinset.1 matching.2)).1.2)
        (fun edge hedge => hrealizes.endpointsInBounds edge
          (((mem_maximum_exhaustiveMancudeEdgeMatchings_iff edges matching.1).1
            (List.mem_toFinset.1 matching.2)).1.1.subset hedge))
        (fun edge hedge => hrealizes.noSelfEdges edge
          (((mem_maximum_exhaustiveMancudeEdgeMatchings_iff edges matching.1).1
            (List.mem_toFinset.1 matching.2)).1.1.subset hedge))).symm)
  calc
    maximumEdges.toFinset.sum (mol.mancudeEdgeMatchingPartnerZ attached.val) =
        maximumEdges.toFinset.attach.sum
          (fun matching => mol.mancudeEdgeMatchingPartnerZ attached.val matching.1) :=
      (Finset.sum_attach _ _).symm
    _ = (mol.toMoleculeGraph.maximumMancudeMatchings attached).attach.sum
          (fun partner =>
            mol.toMoleculeGraph.mancudePartnerAtomicNumber attached partner.1) := by
      simpa [maximumEdges, equivalence] using hsum
    _ = (mol.toMoleculeGraph.maximumMancudeMatchings attached).sum
          (mol.toMoleculeGraph.mancudePartnerAtomicNumber attached) :=
      Finset.sum_attach _ _

private theorem mancudeFamilyMaximumSize_append
    (left right : List (List (ℕ × ℕ))) :
    mancudeFamilyMaximumSize (left ++ right) =
      max (mancudeFamilyMaximumSize left) (mancudeFamilyMaximumSize right) := by
  induction left with
  | nil => simp [mancudeFamilyMaximumSize]
  | cons matching family inductionHypothesis =>
      simp only [List.cons_append, mancudeFamilyMaximumSize, inductionHypothesis]
      omega

private theorem mancudeFamilyMaximumSize_map_cons
    (edge : ℕ × ℕ) (family : List (List (ℕ × ℕ)))
    (hfamily : family ≠ []) :
    mancudeFamilyMaximumSize (family.map (fun matching => edge :: matching)) =
      mancudeFamilyMaximumSize family + 1 := by
  revert hfamily
  induction family with
  | nil => simp
  | cons matching family inductionHypothesis =>
      intro hfamily
      cases family with
      | nil => simp [mancudeFamilyMaximumSize]
      | cons next rest =>
          have htail : next :: rest ≠ [] := by simp
          rw [List.map_cons, mancudeFamilyMaximumSize,
            inductionHypothesis htail]
          simp only [List.length_cons, mancudeFamilyMaximumSize]
          omega

private theorem matching_length_le_mancudeFamilyMaximumSize
    {family : List (List (ℕ × ℕ))} {matching : List (ℕ × ℕ)}
    (hmatching : matching ∈ family) :
    matching.length ≤ mancudeFamilyMaximumSize family := by
  induction family with
  | nil => simp at hmatching
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hmatching
      simp only [mancudeFamilyMaximumSize]
      rcases hmatching with rfl | hmatching
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmatching).trans (Nat.le_max_right _ _)

private theorem maximumMancudeEdgeMatchings_append_of_lt
    (left right : List (List (ℕ × ℕ)))
    (hsize : mancudeFamilyMaximumSize left < mancudeFamilyMaximumSize right) :
    maximumMancudeEdgeMatchings (left ++ right) = maximumMancudeEdgeMatchings right := by
  unfold maximumMancudeEdgeMatchings
  rw [mancudeFamilyMaximumSize_append, max_eq_right hsize.le]
  rw [List.filter_append]
  have hleft : left.filter
      (fun matching => matching.length = mancudeFamilyMaximumSize right) = [] := by
    rw [List.filter_eq_nil_iff]
    intro matching hmatching heq
    have hle := matching_length_le_mancudeFamilyMaximumSize hmatching
    simp only [decide_eq_true_eq] at heq
    omega
  rw [hleft, List.nil_append]

private theorem maximumMancudeEdgeMatchings_append_of_gt
    (left right : List (List (ℕ × ℕ)))
    (hsize : mancudeFamilyMaximumSize right < mancudeFamilyMaximumSize left) :
    maximumMancudeEdgeMatchings (left ++ right) = maximumMancudeEdgeMatchings left := by
  unfold maximumMancudeEdgeMatchings
  rw [mancudeFamilyMaximumSize_append, max_eq_left hsize.le]
  rw [List.filter_append]
  have hright : right.filter
      (fun matching => matching.length = mancudeFamilyMaximumSize left) = [] := by
    rw [List.filter_eq_nil_iff]
    intro matching hmatching heq
    have hle := matching_length_le_mancudeFamilyMaximumSize hmatching
    simp only [decide_eq_true_eq] at heq
    omega
  rw [hright, List.append_nil]

private theorem maximumMancudeEdgeMatchings_append_of_eq
    (left right : List (List (ℕ × ℕ)))
    (hsize : mancudeFamilyMaximumSize left = mancudeFamilyMaximumSize right) :
    maximumMancudeEdgeMatchings (left ++ right) =
      maximumMancudeEdgeMatchings left ++ maximumMancudeEdgeMatchings right := by
  unfold maximumMancudeEdgeMatchings
  rw [mancudeFamilyMaximumSize_append, hsize, max_self, List.filter_append]

private theorem mancudeEdgeMatchingFamilyStats_append_of_lt
    (mol : RawMolecule) (attached : ℕ)
    (left right : List (List (ℕ × ℕ)))
    (hsize : mancudeFamilyMaximumSize left < mancudeFamilyMaximumSize right) :
    mancudeEdgeMatchingFamilyStats mol attached (left ++ right) =
      mancudeEdgeMatchingFamilyStats mol attached right := by
  unfold mancudeEdgeMatchingFamilyStats
  rw [mancudeFamilyMaximumSize_append, max_eq_right hsize.le,
    maximumMancudeEdgeMatchings_append_of_lt left right hsize]

private theorem mancudeEdgeMatchingFamilyStats_append_of_gt
    (mol : RawMolecule) (attached : ℕ)
    (left right : List (List (ℕ × ℕ)))
    (hsize : mancudeFamilyMaximumSize right < mancudeFamilyMaximumSize left) :
    mancudeEdgeMatchingFamilyStats mol attached (left ++ right) =
      mancudeEdgeMatchingFamilyStats mol attached left := by
  unfold mancudeEdgeMatchingFamilyStats
  rw [mancudeFamilyMaximumSize_append, max_eq_left hsize.le,
    maximumMancudeEdgeMatchings_append_of_gt left right hsize]

private theorem mancudeEdgeMatchingFamilyStats_append_of_eq
    (mol : RawMolecule) (attached : ℕ)
    (left right : List (List (ℕ × ℕ)))
    (hsize : mancudeFamilyMaximumSize left = mancudeFamilyMaximumSize right) :
    mancudeEdgeMatchingFamilyStats mol attached (left ++ right) =
      combineMancudeStats
        (mancudeEdgeMatchingFamilyStats mol attached left)
        (mancudeEdgeMatchingFamilyStats mol attached right) := by
  unfold mancudeEdgeMatchingFamilyStats combineMancudeStats
  rw [mancudeFamilyMaximumSize_append,
    maximumMancudeEdgeMatchings_append_of_eq left right hsize]
  simp only [hsize, max_self, lt_self_iff_false, ↓reduceIte,
    List.length_append, List.map_append, List.sum_append]

private theorem mancudeEdgeMatchingFamilyStats_append
    (mol : RawMolecule) (attached : ℕ)
    (left right : List (List (ℕ × ℕ))) :
    mancudeEdgeMatchingFamilyStats mol attached (left ++ right) =
      combineMancudeStats
        (mancudeEdgeMatchingFamilyStats mol attached left)
        (mancudeEdgeMatchingFamilyStats mol attached right) := by
  rcases lt_trichotomy (mancudeFamilyMaximumSize left)
      (mancudeFamilyMaximumSize right) with hlt | heq | hgt
  · rw [mancudeEdgeMatchingFamilyStats_append_of_lt mol attached left right hlt]
    unfold combineMancudeStats mancudeEdgeMatchingFamilyStats
    simp only [hlt, ↓reduceIte]
  · exact mancudeEdgeMatchingFamilyStats_append_of_eq mol attached left right heq
  · rw [mancudeEdgeMatchingFamilyStats_append_of_gt mol attached left right hgt]
    unfold combineMancudeStats mancudeEdgeMatchingFamilyStats
    have hnot : ¬ mancudeFamilyMaximumSize left < mancudeFamilyMaximumSize right :=
      Nat.not_lt_of_ge hgt.le
    simp only [hnot, hgt, ↓reduceIte]

private theorem filter_map_cons_length
    (edge : ℕ × ℕ) (family : List (List (ℕ × ℕ))) (size : ℕ) :
    (family.map (fun matching => edge :: matching)).filter
        (fun matching => matching.length = size + 1) =
      (family.filter (fun matching => matching.length = size)).map
        (fun matching => edge :: matching) := by
  induction family with
  | nil => simp
  | cons matching family inductionHypothesis =>
      simp only [List.map_cons, List.filter_cons, List.length_cons,
        Nat.add_right_cancel_iff, inductionHypothesis]
      split <;> rfl

private theorem maximumMancudeEdgeMatchings_map_cons
    (edge : ℕ × ℕ) (family : List (List (ℕ × ℕ)))
    (hfamily : family ≠ []) :
    maximumMancudeEdgeMatchings (family.map (fun matching => edge :: matching)) =
      (maximumMancudeEdgeMatchings family).map (fun matching => edge :: matching) := by
  unfold maximumMancudeEdgeMatchings
  rw [mancudeFamilyMaximumSize_map_cons edge family hfamily]
  exact filter_map_cons_length edge family (mancudeFamilyMaximumSize family)

private theorem mancudeEdgeMatchingPartnerZ_cons
    (mol : RawMolecule) (attached : ℕ) (edge : ℕ × ℕ)
    (matching : List (ℕ × ℕ)) :
    mol.mancudeEdgeMatchingPartnerZ attached (edge :: matching) =
      mol.mancudeEdgeMatchingPartnerZ attached matching +
        mol.mancudeEdgePartnerZ attached edge := by
  simp [mancudeEdgeMatchingPartnerZ, Nat.add_comm]

private theorem sum_mancudeEdgeMatchingPartnerZ_map_cons
    (mol : RawMolecule) (attached : ℕ) (edge : ℕ × ℕ)
    (family : List (List (ℕ × ℕ))) :
    ((family.map (fun matching => edge :: matching)).map
      (mol.mancudeEdgeMatchingPartnerZ attached)).sum =
      (family.map (mol.mancudeEdgeMatchingPartnerZ attached)).sum +
        family.length * mol.mancudeEdgePartnerZ attached edge := by
  induction family with
  | nil => simp
  | cons matching family inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, mancudeEdgeMatchingPartnerZ_cons,
        inductionHypothesis, List.length_cons, Nat.add_mul, one_mul]
      omega

private theorem mancudeEdgeMatchingFamilyStats_map_cons
    (mol : RawMolecule) (attached : ℕ) (edge : ℕ × ℕ)
    (family : List (List (ℕ × ℕ))) (hfamily : family ≠ []) :
    mancudeEdgeMatchingFamilyStats mol attached
        (family.map (fun matching => edge :: matching)) =
      { size := (mancudeEdgeMatchingFamilyStats mol attached family).size + 1
        count := (mancudeEdgeMatchingFamilyStats mol attached family).count
        partnerZSum :=
          (mancudeEdgeMatchingFamilyStats mol attached family).partnerZSum +
            (mancudeEdgeMatchingFamilyStats mol attached family).count *
              mol.mancudeEdgePartnerZ attached edge } := by
  simp only [mancudeEdgeMatchingFamilyStats,
    mancudeFamilyMaximumSize_map_cons edge family hfamily,
    maximumMancudeEdgeMatchings_map_cons edge family hfamily,
    List.length_map, sum_mancudeEdgeMatchingPartnerZ_map_cons]

/-- The fuel-free production search is exactly the maximum-cardinality summary of the explicit
finite family of edge-occurrence matchings it explores.  In particular, `size`, `count`, and
`partnerZSum` are not merely deterministic outputs of the recursion: they are respectively the
maximum selected-edge cardinality, the number of attaining witnesses, and the sum of the attached
partner atomic numbers over precisely those witnesses. -/
theorem exhaustiveMancudeMatchingStats_eq_edgeMatchingFamilyStats
    (mol : RawMolecule) (attached : ℕ) : ∀ edges,
    mol.exhaustiveMancudeMatchingStats attached edges =
      mol.mancudeEdgeMatchingFamilyStats attached
        (exhaustiveMancudeEdgeMatchings edges)
  | [] => by
      rw [exhaustiveMancudeMatchingStats.eq_1,
        exhaustiveMancudeEdgeMatchings_nil]
      rfl
  | edge :: edges => by
      let remaining := remainingMancudeEdges edge edges
      have hremaining :
          edges.filter (fun candidate =>
            candidate.1 != edge.1 && candidate.2 != edge.1 &&
              candidate.1 != edge.2 && candidate.2 != edge.2) = remaining := by
        rfl
      have hpartner :
          (if (edge.1 == attached) = true then mol.atomZAt edge.2
            else if (edge.2 == attached) = true then mol.atomZAt edge.1 else 0) =
            mol.mancudeEdgePartnerZ attached edge := by
        simp only [mancudeEdgePartnerZ, beq_iff_eq]
      rw [exhaustiveMancudeMatchingStats.eq_2,
        exhaustiveMancudeEdgeMatchings_cons,
        mancudeEdgeMatchingFamilyStats_append,
        mancudeEdgeMatchingFamilyStats_map_cons mol attached edge
          (exhaustiveMancudeEdgeMatchings remaining)
          (exhaustiveMancudeEdgeMatchings_ne_nil remaining),
        exhaustiveMancudeMatchingStats_eq_edgeMatchingFamilyStats mol attached edges,
        hremaining,
        exhaustiveMancudeMatchingStats_eq_edgeMatchingFamilyStats mol attached remaining,
        hpartner]
termination_by edges => edges.length
decreasing_by
  simp_wf
  exact (List.length_filter_le _ _).trans_lt (Nat.lt_succ_self _)

/-- The fueled production call used in Rule 1a has the same exact explicit-family semantics. -/
theorem mancudeMatchingStats_length_succ_eq_edgeMatchingFamilyStats
    (mol : RawMolecule) (attached : ℕ) (edges : List (ℕ × ℕ)) :
    mol.mancudeMatchingStats attached (edges.length + 1) edges =
      some (mol.mancudeEdgeMatchingFamilyStats attached
        (exhaustiveMancudeEdgeMatchings edges)) := by
  rw [mol.mancudeMatchingStats_length_succ attached edges,
    mol.exhaustiveMancudeMatchingStats_eq_edgeMatchingFamilyStats attached edges]

/-- Count field of the fuel-free production summary agrees with the independent maximum family. -/
theorem exhaustiveMancudeMatchingStats_count_eq_independent_card
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges) :
    (mol.exhaustiveMancudeMatchingStats attached.val edges).count =
      (mol.toMoleculeGraph.maximumMancudeMatchings attached).card := by
  rw [mol.exhaustiveMancudeMatchingStats_eq_edgeMatchingFamilyStats attached.val edges]
  change (maximumMancudeEdgeMatchings
    (exhaustiveMancudeEdgeMatchings edges)).length = _
  exact maximumMancudeEdgeMatchings_length_eq_independent_card
    mol attached edges hrealizes

/-- Partner-sum field of the fuel-free production summary agrees with the independent maximum
family. -/
theorem exhaustiveMancudeMatchingStats_partnerZSum_eq_independent_sum
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges) :
    (mol.exhaustiveMancudeMatchingStats attached.val edges).partnerZSum =
      (mol.toMoleculeGraph.maximumMancudeMatchings attached).sum
        (mol.toMoleculeGraph.mancudePartnerAtomicNumber attached) := by
  rw [mol.exhaustiveMancudeMatchingStats_eq_edgeMatchingFamilyStats attached.val edges]
  change ((maximumMancudeEdgeMatchings
    (exhaustiveMancudeEdgeMatchings edges)).map
      (mol.mancudeEdgeMatchingPartnerZ attached.val)).sum = _
  exact maximumMancudeEdgeMatchings_partnerZSum_eq_independent_sum
    mol attached edges hrealizes

/-- Every independent maximum partner saturates exactly twice the production summary's maximum
selected-edge size.  This is the size bridge used by the production support check. -/
theorem mancudeSaturation_eq_two_mul_exhaustiveStats_size
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges)
    (partner : Fin mol.atomCount → Option (Fin mol.atomCount))
    (hmaximum : partner ∈ mol.toMoleculeGraph.maximumMancudeMatchings attached) :
    MoleculeGraph.mancudeSaturation partner =
      2 * (mol.exhaustiveMancudeMatchingStats attached.val edges).size := by
  classical
  have hpartnerMaximum :
      mol.toMoleculeGraph.IsMaximumMancudeMatching attached partner :=
    (Finset.mem_filter.1 hmaximum).2
  let matching := mancudeEdgeMatchingOfPartner edges partner
  have hmatching : IsMancudeEdgeMatching matching edges :=
    mancudeEdgeMatchingOfPartner_isMatching mol attached edges partner
      hrealizes hpartnerMaximum.1
  have hinverse := partnerOf_matchingOfPartner mol attached edges partner
    hrealizes hpartnerMaximum.1
  have hmatchingMaximum : IsMaximumMancudeEdgeMatching matching edges :=
    (partnerOfMancudeEdgeMatching_isMaximum_iff mol attached edges matching
      hrealizes hmatching).1 (by simpa [matching, hinverse] using hpartnerMaximum)
  have hmaximumMem :=
    (mem_maximum_exhaustiveMancudeEdgeMatchings_iff edges matching).2 hmatchingMaximum
  have hlength : matching.length =
      mancudeFamilyMaximumSize (exhaustiveMancudeEdgeMatchings edges) := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.1 hmaximumMem).2
  have hbounds : ∀ edge ∈ matching,
      edge.1 < mol.atomCount ∧ edge.2 < mol.atomCount := by
    intro edge hedge
    exact hrealizes.endpointsInBounds edge (hmatching.1.subset hedge)
  have hloop : ∀ edge ∈ matching, edge.1 ≠ edge.2 := by
    intro edge hedge
    exact hrealizes.noSelfEdges edge (hmatching.1.subset hedge)
  have hsaturation := mancudeSaturation_partnerOfMancudeEdgeMatching matching
    hmatching.2 hbounds hloop
  have hsize : (mol.exhaustiveMancudeMatchingStats attached.val edges).size =
      mancudeFamilyMaximumSize (exhaustiveMancudeEdgeMatchings edges) := by
    rw [mol.exhaustiveMancudeMatchingStats_eq_edgeMatchingFamilyStats attached.val edges]
    rfl
  rw [← hinverse, hsaturation, hlength, hsize]

end RawMolecule

end
end OneCenter
end TetraStereo
