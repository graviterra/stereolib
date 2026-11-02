import TetraStereo.OneCenter.LocalizedActualFirstChiralMinimality
import TetraStereo.OneCenter.LocalizedActualArmReadback
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000












namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open DeclarativeCIP

noncomputable section
open scoped Classical

/-! ## Generic helpers -/

theorem firstChiralRank_mem :
    ∀ (layer : List LabelEntry) (address : List Nat), firstChiralRank layer = some address →
      ∃ e ∈ layer, e.1 = address ∧ IsChiralEntry e
  | [], _, h => by simp [firstChiralRank] at h
  | (rank, label) :: rest, address, h => by
      cases label with
      | none =>
          obtain ⟨e, he, h1, h2⟩ := firstChiralRank_mem rest address (by simpa [firstChiralRank] using h)
          exact ⟨e, List.mem_cons_of_mem _ he, h1, h2⟩
      | some label =>
          cases label with
          | chiral rs =>
              simp only [firstChiralRank, Option.some.injEq] at h
              subst h
              exact ⟨(rank, some (.chiral rs)), List.mem_cons_self, rfl, rs, rfl⟩
          | pseudoasymmetric _ =>
              obtain ⟨e, he, h1, h2⟩ :=
                firstChiralRank_mem rest address (by simpa [firstChiralRank] using h)
              exact ⟨e, List.mem_cons_of_mem _ he, h1, h2⟩

theorem localizedFirstChiralRankPopulation_eq_findSome? :
    ∀ layers : List (List LabelEntry),
      localizedFirstChiralRankPopulation layers =
        (layers.findSome? localizedFirstChiralRankPopulationInLayer).getD []
  | [] => rfl
  | layer :: layers => by
      simp only [localizedFirstChiralRankPopulation, List.findSome?_cons]
      cases localizedFirstChiralRankPopulationInLayer layer with
      | none => exact localizedFirstChiralRankPopulation_eq_findSome? layers
      | some _ => rfl

theorem findSome?_range_of_first {β : Type*} (f : Nat → Option β) :
    ∀ (n : Nat) (first : Nat) (x : β), first < n → f first = some x →
      (∀ d < first, f d = none) → (List.range n).findSome? f = some x
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, first, x, hlt, hx, hbefore => by
      rw [List.range_succ, List.findSome?_append]
      rcases Nat.lt_or_ge first n with h | h
      · rw [findSome?_range_of_first f n first x h hx hbefore]
        rfl
      · have : first = n := by omega
        subst this
        have hnone : (List.range first).findSome? f = none := by
          rw [List.findSome?_eq_none_iff]
          intro d hd
          exact hbefore d (List.mem_range.1 hd)
        rw [hnone]
        simp [hx]

theorem findSome?_range_eq_none {β : Type*} (f : Nat → Option β) (n : Nat)
    (h : ∀ d, f d = none) : (List.range n).findSome? f = none := by
  rw [List.findSome?_eq_none_iff]
  intro d _
  exact h d

theorem list_eq_map_range_getD {α : Type*} (l : List (List α)) :
    l = (List.range l.length).map fun d => l.getD d [] := by
  apply List.ext_getElem (by simp)
  intro i hi _
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem chiralDescriptorAtRank_eq_some_iff (address : List Nat) (e : LabelEntry) (rs : RS) :
    chiralDescriptorAtRank address e = some rs ↔ e.1 = address ∧ e.2 = some (.chiral rs) := by
  obtain ⟨rank, label⟩ := e
  rcases label with _ | ⟨d | _⟩
  · simp [chiralDescriptorAtRank]
  · simp only [chiralDescriptorAtRank]
    by_cases hr : rank = address
    · subst hr
      simp
    · simp [hr]
  · simp [chiralDescriptorAtRank]

/-! ## Readings: chiral labels are eligible senses -/

/-- The sense of an uppercase descriptor letter. -/
def senseOf : RS → DescriptorSense
  | .R => .senior
  | .S => .junior

theorem senseOf_injective : Function.Injective senseOf := by
  intro a b h
  cases a <;> cases b <;> simp [senseOf] at h ⊢

/-- The eligible sense of a reading (the body of `eligibleSense`). -/
def readingSense : OccurrenceReading → Option DescriptorSense
  | .descriptor value => value.chiralSense
  | _ => none

theorem toLocalizedLabel_chiral_iff (reading : OccurrenceReading) (htetra : reading.IsTetrahedral)
    (rs : RS) :
    reading.toLocalizedLabel = some (.chiral rs) ↔ readingSense reading = some (senseOf rs) := by
  cases reading with
  | descriptor value =>
      cases value <;> cases rs <;>
        simp [OccurrenceReading.toLocalizedLabel, Descriptor.toLocalizedLabel, Descriptor.chiralSense,
          senseOf, OccurrenceReading.IsTetrahedral, Descriptor.IsTetrahedral, readingSense] at htetra ⊢
  | outsideInventory => simp [OccurrenceReading.toLocalizedLabel, readingSense]
  | unassigned => simp [OccurrenceReading.toLocalizedLabel, readingSense]
  | unavailable => simp [OccurrenceReading.toLocalizedLabel, readingSense]

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}

section Arm

variable {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
    Option LocalizedAuxiliaryLabel}
  (arm : input.OriginalRootArm center index .rule4a read)
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (unit : DetectedOccurrence input.moleculeGraph)

/-- The reading-based label of a node. -/
abbrev nodeLabel (node : (armGraph arm).Node) : Option LocalizedAuxiliaryLabel :=
  (occurrenceReading input.moleculeGraph descriptorMap unit (armGraph arm) node).toLocalizedLabel

theorem nodeLabel_chiral_iff (hyp : ArmReadback arm descriptorMap unit) (node : (armGraph arm).Node)
    (rs : RS) :
    nodeLabel arm descriptorMap unit node = some (.chiral rs) ↔
      eligibleSense input.moleculeGraph descriptorMap unit (armGraph arm) node = some (senseOf rs) := by
  show _ ↔ readingSense (occurrenceReading input.moleculeGraph descriptorMap unit (armGraph arm) node) =
    some (senseOf rs)
  exact toLocalizedLabel_chiral_iff _ (hyp.tetrahedral node) rs

theorem eligible_iff_nodeLabel_chiral (hyp : ArmReadback arm descriptorMap unit)
    (node : (armGraph arm).Node) :
    Eligible input.moleculeGraph descriptorMap unit (armGraph arm) node ↔
      ∃ rs, nodeLabel arm descriptorMap unit node = some (.chiral rs) := by
  unfold Eligible
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨sense, hsense⟩
    cases sense with
    | senior => exact ⟨.R, (nodeLabel_chiral_iff arm descriptorMap unit hyp node .R).2 hsense⟩
    | junior => exact ⟨.S, (nodeLabel_chiral_iff arm descriptorMap unit hyp node .S).2 hsense⟩
  · rintro ⟨rs, hrs⟩
    exact ⟨senseOf rs, (nodeLabel_chiral_iff arm descriptorMap unit hyp node rs).1 hrs⟩

/-! ## Entries of the root spheres are nodes at that depth -/

theorem hdense_arm (hyp : ArmReadback arm descriptorMap unit) : Dense (toOfficialSourceTree arm.tree).declarativeAddressing :=
  (arm_ordinaryCanonicalAddressing_rankEvidence arm hyp).1

/-- The entry of a root chain, in terms of its endpoint. -/
theorem sphereEntry_root_eq (hyp : ArmReadback arm descriptorMap unit) (d : Nat)
    (chain : List (armGraph arm).Node) (hchain : chain ∈ depthChains (armGraph arm) (toOfficialSourceTree arm.tree).declarativeAddressing d (armGraph arm).root) :
    sphereEntry arm descriptorMap unit (armGraph arm).root chain =
      (referenceRankAddress input.moleculeGraph descriptorMap unit (armGraph arm) (chain.getLastD (armGraph arm).root),
        nodeLabel arm descriptorMap unit (chain.getLastD (armGraph arm).root)) := by
  unfold sphereEntry referenceRankAddress
  rw [rankAddress_eq_chainRankAddress_of_mem input.moleculeGraph (armGraph arm) (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm)) (toOfficialSourceTree arm.tree).declarativeAddressing (hdense_arm arm descriptorMap
    unit hyp) (armGraph arm).width (armGraph arm).height d chain hchain]

theorem mem_sphereOf_root_iff (hyp : ArmReadback arm descriptorMap unit) (d : Nat) (e : LabelEntry) :
    e ∈ sphereOf arm descriptorMap unit d (armGraph arm).root ↔
      ∃ node : (armGraph arm).Node, (armGraph arm).depth node = d ∧
        e = (referenceRankAddress input.moleculeGraph descriptorMap unit (armGraph arm) node,
          nodeLabel arm descriptorMap unit node) := by
  unfold sphereOf
  rw [List.mem_map]
  constructor
  · rintro ⟨chain, hchain, rfl⟩
    refine ⟨chain.getLastD (armGraph arm).root, ?_, sphereEntry_root_eq arm descriptorMap unit hyp d chain hchain⟩
    rw [← mem_depthNodes_root_iff (armGraph arm) (hdense_arm arm descriptorMap unit hyp) d,
      ← depthChains_getLastD (armGraph arm) (toOfficialSourceTree arm.tree).declarativeAddressing d (armGraph arm).root]
    exact List.mem_map_of_mem hchain
  · rintro ⟨node, hdepth, rfl⟩
    have hmem : node ∈ depthNodes (armGraph arm) (toOfficialSourceTree arm.tree).declarativeAddressing d (armGraph arm).root :=
      (mem_depthNodes_root_iff (armGraph arm) (hdense_arm arm descriptorMap unit hyp) d node).2 hdepth
    rw [← depthChains_getLastD (armGraph arm) (toOfficialSourceTree arm.tree).declarativeAddressing d (armGraph arm).root, List.mem_map] at hmem
    obtain ⟨chain, hchain, hlast⟩ := hmem
    refine ⟨chain, hchain, ?_⟩
    rw [sphereEntry_root_eq arm descriptorMap unit hyp d chain hchain, hlast]

/-- The root sphere `d`, as a map over the depth-`d` nodes. -/
theorem sphereOf_root_eq_map (hyp : ArmReadback arm descriptorMap unit) (d : Nat) :
    sphereOf arm descriptorMap unit d (armGraph arm).root =
      (depthNodes (armGraph arm) (toOfficialSourceTree arm.tree).declarativeAddressing d (armGraph arm).root).map fun node =>
        (referenceRankAddress input.moleculeGraph descriptorMap unit (armGraph arm) node,
          nodeLabel arm descriptorMap unit node) := by
  unfold sphereOf
  rw [← depthChains_getLastD (armGraph arm) (toOfficialSourceTree arm.tree).declarativeAddressing d (armGraph arm).root, List.map_map]
  apply List.map_congr_left
  intro chain hchain
  exact sphereEntry_root_eq arm descriptorMap unit hyp d chain hchain

end Arm

/-! ## Counting through a filterMap -/

private theorem length_filter_filterMap {α β : Type*} (f : α → Option β) (p : β → Bool) :
    ∀ l : List α, ((l.filterMap f).filter p).length =
      (l.filter fun a => ((f a).map p).getD false).length
  | [] => rfl
  | a :: l => by
      rw [List.filterMap_cons]
      cases hfa : f a with
      | none =>
          simp only [List.filter_cons, hfa, Option.map_none, Option.getD_none, Bool.false_eq_true,
            if_false]
          exact length_filter_filterMap f p l
      | some b =>
          simp only [List.filter_cons, hfa, Option.map_some, Option.getD_some]
          by_cases hb : p b = true
          · simp only [hb, if_true, List.length_cons]
            rw [length_filter_filterMap f p l]
          · simp only [hb, Bool.false_eq_true, if_false]
            exact length_filter_filterMap f p l

/-- The list form of the independent selection. -/
def toReferenceList : ReferenceSelection → List RS
  | .empty => []
  | .one .senior => [RS.R]
  | .one .junior => [RS.S]
  | .both => [RS.R, RS.S]

section Assembly

variable (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
  (arm : input.OriginalRootArm center index .rule4a (input.molecularReader descriptorMap target))
  (unit : DetectedOccurrence input.moleculeGraph) (hyp : ArmReadback arm descriptorMap unit)

include hyp

/-- Node form of the first-chiral minimality at the root spheres. -/
theorem rankAddress_min_of_firstChiralRank (d : Nat) (first : List Nat)
    (hfirst : firstChiralRank (sphereOf arm descriptorMap unit d (armGraph arm).root) = some first)
    (node : (armGraph arm).Node) (hdepth : (armGraph arm).depth node = d)
    (helig : Eligible input.moleculeGraph descriptorMap unit (armGraph arm) node) :
    first ≤ referenceRankAddress input.moleculeGraph descriptorMap unit (armGraph arm) node := by
  obtain ⟨rs, hrs⟩ := (eligible_iff_nodeLabel_chiral arm descriptorMap unit hyp node).1 helig
  have hmem : (referenceRankAddress input.moleculeGraph descriptorMap unit (armGraph arm) node,
      nodeLabel arm descriptorMap unit node) ∈ sphereOf arm descriptorMap unit d (armGraph arm).root :=
    (mem_sphereOf_root_iff arm descriptorMap unit hyp d _).2 ⟨node, hdepth, rfl⟩
  have := arm_firstChiralRank_minimal descriptorMap target arm hyp (armGraph arm).root arm.tree arm.key
    arm.trace rfl d first (by rw [arm_root_rankedLabels_getD arm hyp]; exact hfirst) _
    (by rw [arm_root_rankedLabels_getD arm hyp]; exact hmem) ⟨rs, hrs⟩
  exact this

theorem exists_node_of_firstChiralRank (d : Nat) (first : List Nat)
    (hfirst : firstChiralRank (sphereOf arm descriptorMap unit d (armGraph arm).root) = some first) :
    ∃ node : (armGraph arm).Node, (armGraph arm).depth node = d ∧
      Eligible input.moleculeGraph descriptorMap unit (armGraph arm) node ∧
        referenceRankAddress input.moleculeGraph descriptorMap unit (armGraph arm) node = first := by
  obtain ⟨e, he, haddr, rs, hrs⟩ := firstChiralRank_mem _ first hfirst
  obtain ⟨node, hdepth, rfl⟩ := (mem_sphereOf_root_iff arm descriptorMap unit hyp d e).1 he
  exact ⟨node, hdepth, (eligible_iff_nodeLabel_chiral arm descriptorMap unit hyp node).2 ⟨rs, hrs⟩,
    haddr⟩

theorem firstChiralRank_eq_none_iff_root (d : Nat) :
    firstChiralRank (sphereOf arm descriptorMap unit d (armGraph arm).root) = none ↔
      ¬ ∃ node : (armGraph arm).Node, (armGraph arm).depth node = d ∧
        Eligible input.moleculeGraph descriptorMap unit (armGraph arm) node := by
  rw [firstChiralRank_eq_none_iff]
  constructor
  · rintro h ⟨node, hdepth, helig⟩
    obtain ⟨rs, hrs⟩ := (eligible_iff_nodeLabel_chiral arm descriptorMap unit hyp node).1 helig
    exact h _ ((mem_sphereOf_root_iff arm descriptorMap unit hyp d _).2 ⟨node, hdepth, rfl⟩) ⟨rs, hrs⟩
  · intro h e he ⟨rs, hrs⟩
    obtain ⟨node, hdepth, rfl⟩ := (mem_sphereOf_root_iff arm descriptorMap unit hyp d e).1 he
    exact h ⟨node, hdepth, (eligible_iff_nodeLabel_chiral arm descriptorMap unit hyp node).2 ⟨rs, hrs⟩⟩

/-- **The actual reference population is the independent selection.** -/
theorem arm_references_eq_referenceSelection :
    localizedRule4bReferencesFromRankedLabels arm.key.rankedLabels =
      toReferenceList (referenceSelection input.moleculeGraph descriptorMap unit (armGraph arm)) := by
  set layers := arm.key.rankedLabels with hlayersDef
  set n := layers.length with hn
  have hS : ∀ d, layers.getD d [] = sphereOf arm descriptorMap unit d (armGraph arm).root :=
    fun d => arm_root_rankedLabels_getD arm hyp d
  have hlayers : layers = (List.range n).map fun d => sphereOf arm descriptorMap unit d (armGraph arm).root := by
    conv_lhs => rw [list_eq_map_range_getD layers]
    exact List.map_congr_left fun d _ => hS d
  have hbeyond : ∀ d, n ≤ d → sphereOf arm descriptorMap unit d (armGraph arm).root = [] := by
    intro d hd
    rw [← hS d, List.getD_eq_getElem?_getD, List.getElem?_eq_none hd]
    rfl
  unfold localizedRule4bReferencesFromRankedLabels
  rw [localizedFirstChiralRankPopulation_eq_findSome?, hlayers, List.findSome?_map,
    show (localizedFirstChiralRankPopulationInLayer ∘ fun d =>
        sphereOf arm descriptorMap unit d (armGraph arm).root) =
      fun d => (firstChiralRank (sphereOf arm descriptorMap unit d (armGraph arm).root)).map
        fun rank => localizedChiralDescriptorsAtRank rank
          (sphereOf arm descriptorMap unit d (armGraph arm).root) from
      funext fun d => localizedFirstChiralRankPopulationInLayer_eq_map_firstChiralRank _]
  by_cases hex : ∃ node : (armGraph arm).Node,
      Eligible input.moleculeGraph descriptorMap unit (armGraph arm) node
  · -- the nearest eligible depth
    have hexd : ∃ d, ∃ node : (armGraph arm).Node, (armGraph arm).depth node = d ∧
        Eligible input.moleculeGraph descriptorMap unit (armGraph arm) node := by
      obtain ⟨node, h⟩ := hex
      exact ⟨_, node, rfl, h⟩
    set d₀ := Nat.find hexd with hd₀def
    have hd₀ : ∃ node : (armGraph arm).Node, (armGraph arm).depth node = d₀ ∧
        Eligible input.moleculeGraph descriptorMap unit (armGraph arm) node := Nat.find_spec hexd
    have hmin : ∀ d, d < d₀ → ¬ ∃ node : (armGraph arm).Node, (armGraph arm).depth node = d ∧
        Eligible input.moleculeGraph descriptorMap unit (armGraph arm) node :=
      fun d hd => Nat.find_min hexd hd
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, firstChiralRank (sphereOf arm descriptorMap unit d₀ (armGraph arm).root) =
        some a₀ := by
      rcases h : firstChiralRank (sphereOf arm descriptorMap unit d₀ (armGraph arm).root) with _ | a
      · exact absurd hd₀ ((firstChiralRank_eq_none_iff_root descriptorMap target arm unit hyp d₀).1 h)
      · exact ⟨a, rfl⟩
    have hd₀n : d₀ < n := by
      by_contra hge
      push_neg at hge
      rw [hbeyond d₀ hge] at ha₀
      simp [firstChiralRank] at ha₀
    have hbefore : ∀ d < d₀, (firstChiralRank (sphereOf arm descriptorMap unit d (armGraph arm).root)).map
        (fun rank => localizedChiralDescriptorsAtRank rank
          (sphereOf arm descriptorMap unit d (armGraph arm).root)) = none := by
      intro d hd
      rw [(firstChiralRank_eq_none_iff_root descriptorMap target arm unit hyp d).2 (hmin d hd)]
      rfl
    rw [findSome?_range_of_first _ n d₀ _ hd₀n (by rw [ha₀]; rfl) hbefore]
    simp only [Option.getD_some]
    set pop := localizedChiralDescriptorsAtRank a₀
      (sphereOf arm descriptorMap unit d₀ (armGraph arm).root) with hpop
    -- the class
    have nearest_iff : ∀ m : (armGraph arm).Node,
        NearestEligible input.moleculeGraph descriptorMap unit (armGraph arm) m ↔
          Eligible input.moleculeGraph descriptorMap unit (armGraph arm) m ∧
            (armGraph arm).depth m = d₀ := by
      intro m
      constructor
      · rintro ⟨helig, hle⟩
        refine ⟨helig, le_antisymm ?_ ?_⟩
        · obtain ⟨node, hdepth, helig'⟩ := hd₀
          rw [← hdepth]
          exact hle node helig'
        · by_contra hlt
          push_neg at hlt
          exact hmin _ hlt ⟨m, rfl, helig⟩
      · rintro ⟨helig, hdepth⟩
        refine ⟨helig, fun other hother => ?_⟩
        rw [hdepth]
        by_contra hlt
        push_neg at hlt
        exact hmin _ hlt ⟨other, rfl, hother⟩
    have class_iff : ∀ m : (armGraph arm).Node,
        InReferenceClass input.moleculeGraph descriptorMap unit (armGraph arm) m ↔
          Eligible input.moleculeGraph descriptorMap unit (armGraph arm) m ∧
            (armGraph arm).depth m = d₀ ∧
              referenceRankAddress input.moleculeGraph descriptorMap unit (armGraph arm) m = a₀ := by
      intro m
      unfold InReferenceClass
      rw [nearest_iff]
      constructor
      · rintro ⟨⟨helig, hdepth⟩, hmax⟩
        refine ⟨helig, hdepth, le_antisymm ?_ ?_⟩
        · obtain ⟨n₀, hdepth₀, helig₀, haddr₀⟩ :=
            exists_node_of_firstChiralRank descriptorMap target arm unit hyp d₀ a₀ ha₀
          have hle := hmax n₀ ((nearest_iff n₀).2 ⟨helig₀, hdepth₀⟩)
          rw [← haddr₀]
          apply not_lt.1
          intro hlt
          rw [referenceRankAddress_lt_iff input.moleculeGraph descriptorMap unit (armGraph arm)
            (toOfficialSourceTree arm.tree).declarativeAddressing (by rw [hdepth₀, hdepth])] at hlt
          exact absurd hle (not_le.2 hlt)
        · exact rankAddress_min_of_firstChiralRank descriptorMap target arm unit hyp d₀ a₀ ha₀ m hdepth helig
      · rintro ⟨helig, hdepth, haddr⟩
        refine ⟨⟨helig, hdepth⟩, fun o ho => ?_⟩
        obtain ⟨helig', hdepth'⟩ := (nearest_iff o).1 ho
        apply not_lt.1
        intro hlt
        rw [← referenceRankAddress_lt_iff input.moleculeGraph descriptorMap unit (armGraph arm)
          (toOfficialSourceTree arm.tree).declarativeAddressing (by rw [hdepth', hdepth])] at hlt
        have := rankAddress_min_of_firstChiralRank descriptorMap target arm unit hyp d₀ a₀ ha₀ o hdepth' helig'
        rw [haddr] at hlt
        exact absurd this (not_le.2 hlt)
    -- counts
    have count : ∀ rs : RS, (pop.filter fun d => d == rs).length =
        ((referenceClass input.moleculeGraph descriptorMap unit (armGraph arm)).filter fun node =>
          eligibleSense input.moleculeGraph descriptorMap unit (armGraph arm) node =
            some (senseOf rs)).card := by
      intro rs
      rw [hpop, localizedChiralDescriptorsAtRank_eq_filterMap,
        sphereOf_root_eq_map arm descriptorMap unit hyp, List.filterMap_map, length_filter_filterMap]
      simp only [Function.comp_def]
      have hnod := depthNodes_nodup (armGraph arm) (toOfficialSourceTree arm.tree).declarativeAddressing
        (hdense_arm arm descriptorMap unit hyp) d₀ (armGraph arm).root
      have key : ∀ P : (armGraph arm).Node → Bool,
          ((depthNodes (armGraph arm) (toOfficialSourceTree arm.tree).declarativeAddressing d₀
            (armGraph arm).root).filter P).length =
          ((depthNodes (armGraph arm) (toOfficialSourceTree arm.tree).declarativeAddressing d₀
            (armGraph arm).root).filter P).toFinset.card :=
        fun P => (List.toFinset_card_of_nodup (hnod.filter P)).symm
      rw [key, List.toFinset_filter]
      congr 1
      ext m
      simp only [Finset.mem_filter, List.mem_toFinset,
        mem_depthNodes_root_iff (armGraph arm) (hdense_arm arm descriptorMap unit hyp), referenceClass,
        Finset.mem_univ, true_and]
      rw [class_iff]
      constructor
      · rintro ⟨hdepth, hb⟩
        cases hc : chiralDescriptorAtRank a₀
            (referenceRankAddress input.moleculeGraph descriptorMap unit (armGraph arm) m,
              nodeLabel arm descriptorMap unit m) with
        | none => rw [hc] at hb; simp at hb
        | some d =>
            rw [hc] at hb
            simp only [Option.map_some, Option.getD_some, beq_iff_eq] at hb
            subst hb
            obtain ⟨haddr, hlabel⟩ := (chiralDescriptorAtRank_eq_some_iff _ _ _).1 hc
            have hsense := (nodeLabel_chiral_iff arm descriptorMap unit hyp m d).1 hlabel
            refine ⟨⟨?_, hdepth, haddr⟩, hsense⟩
            unfold Eligible
            rw [hsense]
            rfl
      · rintro ⟨⟨_, hdepth, haddr⟩, hsense⟩
        refine ⟨hdepth, ?_⟩
        have hlabel := (nodeLabel_chiral_iff arm descriptorMap unit hyp m rs).2 hsense
        rw [(chiralDescriptorAtRank_eq_some_iff a₀ _ rs).2 ⟨haddr, hlabel⟩]
        simp
    have hR := count .R
    have hS' := count .S
    simp only [senseOf] at hR hS'
    -- the population is nonempty
    have hne : pop.isEmpty = false := by
      obtain ⟨e, he, haddr, rs, hrs⟩ := firstChiralRank_mem _ a₀ ha₀
      rw [List.isEmpty_eq_false_iff_exists_mem]
      refine ⟨rs, ?_⟩
      rw [hpop, localizedChiralDescriptorsAtRank_eq_filterMap, List.mem_filterMap]
      exact ⟨e, he, (chiralDescriptorAtRank_eq_some_iff _ _ _).2 ⟨haddr, hrs⟩⟩
    unfold localizedRule4bReferencesFromPopulation referenceSelection
    rw [if_neg (by rw [hne]; decide), if_neg (not_not.2 hex)]
    unfold seniorCount juniorCount
    rw [← hR, ← hS']
    dsimp only
    split_ifs <;> rfl
  · -- no eligible node: no chiral entry in any sphere
    have hnone : ∀ d, (firstChiralRank (sphereOf arm descriptorMap unit d (armGraph arm).root)).map
        (fun rank => localizedChiralDescriptorsAtRank rank
          (sphereOf arm descriptorMap unit d (armGraph arm).root)) = none := by
      intro d
      rw [(firstChiralRank_eq_none_iff_root descriptorMap target arm unit hyp d).2
        (fun ⟨node, _, helig⟩ => hex ⟨node, helig⟩)]
      rfl
    rw [findSome?_range_eq_none _ n hnone]
    unfold localizedRule4bReferencesFromPopulation referenceSelection
    rw [if_pos hex]
    rfl

end Assembly

/-- **Headline (tree-like inputs).**  On a finite acyclic single-bond input, every original-root
arm of the actual molecular reader selects exactly the independently specified references —
including the two-reference case of equally nearest, equally ranked centres. -/
theorem arm_references_eq_referenceSelection_of_treeLike
    (input : LocalizedUniversalReference.Input)
    {center : input.certified.TetrahedralCenter} {index : Fin 4}
    (target : input.certified.LocalizedCIPOccurrence
      (input.certified.certified.input.molecule.atomCount + 1))
    (htargetRoot : target.1.root = center.1) (htargetAddress : target.1.address = [])
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (arm : input.certified.OriginalRootArm center index .rule4a
      (input.certified.molecularReader (actualReferenceDescriptorMap input) target)) :
    localizedRule4bReferencesFromRankedLabels arm.key.rankedLabels =
      toReferenceList (referenceSelection input.certified.moleculeGraph
        (actualReferenceDescriptorMap input) (input.certified.topUnit center) (armGraph arm)) :=
  arm_references_eq_referenceSelection (actualReferenceDescriptorMap input) target arm
    (input.certified.topUnit center)
    (armReadback_of_treeLike input target htargetRoot htargetAddress singleBonded acyclic arm)

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.arm_references_eq_referenceSelection
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.arm_references_eq_referenceSelection_of_treeLike
