import TetraStereo.OneCenter.LocalizedActualRankedLabelsSpheres
import TetraStereo.OneCenter.LocalizedRule4aRankedProjection
import TetraStereo.OneCenter.LocalizedRule4bReferenceAgreement
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
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

/-! ## Chiral entries and the first chiral rank -/

abbrev LabelEntry := OfficialSparseEntry (Option LocalizedAuxiliaryLabel)

def IsChiralEntry (entry : LabelEntry) : Prop := ∃ rs : RS, entry.2 = some (.chiral rs)

theorem firstChiralRank_append :
    ∀ left right : List LabelEntry,
      firstChiralRank (left ++ right) = (firstChiralRank left).or (firstChiralRank right)
  | [], right => by simp [firstChiralRank]
  | (rank, label) :: rest, right => by
      cases label with
      | none => simp [firstChiralRank, firstChiralRank_append rest right]
      | some label =>
          cases label with
          | chiral _ => simp [firstChiralRank]
          | pseudoasymmetric _ => simp [firstChiralRank, firstChiralRank_append rest right]

theorem firstChiralRank_prefixLayer (slot : Nat) :
    ∀ layer : List LabelEntry,
      firstChiralRank (OfficialRuleMajorKey.prefixLayer slot layer) =
        (firstChiralRank layer).map (slot :: ·)
  | [] => rfl
  | (rank, label) :: rest => by
      cases label with
      | none =>
          simp [OfficialRuleMajorKey.prefixLayer, firstChiralRank] at *
          exact firstChiralRank_prefixLayer slot rest
      | some label =>
          cases label with
          | chiral _ => simp [OfficialRuleMajorKey.prefixLayer, firstChiralRank]
          | pseudoasymmetric _ =>
              simp [OfficialRuleMajorKey.prefixLayer, firstChiralRank] at *
              exact firstChiralRank_prefixLayer slot rest

theorem firstChiralRank_eq_none_iff :
    ∀ layer : List LabelEntry, firstChiralRank layer = none ↔ ∀ e ∈ layer, ¬ IsChiralEntry e
  | [] => by simp [firstChiralRank, IsChiralEntry]
  | (rank, label) :: rest => by
      cases label with
      | none =>
          simp only [firstChiralRank, List.mem_cons, forall_eq_or_imp]
          rw [firstChiralRank_eq_none_iff rest]
          simp [IsChiralEntry]
      | some label =>
          cases label with
          | chiral rs =>
              simp only [firstChiralRank, reduceCtorEq, false_iff, not_forall]
              exact ⟨(rank, some (.chiral rs)), List.mem_cons_self, fun h => h ⟨rs, rfl⟩⟩
          | pseudoasymmetric _ =>
              simp only [firstChiralRank, List.mem_cons, forall_eq_or_imp]
              rw [firstChiralRank_eq_none_iff rest]
              simp [IsChiralEntry]

theorem firstChiralRank_flatMap {α : Type*} (f : α → List LabelEntry) :
    ∀ l : List α, firstChiralRank (l.flatMap f) = l.findSome? fun a => firstChiralRank (f a)
  | [] => rfl
  | a :: l => by
      rw [List.flatMap_cons, firstChiralRank_append, List.findSome?_cons,
        firstChiralRank_flatMap f l]
      cases firstChiralRank (f a) <;> rfl

theorem firstChiralRank_singleton_chiral (rank : List Nat) (rs : RS) :
    firstChiralRank [(rank, some (.chiral rs))] = some rank := rfl

private theorem findSome?_eq_some_index {α β : Type*} (f : α → Option β) :
    ∀ (l : List α) (b : β), l.findSome? f = some b →
      ∃ i, ∃ hi : i < l.length, f l[i] = some b ∧ ∀ k (hk : k < i), f (l[k]'(by omega)) = none
  | [], b, h => by simp at h
  | a :: l, b, h => by
      rw [List.findSome?_cons] at h
      cases hfa : f a with
      | some c =>
          rw [hfa] at h
          cases h
          exact ⟨0, by simp, hfa, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
      | none =>
          rw [hfa] at h
          obtain ⟨i, hi, hfi, hbefore⟩ := findSome?_eq_some_index f l b h
          refine ⟨i + 1, by simpa using hi, hfi, ?_⟩
          intro k hk
          cases k with
          | zero => exact hfa
          | succ k => exact hbefore k (by omega)

private theorem mem_flatMap_index {α β : Type*} (g : α → List β) (l : List α) (e : β)
    (h : e ∈ l.flatMap g) : ∃ j, ∃ hj : j < l.length, e ∈ g l[j] := by
  rw [List.mem_flatMap] at h
  obtain ⟨a, ha, he⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha
  exact ⟨j, hj, he⟩

theorem mem_prefixLayer_iff (slot : Nat) (layer : List LabelEntry) (e : LabelEntry) :
    e ∈ OfficialRuleMajorKey.prefixLayer slot layer ↔
      ∃ e' ∈ layer, e = (slot :: e'.1, e'.2) := by
  unfold OfficialRuleMajorKey.prefixLayer
  rw [List.mem_map]
  constructor
  · rintro ⟨e', he', rfl⟩; exact ⟨e', he', rfl⟩
  · rintro ⟨e', he', rfl⟩; exact ⟨e', he', rfl⟩

/-- A projected sphere determines its chiral entries' addresses. -/
theorem exists_chiral_of_projection_mem (layer : List LabelEntry) (address : List Nat)
    (h : (address, [2]) ∈ projectRule4aLayer layer) :
    ∃ e ∈ layer, e.1 = address ∧ IsChiralEntry e := by
  unfold projectRule4aLayer at h
  rw [List.mem_map] at h
  obtain ⟨e, he, heq⟩ := h
  unfold projectRule4aEntry at heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  refine ⟨e, he, h1, ?_⟩
  rcases hl : e.2 with _ | ⟨⟨rs⟩ | ⟨_⟩⟩
  · rw [hl] at h2; simp [localizedCumulativeRule45Priority, localizedRule4aPriority] at h2
  · exact ⟨rs, hl⟩
  · rw [hl] at h2; simp [localizedCumulativeRule45Priority, localizedRule4aPriority] at h2

theorem projection_mem_of_chiral (layer : List LabelEntry) (e : LabelEntry) (he : e ∈ layer)
    (hchiral : IsChiralEntry e) : (e.1, [2]) ∈ projectRule4aLayer layer := by
  obtain ⟨rs, hrs⟩ := hchiral
  unfold projectRule4aLayer
  rw [List.mem_map]
  refine ⟨e, he, ?_⟩
  unfold projectRule4aEntry
  rw [hrs]
  rfl

private theorem getD_map_projection (layers : List (List LabelEntry)) (d : Nat) :
    (layers.map projectRule4aLayer).getD d [] = projectRule4aLayer (layers.getD d []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases layers[d]? <;> rfl

/-! ## Lexicographic facts on rank addresses -/

private theorem cons_le_cons_of_le {r : Nat} {a b : List Nat} (h : b ≤ a) : r :: b ≤ r :: a := by
  apply not_lt.1
  intro hlt
  have : List.Lex (· < ·) (r :: a) (r :: b) := hlt
  rw [List.cons_lex_cons_iff] at this
  rcases this with h' | ⟨_, h'⟩
  · exact lt_irrefl _ h'
  · exact not_lt.2 h h'

private theorem cons_le_cons_of_lt {r r' : Nat} (h : r < r') (a b : List Nat) :
    r :: b ≤ r' :: a := by
  apply not_lt.1
  intro hlt
  have : List.Lex (· < ·) (r' :: a) (r :: b) := hlt
  rw [List.cons_lex_cons_iff] at this
  rcases this with h' | ⟨h', _⟩
  · exact lt_asymm h h'
  · exact absurd h' (ne_of_gt h)



private theorem mem_of_mapM_some {α β : Type*} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ∀ y ∈ ys, ∃ a ∈ l, f a = some y
  | [], ys, h, y, hy => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      simp at hy
  | a :: l, ys, h, y, hy => by
      rw [List.mapM_cons] at h
      cases hfa : f a with
      | none => simp [hfa] at h
      | some b =>
          cases hl : l.mapM f with
          | none => simp [hfa, hl] at h
          | some bs =>
              simp only [hfa, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at h
              subst h
              rcases List.mem_cons.1 hy with rfl | hy'
              · exact ⟨a, List.mem_cons_self, hfa⟩
              · obtain ⟨a', ha', hfa'⟩ := mem_of_mapM_some f l bs hl y hy'
                exact ⟨a', List.mem_cons_of_mem a ha', hfa'⟩

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}


theorem projected_rankedLabels_eq_of_tie
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    {fuel : Nat} {children : List (input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1))}
    {childKeys : List input.LocalizedRerootCumulativeRule45Key}
    (computed : children.mapM (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (input.molecularReader descriptorMap target) fuel) = some childKeys)
    {keyI keyJ : input.LocalizedRerootCumulativeRule45Key} (hI : keyI ∈ childKeys)
    (hJ : keyJ ∈ childKeys)
    (tie : input.compareLocalizedRerootCumulativeRule45Keys keyI keyJ = Ordering.eq) :
    keyI.rankedLabels.map projectRule4aLayer = keyJ.rankedLabels.map projectRule4aLayer := by
  have readEq : input.molecularReader descriptorMap target =
      fun cursor => input.localizedDependencyLabel target (input.molecularView descriptorMap target)
        cursor := rfl
  have derive : ∀ key ∈ childKeys, ∃ cursor,
      input.DeclarativeLocalizedRerootCumulativeRule45Key .rule4a target
        (input.molecularView descriptorMap target) fuel cursor key := by
    intro key hkey
    obtain ⟨cursor, _, hbuilt⟩ := mem_of_mapM_some _ children childKeys computed key hkey
    rw [readEq, input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel]
      at hbuilt
    exact ⟨cursor, input.buildLocalizedRerootCumulativeRule45Key?_sound .rule4a target _ fuel cursor
      key hbuilt⟩
  obtain ⟨cursorI, dI⟩ := derive keyI hI
  obtain ⟨cursorJ, dJ⟩ := derive keyJ hJ
  exact input.declarative_rule4a_rankedLabels_projection_eq target
    (input.molecularView descriptorMap target) fuel cursorI cursorJ keyI keyJ dI dJ
    ((input.compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq keyI keyJ).1 tie)

/-! ## The two cases of the trace induction -/

/-- A single root entry: its first chiral rank is `[]`, as is its only address. -/
theorem terminal_minimal {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel} {label : Option LocalizedAuxiliaryLabel}
    (d : Nat) (first : List Nat)
    (hfirst : firstChiralRank
      ((localizedCumulativeRule45TerminalKey input .rule4a cursor label).rankedLabels.getD d []) =
        some first)
    (e : LabelEntry)
    (he : e ∈ (localizedCumulativeRule45TerminalKey input .rule4a cursor label).rankedLabels.getD d
      []) : first ≤ e.1 := by
  cases d with
  | zero =>
      simp only [List.getD_cons_zero, List.mem_singleton] at hfirst he
      subst he
      rcases label with _ | ⟨_ | _⟩ <;> simp [firstChiralRank] at hfirst
      subst hfirst
      exact le_rfl
  | succ d => simp at he

theorem root_entry_minimal {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel} {label : Option LocalizedAuxiliaryLabel}
    {sortedKeys : List input.LocalizedRerootCumulativeRule45Key} (first : List Nat)
    (hfirst : firstChiralRank
      ((localizedCumulativeRule45StepKey input .rule4a cursor label sortedKeys).rankedLabels.getD 0
        []) = some first)
    (e : LabelEntry)
    (he : e ∈ (localizedCumulativeRule45StepKey input .rule4a cursor label
      sortedKeys).rankedLabels.getD 0 []) : first ≤ e.1 := by
  simp only [List.cons_append, List.nil_append,
    List.getD_cons_zero, List.mem_singleton] at hfirst he
  subst he
  rcases label with _ | ⟨_ | _⟩ <;> simp [firstChiralRank] at hfirst
  subst hfirst
  exact le_rfl

theorem node_minimal
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (arm : input.OriginalRootArm center index .rule4a (input.molecularReader descriptorMap target))
    {unit : DetectedOccurrence input.moleculeGraph} (hyp : ArmReadback arm descriptorMap unit)
    {fuel : Nat}
    (ih : ∀ (node : (armGraph arm).Node)
      (dsub : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
      (key : input.LocalizedRerootCumulativeRule45Key),
      LocalizedActualRecursiveSortTrace input .rule4a (input.molecularReader descriptorMap target)
          fuel dsub key →
        arm.tree.decoratedSubtreeAt? node.1 = some dsub →
          ∀ (d : Nat) (first : List Nat), firstChiralRank (key.rankedLabels.getD d []) = some first →
            ∀ e ∈ key.rankedLabels.getD d [], IsChiralEntry e → first ≤ e.1)
    (node : (armGraph arm).Node)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (children : List (input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1)))
    (childKeys sortedKeys : List input.LocalizedRerootCumulativeRule45Key)
    (sortedTrees : List (LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)))
    (childKeysComputed : children.mapM (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (input.molecularReader descriptorMap target) fuel) = some childKeys)
    (sortedEq : sortedKeys = input.sortLocalizedRerootCumulativeRule45Keys childKeys)
    (childrenTraced : LocalizedActualRecursiveSortTraceList input .rule4a
      (input.molecularReader descriptorMap target) fuel sortedKeys sortedTrees)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (input.molecularReader descriptorMap target cursor)
        sortedTrees))
    (d : Nat) (first : List Nat)
    (hfirst : firstChiralRank ((localizedCumulativeRule45StepKey input .rule4a cursor
      (input.molecularReader descriptorMap target cursor) sortedKeys).rankedLabels.getD d []) =
        some first)
    (e : LabelEntry)
    (he : e ∈ (localizedCumulativeRule45StepKey input .rule4a cursor
      (input.molecularReader descriptorMap target cursor) sortedKeys).rankedLabels.getD d [])
    (hchiral : IsChiralEntry e) : first ≤ e.1 := by
  cases d with
  | zero => exact root_entry_minimal first hfirst e he
  | succ d =>
  -- shared setup
  have hcanon := arm_ordinaryCanonicalAddressing_rankEvidence arm hyp
  have hkeysorted := hcanon.2
  have hdense := denseAt_of_lookup arm node _ lookup
  have childrenEq : (localizedRootTree input cursor (input.molecularReader descriptorMap target cursor)
      sortedTrees).children = sortedTrees := rfl
  rw [childrenEq] at hdense
  have paired := LocalizedActualRecursiveSortTraceList.to_forall₂ childrenTraced
  have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
  set slots := slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
    sortedTrees.length with hslots
  have slotLength : slots.length = sortedTrees.length := by simp [hslots, slotList]
  have childAt : ∀ i (hi : i < sortedTrees.length), ∃ child : (armGraph arm).Node,
      slots[i]? = some child ∧ child.1 = node.1 ++ [i] ∧
        arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
    intro i hi
    obtain ⟨child, slotSome, addr⟩ := slotList_getD_of_lt (addressing :=
      (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
      (count := sortedTrees.length) hdense hi
    have addrFlat : child.1 = node.1 ++ [i] := by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address] at addr
      exact addr
    refine ⟨child, slotSome, addrFlat, ?_⟩
    rw [addrFlat, decoratedSubtreeAt?_append arm.tree node.1 [i], lookup]
    simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem hi]
  have traceAt : ∀ i (hi : i < sortedTrees.length),
      LocalizedActualRecursiveSortTrace input .rule4a (input.molecularReader descriptorMap target)
        fuel (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) :=
    fun i hi => List.Forall₂.get (i := i) paired (by omega) hi
  have represented : ∀ i (hi : i < sortedTrees.length) (child : (armGraph arm).Node),
      arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
        Represented (read := input.molecularReader descriptorMap target)
          (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
          (armGraph arm).width (armGraph arm).height (sortedKeys[i]'(by omega)) child :=
    fun i hi child hl =>
      ⟨sortedTrees[i]'hi, (LocalizedActualRecursiveSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch,
        LocalizedActualRecursiveSortTrace.realizes_of_trace (traceAt i hi),
        (arm_node_bridge arm le_rfl le_rfl child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega))
          (traceAt i hi) hl).2,
        (arm_node_bridge4a arm hyp le_rfl le_rfl child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega))
          (traceAt i hi) hl).2⟩
  have slotGet : ∀ i (hi : i < sortedTrees.length), ∃ child, slots[i]'(by rw [slotLength]; exact hi) = child ∧
      arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
    intro i hi
    obtain ⟨child, slotSome, _, hl⟩ := childAt i hi
    exact ⟨child, Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotSome), hl⟩
  have pairedSlots : List.Forall₂ (Represented (read := input.molecularReader descriptorMap target)
      (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
      (armGraph arm).width (armGraph arm).height) sortedKeys slots := by
    rw [List.forall₂_iff_get]
    refine ⟨by rw [lengthEq, slotLength], ?_⟩
    intro i hi hi'
    simp only [List.get_eq_getElem]
    obtain ⟨child, hget, hl⟩ := slotGet i (by omega)
    rw [hget]
    exact represented i (by omega) child hl
  set oks := slots.map (ordinaryKey input.moleculeGraph (armGraph arm)
    (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
    (armGraph arm).width (armGraph arm).height) with hoks
  have oksSorted : oks.Pairwise fun x y => y ≤ x := by
    have oksEq : rankedOrdinaryKeys input.moleculeGraph (armGraph arm)
        (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
        (armGraph arm).width (armGraph arm).height node = oks := by
      unfold rankedOrdinaryKeys
      exact sortDesc_childKeys_eq_slotOrder _ hdense hkeysorted
    rw [← oksEq]
    exact Certificate.CanonicalSphereKey.sortDesc_pairwise _
  have hranks := rankedChildren_snd_eq_headRanks hyp.rule4aOnly sortedKeys slots pairedSlots
  rw [headRanks_eq_map_rankIndexIn _ oksSorted] at hranks
  have hfst := rankedChildren_fst (input := input) sortedKeys
  set ranked := input.localizedRerootRankedChildren sortedKeys with hranked
  have rankedLength : ranked.length = sortedKeys.length := by
    have := congrArg List.length hfst
    simpa using this
  have hp1 : ∀ i (hi : i < ranked.length), ranked[i].1 = sortedKeys[i]'(by omega) := by
    intro i hi
    have := congrArg (fun l => l[i]?) hfst
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (show i < sortedKeys.length by omega), Option.map_some,
      Option.some.injEq] at this
    exact this
  have hp2 : ∀ i (hi : i < ranked.length), ranked[i].2 =
      rankIndexIn oks (ordinaryKey input.moleculeGraph (armGraph arm)
        (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
        (armGraph arm).width (armGraph arm).height (slots[i]'(by omega))) := by
    intro i hi
    have := congrArg (fun l => l[i]?) hranks
    simp only [hoks, List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (show i < slots.length by omega), Option.map_some,
      Option.some.injEq] at this
    exact this
  have memOks : ∀ i (hi : i < slots.length), ordinaryKey input.moleculeGraph (armGraph arm)
      (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
      (armGraph arm).width (armGraph arm).height slots[i] ∈ oks := fun i hi =>
    List.mem_map_of_mem (List.getElem_mem hi)
  have keyPerm : sortedKeys.Perm childKeys := by
    rw [sortedEq]
    exact input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys
  have keyMem : ∀ i (hi : i < sortedKeys.length), sortedKeys[i] ∈ childKeys := fun i hi =>
    keyPerm.subset (List.getElem_mem hi)
  -- the sphere as a flatMap
  have sphereEq : (localizedCumulativeRule45StepKey input .rule4a cursor
      (input.molecularReader descriptorMap target cursor) sortedKeys).rankedLabels.getD (d + 1) [] =
      ranked.flatMap fun p => OfficialRuleMajorKey.prefixLayer p.2 (p.1.rankedLabels.getD d []) := by
    show ([[([], input.molecularReader descriptorMap target cursor)]] ++
      input.mergeLocalizedRerootRankedLabelChildren sortedKeys).getD (d + 1) [] = _
    rw [List.cons_append, List.nil_append, List.getD_cons_succ,
      getD_mergeLocalizedRerootRankedLabelChildren]
  rw [sphereEq] at hfirst he
  rw [firstChiralRank_flatMap] at hfirst
  obtain ⟨i₀, hi₀, hf₀, hbefore⟩ := findSome?_eq_some_index _ ranked first hfirst
  obtain ⟨j, hj, hej⟩ := mem_flatMap_index _ ranked e he
  rw [firstChiralRank_prefixLayer, Option.map_eq_some_iff] at hf₀
  obtain ⟨b, hb, rfl⟩ := hf₀
  rw [mem_prefixLayer_iff] at hej
  obtain ⟨e', he', rfl⟩ := hej
  have hchiral' : IsChiralEntry e' := hchiral
  -- induction hypothesis at block `i₀`
  obtain ⟨child₀, hget₀, hl₀⟩ := slotGet i₀ (by omega)
  have ihb : ∀ e'' ∈ ranked[i₀].1.rankedLabels.getD d [], IsChiralEntry e'' → b ≤ e''.1 := by
    rw [hp1 i₀ hi₀]
    exact ih child₀ (sortedTrees[i₀]'(by omega)) (sortedKeys[i₀]'(by omega)) (traceAt i₀ (by omega))
      hl₀ d b (by rw [← hp1 i₀ hi₀]; exact hb)
  rcases Nat.lt_trichotomy j i₀ with hlt | rfl | hgt
  · exfalso
    have hnone := hbefore j hlt
    rw [firstChiralRank_prefixLayer, Option.map_eq_none_iff, firstChiralRank_eq_none_iff] at hnone
    exact hnone e' he' hchiral'
  · exact cons_le_cons_of_le (ihb e' he' hchiral')
  · -- ranks are nondecreasing in slot order
    have hjs : j < slots.length := by omega
    have hi₀s : i₀ < slots.length := by omega
    have keyLe : ordinaryKey input.moleculeGraph (armGraph arm)
        (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
        (armGraph arm).width (armGraph arm).height slots[j] ≤
        ordinaryKey input.moleculeGraph (armGraph arm)
          (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
          (armGraph arm).width (armGraph arm).height slots[i₀] := by
      have := (List.pairwise_iff_getElem.1 oksSorted) i₀ j (by simp [hoks]; omega)
        (by simp [hoks]; omega) hgt
      simpa [hoks] using this
    rw [hp2 i₀ hi₀, hp2 j hj]
    rcases lt_or_eq_of_le keyLe with keyLt | keyEq
    · exact cons_le_cons_of_lt (rankIndexIn_lt_of_lt (memOks i₀ hi₀s) keyLt) _ _
    · rw [keyEq]

      obtain ⟨childj, hgetj, hlj⟩ := slotGet j (by omega)
      have tie : input.compareLocalizedRerootCumulativeRule45Keys (sortedKeys[i₀]'(by omega))
          (sortedKeys[j]'(by omega)) = Ordering.eq := by
        rw [Represented.tie_iff hyp.rule4aOnly (represented i₀ (by omega) child₀ hl₀)
          (represented j (by omega) childj hlj)]
        rw [← hget₀, ← hgetj]
        exact keyEq.symm
      have proj := projected_rankedLabels_eq_of_tie descriptorMap target childKeysComputed
        (keyMem i₀ (by omega)) (keyMem j (by omega)) tie
      have projLayer : projectRule4aLayer ((sortedKeys[i₀]'(by omega)).rankedLabels.getD d []) =
          projectRule4aLayer ((sortedKeys[j]'(by omega)).rankedLabels.getD d []) := by
        rw [← getD_map_projection, ← getD_map_projection, proj]
      have hmem : (e'.1, [2]) ∈ projectRule4aLayer ((sortedKeys[i₀]'(by omega)).rankedLabels.getD d []) := by
        rw [projLayer, ← hp1 j hj]
        exact projection_mem_of_chiral _ e' he' hchiral'
      obtain ⟨e'', he'', hadd, hchiral''⟩ := exists_chiral_of_projection_mem _ _ hmem
      have hle := ihb e'' (by rw [hp1 i₀ hi₀]; exact he'') hchiral''
      rw [hadd] at hle
      exact cons_le_cons_of_le hle

/-! ## Minimality -/

/-- **The first chiral entry has the least rank address** among the chiral entries of its sphere,
at every node of an actual arm of the molecular reader. -/
theorem arm_firstChiralRank_minimal
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (arm : input.OriginalRootArm center index .rule4a (input.molecularReader descriptorMap target))
    {unit : DetectedOccurrence input.moleculeGraph} (hyp : ArmReadback arm descriptorMap unit) :
    ∀ {fuel : Nat} (node : (armGraph arm).Node)
      (dsub : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
      (key : input.LocalizedRerootCumulativeRule45Key),
      LocalizedActualRecursiveSortTrace input .rule4a (input.molecularReader descriptorMap target)
          fuel dsub key →
        arm.tree.decoratedSubtreeAt? node.1 = some dsub →
          ∀ (d : Nat) (first : List Nat), firstChiralRank (key.rankedLabels.getD d []) = some first →
            ∀ e ∈ key.rankedLabels.getD d [], IsChiralEntry e → first ≤ e.1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro node dsub key trace lookup d first hfirst e he hchiral
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren _fullMatch _realizes =>
          exact terminal_minimal d first hfirst e he
  | succ fuel ih =>
      intro node dsub key trace lookup d first hfirst e he hchiral
      rcases LocalizedActualRecursiveSortTrace.structure_of_trace trace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, children, childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, _childrenEq,
          _childrenComputed, _nonempty, childKeysComputed, sortedEq, _constitutionalDescending,
          childrenTraced⟩
      · subst dsub; subst key
        exact terminal_minimal d first hfirst e he
      · subst dsub; subst key
        exact node_minimal descriptorMap target arm hyp ih node cursor children childKeys sortedKeys
          sortedTrees childKeysComputed sortedEq childrenTraced lookup d first hfirst e he hchiral
