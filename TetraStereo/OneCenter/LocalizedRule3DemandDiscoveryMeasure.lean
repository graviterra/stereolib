import TetraStereo.OneCenter.LocalizedRule3DemandRankTable

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Fold a total discovery step while retaining every previously completed rank and all requested
vertices. The new-vertex predicate tracks a structural measure independently of computed ranks. -/
theorem rule3DemandFold_total
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (step : input.Rule3DemandRankTable fuel → input.LocalizedRerootCursor fuel →
      Except (input.Rule3DemandDiscoveryFailure fuel) (input.Rule3DemandRankTable fuel))
    (newVertex : input.LocalizedRerootCursor fuel → Prop)
    (roots : List (input.LocalizedRerootCursor fuel))
    (total : ∀ cursor ∈ roots, ∀ before, input.Rule3DemandRankTableValid before →
      ∃ after, step before cursor = .ok after ∧ input.Rule3DemandRankTableValid after ∧
        Rule3DemandTableExtends before after ∧ cursor ∈ after.map Prod.fst ∧
        (∀ item ∈ after.map Prod.fst, item ∈ before.map Prod.fst ∨ newVertex item))
    (table : input.Rule3DemandRankTable fuel) (valid : input.Rule3DemandRankTableValid table) :
    ∃ finished, roots.foldlM step table = .ok finished ∧ input.Rule3DemandRankTableValid finished ∧
      Rule3DemandTableExtends table finished ∧ (∀ root ∈ roots, root ∈ finished.map Prod.fst) ∧
      (∀ item ∈ finished.map Prod.fst, item ∈ table.map Prod.fst ∨ newVertex item) := by
  induction roots generalizing table with
  | nil =>
    exact ⟨table, rfl, valid, Rule3DemandTableExtends.refl table, by simp,
      fun _ present => Or.inl present⟩
  | cons first rest ih =>
    obtain ⟨middle, firstDone, middleValid, firstExtension, firstPresent, firstNew⟩ :=
      total first (by simp) table valid
    obtain ⟨finished, restDone, finishedValid, restExtension, restCovered, restNew⟩ :=
      ih (fun cursor present => total cursor (by simp [present])) middle middleValid
    refine ⟨finished, ?_, finishedValid, firstExtension.trans restExtension, ?_, ?_⟩
    · simp [List.foldlM_cons, firstDone, bind, Except.bind, restDone]
    · intro cursor present
      rcases List.mem_cons.mp present with equal | present
      · subst cursor
        exact (restExtension first firstPresent).1
      · exact restCovered cursor present
    · intro cursor present
      rcases restNew cursor present with earlier | new
      · exact firstNew cursor earlier
      · exact Or.inr new

/-- A strictly decreasing structural measure makes the existing memoized DFS succeed. The
measure is used only in the proof: the runtime still discovers and checks all its own ranks. -/
theorem discoverRule3DemandRanks_total_of_measure
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (domain : input.LocalizedRerootCursor fuel → Prop) (measure : input.LocalizedRerootCursor fuel → Nat)
    (decreases : ∀ cursor, domain cursor → ∀ child ∈ input.rule3DemandSuccessors cursor,
      domain child ∧ measure child < measure cursor) :
    ∀ budget active table cursor, input.Rule3DemandRankTableValid table → domain cursor →
      measure cursor < budget → (∀ ancestor ∈ active, measure cursor < measure ancestor) →
      ∃ finished, input.discoverRule3DemandRanks budget active table cursor = .ok finished ∧
        input.Rule3DemandRankTableValid finished ∧ Rule3DemandTableExtends table finished ∧
        cursor ∈ finished.map Prod.fst ∧
        (∀ item ∈ finished.map Prod.fst, item ∈ table.map Prod.fst ∨ measure item ≤ measure cursor) := by
  intro budget
  induction budget with
  | zero => intros; omega
  | succ budget ih =>
    intro active table cursor valid inDomain bounded ancestors
    by_cases known : (rule3DemandTableLookup table cursor).isSome = true
    · exact ⟨table, by simp [discoverRule3DemandRanks, known], valid,
        Rule3DemandTableExtends.refl table, (rule3DemandTableLookup_isSome_iff table cursor).mp known,
        fun _ present => Or.inl present⟩
    · have fresh : cursor ∉ table.map Prod.fst := fun present =>
        known ((rule3DemandTableLookup_isSome_iff table cursor).mpr present)
      have inactive : cursor ∉ active := by
        intro present
        have impossible := ancestors cursor present
        omega
      have total : ∀ child ∈ input.rule3DemandSuccessors cursor, ∀ before,
          input.Rule3DemandRankTableValid before →
          ∃ after, input.discoverRule3DemandRanks budget (cursor :: active) before child = .ok after ∧
            input.Rule3DemandRankTableValid after ∧ Rule3DemandTableExtends before after ∧
            child ∈ after.map Prod.fst ∧
            (∀ item ∈ after.map Prod.fst, item ∈ before.map Prod.fst ∨ measure item < measure cursor) := by
        intro child present before beforeValid
        obtain ⟨childDomain, childBelow⟩ := decreases cursor inDomain child present
        have childAncestors : ∀ ancestor ∈ cursor :: active, measure child < measure ancestor := by
          intro ancestor present
          rcases List.mem_cons.mp present with rfl | present
          · exact childBelow
          · exact childBelow.trans (ancestors ancestor present)
        obtain ⟨after, computed, afterValid, extension, member, added⟩ :=
          ih (cursor :: active) before child beforeValid childDomain (by omega) childAncestors
        refine ⟨after, computed, afterValid, extension, member, ?_⟩
        intro item present
        rcases added item present with old | below
        · exact Or.inl old
        · exact Or.inr (below.trans_lt childBelow)
      obtain ⟨finished, folded, finishedValid, extension, covered, added⟩ :=
        input.rule3DemandFold_total
          (fun before child => input.discoverRule3DemandRanks budget (cursor :: active) before child)
          (fun item => measure item < measure cursor) (input.rule3DemandSuccessors cursor) total table valid
      have stillFresh : cursor ∉ finished.map Prod.fst := by
        intro present
        rcases added cursor present with old | below
        · exact fresh old
        · omega
      let result := (cursor, input.rule3DemandRequiredHeight finished cursor) :: finished
      have newExtension := rule3DemandTableExtends_cons finished cursor
        (input.rule3DemandRequiredHeight finished cursor) stillFresh
      refine ⟨result, ?_, input.rule3DemandRankTableValid_cons finished finishedValid cursor stillFresh covered,
        extension.trans newExtension, by simp [result], ?_⟩
      · simp [discoverRule3DemandRanks, known, inactive, folded, result]
      · intro item present
        simp only [result, List.map_cons, List.mem_cons] at present
        rcases present with rfl | present
        · exact Or.inr (Nat.le_refl _)
        · rcases added item present with old | below
          · exact Or.inl old
          · exact Or.inr below.le

/-- Every requested root is constructed with a checked table when one common structural budget
dominates a decreasing measure on the reachable domain. No computed rank is assumed. -/
theorem discoverRule3DemandRoots_total_of_measure
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (domain : input.LocalizedRerootCursor fuel → Prop) (measure : input.LocalizedRerootCursor fuel → Nat)
    (decreases : ∀ cursor, domain cursor → ∀ child ∈ input.rule3DemandSuccessors cursor,
      domain child ∧ measure child < measure cursor)
    (budget : Nat) (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ root ∈ roots, domain root)
    (bounded : ∀ root ∈ roots, measure root < budget) :
    ∃ table, roots.foldlM (fun known root => input.discoverRule3DemandRanks budget [] known root) [] = .ok table ∧
      input.Rule3DemandRankTableValid table ∧ (∀ root ∈ roots, root ∈ table.map Prod.fst) := by
  have total : ∀ root ∈ roots, ∀ before, input.Rule3DemandRankTableValid before →
      ∃ after, input.discoverRule3DemandRanks budget [] before root = .ok after ∧
        input.Rule3DemandRankTableValid after ∧ Rule3DemandTableExtends before after ∧
        root ∈ after.map Prod.fst ∧ (∀ item ∈ after.map Prod.fst, item ∈ before.map Prod.fst ∨ True) := by
    intro root present before valid
    obtain ⟨after, computed, afterValid, extension, member, _⟩ :=
      input.discoverRule3DemandRanks_total_of_measure domain measure decreases budget [] before root valid
        (rootDomain root present) (bounded root present) (by simp)
    exact ⟨after, computed, afterValid, extension, member, fun _ _ => Or.inr trivial⟩
  obtain ⟨table, computed, valid, _, covered, _⟩ :=
    input.rule3DemandFold_total _ (fun _ => True) roots total [] (by simp [Rule3DemandRankTableValid])
  exact ⟨table, computed, valid, covered⟩

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
