import TetraStereo.Certificate.WeightedDemandGraph
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
























namespace TetraStereo.Certificate.WeightedDemand

/-! ## Folding one total discovery step over a list of roots -/

/-- Fold a total discovery step while retaining every previously completed rank and all requested
vertices. The new-vertex predicate tracks a structural measure independently of computed ranks. -/
theorem fold_total {α : Type} [DecidableEq α] (g : Graph α)
    (step : Table α → α → Except (DiscoveryFailure α) (Table α))
    (newVertex : α → Prop) (roots : List α)
    (total : ∀ cursor ∈ roots, ∀ before, TableValid g before →
      ∃ after, step before cursor = .ok after ∧ TableValid g after ∧
        TableExtends before after ∧ cursor ∈ after.map Prod.fst ∧
        (∀ item ∈ after.map Prod.fst, item ∈ before.map Prod.fst ∨ newVertex item))
    (table : Table α) (valid : TableValid g table) :
    ∃ finished, roots.foldlM step table = .ok finished ∧ TableValid g finished ∧
      TableExtends table finished ∧ (∀ root ∈ roots, root ∈ finished.map Prod.fst) ∧
      (∀ item ∈ finished.map Prod.fst, item ∈ table.map Prod.fst ∨ newVertex item) := by
  induction roots generalizing table with
  | nil =>
    exact ⟨table, rfl, valid, TableExtends.refl table, by simp,
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

/-! ## DFS totality from a strictly decreasing measure -/

/-- A strictly decreasing structural measure makes the memoized DFS succeed. The measure is used
only in the proof: the runtime still discovers and checks all its own ranks. -/
theorem discover_total_of_measure {α : Type} [DecidableEq α] (g : Graph α)
    (domain : α → Prop) (measure : α → Nat)
    (decreases : ∀ cursor, domain cursor → ∀ child ∈ successors g cursor,
      domain child ∧ measure child < measure cursor) :
    ∀ budget active table cursor, TableValid g table → domain cursor →
      measure cursor < budget → (∀ ancestor ∈ active, measure cursor < measure ancestor) →
      ∃ finished, discover g budget active table cursor = .ok finished ∧
        TableValid g finished ∧ TableExtends table finished ∧
        cursor ∈ finished.map Prod.fst ∧
        (∀ item ∈ finished.map Prod.fst, item ∈ table.map Prod.fst ∨ measure item ≤ measure cursor) := by
  intro budget
  induction budget with
  | zero => intros; omega
  | succ budget ih =>
    intro active table cursor valid inDomain bounded ancestors
    by_cases known : (lookup table cursor).isSome = true
    · exact ⟨table, by simp [discover, known], valid,
        TableExtends.refl table, (lookup_isSome_iff table cursor).mp known,
        fun _ present => Or.inl present⟩
    · have fresh : cursor ∉ table.map Prod.fst := fun present =>
        known ((lookup_isSome_iff table cursor).mpr present)
      have inactive : cursor ∉ active := by
        intro present
        have impossible := ancestors cursor present
        omega
      have total : ∀ child ∈ successors g cursor, ∀ before, TableValid g before →
          ∃ after, discover g budget (cursor :: active) before child = .ok after ∧
            TableValid g after ∧ TableExtends before after ∧
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
        fold_total g (fun before child => discover g budget (cursor :: active) before child)
          (fun item => measure item < measure cursor) (successors g cursor) total table valid
      have stillFresh : cursor ∉ finished.map Prod.fst := by
        intro present
        rcases added cursor present with old | below
        · exact fresh old
        · omega
      let result := (cursor, requiredHeight g finished cursor) :: finished
      have newExtension := TableExtends.cons finished cursor
        (requiredHeight g finished cursor) stillFresh
      refine ⟨result, ?_, tableValid_cons g finished finishedValid cursor stillFresh covered,
        extension.trans newExtension, by simp [result], ?_⟩
      · simp [discover, known, inactive, folded, result]
      · intro item present
        simp only [result, List.map_cons, List.mem_cons] at present
        rcases present with rfl | present
        · exact Or.inr (Nat.le_refl _)
        · rcases added item present with old | below
          · exact Or.inl old
          · exact Or.inr below.le

/-- Every requested root is constructed with a checked table when one common structural budget
dominates a decreasing measure on the reachable domain. No computed rank is assumed. -/
theorem discoverRoots_total_of_measure {α : Type} [DecidableEq α] (g : Graph α)
    (domain : α → Prop) (measure : α → Nat)
    (decreases : ∀ cursor, domain cursor → ∀ child ∈ successors g cursor,
      domain child ∧ measure child < measure cursor)
    (budget : Nat) (roots : List α)
    (rootDomain : ∀ root ∈ roots, domain root)
    (bounded : ∀ root ∈ roots, measure root < budget) :
    ∃ table, roots.foldlM (fun known root => discover g budget [] known root) [] = .ok table ∧
      TableValid g table ∧ (∀ root ∈ roots, root ∈ table.map Prod.fst) := by
  have total : ∀ root ∈ roots, ∀ before, TableValid g before →
      ∃ after, discover g budget [] before root = .ok after ∧
        TableValid g after ∧ TableExtends before after ∧ root ∈ after.map Prod.fst ∧
        (∀ item ∈ after.map Prod.fst, item ∈ before.map Prod.fst ∨ True) := by
    intro root present before valid
    obtain ⟨after, computed, afterValid, extension, member, _⟩ :=
      discover_total_of_measure g domain measure decreases budget [] before root valid
        (rootDomain root present) (bounded root present) (by simp)
    exact ⟨after, computed, afterValid, extension, member, fun _ _ => Or.inr trivial⟩
  obtain ⟨table, computed, valid, _, covered, _⟩ :=
    fold_total g (fun known root => discover g budget [] known root) (fun _ => True) roots total []
      (by simp [TableValid])
  exact ⟨table, computed, valid, covered⟩

/-! ## Finite reachable acyclicity -/

theorem reachable_child {α : Type} (g : Graph α) (roots : List α) (cursor child : α)
    (reachable : Reachable g roots cursor) (edge : Edge g cursor child) :
    Reachable g roots child := by
  obtain ⟨root, member, path⟩ := reachable
  exact ⟨root, member, path.tail edge⟩

/-- A finite acyclic domain supplies a bounded decreasing measure independently of any proposed
rank table. This cardinal argument is proof-only and never runs during discovery. -/
theorem finiteDemandMeasure {α : Type} [Fintype α]
    (edge : α → α → Prop) (domain : α → Prop)
    (closed : ∀ parent, domain parent → ∀ child, edge parent child → domain child)
    (acyclic : ∀ parent, domain parent → ¬ Relation.TransGen edge parent parent) :
    ∃ measure : α → Nat, (∀ cursor, measure cursor ≤ Fintype.card α) ∧
      ∀ parent, domain parent → ∀ child, edge parent child →
        domain child ∧ measure child < measure parent := by
  classical
  let descendants (cursor : α) : Finset α :=
    Finset.univ.filter (fun item => Relation.ReflTransGen edge cursor item)
  refine ⟨fun cursor => (descendants cursor).card, ?_, ?_⟩
  · intro cursor
    exact Finset.card_le_card (Finset.filter_subset _ _)
  · intro parent parentDomain child childEdge
    refine ⟨closed parent parentDomain child childEdge, Finset.card_lt_card ?_⟩
    have subset : descendants child ⊆ descendants parent := by
      intro item present
      simp only [descendants, Finset.mem_filter, Finset.mem_univ, true_and] at present ⊢
      exact Relation.ReflTransGen.head childEdge present
    have self : parent ∈ descendants parent := by
      simp only [descendants, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.ReflTransGen.refl
    have absent : parent ∉ descendants child := by
      intro present
      simp only [descendants, Finset.mem_filter, Finset.mem_univ, true_and] at present
      exact acyclic parent parentDomain (Relation.TransGen.head' childEdge present)
    exact Finset.ssubset_iff_subset_ne.mpr ⟨subset, fun equal => absent (equal.symm ▸ self)⟩




theorem prepare_total_of_acyclic {α : Type} [Fintype α] [DecidableEq α] (g : Graph α)
    (roots : List α) (acyclic : Acyclic g roots) :
    ∃ plan, prepare g (Fintype.card α + 1) roots = .ok plan := by
  obtain ⟨measure, measureBound, decreases⟩ :=
    finiteDemandMeasure (Edge g) (Reachable g roots)
      (fun parent reachable child edge => reachable_child g roots parent child reachable edge) acyclic
  let budget := Fintype.card α + 1
  obtain ⟨table, computed, valid, covered⟩ :=
    discoverRoots_total_of_measure g (Reachable g roots) measure decreases budget roots
      (fun root present => ⟨root, present, Relation.ReflTransGen.refl⟩)
      (fun root _ => by
        have bounded := measureBound root
        dsimp [budget]
        omega)
  let ranks : RankCertificate g := certificateOfValid g table valid
  let plan : Plan g roots := { ranks, covers := covered }
  refine ⟨plan, ?_⟩
  dsimp [budget] at computed
  simp only [prepare, computed, check?_of_valid g table valid, bind, Except.bind, ranks, plan]
  have hcovers : ∀ root ∈ roots, root ∈ (certificateOfValid g table valid).vertices := covered
  rw [dif_pos hcovers]

/-! ## Exactness: success iff acyclic -/



theorem prepare_success_iff_acyclic {α : Type} [Fintype α] [DecidableEq α] (g : Graph α)
    (roots : List α) :
    (∃ plan, prepare g (Fintype.card α + 1) roots = .ok plan) ↔ Acyclic g roots := by
  exact ⟨fun ⟨plan, _⟩ => plan.acyclic, prepare_total_of_acyclic g roots⟩

/-- Graph rejection has a concrete mathematical cause: a reachable cycle in the conservative
potential-demand graph. -/
theorem prepare_error_has_cycle {α : Type} [Fintype α] [DecidableEq α] (g : Graph α)
    (roots : List α) (failure : DiscoveryFailure α)
    (failed : prepare g (Fintype.card α + 1) roots = .error failure) :
    ∃ cursor, Reachable g roots cursor ∧ Relation.TransGen (Edge g) cursor cursor := by
  classical
  by_contra absent
  have acyclic : Acyclic g roots := by
    intro cursor reachable cycle
    exact absent ⟨cursor, reachable, cycle⟩
  obtain ⟨plan, succeeds⟩ := prepare_total_of_acyclic g roots acyclic
  rw [failed] at succeeds
  contradiction

end TetraStereo.Certificate.WeightedDemand
