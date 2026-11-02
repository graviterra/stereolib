import TetraStereo.OneCenter.LocalizedRule3DemandDiscoveryMeasure
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- The exact occurrence/cut identity of a cursor. -/
def localizedRerootCursorEquiv (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedRerootCursor fuel ≃
      input.LocalizedCIPOccurrence fuel × Option (input.LocalizedCIPOccurrence fuel) where
  toFun cursor := (cursor.occurrence, cursor.previous?)
  invFun pair := { occurrence := pair.1, previous? := pair.2 }
  left_inv cursor := by cases cursor; rfl
  right_inv pair := by cases pair; rfl

/-- Finite carrier instances are used only to justify discovery's numerical budget. The runtime
does not enumerate all occurrence/cut pairs. -/
def localizedOccurrenceFintype (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    Fintype (input.LocalizedCIPOccurrence fuel) :=
  Fintype.ofList (input.localizedOccurrenceCarrier fuel) (input.localizedOccurrenceCarrier_complete fuel)

def localizedRerootCursorFintype (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    Fintype (input.LocalizedRerootCursor fuel) :=
  letI := input.localizedOccurrenceFintype fuel
  Fintype.ofEquiv _ (input.localizedRerootCursorEquiv fuel).symm

theorem localizedRerootCursor_card (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    [Fintype (input.LocalizedRerootCursor fuel)] :
    Fintype.card (input.LocalizedRerootCursor fuel) =
      (input.localizedOccurrenceCarrier fuel).length * ((input.localizedOccurrenceCarrier fuel).length + 1) := by
  letI := input.localizedOccurrenceFintype fuel
  have occurrenceCard : Fintype.card (input.LocalizedCIPOccurrence fuel) =
      (input.localizedOccurrenceCarrier fuel).length := by
    change (input.localizedOccurrenceCarrier fuel).toFinset.card = _
    exact List.toFinset_card_of_nodup (input.localizedOccurrenceCarrier_nodup fuel)
  rw [Fintype.card_congr (input.localizedRerootCursorEquiv fuel), Fintype.card_prod,
    Fintype.card_option, occurrenceCard]

def Rule3DemandEdge (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (parent child : input.LocalizedRerootCursor fuel) : Prop :=
  child ∈ input.rule3DemandSuccessors parent

def Rule3DemandReachable (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) (cursor : input.LocalizedRerootCursor fuel) : Prop :=
  ∃ root ∈ roots, Relation.ReflTransGen input.Rule3DemandEdge root cursor

/-- Only the graph reachable from the requested frame must be acyclic. Other molecular cursors
and unused occurrence/cut pairs impose no condition. -/
def Rule3DemandAcyclic (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) : Prop :=
  ∀ cursor, input.Rule3DemandReachable roots cursor → ¬ Relation.TransGen input.Rule3DemandEdge cursor cursor

theorem rule3DemandReachable_child (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) (cursor child : input.LocalizedRerootCursor fuel)
    (reachable : input.Rule3DemandReachable roots cursor) (edge : input.Rule3DemandEdge cursor child) :
    input.Rule3DemandReachable roots child := by
  obtain ⟨root, member, path⟩ := reachable
  exact ⟨root, member, path.tail edge⟩

/-- A finite acyclic reachable graph supplies a bounded decreasing measure independently of any
proposed rank table. This cardinal argument is proof-only and never runs during discovery. -/
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




theorem prepareRule3DemandPlan_total_of_acyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) (acyclic : input.Rule3DemandAcyclic roots) :
    ∃ plan, input.prepareRule3DemandPlan roots = .ok plan := by
  letI := input.localizedRerootCursorFintype fuel
  obtain ⟨measure, measureBound, decreases⟩ :=
    finiteDemandMeasure input.Rule3DemandEdge (input.Rule3DemandReachable roots)
      (fun parent reachable child edge => input.rule3DemandReachable_child roots parent child reachable edge) acyclic
  let budget := (input.localizedOccurrenceCarrier fuel).length *
    ((input.localizedOccurrenceCarrier fuel).length + 1) + 1
  obtain ⟨table, computed, valid, covered⟩ :=
    input.discoverRule3DemandRoots_total_of_measure (input.Rule3DemandReachable roots) measure decreases budget roots
      (fun root present => ⟨root, present, Relation.ReflTransGen.refl⟩)
      (fun root _ => by
        have bounded := measureBound root
        rw [input.localizedRerootCursor_card fuel] at bounded
        dsimp [budget]
        omega)
  let ranks : input.Rule3DemandRankCertificate fuel :=
    { vertices := table.map Prod.fst, height := rule3DemandTableHeight table,
      positive := valid.1, children := valid.2.1, callbacks := valid.2.2 }
  let plan : input.Rule3DemandPlan roots := { ranks, covers := covered }
  refine ⟨plan, ?_⟩
  dsimp [budget] at computed
  simp [prepareRule3DemandPlan, computed, bind, Except.bind,
    checkRule3DemandRanks?, valid, ranks, plan]
  rw [dif_pos covered]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
