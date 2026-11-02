import TetraStereo.KernelOnly
import TetraStereo.OneCenter.LocalizedPreflightDemandTotality
import TetraStereo.OneCenter.LocalizedAxialRootPerception

set_option autoImplicit false




















































namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand

/-! ## The independent input-graph domain -/

/-- **The unbranched input domain.**  Every atom of the certified molecule carries at most two
physical order-two neighbours.  This is a graph fact (`localizedOrderTwoNeighbors` is a filtered
sorted neighbour finset), independent of demand discovery, rank tables and evaluation outcomes. -/
def UnbranchedDoubleBondInput (input : CertifiedLocalizedCIPInput) : Prop :=
  ∀ atom : input.Atom, (input.localizedOrderTwoNeighbors atom).length ≤ 2

/-- The unbranched domain is decidable: it is a finite conjunction of length comparisons. -/
instance unbranchedDoubleBondInputDecidable (input : CertifiedLocalizedCIPInput) :
    Decidable input.UnbranchedDoubleBondInput := by
  unfold UnbranchedDoubleBondInput
  infer_instance

/-- Three distinct members force length at least three.  Used to certify that the concrete
branched fixture violates the unbranched domain. -/
theorem three_le_length_of_nodup_of_mem {α : Type} [DecidableEq α] {values : List α}
    (nodup : values.Nodup) {first second third : α}
    (firstPresent : first ∈ values) (secondPresent : second ∈ values)
    (thirdPresent : third ∈ values)
    (firstSecond : first ≠ second) (firstThird : first ≠ third)
    (secondThird : second ≠ third) :
    3 ≤ values.length := by
  rw [← List.toFinset_card_of_nodup nodup]
  have subset : ({first, second, third} : Finset α) ⊆ values.toFinset := by
    intro item present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl | rfl
    · simpa using firstPresent
    · simpa using secondPresent
    · simpa using thirdPresent
  have firstNot : first ∉ ({second, third} : Finset α) := by
    simp [firstSecond, firstThird]
  have secondNot : second ∉ ({third} : Finset α) := by
    simp [secondThird]
  have cardThree : ({first, second, third} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem firstNot,
      Finset.card_insert_of_notMem secondNot, Finset.card_singleton]
  have bounded := Finset.card_le_card subset
  omega

/-! ## The rank witness: published sibling interface -/











structure UnbranchedDemandRank (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (g : Graph (input.LocalizedRerootCursor fuel)) : Type where
  /-- Admission: the input graph is unbranched. -/
  unbranched : input.UnbranchedDoubleBondInput
  /-- Admission: every requested root is an actual valid cursor. -/
  rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root
  /-- The closed domain on which the measure decreases. -/
  domain : input.LocalizedRerootCursor fuel → Prop
  /-- The strictly decreasing natural measure (the sibling rank). -/
  measure : input.LocalizedRerootCursor fuel → Nat
  /-- Every requested root belongs to the domain. -/
  rootDomain : ∀ root ∈ roots, domain root
  /-- Every actual successor of a domain cursor stays in the domain and strictly decreases. -/
  decreases : ∀ cursor, domain cursor → ∀ child ∈ successors g cursor,
    domain child ∧ measure child < measure cursor

/-- Admission facts carried by a rank witness. -/
theorem UnbranchedDemandRank.admission
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    {g : Graph (input.LocalizedRerootCursor fuel)}
    (rank : input.UnbranchedDemandRank roots g) :
    input.UnbranchedDoubleBondInput ∧
      (∀ root ∈ roots, input.LocalizedRerootCursorValid root) :=
  ⟨rank.unbranched, rank.rootValid⟩

/-- A decreasing rank witness makes the reachable part of its weighted demand graph acyclic.
This is the generic core; `acyclic_reachable_of_decreasing` is the existing relation-generic
theorem and `Edge g` is definitionally membership in `successors g`. -/
theorem acyclic_of_unbranchedDemandRank
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    {g : Graph (input.LocalizedRerootCursor fuel)}
    (rank : input.UnbranchedDemandRank roots g) :
    Acyclic g roots := by
  refine acyclic_reachable_of_decreasing (Edge g) roots rank.domain rank.measure
    rank.rootDomain ?_
  intro parent inDomain child edge
  exact rank.decreases parent inDomain child edge

/-! ## The actual extended demand graph -/

/-- The rank witness specialized to the concrete extended graph
`extendedWeightedDemandGraph` (executable cut-neighborhood children weight one, extended endpoint
requests weight two). -/
abbrev UnbranchedExtendedDemandRank (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (roots : List (input.LocalizedRerootCursor fuel)) : Type :=
  input.UnbranchedDemandRank (fuel := fuel) roots (input.extendedWeightedDemandGraph fuel)

/-- Extended-graph acyclicity from the sibling rank.  No acyclicity hypothesis is taken. -/
theorem unbranchedExtendedDemandAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedExtendedDemandRank fuel roots) :
    input.ExtendedRule3DemandAcyclic roots :=
  (input.extendedWeightedDemandGraph_acyclic fuel roots).mp
    (acyclic_of_unbranchedDemandRank input rank)

/-- Generic weighted-graph acyclicity of the actual extended instantiation, from the same rank. -/
theorem unbranchedExtendedWeightedDemandAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedExtendedDemandRank fuel roots) :
    Acyclic (input.extendedWeightedDemandGraph fuel) roots :=
  acyclic_of_unbranchedDemandRank input rank

/-- **DFS-level totality.**  The actual executable
`discoverExtendedRule3DemandRanks` succeeds on all roots of the unbranched domain, provided the
sibling measure is bounded by the chosen budget at the roots.  This is
`discoverExtendedRule3DemandRanks_total_of_measure` instantiated with the witness; the runtime
still discovers and checks every rank itself. -/
theorem unbranchedExtendedDemandDiscover_total
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedExtendedDemandRank fuel roots)
    (budget : Nat)
    (bounded : ∀ root ∈ roots, rank.measure root < budget) :
    ∃ table,
      roots.foldlM (fun known root =>
        input.discoverExtendedRule3DemandRanks budget [] known root) [] = .ok table ∧
      input.ExtendedRule3DemandRankTableValid table ∧
      (∀ root ∈ roots, root ∈ table.map Prod.fst) := by
  refine input.discoverExtendedRule3DemandRoots_total_of_measure rank.domain rank.measure
    ?_ budget roots rank.rootDomain bounded
  intro cursor inDomain child present
  exact rank.decreases cursor inDomain child present




theorem unbranchedExtendedDemandPlan_total
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedExtendedDemandRank fuel roots) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan :=
  input.prepareExtendedRule3DemandPlan_total_of_acyclic roots
    (input.unbranchedExtendedDemandAcyclic roots rank)





theorem unbranchedExtendedDemandPlan_noCycleError
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedExtendedDemandRank fuel roots) :
    ∀ cursor, input.prepareExtendedRule3DemandPlan roots ≠ .error (.cycle cursor) := by
  intro cursor failed
  obtain ⟨plan, succeeds⟩ := input.unbranchedExtendedDemandPlan_total roots rank
  rw [succeeds] at failed
  cases failed

/-- Stronger form: on the unbranched domain the constructor returns no error at all. -/
theorem unbranchedExtendedDemandPlan_noError
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedExtendedDemandRank fuel roots)
    (failure : input.Rule3DemandDiscoveryFailure fuel) :
    input.prepareExtendedRule3DemandPlan roots ≠ .error failure := by
  intro failed
  obtain ⟨plan, succeeds⟩ := input.unbranchedExtendedDemandPlan_total roots rank
  rw [succeeds] at failed
  cases failed


theorem ExtendedRule3DemandPlan.toWeightedPlan_bound
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots) :
    plan.toWeightedPlan.bound = plan.bound := by
  show listHeight plan.ranks.height roots + 1 =
    rule3CursorListHeight plan.ranks.height roots + 1
  rw [weightedListHeight_eq_rule3CursorListHeight]












theorem unbranchedExtendedDemandTotality
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedExtendedDemandRank fuel roots) :
    ∃ plan : input.ExtendedRule3DemandPlan roots,
      input.prepareExtendedRule3DemandPlan roots = .ok plan ∧
      input.ExtendedRule3DemandAcyclic roots ∧
      Acyclic (input.extendedWeightedDemandGraph fuel) roots ∧
      (∀ root ∈ roots, root ∈ plan.ranks.vertices) ∧
      plan.bound = rule3CursorListHeight plan.ranks.height roots + 1 ∧
      plan.toWeightedPlan.bound = plan.bound ∧
      (∀ (target : input.LocalizedCIPOccurrence fuel)
        (view : input.LocalizedDependencyView target) (budget : Nat),
        plan.bound ≤ budget →
          plan.evaluate target view =
            input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget roots) ∧
      (∀ (target : input.LocalizedCIPOccurrence fuel)
        (view : input.LocalizedDependencyView target)
        (frame : input.LocalizedRule3CanonicalKeyFrame),
        plan.evaluate target view = some frame →
          input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view plan.bound roots
            frame) := by
  obtain ⟨plan, succeeds⟩ := input.unbranchedExtendedDemandPlan_total roots rank
  have acyclic := input.unbranchedExtendedDemandAcyclic roots rank
  exact ⟨plan, succeeds, acyclic,
    (input.extendedWeightedDemandGraph_acyclic fuel roots).mp acyclic,
    plan.covers, rfl, ExtendedRule3DemandPlan.toWeightedPlan_bound plan,
    fun target view budget enough => plan.evaluate_eq_above target view budget enough,
    fun target view frame computed => plan.evaluate_sound target view frame computed⟩

/-! ## Preflight-pruned demand discovery -/

/-- The rank witness specialized to the preflight-pruned graph.  It may be supplied directly by
the sibling, or derived from the extended witness because the preflight graph only removes edges. -/
abbrev UnbranchedPreflightDemandRank (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (roots : List (input.LocalizedRerootCursor fuel)) : Type :=
  input.UnbranchedDemandRank (fuel := fuel) roots
    (input.preflightExtendedWeightedDemandGraph fuel)

/-- Preflight-graph acyclicity from a preflight-specific rank witness. -/
theorem unbranchedPreflightAcyclic_of_rank
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedPreflightDemandRank fuel roots) :
    Acyclic (input.preflightExtendedWeightedDemandGraph fuel) roots :=
  acyclic_of_unbranchedDemandRank input rank

/-- Preflight-graph acyclicity from the extended rank witness (edge removal preserves
acyclicity). -/
theorem unbranchedPreflightAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedExtendedDemandRank fuel roots) :
    Acyclic (input.preflightExtendedWeightedDemandGraph fuel) roots :=
  input.preflightExtendedWeightedDemandAcyclic_of_extended roots
    (input.unbranchedExtendedDemandAcyclic roots rank)



theorem unbranchedPreflightPlan_total
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedExtendedDemandRank fuel roots) :
    ∃ plan, input.preparePreflightExtendedDemandPlan roots = .ok plan :=
  input.preparePreflightExtendedDemandPlan_total_of_acyclic roots
    (input.unbranchedPreflightAcyclic roots rank)


theorem unbranchedPreflightPlan_total_of_rank
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedPreflightDemandRank fuel roots) :
    ∃ plan, input.preparePreflightExtendedDemandPlan roots = .ok plan :=
  input.preparePreflightExtendedDemandPlan_total_of_acyclic roots
    (input.unbranchedPreflightAcyclic_of_rank roots rank)

/-- **No cycle error for the preflight constructor.**  The fixed structural budget never produces
a cycle refusal on the unbranched domain. -/
theorem unbranchedPreflightPlan_noCycleError
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedExtendedDemandRank fuel roots) :
    ∀ cursor, input.preparePreflightExtendedDemandPlan roots ≠ .error (.cycle cursor) := by
  intro cursor failed
  obtain ⟨plan, succeeds⟩ := input.unbranchedPreflightPlan_total roots rank
  rw [succeeds] at failed
  cases failed

/-- Stronger preflight form: no error at all on the unbranched domain. -/
theorem unbranchedPreflightPlan_noError
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedExtendedDemandRank fuel roots)
    (failure : DiscoveryFailure (input.LocalizedRerootCursor fuel)) :
    input.preparePreflightExtendedDemandPlan roots ≠ .error failure := by
  intro failed
  obtain ⟨plan, succeeds⟩ := input.unbranchedPreflightPlan_total roots rank
  rw [succeeds] at failed
  cases failed



theorem unbranchedPreflightTotality
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rank : input.UnbranchedExtendedDemandRank fuel roots)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    ∃ plan : Plan (input.preflightExtendedWeightedDemandGraph fuel) roots,
      input.preparePreflightExtendedDemandPlan roots = .ok plan ∧
      Acyclic (input.preflightExtendedWeightedDemandGraph fuel) roots ∧
      (∀ root ∈ roots, root ∈ plan.ranks.vertices) ∧
      plan.bound = listHeight plan.ranks.height roots + 1 ∧
      (∀ budget, plan.bound ≤ budget →
        preflightExtendedDemandEvaluate plan target view =
          input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget roots) ∧
      (∀ frame, preflightExtendedDemandEvaluate plan target view = some frame →
        input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view plan.bound roots
          frame) := by
  obtain ⟨plan, succeeds⟩ := input.unbranchedPreflightPlan_total roots rank
  exact ⟨plan, succeeds, input.unbranchedPreflightAcyclic roots rank, plan.covers, rfl,
    fun budget enough => preflightExtendedDemandEvaluate_eq_above plan target view budget enough,
    fun frame computed => preflightExtendedDemandEvaluate_sound plan target view frame computed⟩

/-! ## The exact remaining semantic interface

Discovery totality and the computed fuel bound say nothing about whether the evaluator finds a
frame.  The next definitions and theorems isolate that obligation exactly. -/




def ExtendedDemandFrameExistsAt (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel)) (budget : Nat) : Prop :=
  ∃ frame : input.LocalizedRule3CanonicalKeyFrame,
    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget roots = some frame


theorem extendedDemandFrameExistsAt_iff_evaluate
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    input.ExtendedDemandFrameExistsAt target view roots plan.bound ↔
      ∃ frame, plan.evaluate target view = some frame :=
  Iff.rfl

/-- Refusal is exactly the negation of the semantic obligation. -/
theorem extendedDemandEvaluate_refusal_iff
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    (¬ ∃ frame, plan.evaluate target view = some frame) ↔
      plan.evaluate target view = none := by
  constructor
  · intro absent
    cases computed : plan.evaluate target view with
    | none => rfl
    | some frame => exact (absent ⟨frame, computed⟩).elim
  · rintro none ⟨frame, computed⟩
    rw [none] at computed
    cases computed

/-- A successful evaluation yields both the semantic obligation at the discovered bound and its
declarative frame meaning. -/
theorem extendedDemandFrame_of_evaluate_some
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : plan.evaluate target view = some frame) :
    input.ExtendedDemandFrameExistsAt target view roots plan.bound ∧
      input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view plan.bound roots frame :=
  ⟨⟨frame, computed⟩, plan.evaluate_sound target view frame computed⟩

/-- **Semantic closure at an independent budget.**  If the evaluator returns a frame at any budget
above the discovered bound, then it returns that frame at the discovered bound as well, and the
frame has the declarative extended short-circuit meaning there.  This isolates the only remaining
semantic premise; it is not derived from termination or from the unbranched graph domain. -/
theorem extendedDemandFrame_of_exists_at_budget
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (budget : Nat) (enough : plan.bound ≤ budget)
    (frameAt : input.ExtendedDemandFrameExistsAt target view roots budget) :
    ∃ frame, plan.evaluate target view = some frame ∧
      input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view plan.bound roots frame := by
  obtain ⟨frame, computed⟩ := frameAt
  have stable := plan.evaluate_eq_above target view budget enough
  have evalSome : plan.evaluate target view = some frame := stable.trans computed
  exact ⟨frame, evalSome, plan.evaluate_sound target view frame evalSome⟩

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput











namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- **Graph-side exclusion.**  Three distinct physical order-two neighbours at one atom put the
input outside `UnbranchedDoubleBondInput`.  All three premises are concrete bond facts
(`moleculeGraph.bond atom neighbor = 2`), i.e. scientific input-graph facts. -/
theorem not_unbranched_of_three_orderTwoNeighbors
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {first second third : input.Atom}
    (firstBond : input.moleculeGraph.bond atom first = 2)
    (secondBond : input.moleculeGraph.bond atom second = 2)
    (thirdBond : input.moleculeGraph.bond atom third = 2)
    (firstSecond : first ≠ second) (firstThird : first ≠ third)
    (secondThird : second ≠ third) :
    ¬ input.UnbranchedDoubleBondInput := by
  intro unbranched
  have long : 3 ≤ (input.localizedOrderTwoNeighbors atom).length :=
    three_le_length_of_nodup_of_mem (input.localizedOrderTwoNeighbors_nodup atom)
      ((input.mem_localizedOrderTwoNeighbors_iff atom first).mpr firstBond)
      ((input.mem_localizedOrderTwoNeighbors_iff atom second).mpr secondBond)
      ((input.mem_localizedOrderTwoNeighbors_iff atom third).mpr thirdBond)
      firstSecond firstThird secondThird
  exact absurd (unbranched atom) (by omega)

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput




































assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.three_le_length_of_nodup_of_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.acyclic_of_unbranchedDemandRank
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedExtendedDemandAcyclic
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedExtendedDemandDiscover_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedExtendedDemandPlan_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedExtendedDemandPlan_noCycleError
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedExtendedDemandTotality
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedPreflightPlan_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedPreflightPlan_noCycleError
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedPreflightTotality
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandFrame_of_exists_at_budget
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.not_unbranched_of_three_orderTwoNeighbors
