import TetraStereo.OneCenter.ConstitutionalRootStageAvailability
import TetraStereo.OneCenter.RawFramedConstitutionalFuelStability
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Raw framed demand dependency

This module pins down exactly which auxiliary-occurrence facts the *actual* raw framed
evaluator (`FrameRuntime.decisionComplete?`) reads after the strict constitutional
short-circuit fails to separate a pair, and it exhibits a concrete re-based frame where,
after a constitutional tie, the complete decision is state sensitive.

The read boundary is determined by tracing the actual comparator, not by an abstract
desired-answer model:

* a *strict* actual constitutional result (`compareBranch? ... .rule2` returns `lt`/`gt`)
  short-circuits before any state read (already proved in
  `RawFramedConstitutionalIndependence`);
* a constitutional tie against the *empty* state returns the tie without reading any
  occurrence (`decisionComplete?_empty_state` below);
* a constitutional tie against a *nonempty* state enters the descriptor rules.  The Rule-4a
  comparison (`compareDescriptorAtTiedRoot? ... .rule4a`) reads the auxiliary state only
  through `occurrenceNodePriority`, hence only through `state.factAt?` at the two compared
  nodes; if that first sphere is decisive, the whole complete decision is a function of
  exactly those two occurrence-local reads plus the emptiness of the state
  (`decisionComplete?_congr_of_tied_rule4a_decisive` below);
* deeper ties continue into Rule 4b / Rule 4c / Rule 5, which read `state.factAt?` at the
  expanded descriptor subtree and the whole-state predicates `state.isEmpty` and
  `state.any (fun fact => !fact.uppercase)`.  That parent dependence is the *residual* region
  left to `Rule4bReferenceDependencyAudit`; it is characterized, not solved, here.

The actual molecular witness is the C0 re-based frame of
`ConstitutionalRootStageAvailability` over `C[C@@H](Cl)[C@@H]([C@H](Cl)C)Br`: its two arms
`c2ArmCursor`/`c3ArmCursor` tie constitutionally, so the strict short-circuit cannot fire,
and the empty state ties while the real batch state `[c3Fact]` separates by Rule 4a.  The
two states differ on the C3 arm occurrence read, which is an allowed deeper read; this is
state sensitivity, not an insufficiency of the constitutional depth.  C0's own production
fact `c0AuxFact` is present in the production state but is not read by this comparison:
presence-without-demand, not a dependency cycle.
-/

namespace TetraStereo
namespace OneCenter
namespace RawFramedDemandDependency

open RawMolecule
open ConstitutionalRootStageAvailability

/-! ## A. Occurrence-local auxiliary reads -/

/-- `occurrenceNodePriority` reads the auxiliary state only at the single occurrence key of
the cursor it is asked about.  If two states carry the same fact at `cursor.node`, the
priority is the same. -/
theorem occurrenceNodePriority_congr
    (state₁ state₂ : OccurrenceAuxState) (stage : RawDescriptorRuleStage) (leftSide : Bool)
    (cursor : CanonicalRerootCursor)
    (h : state₁.factAt? cursor.node = state₂.factAt? cursor.node) :
    occurrenceNodePriority state₁ stage leftSide cursor =
      occurrenceNodePriority state₂ stage leftSide cursor := by
  simp [occurrenceNodePriority, h]

/-- The Rule-4c carrier projection likewise reads only the single occurrence key of its
cursor. -/
theorem occurrenceRule4cCarrierAt?_congr
    (state₁ state₂ : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (h : state₁.factAt? cursor.node = state₂.factAt? cursor.node) :
    occurrenceRule4cCarrierAt? state₁ cursor = occurrenceRule4cCarrierAt? state₂ cursor := by
  simp [occurrenceRule4cCarrierAt?, h]

/-- The pure first-sphere descriptor label comparison reads the state only at the original
occurrence nodes of the compared cursors.  Agreement of the fact at every such node forces
the label comparison to agree. -/
theorem compareDescriptorPairLabels_congr
    (mol : RawMolecule) (state₁ state₂ : OccurrenceAuxState) (stage : RawDescriptorRuleStage)
    (pairs : List (FrameRuntime.Cursor × FrameRuntime.Cursor))
    (h : ∀ lft rgt, (lft, rgt) ∈ pairs →
      state₁.factAt? (lft.original mol).node = state₂.factAt? (lft.original mol).node ∧
      state₁.factAt? (rgt.original mol).node = state₂.factAt? (rgt.original mol).node) :
    FrameRuntime.compareDescriptorPairLabels mol state₁ stage pairs =
      FrameRuntime.compareDescriptorPairLabels mol state₂ stage pairs := by
  revert h
  induction pairs with
  | nil => intro _; rfl
  | cons pair rest ih =>
      intro h
      rcases pair with ⟨lf, rt⟩
      have hpair := h lf rt (List.mem_cons_self ..)
      have hrest : ∀ l r, (l, r) ∈ rest →
          state₁.factAt? (l.original mol).node = state₂.factAt? (l.original mol).node ∧
          state₁.factAt? (r.original mol).node = state₂.factAt? (r.original mol).node :=
        fun l r hm => h l r (List.mem_cons_of_mem (lf, rt) hm)
      simp only [FrameRuntime.compareDescriptorPairLabels]
      rw [occurrenceNodePriority_congr state₁ state₂ stage true (lf.original mol) hpair.1]
      rw [occurrenceNodePriority_congr state₁ state₂ stage false (rt.original mol) hpair.2]
      cases hcmp : compare (occurrenceNodePriority state₂ stage true (lf.original mol))
          (occurrenceNodePriority state₂ stage false (rt.original mol)) with
      | eq => exact ih hrest
      | lt => rfl
      | gt => rfl

/-- The checked first-sphere descriptor label comparison has the same read-locality: the
validation pass is state-free, so state agreement at the compared occurrence nodes forces
agreement of the checked comparison. -/
theorem compareDescriptorPairLabels?_congr
    (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (state₁ state₂ : OccurrenceAuxState) (stage : RawDescriptorRuleStage)
    (pairs : List (FrameRuntime.Cursor × FrameRuntime.Cursor))
    (h : ∀ lft rgt, (lft, rgt) ∈ pairs →
      state₁.factAt? (lft.original mol).node = state₂.factAt? (lft.original mol).node ∧
      state₁.factAt? (rgt.original mol).node = state₂.factAt? (rgt.original mol).node) :
    FrameRuntime.compareDescriptorPairLabels? mol profile state₁ stage pairs =
      FrameRuntime.compareDescriptorPairLabels? mol profile state₂ stage pairs := by
  simp [FrameRuntime.compareDescriptorPairLabels?,
    compareDescriptorPairLabels_congr mol state₁ state₂ stage pairs h]

/-! ## B. The decisive Rule-4a short-circuit seam -/

/-- A decisive (non-tie) first-sphere descriptor label short-circuits `compareDescriptorRule?`
before any child expansion: `beforeLeft` / `beforeRight` and `nextDescriptorPairs?` are never
consulted.  The fast-mode width cap is discharged by `guardFalse`. -/
theorem compareDescriptorRule?_eq_of_pairLabels_strict
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (stage : RawDescriptorRuleStage) (fuel : Nat)
    (pairs : List (FrameRuntime.Cursor × FrameRuntime.Cursor)) (order : Ordering)
    (guardFalse : (!authoritative && (RawMolecule.defaultBranchWidthCap < pairs.length)) = false)
    (labels : FrameRuntime.compareDescriptorPairLabels? mol profile state stage pairs = some order)
    (strict : order ≠ Ordering.eq) :
    FrameRuntime.compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight
        stage fuel pairs = some order := by
  cases fuel with
  | zero =>
      simp only [FrameRuntime.compareDescriptorRule?, guardFalse, labels]
      cases order with
      | lt => rfl
      | gt => rfl
      | eq => exact absurd rfl strict
  | succ f =>
      simp only [FrameRuntime.compareDescriptorRule?, guardFalse, labels]
      cases order with
      | lt => rfl
      | gt => rfl
      | eq => exact absurd rfl strict

/-- A decisive Rule-4a first sphere at the tied root therefore decides the whole
`compareDescriptorAtTiedRoot?` at stage `.rule4a`. -/
theorem compareDescriptorAtTiedRoot?_eq_of_rule4a_labels_strict
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat)
    (left right : FrameRuntime.Cursor) (order : Ordering)
    (guardFalse : (!authoritative && (RawMolecule.defaultBranchWidthCap <
        [(left, right)].length)) = false)
    (labels : FrameRuntime.compareDescriptorPairLabels? mol profile state
      RawDescriptorRuleStage.rule4a [(left, right)] = some order)
    (strict : order ≠ Ordering.eq) :
    FrameRuntime.compareDescriptorAtTiedRoot? mol profile authoritative state fuel
      RawDescriptorRuleStage.rule4a left right = some order := by
  dsimp only [FrameRuntime.compareDescriptorAtTiedRoot?,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal]
  have hrule : FrameRuntime.compareDescriptorRule? mol profile authoritative state
      (FrameRuntime.compareDescriptorBranchAt? mol profile authoritative state fuel
        RawDescriptorRuleStage.rule4a)
      (FrameRuntime.compareDescriptorBranchAt? mol profile authoritative state fuel
        RawDescriptorRuleStage.rule4a)
      RawDescriptorRuleStage.rule4a fuel [(left, right)] = some order :=
    compareDescriptorRule?_eq_of_pairLabels_strict mol profile authoritative state
      (FrameRuntime.compareDescriptorBranchAt? mol profile authoritative state fuel
        RawDescriptorRuleStage.rule4a)
      (FrameRuntime.compareDescriptorBranchAt? mol profile authoritative state fuel
        RawDescriptorRuleStage.rule4a)
      RawDescriptorRuleStage.rule4a fuel [(left, right)] order guardFalse labels strict
  rw [hrule]
  cases order <;> rfl

/-! ## C. Empty-state tie -/

/-- Against the empty auxiliary state the complete decision is exactly the actual
constitutional result: strict results are returned verbatim and a constitutional tie is
returned as a tie, with no occurrence read at all. -/
theorem decisionComplete?_empty_state
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (fuel : Nat) (left right : CanonicalRerootCursor) :
    FrameRuntime.decisionComplete? mol profile authoritative [] fuel left right =
      (FrameRuntime.compareBranch? mol profile authoritative fuel CanonicalRuleStage.rule2
        (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right)).map
        (fun order => if order != Ordering.eq then { ordering := order }
          else { ordering := Ordering.eq }) := by
  unfold FrameRuntime.decisionComplete?
  cases h : FrameRuntime.compareBranch? mol profile authoritative fuel CanonicalRuleStage.rule2
      (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) with
  | none => simp
  | some order => cases order <;> rfl

/-! ## D. Main read-locality theorem -/

/-- **The useful general lemma.**  Fix a tied pair of roots (the strict constitutional
short-circuit did not fire) and two nonempty states.  If the Rule-4a first sphere of the
actual authoritative comparator is decisive, then the *complete* decision depends on the
auxiliary state only through the two occurrence-local reads
`state.factAt? left.node` and `state.factAt? right.node`: any two states that agree on those
two reads (and are both nonempty) yield the same complete decision. -/
theorem decisionComplete?_congr_of_tied_rule4a_decisive
    (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (fuel : Nat) (left right : CanonicalRerootCursor)
    (state₁ state₂ : OccurrenceAuxState) (order : Ordering)
    (tie : FrameRuntime.compareBranch? mol profile true fuel CanonicalRuleStage.rule2
      (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) = some Ordering.eq)
    (nonempty₁ : state₁.isEmpty = false) (nonempty₂ : state₂.isEmpty = false)
    (hleft : state₁.factAt? left.node = state₂.factAt? left.node)
    (hright : state₁.factAt? right.node = state₂.factAt? right.node)
    (labels₁ : FrameRuntime.compareDescriptorPairLabels? mol profile state₁
      RawDescriptorRuleStage.rule4a
      [(FrameRuntime.Cursor.actual left, FrameRuntime.Cursor.actual right)] = some order)
    (strict : order ≠ Ordering.eq) :
    FrameRuntime.decisionComplete? mol profile true state₁ fuel left right =
      FrameRuntime.decisionComplete? mol profile true state₂ fuel left right := by
  have guard : (!true && (RawMolecule.defaultBranchWidthCap <
      [(FrameRuntime.Cursor.actual left, FrameRuntime.Cursor.actual right)].length)) = false :=
    RawFramedConstitutionalFuelStability.singleton_cap_eq_false true
      (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right)
  have labels₂ : FrameRuntime.compareDescriptorPairLabels? mol profile state₂
      RawDescriptorRuleStage.rule4a
      [(FrameRuntime.Cursor.actual left, FrameRuntime.Cursor.actual right)] = some order := by
    have hpairwise : ∀ l r, (l, r) ∈
        [(FrameRuntime.Cursor.actual left, FrameRuntime.Cursor.actual right)] →
        state₁.factAt? (l.original mol).node = state₂.factAt? (l.original mol).node ∧
        state₁.factAt? (r.original mol).node = state₂.factAt? (r.original mol).node := by
      intro l r hm
      have hsingle : l = FrameRuntime.Cursor.actual left ∧ r = FrameRuntime.Cursor.actual right := by
        simpa using hm
      rcases hsingle with ⟨rfl, rfl⟩
      simp only [FrameRuntime.Cursor.original]
      exact ⟨hleft, hright⟩
    have hcongr : FrameRuntime.compareDescriptorPairLabels? mol profile state₁
        RawDescriptorRuleStage.rule4a
        [(FrameRuntime.Cursor.actual left, FrameRuntime.Cursor.actual right)] =
      FrameRuntime.compareDescriptorPairLabels? mol profile state₂
        RawDescriptorRuleStage.rule4a
        [(FrameRuntime.Cursor.actual left, FrameRuntime.Cursor.actual right)] :=
      compareDescriptorPairLabels?_congr mol profile state₁ state₂ RawDescriptorRuleStage.rule4a
        [(FrameRuntime.Cursor.actual left, FrameRuntime.Cursor.actual right)] hpairwise
    rw [← hcongr]
    exact labels₁
  have r4a₁ : FrameRuntime.compareDescriptorAtTiedRoot? mol profile true state₁ fuel
      RawDescriptorRuleStage.rule4a (FrameRuntime.Cursor.actual left)
      (FrameRuntime.Cursor.actual right) = some order :=
    compareDescriptorAtTiedRoot?_eq_of_rule4a_labels_strict mol profile true state₁ fuel
      (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) order guard labels₁ strict
  have r4a₂ : FrameRuntime.compareDescriptorAtTiedRoot? mol profile true state₂ fuel
      RawDescriptorRuleStage.rule4a (FrameRuntime.Cursor.actual left)
      (FrameRuntime.Cursor.actual right) = some order :=
    compareDescriptorAtTiedRoot?_eq_of_rule4a_labels_strict mol profile true state₂ fuel
      (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) order guard labels₂ strict
  have eval₁ : FrameRuntime.decisionComplete? mol profile true state₁ fuel left right =
      some { ordering := order } := by
    unfold FrameRuntime.decisionComplete?
    rw [tie]
    rw [nonempty₁]
    rw [r4a₁]
    cases order with
    | lt => rfl
    | gt => rfl
    | eq => exact absurd rfl strict
  have eval₂ : FrameRuntime.decisionComplete? mol profile true state₂ fuel left right =
      some { ordering := order } := by
    unfold FrameRuntime.decisionComplete?
    rw [tie]
    rw [nonempty₂]
    rw [r4a₂]
    cases order with
    | lt => rfl
    | gt => rfl
    | eq => exact absurd rfl strict
  rw [eval₁, eval₂]

/-! ## E. Actual molecular witness -/

/-- At the actual C0 re-based frame the two arms are constitutionally tied (the strict
short-circuit cannot fire), and the actual complete decision is *state sensitive*: the empty
state returns `eq`, while the real batch state `[c3Fact]` returns `lt`.

This is only a pointwise state-sensitivity statement.  The two states disagree on the
`factAt?` read at the C3 arm node, which is an *allowed* deeper occurrence read (the C3 arm
node has history `[c3, middle, c2]`, strictly deeper than the C2 arm node with history
`[c2]`); the theorem therefore
does **not** claim that the constitutional depth is insufficient, and it is not a
"strict-depth counterexample".  It also does not assert a general congruence theorem below a
Rule-4a tie: that is `decisionComplete?_congr_of_tied_rule4a_decisive`, which additionally
requires the Rule-4a first sphere to be decisive and agreement of the two root reads. -/
theorem c0_rebased_constitutional_tie_state_sensitive :
    FrameRuntime.compareBranch? mol c0Profile true fuel CanonicalRuleStage.rule2
        (FrameRuntime.Cursor.actual c2ArmCursor) (FrameRuntime.Cursor.actual c3ArmCursor) =
        some Ordering.eq ∧
      OccurrenceAuxState.factAt? ([] : OccurrenceAuxState) c2ArmCursor.node = none ∧
      OccurrenceAuxState.factAt? ([] : OccurrenceAuxState) c3ArmCursor.node = none ∧
      OccurrenceAuxState.factAt? ([c3Fact] : OccurrenceAuxState) c2ArmCursor.node = none ∧
      OccurrenceAuxState.factAt? ([c3Fact] : OccurrenceAuxState) c3ArmCursor.node =
        some c3Fact ∧
      FrameRuntime.decisionComplete? mol c0Profile true [] fuel c2ArmCursor c3ArmCursor =
        some { ordering := Ordering.eq } ∧
      FrameRuntime.decisionComplete? mol c0Profile true [c3Fact] fuel c2ArmCursor c3ArmCursor =
        some { ordering := Ordering.lt } := by
  exact ⟨c0_framed_constitutional_tie.2.2.2, by decide, by decide, by decide, by decide,
    c0_framed_state_sensitivity.1, c0_framed_state_sensitivity.2.1⟩

/-- The actual production state for centre C2 is `[c3Fact, c0AuxFact]`; it contains C0's own
auxiliary label (`c0AuxFact`) keyed at C0's occurrence.  That label is *present but not
demanded*: the C0 arm comparison never reads that key, so labelling C0 against the batch
state `[c3Fact]` and against the full production state gives the same decision, by the
general read-locality lemma applied to the two actual reads (C2 arm absent, C3 arm present).
This is presence-without-demand, not a dependency cycle. -/
theorem c0_rebased_decision_ignores_own_fact :
    FrameRuntime.decisionComplete? mol c0Profile true [c3Fact] fuel c2ArmCursor c3ArmCursor =
      FrameRuntime.decisionComplete? mol c0Profile true [c3Fact, c0AuxFact] fuel
        c2ArmCursor c3ArmCursor := by
  refine decisionComplete?_congr_of_tied_rule4a_decisive mol c0Profile fuel c2ArmCursor c3ArmCursor
    [c3Fact] [c3Fact, c0AuxFact] Ordering.lt ?tie ?nonempty₁ ?nonempty₂ ?hleft ?hright ?labels₁ ?strict
  · exact c0_framed_constitutional_tie.2.2.2
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

end RawFramedDemandDependency
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/
assert_kernel_only TetraStereo.OneCenter.RawFramedDemandDependency.occurrenceNodePriority_congr
assert_kernel_only TetraStereo.OneCenter.RawFramedDemandDependency.occurrenceRule4cCarrierAt?_congr
assert_kernel_only TetraStereo.OneCenter.RawFramedDemandDependency.compareDescriptorPairLabels_congr
assert_kernel_only TetraStereo.OneCenter.RawFramedDemandDependency.compareDescriptorPairLabels?_congr
assert_kernel_only TetraStereo.OneCenter.RawFramedDemandDependency.compareDescriptorRule?_eq_of_pairLabels_strict
assert_kernel_only TetraStereo.OneCenter.RawFramedDemandDependency.compareDescriptorAtTiedRoot?_eq_of_rule4a_labels_strict
assert_kernel_only TetraStereo.OneCenter.RawFramedDemandDependency.decisionComplete?_empty_state
assert_kernel_only TetraStereo.OneCenter.RawFramedDemandDependency.decisionComplete?_congr_of_tied_rule4a_decisive
assert_kernel_only TetraStereo.OneCenter.RawFramedDemandDependency.c0_rebased_constitutional_tie_state_sensitive
assert_kernel_only TetraStereo.OneCenter.RawFramedDemandDependency.c0_rebased_decision_ignores_own_fact
