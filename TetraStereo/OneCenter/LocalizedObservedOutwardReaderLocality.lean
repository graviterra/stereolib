import TetraStereo.OneCenter.LocalizedOutwardWholeStateKeyAgreement
import TetraStereo.OneCenter.LocalizedObservedCumulativeAvailability
import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Reader locality of the observed cumulative builder on outward branches

`LocalizedObservedCumulativeRule45Key` defines the fail-closed observed cumulative builder
`buildLocalizedObservedCumulativeRule45Key?`, which separates its Rule-1b observation
(`observe : OfficialCIPNode input.Atom → Option Nat`) from its auxiliary-label reader
(`read : cursor → Option LocalizedAuxiliaryLabel`).  The shipped reader-congruence theorem
`buildLocalizedRerootCumulativeRule45KeyWithRead?_congr_of_reachable` covers only the parametric
builder whose constitutional root key is the stored total distance.  This module proves the
corresponding fact for the observed builder, for an **arbitrary partial observer**:

* `observedOutwardCumulative_congr_of_reachable` — if two label readers agree on every
  executable-reroot cursor reachable from a start cursor, the two observed cumulative builds are
  the *same full `Option` key* at that cursor, for every fuel, every stage and every observer.  The
  proof is a genuine recursion on the structural fuel and on the actual `List.mapM`; the fail-closed
  `none` outcome is covered too, and no key equality is assumed.
* `observedOutwardCumulative_wholeState_eq_of_outward_reachable` — on an outward branch the
  whole-state reader `fun cursor => state cursor.occurrence` and the restricted dependency reader
  `localizedDependencyLabel target (localizedDependencyView state target)` build equal observed
  keys at every fuel.  The reader agreement itself is the existing actual-carrier-support theorem
  `wholeStateReader_eq_restrictedReader_of_outward_reachable`; it is not re-assumed.

The remaining results instantiate this at an actually computed four-ligand occurrence frame
(`localizedOccurrenceFourLigandFrame? target = some frame`):

* `observedOutwardFrame_cursor_key_eq` — for an outward frame cursor (address
  `target.address ++ [slot]`, which is the actual executable-child relation to the target-start
  cursor by `localizedOccurrenceFourLigandFrame_cursors_eq_executable`) the whole-state and
  restricted builds coincide at every fuel.
* `observedOutwardFrame_pair_comparison_eq` — for two outward frame cursors and a pointwise-total
  observer, the cumulative comparison of the whole-state keys equals the comparison of the
  restricted keys at the numeric bound `2 * (carrierFuel + 1)`.
* `observedOutwardRootFrame_pair_comparison_eq` — the root/final-frame form: at a target whose
  address is empty every frame cursor is outward, so the pairwise comparison is view-independent
  without any address side condition.

In those corollaries key *existence* is **derived** from the existing structural availability
theorem `buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice` (with its
explicit pointwise-totality premise and the actual path validity of the frame cursor), rather than
assumed as an output equality.

## Scope

Everything here is observer-parametric and purely about the builder's recursion: it makes no claim
about 2013 chemical fidelity, about `sourceObservation2013`, about global internal-target locality,
or about the parent branch.  In particular the parent cursor is deliberately excluded, because the
restricted dependency read may be `none` there while the whole-state read need not be.
-/

/-! ## Generic `List.mapM` congruence on list members -/

/-- Pointwise agreement on the members of a list lifts through `List.mapM`.  Membership is enough
because `mapM` only applies the reader to list members. -/
private theorem observedOutward_list_mapM_congr_on {α β : Type*}
    (first second : α → Option β) :
    ∀ values : List α,
      (∀ value, value ∈ values → first value = second value) →
      values.mapM first = values.mapM second
  | [], _ => rfl
  | value :: values, agrees => by
      simp [List.mapM_cons, agrees value (by simp),
        observedOutward_list_mapM_congr_on first second values
          (fun member memberPresent => agrees member (by simp [memberPresent]))]

/-! ## Reader congruence of the observed cumulative builder -/

/-- **Reader congruence of the observed cumulative builder.**

If two label readers agree on every executable-reroot cursor reachable from a starting cursor, the
two observed cumulative builds are equal at that cursor for every fuel, every stage and every
observer.  The proof recurses on the actual structural fuel and on the actual `List.mapM` over the
executable children; it never assumes equality of the built keys and it covers the fail-closed
`none` outcome. -/
theorem observedOutwardCumulative_congr_of_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (first second : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      Relation.ReflTransGen (E input) start cursor → first cursor = second cursor) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      input.buildLocalizedObservedCumulativeRule45Key? stage observe first fuel cursor =
        input.buildLocalizedObservedCumulativeRule45Key? stage observe second fuel cursor
  | 0, cursor, reach => by
      unfold buildLocalizedObservedCumulativeRule45Key?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · have cursorAgree := agree cursor reach
            simp [terminal, cursorAgree]
          · simp [terminal]
  | fuel + 1, cursor, reach => by
      unfold buildLocalizedObservedCumulativeRule45Key?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · have cursorAgree := agree cursor reach
            simp [terminal, cursorAgree]
          · have childrenEq : children = input.executableLocalizedRerootChildren cursor := by
              rw [input.localizedRerootChildren?_eq_some_executable cursor] at childrenComputed
              exact (Option.some.inj childrenComputed).symm
            have mapCongr : children.mapM
                  (input.buildLocalizedObservedCumulativeRule45Key? stage observe first fuel) =
                children.mapM
                  (input.buildLocalizedObservedCumulativeRule45Key? stage observe second fuel) := by
              refine observedOutward_list_mapM_congr_on
                (input.buildLocalizedObservedCumulativeRule45Key? stage observe first fuel)
                (input.buildLocalizedObservedCumulativeRule45Key? stage observe second fuel)
                children ?_
              intro child childPresent
              have childEdge : E input cursor child := by
                unfold E
                rwa [← childrenEq]
              have childReach : Relation.ReflTransGen (E input) cursor child :=
                Relation.ReflTransGen.single childEdge
              exact observedOutwardCumulative_congr_of_reachable
                input stage observe first second start agree fuel child (reach.trans childReach)
            have cursorAgree := agree cursor reach
            simp [terminal, cursorAgree, mapCongr]

/-! ## Whole-state agreement on outward branches -/

/-- **Whole-state agreement on outward branches for the observed builder.**

At every cursor reachable outward from a strictly-deeper executable child of the target-start
cursor, the whole-state label reader and the restricted dependency reader build equal observed
cumulative keys at every fuel and stage.  The reader agreement is supplied by the existing
actual-carrier-support theorem; the equality is of the whole `Option` value, so the descriptor, the
labels and the ranked labels agree exactly. -/
theorem observedOutwardCumulative_wholeState_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    ∀ fuel : Nat,
      input.buildLocalizedObservedCumulativeRule45Key? stage observe
          (fun cursor => state cursor.occurrence) fuel child =
        input.buildLocalizedObservedCumulativeRule45Key? stage observe
          (fun cursor => input.localizedDependencyLabel target
            (input.localizedDependencyView state target) cursor) fuel child := by
  intro fuel
  exact input.observedOutwardCumulative_congr_of_reachable
    stage observe
    (fun cursor => state cursor.occurrence)
    (fun cursor => input.localizedDependencyLabel target
      (input.localizedDependencyView state target) cursor)
    child
    (input.wholeStateReader_eq_restrictedReader_of_outward_reachable
      target state first child firstChild firstDeeper reachable)
    fuel child Relation.ReflTransGen.refl

/-! ## Outward cursors of an actual four-ligand frame -/

/-- **Each outward frame cursor has reader-independent observed keys.**

At an actually computed four-ligand frame, a cursor whose address is `target.address ++ [slot]` is
an executable child of the target-start cursor.  Whole-state and restricted dependency builds at
that cursor coincide at every fuel, for every stage and every observer. -/
theorem observedOutwardFrame_cursor_key_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (index : Fin 4)
    (outward : input.IsLocalizedActualFrameOutwardCursor target (frame.cursorAt index)) :
    ∀ fuel : Nat,
      input.buildLocalizedObservedCumulativeRule45Key? stage observe
          (fun cursor => state cursor.occurrence) fuel (frame.cursorAt index) =
        input.buildLocalizedObservedCumulativeRule45Key? stage observe
          (fun cursor => input.localizedDependencyLabel target
            (input.localizedDependencyView state target) cursor) fuel (frame.cursorAt index) := by
  have childrenEq : frame.cursors = input.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) :=
    input.localizedOccurrenceFourLigandFrame_cursors_eq_executable target frame computed
  have firstChild : frame.cursorAt index ∈ input.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) := by
    rw [← childrenEq]
    exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)
  obtain ⟨slot, slotEq⟩ := outward
  have firstDeeper : target.1.address.length <
      (frame.cursorAt index).occurrence.1.address.length := by
    rw [slotEq, List.length_append]
    simp
  intro fuel
  exact input.observedOutwardCumulative_wholeState_eq_of_outward_reachable
    stage observe target state (frame.cursorAt index) (frame.cursorAt index)
    firstChild firstDeeper Relation.ReflTransGen.refl fuel

/-- Path validity of an indexed frame cursor, from the actual frame construction. -/
private theorem observedOutwardFrame_cursor_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    input.LocalizedRerootCursorValid (frame.cursorAt index) :=
  input.localizedOccurrenceFourLigandFrame_cursor_valid target frame computed
    (frame.cursorAt index)
    (List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index))

/-- **Outward/outward frame comparison is view-independent, with derived key existence.**

For two outward cursors of an actually computed four-ligand frame, a pointwise-total observer and
the observed builder at the numeric bound `2 * (carrierFuel + 1)`, keys exist for all four builds
(whole-state and restricted, left and right) by the existing structural availability theorem.
Moreover the resulting whole-state cumulative comparison equals the restricted comparison.  In
particular a constitutional tie that forces the comparator into the descriptor projection cannot
be resolved differently by the two views. -/
theorem observedOutwardFrame_pair_comparison_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (totalObserver : ∀ node : OfficialCIPNode input.Atom, (observe node).isSome = true)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (left right : Fin 4)
    (leftOutward : input.IsLocalizedActualFrameOutwardCursor target (frame.cursorAt left))
    (rightOutward : input.IsLocalizedActualFrameOutwardCursor target (frame.cursorAt right)) :
    ∃ leftWhole rightWhole leftRestricted rightRestricted,
      input.buildLocalizedObservedCumulativeRule45Key? stage observe
          (fun cursor => state cursor.occurrence) (2 * (carrierFuel + 1))
          (frame.cursorAt left) = some leftWhole ∧
      input.buildLocalizedObservedCumulativeRule45Key? stage observe
          (fun cursor => state cursor.occurrence) (2 * (carrierFuel + 1))
          (frame.cursorAt right) = some rightWhole ∧
      input.buildLocalizedObservedCumulativeRule45Key? stage observe
          (fun cursor => input.localizedDependencyLabel target
            (input.localizedDependencyView state target) cursor)
          (2 * (carrierFuel + 1)) (frame.cursorAt left) = some leftRestricted ∧
      input.buildLocalizedObservedCumulativeRule45Key? stage observe
          (fun cursor => input.localizedDependencyLabel target
            (input.localizedDependencyView state target) cursor)
          (2 * (carrierFuel + 1)) (frame.cursorAt right) = some rightRestricted ∧
      input.compareLocalizedRerootCumulativeRule45Keys leftWhole rightWhole =
        input.compareLocalizedRerootCumulativeRule45Keys leftRestricted rightRestricted := by
  obtain ⟨leftWhole, leftWholeBuilt⟩ :=
    input.buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
      stage observe (fun cursor => state cursor.occurrence) (frame.cursorAt left)
      (input.observedOutwardFrame_cursor_valid target frame computed left) totalObserver
  obtain ⟨rightWhole, rightWholeBuilt⟩ :=
    input.buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
      stage observe (fun cursor => state cursor.occurrence) (frame.cursorAt right)
      (input.observedOutwardFrame_cursor_valid target frame computed right) totalObserver
  obtain ⟨leftRestricted, leftRestrictedBuilt⟩ :=
    input.buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
      stage observe
      (fun cursor => input.localizedDependencyLabel target
        (input.localizedDependencyView state target) cursor)
      (frame.cursorAt left)
      (input.observedOutwardFrame_cursor_valid target frame computed left) totalObserver
  obtain ⟨rightRestricted, rightRestrictedBuilt⟩ :=
    input.buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
      stage observe
      (fun cursor => input.localizedDependencyLabel target
        (input.localizedDependencyView state target) cursor)
      (frame.cursorAt right)
      (input.observedOutwardFrame_cursor_valid target frame computed right) totalObserver
  have leftEq := input.observedOutwardFrame_cursor_key_eq
    stage observe target frame computed state left leftOutward (2 * (carrierFuel + 1))
  have rightEq := input.observedOutwardFrame_cursor_key_eq
    stage observe target frame computed state right rightOutward (2 * (carrierFuel + 1))
  have leftKeyEq : leftWhole = leftRestricted :=
    Option.some.inj (leftWholeBuilt.symm.trans (leftEq.trans leftRestrictedBuilt))
  have rightKeyEq : rightWhole = rightRestricted :=
    Option.some.inj (rightWholeBuilt.symm.trans (rightEq.trans rightRestrictedBuilt))
  exact ⟨leftWhole, rightWhole, leftRestricted, rightRestricted,
    leftWholeBuilt, rightWholeBuilt, leftRestrictedBuilt, rightRestrictedBuilt,
    by rw [leftKeyEq, rightKeyEq]⟩

/-- **Root/final-frame outward comparison is view-independent.**

At a root occurrence (`target.address = []`) every frame cursor is outward, so the pairwise
comparison agrees between the two readers for any two indices, with key existence again derived
from total observer availability. -/
theorem observedOutwardRootFrame_pair_comparison_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (totalObserver : ∀ node : OfficialCIPNode input.Atom, (observe node).isSome = true)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (rootAddress : target.1.address = [])
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (left right : Fin 4) :
    ∃ leftWhole rightWhole leftRestricted rightRestricted,
      input.buildLocalizedObservedCumulativeRule45Key? stage observe
          (fun cursor => state cursor.occurrence) (2 * (carrierFuel + 1))
          (frame.cursorAt left) = some leftWhole ∧
      input.buildLocalizedObservedCumulativeRule45Key? stage observe
          (fun cursor => state cursor.occurrence) (2 * (carrierFuel + 1))
          (frame.cursorAt right) = some rightWhole ∧
      input.buildLocalizedObservedCumulativeRule45Key? stage observe
          (fun cursor => input.localizedDependencyLabel target
            (input.localizedDependencyView state target) cursor)
          (2 * (carrierFuel + 1)) (frame.cursorAt left) = some leftRestricted ∧
      input.buildLocalizedObservedCumulativeRule45Key? stage observe
          (fun cursor => input.localizedDependencyLabel target
            (input.localizedDependencyView state target) cursor)
          (2 * (carrierFuel + 1)) (frame.cursorAt right) = some rightRestricted ∧
      input.compareLocalizedRerootCumulativeRule45Keys leftWhole rightWhole =
        input.compareLocalizedRerootCumulativeRule45Keys leftRestricted rightRestricted := by
  obtain ⟨_leftOutward, leftOutward⟩ :=
    input.localizedOccurrenceFourLigandFrame_root_all_outward target frame computed
      rootAddress left
  obtain ⟨_rightOutward, rightOutward⟩ :=
    input.localizedOccurrenceFourLigandFrame_root_all_outward target frame computed
      rootAddress right
  exact input.observedOutwardFrame_pair_comparison_eq
    stage observe totalObserver target frame computed state left right leftOutward rightOutward

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.observedOutwardCumulative_congr_of_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.observedOutwardCumulative_wholeState_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.observedOutwardFrame_cursor_valid
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.observedOutwardFrame_cursor_key_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.observedOutwardFrame_pair_comparison_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.observedOutwardRootFrame_pair_comparison_eq
