import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Whole-state key agreement on outward reroot branches

`LocalizedParametricCumulativeLabels` separates label *reading* from key *construction* through the
parametric builder `buildLocalizedRerootCumulativeRule45KeyWithRead?`, and
`LocalizedOutwardRerootDependencySupport` proves that the restricted dependency read
`localizedDependencyLabel target (localizedDependencyView state target) cursor` equals the
unrestricted whole-state read `state cursor.occurrence` at every cursor reachable outward from a
strictly-deeper first child of the target-start cursor.

This module composes those two facts without assuming any key equality:

* a fuel-recursive congruence theorem for `buildLocalizedRerootCumulativeRule45KeyWithRead?`: two
  readers that agree on every executable-reroot cursor reachable from a starting cursor build the
  *same full* `Option` key at that cursor, for every fuel, proved by actual induction on the
  structural fuel and the actual `List.mapM` recursion;
* the whole-state instantiation: on an outward branch the whole-state reader
  `fun cursor => state cursor.occurrence` and the shipped restricted builder
  `buildLocalizedRerootCumulativeRule45Key? stage target (localizedDependencyView state target)`
  produce exactly equal `Option` keys at every stage and every fuel, including the fail-closed
  `none` outcome (so `rankedLabels`, hence the Rule-4b reference selection, agree exactly);
* the straight composition of the same agreement through the existing unique-reference Rule-4c
  wrapper, giving a whole-state twin of `buildLocalizedRerootUniqueReferenceRule4cKey?`.

The parent branch (the target-start cursor and anything reached by returning toward the root) is
deliberately *excluded*.  At the target-start cursor the restricted read is `none` (the target is
not a strict dependency of itself) while the whole-state read is `state target.occurrence`; the two
root labels can differ, and that difference can change the Rule-4b reference population and the
ranked-label layer.  Equality of cumulative rank classes of the projected constitutional keys does
not repair that difference, so no parent-branch agreement is claimed here.  Existing
executable-children/decorative bridges (`localizedRerootChildren?_eq_some_executable` and `E`) are
reused as-is; no parent certificate is rebuilt.
-/

namespace CertifiedLocalizedCIPInput

/-! ## Generic `List.mapM` congruence under reachability -/

/-- Pointwise agreement on the members of a list lifts through `List.mapM`.  Membership is enough
because `mapM` only applies the reader to list members. -/
private theorem list_mapM_congr_on {α β : Type*} (first second : α → Option β) :
    ∀ values : List α,
      (∀ value, value ∈ values → first value = second value) →
      values.mapM first = values.mapM second
  | [], _ => rfl
  | value :: values, agrees => by
      simp [List.mapM_cons, agrees value (by simp),
        list_mapM_congr_on first second values
          (fun member memberPresent => agrees member (by simp [memberPresent]))]

/-! ## Fuel-recursive congruence of the parametric builder -/

/-- If two label readers agree on every executable-reroot cursor reachable from a starting cursor,
the two parametric cumulative builds are equal at that cursor for every fuel.  The proof recurses on
the actual structural fuel and on the actual `List.mapM` over the executable children; it never
assumes equality of the built keys. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_congr_of_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (first second : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      Relation.ReflTransGen (E input) start cursor → first cursor = second cursor) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        stage first fuel cursor =
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        stage second fuel cursor
  | 0, cursor, reach => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · have cursorAgree := agree cursor reach
            simp [terminal, cursorAgree]
          · simp [terminal]
  | fuel + 1, cursor, reach => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead?
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
                  (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                    stage first fuel) =
                children.mapM
                  (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                    stage second fuel) := by
              refine list_mapM_congr_on
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage first fuel)
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage second fuel)
                children ?_
              intro child childPresent
              have childEdge : E input cursor child := by
                unfold E
                rwa [← childrenEq]
              have childReach : Relation.ReflTransGen (E input) cursor child :=
                Relation.ReflTransGen.single childEdge
              exact buildLocalizedRerootCumulativeRule45KeyWithRead?_congr_of_reachable
                input stage first second start agree fuel child (reach.trans childReach)
            have cursorAgree := agree cursor reach
            simp [terminal, cursorAgree, mapCongr]

/-! ## Whole-state agreement -/

/-- On an outward branch, the whole-state reader and the restricted dependency reader agree on
every cursor of the outward subtree below `child`.  This is the exact reader agreement needed by
the congruence theorem, obtained from the existing
`outward_reachable_dependencyLabel_eq_state`. -/
theorem wholeStateReader_eq_restrictedReader_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      Relation.ReflTransGen (E input) child cursor →
      state cursor.occurrence =
        input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor := by
  intro cursor cursorReach
  exact (input.outward_reachable_dependencyLabel_eq_state target state
    first cursor firstChild firstDeeper (reachable.trans cursorReach)).symm

/-- Exact full `Option` key equality: on an outward branch the whole-state parametric build equals
the shipped restricted builder at every stage and every fuel.  The equality is of the whole `Option`
key, so the fail-closed `none` outcome is equal too; no comparison ordering is used and no key
equality is assumed. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    ∀ fuel : Nat,
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
        (fun cursor => state cursor.occurrence) fuel child =
      input.buildLocalizedRerootCumulativeRule45Key? stage target
        (input.localizedDependencyView state target) fuel child := by
  intro fuel
  calc
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
        (fun cursor => state cursor.occurrence) fuel child =
        input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
          (fun cursor => input.localizedDependencyLabel target
            (input.localizedDependencyView state target) cursor) fuel child := by
      exact input.buildLocalizedRerootCumulativeRule45KeyWithRead?_congr_of_reachable
        stage (fun cursor => state cursor.occurrence)
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor)
        child
        (input.wholeStateReader_eq_restrictedReader_of_outward_reachable
          target state first child firstChild firstDeeper reachable)
        fuel child Relation.ReflTransGen.refl
    _ = input.buildLocalizedRerootCumulativeRule45Key? stage target
          (input.localizedDependencyView state target) fuel child := by
      exact input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
        stage target (input.localizedDependencyView state target) fuel child

/-- Successful whole-state and shipped compilations on an outward branch yield the *same* key, not
merely comparable projections. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_key_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child)
    (fuel : Nat)
    (wholeKey shippedKey : input.LocalizedRerootCumulativeRule45Key)
    (wholeComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (fun cursor => state cursor.occurrence) fuel child = some wholeKey)
    (shippedComputed : input.buildLocalizedRerootCumulativeRule45Key? stage target
      (input.localizedDependencyView state target) fuel child = some shippedKey) :
    wholeKey = shippedKey := by
  have total := input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
    stage target state first child firstChild firstDeeper reachable fuel
  rw [wholeComputed, shippedComputed] at total
  exact Option.some.inj total

/-- On an outward branch the whole-state ranked labels are exactly the shipped ranked labels, so
the P-92.5.2.1(b) reference population is exactly the shipped one. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_rankedLabels_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child)
    (fuel : Nat)
    (wholeKey shippedKey : input.LocalizedRerootCumulativeRule45Key)
    (wholeComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (fun cursor => state cursor.occurrence) fuel child = some wholeKey)
    (shippedComputed : input.buildLocalizedRerootCumulativeRule45Key? stage target
      (input.localizedDependencyView state target) fuel child = some shippedKey) :
    wholeKey.rankedLabels = shippedKey.rankedLabels := by
  have keyEq := input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_key_eq_of_outward_reachable
    stage target state first child firstChild firstDeeper reachable fuel
    wholeKey shippedKey wholeComputed shippedComputed
  subst shippedKey
  rfl

/-- On an outward branch the Rule-4b reference selection from the whole-state Rule-4a ranked labels
equals the shipped reference selection exactly. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_rule4bReferences_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child)
    (fuel : Nat)
    (wholeKey shippedKey : input.LocalizedRerootCumulativeRule45Key)
    (wholeComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (fun cursor => state cursor.occurrence) fuel child = some wholeKey)
    (shippedComputed : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target
      (input.localizedDependencyView state target) fuel child = some shippedKey) :
    localizedRule4bReferencesFromRankedLabels wholeKey.rankedLabels =
      localizedRule4bReferencesFromRankedLabels shippedKey.rankedLabels := by
  have keyEq := input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_key_eq_of_outward_reachable
    .rule4a target state first child firstChild firstDeeper reachable fuel
    wholeKey shippedKey wholeComputed shippedComputed
  subst shippedKey
  rfl

/-! ## Whole-state unique-reference Rule-4c extension -/

/-- Whole-state twin of `buildLocalizedRerootUniqueReferenceRule4cKey?`: the same fail-closed
unique-reference composition, but each cumulative hierarchy is compiled through the whole-state
reader.  Empty and two-reference populations still fail closed. -/
noncomputable def buildLocalizedRerootWholeStateUniqueReferenceRule4cKey?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (_target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootUniqueReferenceRule4cKey := do
  let rule4aKey ← input.buildLocalizedRerootCumulativeRule45KeyWithRead?
    .rule4a (fun cursor => state cursor.occurrence) fuel cursor
  match localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels with
  | [reference] =>
      let rule4cKey ← input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        (.rule4c reference) (fun cursor => state cursor.occurrence) fuel cursor
      some { rule4aKey := rule4aKey, reference := reference, rule4cKey := rule4cKey }
  | _ => none

/-- On an outward branch the whole-state unique-reference Rule-4c key equals the shipped restricted
one, for every fuel.  This is a straight composition of the whole-state cumulative agreement: the
Rule-4a key, its unique reference, and the Rule-4c key under that reference all agree exactly. -/
theorem buildLocalizedRerootWholeStateUniqueReferenceRule4cKey?_eq_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    ∀ fuel : Nat,
      input.buildLocalizedRerootWholeStateUniqueReferenceRule4cKey?
        target state fuel child =
      input.buildLocalizedRerootUniqueReferenceRule4cKey?
        target (input.localizedDependencyView state target) fuel child := by
  intro fuel
  unfold buildLocalizedRerootWholeStateUniqueReferenceRule4cKey?
    buildLocalizedRerootUniqueReferenceRule4cKey?
  cases rule4aWhole : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a (fun cursor => state cursor.occurrence) fuel child with
  | none =>
      have rule4aShipped : input.buildLocalizedRerootCumulativeRule45Key?
          .rule4a target (input.localizedDependencyView state target) fuel child = none := by
        rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
          .rule4a target state first child firstChild firstDeeper reachable fuel]
        exact rule4aWhole
      simp [rule4aShipped]
  | some rule4aKey =>
      have rule4aShipped : input.buildLocalizedRerootCumulativeRule45Key?
          .rule4a target (input.localizedDependencyView state target) fuel child = some rule4aKey := by
        rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
          .rule4a target state first child firstChild firstDeeper reachable fuel]
        exact rule4aWhole
      simp [rule4aShipped]
      cases referencesComputed : localizedRule4bReferencesFromRankedLabels
          rule4aKey.rankedLabels with
      | nil => simp
      | cons reference references =>
          cases references with
          | nil =>
              cases rule4cWhole : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  (.rule4c reference) (fun cursor => state cursor.occurrence) fuel child with
              | none =>
                  have rule4cShipped : input.buildLocalizedRerootCumulativeRule45Key?
                      (.rule4c reference) target (input.localizedDependencyView state target)
                      fuel child = none := by
                    rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
                      (.rule4c reference) target state first child firstChild firstDeeper reachable fuel]
                    exact rule4cWhole
                  simp [rule4cWhole, rule4cShipped]
              | some rule4cKey =>
                  have rule4cShipped : input.buildLocalizedRerootCumulativeRule45Key?
                      (.rule4c reference) target (input.localizedDependencyView state target)
                      fuel child = some rule4cKey := by
                    rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
                      (.rule4c reference) target state first child firstChild firstDeeper reachable fuel]
                    exact rule4cWhole
                  simp [rule4cWhole, rule4cShipped]
          | cons second rest => simp

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The guarded declarations are the fuel-recursive congruence, the whole-state agreement theorems and
corollaries, and the whole-state unique-reference Rule-4c builder and its agreement theorem.
`assert_kernel_only` permits exactly `propext`, `Classical.choice` and `Quot.sound`, and rejects
`sorryAx`, project axioms and native/compiler trust. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_congr_of_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateReader_eq_restrictedReader_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_key_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_rankedLabels_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_wholeState_rule4bReferences_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootWholeStateUniqueReferenceRule4cKey?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootWholeStateUniqueReferenceRule4cKey?_eq_of_outward_reachable
