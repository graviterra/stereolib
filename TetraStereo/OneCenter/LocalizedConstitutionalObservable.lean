import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Exactly the three projections inspected by Rules 1a, 1b and 2. -/
structure LocalizedConstitutionalObservable where
  rule1a : List (List (OfficialSparseEntry Nat))
  rule1b : List (List (OfficialSparseEntry Nat))
  rule2 : List (List (OfficialSparseEntry Nat))
  deriving DecidableEq

def constitutionalObservable {V : Type*} (key : OfficialRuleMajorKey V) :
    LocalizedConstitutionalObservable := ⟨key.rule1a, key.rule1b, key.rule2⟩

def compareConstitutionalObservable :
    LocalizedConstitutionalObservable → LocalizedConstitutionalObservable → Ordering :=
  compareLex
    (Ordering.byKey LocalizedConstitutionalObservable.rule1a
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
    (compareLex
      (Ordering.byKey LocalizedConstitutionalObservable.rule1b
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
      (Ordering.byKey LocalizedConstitutionalObservable.rule2
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)))

theorem compareConstitutionalObservable_eq_iff (left right : LocalizedConstitutionalObservable) :
    compareConstitutionalObservable left right = .eq ↔ left = right := by
  simp only [compareConstitutionalObservable, compareLex_eq_eq, Ordering.byKey,
    compareSparseLayers_compareNat_eq_iff, compareSparseLayers_compareRule1b_eq_iff]
  cases left
  cases right
  simp only [LocalizedConstitutionalObservable.mk.injEq]

theorem compareConstitutionalObservable_transCmp : Std.TransCmp compareConstitutionalObservable := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  letI : Std.TransCmp OfficialRuleMajorKey.compareRule1b := by
    unfold OfficialRuleMajorKey.compareRule1b
    infer_instance
  unfold compareConstitutionalObservable OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
  infer_instance

theorem ruleMajor_compare_eq_observable {V : Type*} (left right : OfficialRuleMajorKey V) :
    OfficialRuleMajorKey.compare left right =
      compareConstitutionalObservable (constitutionalObservable left)
        (constitutionalObservable right) := rfl

/-- Comparison is insensitive to provenance and completeness metadata. -/
theorem ruleMajor_compare_congr {V W : Type*}
    (left right : OfficialRuleMajorKey V) (otherLeft otherRight : OfficialRuleMajorKey W)
    (hl : constitutionalObservable left = constitutionalObservable otherLeft)
    (hr : constitutionalObservable right = constitutionalObservable otherRight) :
    OfficialRuleMajorKey.compare left right = OfficialRuleMajorKey.compare otherLeft otherRight := by
  simp only [ruleMajor_compare_eq_observable, hl, hr]

private theorem pairwise_observable {V : Type*} (keys : List (OfficialRuleMajorKey V))
    (descending : OfficialRuleMajorKey.Descending keys) :
    (keys.map constitutionalObservable).Pairwise
      (fun left right => compareConstitutionalObservable left right ≠ .lt) := by
  exact descending.map constitutionalObservable (fun _ _ h => h)

/-- Sorting can change the order of tied source records but not their observable sequence. -/
theorem constitutional_observables_eq_of_perm {V : Type*}
    (left right : List (OfficialRuleMajorKey V))
    (permutation : (left.map constitutionalObservable).Perm (right.map constitutionalObservable))
    (hl : OfficialRuleMajorKey.Descending left)
    (hr : OfficialRuleMajorKey.Descending right) :
    left.map constitutionalObservable = right.map constitutionalObservable := by
  haveI := compareConstitutionalObservable_transCmp
  exact List.Perm.eq_of_pairwise
    (le := fun a b => compareConstitutionalObservable a b ≠ .lt)
    (fun a b _ _ lower upper => (compareConstitutionalObservable_eq_iff a b).mp (by
      refine Ordering.eq_eq_of_isLE_of_isGE ?_ (Ordering.ne_lt_iff_isGE.mp lower)
      rw [← Std.OrientedCmp.isGE_eq_isLE]
      exact Ordering.ne_lt_iff_isGE.mp upper))
    (pairwise_observable left hl) (pairwise_observable right hr) permutation

private def mergeObserved {α : Type*}
    (children : List (List (List (OfficialSparseEntry α)))) :=
  let count := children.foldl (fun longest child => max longest child.length) 0
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2 (child.1.getD depth [])

private theorem mergeChildren_eq_observed {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.mergeChildren children layers = mergeObserved (children.map layers) := by
  simp only [OfficialRuleMajorKey.mergeChildren, OfficialRuleMajorKey.childLayerCount,
    mergeObserved, List.foldl_map, List.zipIdx_map, List.flatMap_map]
  rfl

theorem assembled_constitutional_observable_eq {V : Type*}
    (root : OfficialRuleMajorKey V) (left right : List (OfficialRuleMajorKey V))
    (observations : left.map constitutionalObservable = right.map constitutionalObservable) :
    constitutionalObservable (OfficialRuleMajorKey.assemble root left) =
      constitutionalObservable (OfficialRuleMajorKey.assemble root right) := by
  have h1a := congrArg (List.map LocalizedConstitutionalObservable.rule1a) observations
  have h1b := congrArg (List.map LocalizedConstitutionalObservable.rule1b) observations
  have h2 := congrArg (List.map LocalizedConstitutionalObservable.rule2) observations
  simp only [List.map_map, Function.comp_def, constitutionalObservable] at h1a h1b h2
  simp only [constitutionalObservable, OfficialRuleMajorKey.assemble,
    mergeChildren_eq_observed, h1a, h1b, h2]

private theorem children_unique
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) {left right}
    (hl : input.DeclarativeLocalizedRerootChildren cursor left)
    (hr : input.DeclarativeLocalizedRerootChildren cursor right) : left = right := by
  exact Option.some.inj (((input.localizedRerootChildren?_eq_some_iff cursor left).mpr hl).symm.trans
    ((input.localizedRerootChildren?_eq_some_iff cursor right).mpr hr))

private theorem key_list_observables_unique
    (input : CertifiedLocalizedCIPInput) {carrierFuel leftFuel rightFuel : Nat}
    (unique : ∀ cursor left right,
      input.DeclarativeLocalizedRerootRuleMajorKey (carrierFuel := carrierFuel)
        leftFuel cursor left →
      input.DeclarativeLocalizedRerootRuleMajorKey rightFuel cursor right →
      constitutionalObservable left = constitutionalObservable right) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel)) left right,
      input.DeclarativeLocalizedRerootRuleMajorKeyList leftFuel cursors left →
      input.DeclarativeLocalizedRerootRuleMajorKeyList rightFuel cursors right →
      left.map constitutionalObservable = right.map constitutionalObservable := by
  intro cursors
  induction cursors with
  | nil => intro left right hl hr; cases hl; cases hr; rfl
  | cons cursor cursors ih =>
      intro left right hl hr
      cases hl with
      | cons lh lt =>
          cases hr with
          | cons rh rt =>
              simp only [List.map_cons, unique cursor _ _ lh rh, ih _ _ lt rt]

/-- Successful independent constitutional derivations agree at arbitrary, possibly different,
recursion budgets. Exact provenance records need not agree when tied children are permuted. -/
theorem declarative_constitutional_observable_unique
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ leftFuel rightFuel (cursor : input.LocalizedRerootCursor carrierFuel) left right,
      input.DeclarativeLocalizedRerootRuleMajorKey leftFuel cursor left →
      input.DeclarativeLocalizedRerootRuleMajorKey rightFuel cursor right →
      constitutionalObservable left = constitutionalObservable right := by
  intro leftFuel
  induction leftFuel with
  | zero =>
      intro rightFuel cursor left right hl hr
      cases hl with
      | terminal lf le =>
          cases hr with
          | terminal rf re => rfl
          | branch rf rn rd rp rs =>
              exact False.elim (rn ((children_unique input cursor lf rf).symm.trans le))
  | succ leftFuel ih =>
      intro rightFuel cursor left right hl hr
      cases hl with
      | terminal lf le =>
          cases hr with
          | terminal rf re => rfl
          | branch rf rn rd rp rs =>
              exact False.elim (rn ((children_unique input cursor lf rf).symm.trans le))
      | branch lf ln ld lp ls =>
          cases hr with
          | terminal rf re =>
              exact False.elim (ln ((children_unique input cursor lf rf).trans re))
          | branch rf rn rd rp rs =>
              have frames := children_unique input cursor lf rf
              cases frames
              have childObservations := key_list_observables_unique input (ih _) _ _ _ ld rd
              have observedPerm := (lp.map constitutionalObservable).trans
                ((List.Perm.of_eq childObservations).trans (rp.map constitutionalObservable).symm)
              exact assembled_constitutional_observable_eq _ _ _
                (constitutional_observables_eq_of_perm _ _ observedPerm ls rs)

theorem compiled_constitutional_observable_eq_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compiledFuel derivedFuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (compiled derived : OfficialRuleMajorKey input.Atom)
    (computed : input.buildLocalizedRerootRuleMajorKey? compiledFuel cursor = some compiled)
    (meaning : input.DeclarativeLocalizedRerootRuleMajorKey derivedFuel cursor derived) :
    constitutionalObservable compiled = constitutionalObservable derived :=
  input.declarative_constitutional_observable_unique compiledFuel derivedFuel cursor compiled derived
    (input.buildLocalizedRerootRuleMajorKey?_sound compiledFuel cursor compiled computed) meaning

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
