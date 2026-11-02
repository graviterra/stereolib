import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
Independent cumulative-key derivations may order tied children differently. Their comparison-visible
observations nevertheless agree. Exact labels and hierarchy populations require separate arguments.
-/

/-- Descending observable permutations have identical observation sequences, even when full keys
are not permutations because their hidden label or provenance fields differ. -/
theorem cumulative_observables_eq_of_observable_perm
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootCumulativeRule45Key)
    (permutation : (left.map input.localizedRerootCumulativeRule45Observable).Perm
      (right.map input.localizedRerootCumulativeRule45Observable))
    (leftDescending : input.LocalizedRerootCumulativeRule45KeysDescending left)
    (rightDescending : input.LocalizedRerootCumulativeRule45KeysDescending right) :
    left.map input.localizedRerootCumulativeRule45Observable =
      right.map input.localizedRerootCumulativeRule45Observable := by
  haveI : Std.TransCmp compareLocalizedCumulativeRule45Observable :=
    compareLocalizedCumulativeRule45Observable_transCmp
  exact List.Perm.eq_of_pairwise
    (le := fun left right =>
      compareLocalizedCumulativeRule45Observable left right ≠ Ordering.lt)
    (fun a b _ _ lower upper =>
      (compareLocalizedCumulativeRule45Observable_eq_iff a b).mp (by
        refine Ordering.eq_eq_of_isLE_of_isGE ?_ (Ordering.ne_lt_iff_isGE.mp lower)
        rw [← Std.OrientedCmp.isGE_eq_isLE]
        exact Ordering.ne_lt_iff_isGE.mp upper))
    (input.observable_pairwise_of_descending left leftDescending)
    (input.observable_pairwise_of_descending right rightDescending) permutation

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

private theorem mergeDescriptor_eq_observed
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootDescriptorChildren children =
      mergeObserved (children.map (fun child => child.descriptor)) := by
  simp only [mergeLocalizedRerootDescriptorChildren, localizedRerootDescriptorChildLayerCount,
    mergeObserved, List.foldl_map, List.zipIdx_map, List.flatMap_map]
  rfl

private theorem assembled_observable_eq
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (descriptorRoot : List (List (OfficialSparseEntry (List Nat))))
    (left right : List input.LocalizedRerootCumulativeRule45Key)
    (observations : left.map input.localizedRerootCumulativeRule45Observable =
      right.map input.localizedRerootCumulativeRule45Observable)
    (leftLabels rightLabels leftRanks rightRanks :
      List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    input.localizedRerootCumulativeRule45Observable
      { constitutional := OfficialRuleMajorKey.assemble root (left.map (·.constitutional)),
        descriptor := descriptorRoot ++ input.mergeLocalizedRerootDescriptorChildren left,
        labels := leftLabels, rankedLabels := leftRanks } =
    input.localizedRerootCumulativeRule45Observable
      { constitutional := OfficialRuleMajorKey.assemble root (right.map (·.constitutional)),
        descriptor := descriptorRoot ++ input.mergeLocalizedRerootDescriptorChildren right,
        labels := rightLabels, rankedLabels := rightRanks } := by
  have h1a := congrArg (List.map LocalizedCumulativeRule45Observable.rule1a) observations
  have h1b := congrArg (List.map LocalizedCumulativeRule45Observable.rule1b) observations
  have h2 := congrArg (List.map LocalizedCumulativeRule45Observable.rule2) observations
  have hd := congrArg (List.map LocalizedCumulativeRule45Observable.descriptor) observations
  simp only [List.map_map, Function.comp_def,
    localizedRerootCumulativeRule45Observable_rule1a,
    localizedRerootCumulativeRule45Observable_rule1b,
    localizedRerootCumulativeRule45Observable_rule2,
    localizedRerootCumulativeRule45Observable_descriptor] at h1a h1b h2 hd
  simp only [localizedRerootCumulativeRule45Observable, OfficialRuleMajorKey.assemble,
    mergeChildren_eq_observed, mergeDescriptor_eq_observed, List.map_map, Function.comp_def,
    h1a, h1b, h2, hd]

private theorem children_unique
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) {left right}
    (hl : input.DeclarativeLocalizedRerootChildren cursor left)
    (hr : input.DeclarativeLocalizedRerootChildren cursor right) : left = right := by
  exact Option.some.inj (((input.localizedRerootChildren?_eq_some_iff cursor left).mpr hl).symm.trans
    ((input.localizedRerootChildren?_eq_some_iff cursor right).mpr hr))

private theorem label_unique
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) {left right}
    (hl : input.DeclarativeLocalizedDependencyLabel target view cursor left)
    (hr : input.DeclarativeLocalizedDependencyLabel target view cursor right) : left = right :=
  ((input.localizedDependencyLabel_eq_iff target view cursor left).mpr hl).symm.trans
    ((input.localizedDependencyLabel_eq_iff target view cursor right).mpr hr)

private theorem key_list_observables_unique
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (unique : ∀ cursor left right,
      input.DeclarativeLocalizedRerootCumulativeRule45Key stage target view fuel cursor left →
      input.DeclarativeLocalizedRerootCumulativeRule45Key stage target view fuel cursor right →
      input.localizedRerootCumulativeRule45Observable left =
        input.localizedRerootCumulativeRule45Observable right) :
    ∀ cursors left right,
      input.DeclarativeLocalizedRerootCumulativeRule45KeyList stage target view fuel cursors left →
      input.DeclarativeLocalizedRerootCumulativeRule45KeyList stage target view fuel cursors right →
      left.map input.localizedRerootCumulativeRule45Observable =
        right.map input.localizedRerootCumulativeRule45Observable := by
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

/-- Two independent derivations of the same cursor have the same comparison-visible key, without
assuming either executable success or equal hidden label fields. -/
theorem declarative_cumulative_key_observable_unique
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor left right,
      input.DeclarativeLocalizedRerootCumulativeRule45Key stage target view fuel cursor left →
      input.DeclarativeLocalizedRerootCumulativeRule45Key stage target view fuel cursor right →
      input.localizedRerootCumulativeRule45Observable left =
        input.localizedRerootCumulativeRule45Observable right := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor left right hl hr
      cases hl with
      | terminal lf le lo =>
          cases hr with
          | terminal rf re ro =>
              have labels := label_unique input target view cursor lo ro
              cases labels
              rfl
  | succ fuel ih =>
      intro cursor left right hl hr
      cases hl with
      | terminal lf le lo =>
          cases hr with
          | terminal rf re ro =>
              have labels := label_unique input target view cursor lo ro
              cases labels
              rfl
          | branch rf rn ro rd rp rs =>
              exact False.elim (rn ((children_unique input cursor lf rf).symm.trans le))
      | branch lf ln lo ld lp ls =>
          cases hr with
          | terminal rf re ro =>
              exact False.elim (ln ((children_unique input cursor lf rf).trans re))
          | branch rf rn ro rd rp rs =>
              have frames := children_unique input cursor lf rf
              cases frames
              have labels := label_unique input target view cursor lo ro
              cases labels
              have childObservations := key_list_observables_unique input stage target view ih _ _ _ ld rd
              have observedPerm := (lp.map input.localizedRerootCumulativeRule45Observable).trans
                ((List.Perm.of_eq childObservations).trans
                  (rp.map input.localizedRerootCumulativeRule45Observable).symm)
              have sortedObservations := input.cumulative_observables_eq_of_observable_perm
                _ _ observedPerm ls rs
              exact assembled_observable_eq input _ _ _ _ sortedObservations _ _ _ _

/-- Every successful executable key agrees observationally with every independent derivation. -/
theorem compiled_cumulative_key_observable_eq_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (compiled derived : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel cursor =
      some compiled)
    (derivation : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor derived) :
    input.localizedRerootCumulativeRule45Observable compiled =
      input.localizedRerootCumulativeRule45Observable derived :=
  input.declarative_cumulative_key_observable_unique stage target view fuel cursor compiled derived
    (input.buildLocalizedRerootCumulativeRule45Key?_sound stage target view fuel cursor compiled computed)
    derivation

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
