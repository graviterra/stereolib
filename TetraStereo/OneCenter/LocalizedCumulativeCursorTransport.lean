import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableUnique
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable
import TetraStereo.OneCenter.LocalizedCumulativeUppercaseReflection

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput



































/-! ## Actual list plumbing -/

/-- A permutation of actual children into a list pointwise related to the other actual child list
preserves emptiness, hence terminality at every fuel. -/
private theorem perm_forall₂_nil_iff {α : Type*} {R : α → α → Prop}
    {left middle right : List α}
    (permutation : left.Perm middle) (related : List.Forall₂ R middle right) :
    left = [] ↔ right = [] := by
  constructor
  · intro leftEmpty
    cases leftEmpty
    have middleEmpty : middle = [] := permutation.symm.eq_nil
    cases middleEmpty
    exact List.forall₂_nil_left_iff.mp related
  · intro rightEmpty
    cases rightEmpty
    have middleEmpty : middle = [] := List.forall₂_nil_right_iff.mp related
    cases middleEmpty
    exact permutation.eq_nil

/-- Option `mapM` at one cons, in the form used by the transport induction. -/
private theorem mapM_cons_option {α β : Type*} (f : α → Option β) (head : α)
    (rest : List α) :
    (head :: rest).mapM f =
      f head >>= fun value => (rest.mapM f).map fun tail => value :: tail := by
  rw [List.mapM_cons]
  cases rest.mapM f with
  | none => rfl
  | some tail => rfl

/-! ## Unfolding equations for the actual builder

These are definitional rewrites only: the right-hand sides are the production branches after the
unconditional actual child totality `localizedRerootChildren?_eq_some_executable`. -/

private theorem buildWithRead_zero_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read 0 cursor =
      (if input.executableLocalizedRerootChildren cursor = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage (read cursor))]]
            labels := [[([], read cursor)]]
            rankedLabels := [[([], read cursor)]] }
      else none) := by
  unfold buildLocalizedRerootCumulativeRule45KeyWithRead?
  rw [input.localizedRerootChildren?_eq_some_executable]
  rfl

private theorem buildWithRead_succ_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read (Nat.succ fuel) cursor =
      (if input.executableLocalizedRerootChildren cursor = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage (read cursor))]]
            labels := [[([], read cursor)]]
            rankedLabels := [[([], read cursor)]] }
      else
        (input.executableLocalizedRerootChildren cursor).mapM
            (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel) >>=
          fun childKeys =>
            let sorted := input.sortLocalizedRerootCumulativeRule45Keys childKeys
            some
              { constitutional := OfficialRuleMajorKey.assemble
                  (input.moleculeGraph.officialRuleMajorRootKey
                    cursor.occurrence.1.node false)
                  (sorted.map fun child => child.constitutional)
                descriptor := [[([], localizedCumulativeRule45Priority stage (read cursor))]] ++
                  input.mergeLocalizedRerootDescriptorChildren sorted
                labels := [[([], read cursor)]] ++
                  input.mergeLocalizedRerootLabelChildren sorted
                rankedLabels := [[([], read cursor)]] ++
                  input.mergeLocalizedRerootRankedLabelChildren sorted }) := by
  unfold buildLocalizedRerootCumulativeRule45KeyWithRead?
  rw [input.localizedRerootChildren?_eq_some_executable]
  rfl

/-- Two successful `mapM` executions are comparison-compatible when they fail together and their
successful key lists are permutations after observation. -/
private abbrev OptionObservablePerm {β γ : Type*} (observe : β → γ)
    (left right : Option (List β)) : Prop :=
  left.isSome = right.isSome ∧
    ∀ leftKeys rightKeys, left = some leftKeys → right = some rightKeys →
      (leftKeys.map observe).Perm (rightKeys.map observe)

/-- Two successful `mapM` executions are comparison-compatible when they fail together and their
successful key lists agree after observation. -/
private abbrev OptionObservableEq {β γ : Type*} (observe : β → γ)
    (left right : Option (List β)) : Prop :=
  left.isSome = right.isSome ∧
    ∀ leftKeys rightKeys, left = some leftKeys → right = some rightKeys →
      leftKeys.map observe = rightKeys.map observe

private theorem optionObservablePerm_map_cons {β γ : Type*} {observe : β → γ}
    {left right : Option (List β)} (hypothesis : OptionObservablePerm observe left right)
    (head : β) :
    OptionObservablePerm observe
      (Option.map (fun tail => head :: tail) left)
      (Option.map (fun tail => head :: tail) right) := by
  refine ⟨by simp [Option.isSome_map, hypothesis.1], ?_⟩
  intro leftKeys rightKeys leftComputed rightComputed
  rcases Option.map_eq_some_iff.mp leftComputed with
    ⟨leftTail, leftTailComputed, rfl⟩
  rcases Option.map_eq_some_iff.mp rightComputed with
    ⟨rightTail, rightTailComputed, rfl⟩
  simp only [List.map_cons]
  exact (hypothesis.2 leftTail rightTail leftTailComputed rightTailComputed).cons
    (observe head)

/-- Swapping two leading key observations of one shared successful tail is a permutation of the
observed key lists. -/
private theorem optionObservablePerm_map_cons_map_cons_swap {β γ : Type*}
    {observe : β → γ} (value : Option (List β)) (firstHead secondHead : β) :
    OptionObservablePerm observe
      (Option.map (fun tail => secondHead :: tail)
        (Option.map (fun tail => firstHead :: tail) value))
      (Option.map (fun tail => firstHead :: tail)
        (Option.map (fun tail => secondHead :: tail) value)) := by
  cases value with
  | none =>
      refine ⟨rfl, ?_⟩
      intro leftKeys rightKeys leftComputed _
      simp at leftComputed
  | some tail =>
      refine ⟨rfl, ?_⟩
      intro leftKeys rightKeys leftComputed rightComputed
      simp only [Option.map_some, Option.some.injEq] at leftComputed rightComputed
      cases leftComputed
      cases rightComputed
      simp only [List.map_cons]
      exact List.Perm.swap (observe firstHead) (observe secondHead) (tail.map observe)

private theorem optionObservableEq_map_cons_congr {β γ : Type*} {observe : β → γ}
    {left right : Option (List β)} {leftHead rightHead : β}
    (hypothesis : OptionObservableEq observe left right)
    (headObserved : observe leftHead = observe rightHead) :
    OptionObservableEq observe
      (Option.map (fun tail => leftHead :: tail) left)
      (Option.map (fun tail => rightHead :: tail) right) := by
  refine ⟨by simp [Option.isSome_map, hypothesis.1], ?_⟩
  intro leftKeys rightKeys leftComputed rightComputed
  rcases Option.map_eq_some_iff.mp leftComputed with
    ⟨leftTail, leftTailComputed, rfl⟩
  rcases Option.map_eq_some_iff.mp rightComputed with
    ⟨rightTail, rightTailComputed, rfl⟩
  simp only [List.map_cons]
  rw [headObserved, hypothesis.2 leftTail rightTail leftTailComputed rightTailComputed]

/-- Permuting the input list preserves both the failure status of `mapM` and, on success, the
permutation class of the observed result lists. -/
private theorem mapM_perm_observable {α β γ : Type*}
    (observe : β → γ) (f : α → Option β) :
    ∀ {left right : List α}, left.Perm right →
      OptionObservablePerm observe (left.mapM f) (right.mapM f) := by
  intro left right permutation
  refine permutation.rec
    (motive := fun left right _ =>
      OptionObservablePerm observe (left.mapM f) (right.mapM f))
    ?_ ?_ ?_ ?_
  · refine ⟨rfl, ?_⟩
    intro leftKeys rightKeys leftComputed rightComputed
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at leftComputed rightComputed
    cases leftComputed
    cases rightComputed
    exact List.Perm.refl _
  · intro value l₁ l₂ permutation inductionHypothesis
    simp only [mapM_cons_option]
    cases headComputed : f value with
    | none =>
        change OptionObservablePerm observe none none
        refine ⟨rfl, ?_⟩
        intro leftKeys rightKeys leftComputed _
        simp at leftComputed
    | some head =>
        change OptionObservablePerm observe
          (Option.map (fun tail => head :: tail) (l₁.mapM f))
          (Option.map (fun tail => head :: tail) (l₂.mapM f))
        exact optionObservablePerm_map_cons inductionHypothesis head
  · intro first second rest
    simp only [mapM_cons_option]
    cases firstComputed : f first with
    | none =>
        cases secondComputed : f second with
        | none =>
            change OptionObservablePerm observe none none
            refine ⟨rfl, ?_⟩
            intro leftKeys rightKeys leftComputed _
            simp at leftComputed
        | some secondHead =>
            change OptionObservablePerm observe none none
            refine ⟨rfl, ?_⟩
            intro leftKeys rightKeys leftComputed _
            simp at leftComputed
    | some firstHead =>
        cases secondComputed : f second with
        | none =>
            change OptionObservablePerm observe none none
            refine ⟨rfl, ?_⟩
            intro leftKeys rightKeys leftComputed _
            simp at leftComputed
        | some secondHead =>
            change OptionObservablePerm observe
              (Option.map (fun tail => secondHead :: tail)
                (Option.map (fun tail => firstHead :: tail) (rest.mapM f)))
              (Option.map (fun tail => firstHead :: tail)
                (Option.map (fun tail => secondHead :: tail) (rest.mapM f)))
            exact optionObservablePerm_map_cons_map_cons_swap
              (rest.mapM f) firstHead secondHead
  · intro l₁ middle l₃ firstPermutation secondPermutation
      firstHypothesis secondHypothesis
    refine ⟨firstHypothesis.1.trans secondHypothesis.1, ?_⟩
    intro leftKeys rightKeys leftComputed rightComputed
    have middleSome : (middle.mapM f).isSome = true := by
      rw [← firstHypothesis.1, leftComputed]
      rfl
    rcases Option.isSome_iff_exists.mp middleSome with ⟨middleKeys, middleComputed⟩
    exact (firstHypothesis.2 leftKeys middleKeys leftComputed middleComputed).trans
      (secondHypothesis.2 middleKeys rightKeys middleComputed rightComputed)

/-- Pointwise agreement of the observed `Option` values over `List.Forall₂` preserves both the
failure status of `mapM` and, on success, equality of the observed result lists (in order). -/
private theorem mapM_forall₂_observable {α β γ : Type*}
    (observe : β → γ) (first second : α → Option β) (R : α → α → Prop)
    (pointwise : ∀ left right, R left right →
      (first left).map observe = (second right).map observe) :
    ∀ {left right : List α}, List.Forall₂ R left right →
      OptionObservableEq observe (left.mapM first) (right.mapM second) := by
  intro left right related
  refine related.rec
    (motive := fun left right _ =>
      OptionObservableEq observe (left.mapM first) (right.mapM second))
    ?_ ?_
  · refine ⟨rfl, ?_⟩
    intro leftKeys rightKeys leftComputed rightComputed
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at leftComputed rightComputed
    cases leftComputed
    cases rightComputed
    rfl
  · intro leftNode rightNode leftTail rightTail headRelated tailRelated
      inductionHypothesis
    simp only [mapM_cons_option]
    cases leftComputed : first leftNode with
    | none =>
        cases rightComputed : second rightNode with
        | none =>
            change OptionObservableEq observe none none
            refine ⟨rfl, ?_⟩
            intro leftKeys rightKeys leftComputedTail _
            simp at leftComputedTail
        | some rightValue =>
            have headMapped := pointwise leftNode rightNode headRelated
            rw [leftComputed, rightComputed] at headMapped
            simp at headMapped
    | some leftValue =>
        cases rightComputed : second rightNode with
        | none =>
            have headMapped := pointwise leftNode rightNode headRelated
            rw [leftComputed, rightComputed] at headMapped
            simp at headMapped
        | some rightValue =>
            have headObserved : observe leftValue = observe rightValue := by
              have mapped := pointwise leftNode rightNode headRelated
              rw [leftComputed, rightComputed] at mapped
              simpa using mapped
            change OptionObservableEq observe
              (Option.map (fun tail => leftValue :: tail) (leftTail.mapM first))
              (Option.map (fun tail => rightValue :: tail) (rightTail.mapM second))
            exact optionObservableEq_map_cons_congr inductionHypothesis headObserved

/-- Combining an actual child permutation with pointwise related actual children: the two
`mapM` executions either both fail or produce observed child-key lists that are permutations of
one another. -/
private theorem mapM_perm_forall₂_observable {α β γ : Type*}
    (observe : β → γ) (first second : α → Option β) (R : α → α → Prop)
    (pointwise : ∀ left right, R left right →
      (first left).map observe = (second right).map observe) :
    ∀ {left middle right : List α}, left.Perm middle →
      List.Forall₂ R middle right →
      (left.mapM first).isSome = (right.mapM second).isSome ∧
        (∀ leftKeys rightKeys, left.mapM first = some leftKeys →
          right.mapM second = some rightKeys →
          (leftKeys.map observe).Perm (rightKeys.map observe)) := by
  intro left middle right permutation related
  have ordered := mapM_forall₂_observable observe first second R pointwise related
  have permuted := mapM_perm_observable observe first permutation
  refine ⟨permuted.1.trans ordered.1, ?_⟩
  intro leftKeys rightKeys leftComputed rightComputed
  have middleSome : (middle.mapM first).isSome = true := by
    rw [← permuted.1, leftComputed]
    rfl
  rcases Option.isSome_iff_exists.mp middleSome with ⟨middleKeys, middleComputed⟩
  exact (permuted.2 leftKeys middleKeys leftComputed middleComputed).trans
    (List.Perm.of_eq
      (ordered.2 middleKeys rightKeys middleComputed rightComputed))

/-! ## Observable projection of actual assembly

The private `assembled_observable_eq` of `LocalizedCumulativeKeyObservableUnique` fixes one
constitutional root.  Cross-cursor transport only knows the three compared rule projections of
each root, so the public helper below accepts the actual merge factorization and equality of the
three rule projections separately.  It is a congruence statement about the actual
`OfficialRuleMajorKey.assemble` and the actual cumulative merge, not a second sort. -/

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
      mergeObserved (children.map fun child => child.descriptor) := by
  simp only [mergeLocalizedRerootDescriptorChildren, localizedRerootDescriptorChildLayerCount,
    mergeObserved, List.foldl_map, List.zipIdx_map, List.flatMap_map]
  rfl

private theorem mergeChildren_congr {V α : Type*}
    {children children' : List (OfficialRuleMajorKey V)}
    {layers layers' : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))}
    (equal : children.map layers = children'.map layers') :
    OfficialRuleMajorKey.mergeChildren children layers =
      OfficialRuleMajorKey.mergeChildren children' layers' := by
  rw [mergeChildren_eq_observed, mergeChildren_eq_observed, equal]

/-- Public assembly congruence for cumulative observables.  Two assembled actual keys with the
same root Rule-1a/1b/2 projections, the same cumulative root descriptor and child lists whose
observed projections agree have equal cumulative observables.  Exact labels, ranked labels,
provenance nodes and the completeness flag are irrelevant to this projection. -/
theorem localizedRerootCumulativeRule45Observable_assemble_eq
    (input : CertifiedLocalizedCIPInput)
    {leftRoot rightRoot : OfficialRuleMajorKey input.Atom}
    {leftDescriptorRoot rightDescriptorRoot :
      List (List (OfficialSparseEntry (List Nat)))}
    {left right : List input.LocalizedRerootCumulativeRule45Key}
    {leftLabels rightLabels :
      List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))}
    {leftRankedLabels rightRankedLabels :
      List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))}
    (root1a : leftRoot.rule1a = rightRoot.rule1a)
    (root1b : leftRoot.rule1b = rightRoot.rule1b)
    (root2 : leftRoot.rule2 = rightRoot.rule2)
    (descriptorRoot : leftDescriptorRoot = rightDescriptorRoot)
    (observations : left.map (input.localizedRerootCumulativeRule45Observable) =
      right.map (input.localizedRerootCumulativeRule45Observable)) :
    input.localizedRerootCumulativeRule45Observable
      { constitutional := OfficialRuleMajorKey.assemble leftRoot
          (left.map fun child => child.constitutional)
        descriptor := leftDescriptorRoot ++
          input.mergeLocalizedRerootDescriptorChildren left
        labels := leftLabels
        rankedLabels := leftRankedLabels } =
    input.localizedRerootCumulativeRule45Observable
      { constitutional := OfficialRuleMajorKey.assemble rightRoot
          (right.map fun child => child.constitutional)
        descriptor := rightDescriptorRoot ++
          input.mergeLocalizedRerootDescriptorChildren right
        labels := rightLabels
        rankedLabels := rightRankedLabels } := by
  have layer1a :
      (left.map fun child => child.constitutional.rule1a) =
        (right.map fun child => child.constitutional.rule1a) := by
    have mapped := congrArg (List.map LocalizedCumulativeRule45Observable.rule1a) observations
    simpa [List.map_map, Function.comp_def, localizedRerootCumulativeRule45Observable]
      using mapped
  have layer1b :
      (left.map fun child => child.constitutional.rule1b) =
        (right.map fun child => child.constitutional.rule1b) := by
    have mapped := congrArg (List.map LocalizedCumulativeRule45Observable.rule1b) observations
    simpa [List.map_map, Function.comp_def, localizedRerootCumulativeRule45Observable]
      using mapped
  have layer2 :
      (left.map fun child => child.constitutional.rule2) =
        (right.map fun child => child.constitutional.rule2) := by
    have mapped := congrArg (List.map LocalizedCumulativeRule45Observable.rule2) observations
    simpa [List.map_map, Function.comp_def, localizedRerootCumulativeRule45Observable]
      using mapped
  have layerDescriptor :
      (left.map fun child => child.descriptor) =
        (right.map fun child => child.descriptor) := by
    have mapped :=
      congrArg (List.map LocalizedCumulativeRule45Observable.descriptor) observations
    simpa [List.map_map, Function.comp_def, localizedRerootCumulativeRule45Observable]
      using mapped
  have merge1a :
      OfficialRuleMajorKey.mergeChildren
          (left.map fun child => child.constitutional) OfficialRuleMajorKey.rule1a =
        OfficialRuleMajorKey.mergeChildren
          (right.map fun child => child.constitutional) OfficialRuleMajorKey.rule1a := by
    apply mergeChildren_congr
    simpa only [List.map_map, Function.comp_def] using layer1a
  have merge1b :
      OfficialRuleMajorKey.mergeChildren
          (left.map fun child => child.constitutional) OfficialRuleMajorKey.rule1b =
        OfficialRuleMajorKey.mergeChildren
          (right.map fun child => child.constitutional) OfficialRuleMajorKey.rule1b := by
    apply mergeChildren_congr
    simpa only [List.map_map, Function.comp_def] using layer1b
  have merge2 :
      OfficialRuleMajorKey.mergeChildren
          (left.map fun child => child.constitutional) OfficialRuleMajorKey.rule2 =
        OfficialRuleMajorKey.mergeChildren
          (right.map fun child => child.constitutional) OfficialRuleMajorKey.rule2 := by
    apply mergeChildren_congr
    simpa only [List.map_map, Function.comp_def] using layer2
  have mergeDescriptor :
      input.mergeLocalizedRerootDescriptorChildren left =
        input.mergeLocalizedRerootDescriptorChildren right := by
    rw [mergeDescriptor_eq_observed, mergeDescriptor_eq_observed, layerDescriptor]
  simp only [localizedRerootCumulativeRule45Observable, OfficialRuleMajorKey.assemble,
    root1a, merge1a, root1b, merge1b, root2, merge2, descriptorRoot, mergeDescriptor]

/-- Terminal cumulative observables only read the actual node atom label, the stored Rule-1b
original-root distance and the cumulative root priority vector. -/
private theorem terminalObservable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stageL stageR : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (x y : input.LocalizedRerootCursor carrierFuel)
    (atomLabel : input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node)
    (rootDistance : x.occurrence.1.node.rule1bRootDistance =
      y.occurrence.1.node.rule1bRootDistance)
    (rootPriority : localizedCumulativeRule45Priority stageL (readL x) =
      localizedCumulativeRule45Priority stageR (readR y)) :
    input.localizedRerootCumulativeRule45Observable
      { constitutional := input.moleculeGraph.officialRuleMajorRootKey
          x.occurrence.1.node true
        descriptor := [[([], localizedCumulativeRule45Priority stageL (readL x))]]
        labels := [[([], readL x)]]
        rankedLabels := [[([], readL x)]] } =
    input.localizedRerootCumulativeRule45Observable
      { constitutional := input.moleculeGraph.officialRuleMajorRootKey
          y.occurrence.1.node true
        descriptor := [[([], localizedCumulativeRule45Priority stageR (readR y))]]
        labels := [[([], readR y)]]
        rankedLabels := [[([], readR y)]] } := by
  simp only [localizedRerootCumulativeRule45Observable,
    MoleculeGraph.officialRuleMajorRootKey]
  rw [atomLabel, rootDistance, rootPriority]

/-! ## The actual forward transport theorem -/

/-- Forward comparison-key transport for the actual cumulative builder.  For any relation `R` on
actual reroot cursors satisfying the four structural clauses above, two actual
`buildLocalizedRerootCumulativeRule45KeyWithRead?` executions at the *same* fuel have the same
comparison-visible observable, whether or not either build succeeds.

At a terminal cursor the root atom label, stored original-root Rule-1b distance and root priority
vector determine the observable.  At a branch, the actual child lists are permutations related by
`R`; the induction hypothesis pairs the child `Option` observables, so the actual `mapM` steps
either both fail or produce observed key lists that are permutations of one another.  The actual
descending sort and the public `cumulative_observables_eq_of_observable_perm` then make the sorted
observable sequences identical, and `localizedRerootCumulativeRule45Observable_assemble_eq`
assembles the parent.  No key equality, label equality or sort-success premise is used. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stageL stageR : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (R : input.LocalizedRerootCursor carrierFuel →
      input.LocalizedRerootCursor carrierFuel → Prop)
    (atomLabel : ∀ x y, R x y →
      input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
        input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node)
    (rootDistance : ∀ x y, R x y →
      x.occurrence.1.node.rule1bRootDistance =
        y.occurrence.1.node.rule1bRootDistance)
    (children : ∀ x y, R x y →
      ∃ related,
        (input.executableLocalizedRerootChildren x).Perm related ∧
          List.Forall₂ R related (input.executableLocalizedRerootChildren y))
    (rootPriority : ∀ x y, R x y →
      localizedCumulativeRule45Priority stageL (readL x) =
        localizedCumulativeRule45Priority stageR (readR y)) :
    ∀ (fuel : Nat) (x y : input.LocalizedRerootCursor carrierFuel), R x y →
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stageL readL fuel x).map
          (input.localizedRerootCumulativeRule45Observable) =
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stageR readR fuel y).map
          (input.localizedRerootCumulativeRule45Observable) := by
  intro fuel
  induction fuel with
  | zero =>
      intro x y related
      rw [buildWithRead_zero_eq input stageL readL x,
        buildWithRead_zero_eq input stageR readR y]
      rcases children x y related with ⟨relatedChildren, permutation, forall₂⟩
      have terminalIff : input.executableLocalizedRerootChildren x = [] ↔
          input.executableLocalizedRerootChildren y = [] :=
        perm_forall₂_nil_iff permutation forall₂
      by_cases emptyLeft : input.executableLocalizedRerootChildren x = []
      · have emptyRight : input.executableLocalizedRerootChildren y = [] :=
          terminalIff.mp emptyLeft
        rw [if_pos emptyLeft, if_pos emptyRight]
        exact congrArg some (terminalObservable_eq input stageL stageR readL readR x y
          (atomLabel x y related) (rootDistance x y related) (rootPriority x y related))
      · have nonemptyRight : input.executableLocalizedRerootChildren y ≠ [] := by
          intro emptyRight
          exact emptyLeft (terminalIff.mpr emptyRight)
        rw [if_neg emptyLeft, if_neg nonemptyRight]
  | succ fuel inductionHypothesis =>
      intro x y related
      rw [buildWithRead_succ_eq input stageL readL fuel x,
        buildWithRead_succ_eq input stageR readR fuel y]
      rcases children x y related with ⟨relatedChildren, permutation, forall₂⟩
      have terminalIff : input.executableLocalizedRerootChildren x = [] ↔
          input.executableLocalizedRerootChildren y = [] :=
        perm_forall₂_nil_iff permutation forall₂
      by_cases emptyLeft : input.executableLocalizedRerootChildren x = []
      · have emptyRight : input.executableLocalizedRerootChildren y = [] :=
          terminalIff.mp emptyLeft
        rw [if_pos emptyLeft, if_pos emptyRight]
        exact congrArg some (terminalObservable_eq input stageL stageR readL readR x y
          (atomLabel x y related) (rootDistance x y related) (rootPriority x y related))
      · have nonemptyRight : input.executableLocalizedRerootChildren y ≠ [] := by
          intro emptyRight
          exact emptyLeft (terminalIff.mpr emptyRight)
        rw [if_neg emptyLeft, if_neg nonemptyRight]
        have transported := mapM_perm_forall₂_observable
          (observe := input.localizedRerootCumulativeRule45Observable)
          (first := input.buildLocalizedRerootCumulativeRule45KeyWithRead? stageL readL fuel)
          (second := input.buildLocalizedRerootCumulativeRule45KeyWithRead? stageR readR fuel)
          (R := R)
          (pointwise := fun left right relatedChild =>
            inductionHypothesis left right relatedChild)
          permutation forall₂
        cases leftMap : (input.executableLocalizedRerootChildren x).mapM
            (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stageL readL fuel) with
        | none =>
            have rightMap : (input.executableLocalizedRerootChildren y).mapM
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stageR readR fuel) =
                none := by
              have status := transported.1
              rw [leftMap] at status
              cases rightComputed : (input.executableLocalizedRerootChildren y).mapM
                  (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                    stageR readR fuel) with
              | none => rfl
              | some keys =>
                  rw [rightComputed] at status
                  simp at status
            rw [rightMap]
            rfl
        | some leftKeys =>
            have rightStatus : ((input.executableLocalizedRerootChildren y).mapM
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  stageR readR fuel)).isSome = true := by
              rw [← transported.1]
              rw [leftMap]
              rfl
            rcases Option.isSome_iff_exists.mp rightStatus with ⟨rightKeys, rightMap⟩
            have sortedPermutation :
                ((input.sortLocalizedRerootCumulativeRule45Keys leftKeys).map
                    (input.localizedRerootCumulativeRule45Observable)).Perm
                  ((input.sortLocalizedRerootCumulativeRule45Keys rightKeys).map
                    (input.localizedRerootCumulativeRule45Observable)) :=
              ((input.sortLocalizedRerootCumulativeRule45Keys_perm leftKeys).map
                  (input.localizedRerootCumulativeRule45Observable)).trans
                ((transported.2 leftKeys rightKeys leftMap rightMap).trans
                  ((input.sortLocalizedRerootCumulativeRule45Keys_perm rightKeys).map
                    (input.localizedRerootCumulativeRule45Observable)).symm)
            have sortedObservations :=
              input.cumulative_observables_eq_of_observable_perm
                (input.sortLocalizedRerootCumulativeRule45Keys leftKeys)
                (input.sortLocalizedRerootCumulativeRule45Keys rightKeys)
                sortedPermutation
                (input.sortLocalizedRerootCumulativeRule45Keys_descending leftKeys)
                (input.sortLocalizedRerootCumulativeRule45Keys_descending rightKeys)
            have root1a :
                (input.moleculeGraph.officialRuleMajorRootKey
                  x.occurrence.1.node false).rule1a =
                  (input.moleculeGraph.officialRuleMajorRootKey
                    y.occurrence.1.node false).rule1a := by
              simp only [MoleculeGraph.officialRuleMajorRootKey]
              rw [atomLabel x y related]
            have root1b :
                (input.moleculeGraph.officialRuleMajorRootKey
                  x.occurrence.1.node false).rule1b =
                  (input.moleculeGraph.officialRuleMajorRootKey
                    y.occurrence.1.node false).rule1b := by
              simp only [MoleculeGraph.officialRuleMajorRootKey]
              rw [rootDistance x y related]
            have root2 :
                (input.moleculeGraph.officialRuleMajorRootKey
                  x.occurrence.1.node false).rule2 =
                  (input.moleculeGraph.officialRuleMajorRootKey
                    y.occurrence.1.node false).rule2 := by
              simp only [MoleculeGraph.officialRuleMajorRootKey]
              rw [atomLabel x y related]
            have descriptorRoot :
                ([[([], localizedCumulativeRule45Priority stageL (readL x))]] :
                  List (List (OfficialSparseEntry (List Nat)))) =
                  [[([], localizedCumulativeRule45Priority stageR (readR y))]] := by
              rw [rootPriority x y related]
            simpa only [rightMap, Option.bind_some, Option.map_some] using
              congrArg some
                (localizedRerootCumulativeRule45Observable_assemble_eq input
                  root1a root1b root2 descriptorRoot sortedObservations)

/-! ## Production specialization -/

/-- The same transport statement for the actual production builder
`buildLocalizedRerootCumulativeRule45Key?`, obtained by rewriting both sides with
`buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel`. -/
theorem buildLocalizedRerootCumulativeRule45Key?_map_observable_eq_of_related
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stageL stageR : LocalizedCumulativeRule45Stage)
    (targetL : input.LocalizedCIPOccurrence carrierFuel)
    (viewL : input.LocalizedDependencyView targetL)
    (targetR : input.LocalizedCIPOccurrence carrierFuel)
    (viewR : input.LocalizedDependencyView targetR)
    (R : input.LocalizedRerootCursor carrierFuel →
      input.LocalizedRerootCursor carrierFuel → Prop)
    (atomLabel : ∀ x y, R x y →
      input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
        input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node)
    (rootDistance : ∀ x y, R x y →
      x.occurrence.1.node.rule1bRootDistance =
        y.occurrence.1.node.rule1bRootDistance)
    (children : ∀ x y, R x y →
      ∃ related,
        (input.executableLocalizedRerootChildren x).Perm related ∧
          List.Forall₂ R related (input.executableLocalizedRerootChildren y))
    (rootPriority : ∀ x y, R x y →
      localizedCumulativeRule45Priority stageL
          (input.localizedDependencyLabel targetL viewL x) =
        localizedCumulativeRule45Priority stageR
          (input.localizedDependencyLabel targetR viewR y)) :
    ∀ (fuel : Nat) (x y : input.LocalizedRerootCursor carrierFuel), R x y →
      (input.buildLocalizedRerootCumulativeRule45Key? stageL targetL viewL fuel x).map
          (input.localizedRerootCumulativeRule45Observable) =
        (input.buildLocalizedRerootCumulativeRule45Key? stageR targetR viewR fuel y).map
          (input.localizedRerootCumulativeRule45Observable) := by
  intro fuel x y related
  rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      stageL targetL viewL fuel x,
    ← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      stageR targetR viewR fuel y]
  exact input.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related
    stageL stageR
    (input.localizedDependencyLabel targetL viewL)
    (input.localizedDependencyLabel targetR viewR)
    R atomLabel rootDistance children rootPriority fuel x y related

/-- Production specialization with one stage and one restricted dependency reader on both sides.
Equal actual dependency readings at `R`-related cursors supply the root-priority clause. -/
theorem buildLocalizedRerootCumulativeRule45Key?_map_observable_eq_of_related_sameSource
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (R : input.LocalizedRerootCursor carrierFuel →
      input.LocalizedRerootCursor carrierFuel → Prop)
    (atomLabel : ∀ x y, R x y →
      input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
        input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node)
    (rootDistance : ∀ x y, R x y →
      x.occurrence.1.node.rule1bRootDistance =
        y.occurrence.1.node.rule1bRootDistance)
    (children : ∀ x y, R x y →
      ∃ related,
        (input.executableLocalizedRerootChildren x).Perm related ∧
          List.Forall₂ R related (input.executableLocalizedRerootChildren y))
    (labels : ∀ x y, R x y →
      input.localizedDependencyLabel target view x =
        input.localizedDependencyLabel target view y) :
    ∀ (fuel : Nat) (x y : input.LocalizedRerootCursor carrierFuel), R x y →
      (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel x).map
          (input.localizedRerootCumulativeRule45Observable) =
        (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel y).map
          (input.localizedRerootCumulativeRule45Observable) :=
  input.buildLocalizedRerootCumulativeRule45Key?_map_observable_eq_of_related
    stage stage target view target view R atomLabel rootDistance children
    (fun x y related => by rw [labels x y related])

/-! ## Mirror specialization -/

/-- Mirror form of the forward transport: the right stage and reader are the uppercase
reflections of the left ones.  The only reader premise is the actual reflected-reading equation
`readR y = reflectUppercaseOptionalLabel (readL x)` on `R`-related cursors; the root-priority
clause follows from `localizedCumulativeRule45Priority_reflectLocalizedCumulativeRule45Stage`. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related_reflectUppercase
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (R : input.LocalizedRerootCursor carrierFuel →
      input.LocalizedRerootCursor carrierFuel → Prop)
    (atomLabel : ∀ x y, R x y →
      input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
        input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node)
    (rootDistance : ∀ x y, R x y →
      x.occurrence.1.node.rule1bRootDistance =
        y.occurrence.1.node.rule1bRootDistance)
    (children : ∀ x y, R x y →
      ∃ related,
        (input.executableLocalizedRerootChildren x).Perm related ∧
          List.Forall₂ R related (input.executableLocalizedRerootChildren y))
    (readerReflect : ∀ x y, R x y →
      readR y = reflectUppercaseOptionalLabel (readL x)) :
    ∀ (fuel : Nat) (x y : input.LocalizedRerootCursor carrierFuel), R x y →
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          stage readL fuel x).map
          (input.localizedRerootCumulativeRule45Observable) =
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (reflectLocalizedCumulativeRule45Stage stage) readR fuel y).map
          (input.localizedRerootCumulativeRule45Observable) :=
  input.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related
    stage (reflectLocalizedCumulativeRule45Stage stage) readL readR R
    atomLabel rootDistance children
    (fun x y related => by
      rw [readerReflect x y related,
        localizedCumulativeRule45Priority_reflectLocalizedCumulativeRule45Stage])

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

`assert_kernel_only` permits exactly `propext`, `Classical.choice` and `Quot.sound`, and rejects
`sorryAx`, project axioms and native/compiler trust. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCumulativeRule45Observable_assemble_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_map_observable_eq_of_related
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_map_observable_eq_of_related_sameSource
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related_reflectUppercase
