import TetraStereo.OneCenter.CanonicalRule3SortInvariance

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace RawMolecule































/-! ## Field projections of the comparison-visible structures -/

private theorem canonicalRule3Observable_rule1a (key : CanonicalRule3Key) :
    (canonicalRule3Observable key).rule1a =
      mapCanonicalAtomicLayers key.constitutional.rule1a :=
  rfl

private theorem canonicalRule3Observable_rule1b (key : CanonicalRule3Key) :
    (canonicalRule3Observable key).rule1b = key.constitutional.rule1b :=
  rfl

private theorem canonicalRule3Observable_rule2 (key : CanonicalRule3Key) :
    (canonicalRule3Observable key).rule2 = key.constitutional.rule2 :=
  rfl

private theorem canonicalRule3Observable_rule3 (key : CanonicalRule3Key) :
    (canonicalRule3Observable key).rule3 = key.rule3 :=
  rfl

private theorem canonicalRule3ComparisonProjection_observable (key : CanonicalRule3Key) :
    (canonicalRule3ComparisonProjection key).observable = canonicalRule3Observable key :=
  rfl

private theorem canonicalRule3ComparisonProjection_complete (key : CanonicalRule3Key) :
    (canonicalRule3ComparisonProjection key).complete = key.constitutional.complete :=
  rfl

/-- The supplied core does not register extensionality lemmas for its structures (it declares
none and does not mark them `@[ext]`), so equality of the comparison-visible structure is
established explicitly from its four field equalities. -/
private theorem canonicalRule3Observable_eq_of_fields
    {left right : CanonicalRule3Observable}
    (hRule1a : left.rule1a = right.rule1a)
    (hRule1b : left.rule1b = right.rule1b)
    (hRule2 : left.rule2 = right.rule2)
    (hRule3 : left.rule3 = right.rule3) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Equality of the comparison projection from its two field equalities. -/
private theorem canonicalRule3ComparisonProjection_eq_of_fields
    {left right : CanonicalRule3ComparisonProjection}
    (hObservable : left.observable = right.observable)
    (hComplete : left.complete = right.complete) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Projecting Rule-1a layers commutes with list append. -/
private theorem mapCanonicalAtomicLayers_append
    (left right : List (List CanonicalAtomicEntry)) :
    mapCanonicalAtomicLayers (left ++ right) =
      mapCanonicalAtomicLayers left ++ mapCanonicalAtomicLayers right := by
  simp only [mapCanonicalAtomicLayers, List.map_append]

/-! ## The concrete child compiler

The core `compileRule3Children` is monomorphic in `CanonicalRule3Key`.  The projection lemmas
below need only that same type, so no second compiler is introduced: every statement is about
the actual core function. -/

/-- One unfolding step of the concrete child compiler. -/
private theorem compileRule3Children_cons
    (compile : CanonicalBranchNode → Option CanonicalRule3Key)
    (node : CanonicalBranchNode) (nodes : List CanonicalBranchNode) :
    compileRule3Children compile (node :: nodes) =
      Option.bind (compile node) fun key =>
        Option.bind (compileRule3Children compile nodes) fun keys => some (key :: keys) := by
  simp only [compileRule3Children]
  cases compile node <;> cases compileRule3Children compile nodes <;> rfl

/-- A permutation of the node list preserves compilation success up to a permutation of the
compiled keys. -/
private theorem compileRule3Children_perm_of_perm
    (compile : CanonicalBranchNode → Option CanonicalRule3Key)
    {left right : List CanonicalBranchNode} (hperm : left.Perm right) :
    ∀ {keys : List CanonicalRule3Key},
      compileRule3Children compile left = some keys →
        ∃ otherKeys : List CanonicalRule3Key,
          compileRule3Children compile right = some otherKeys ∧ keys.Perm otherKeys := by
  induction hperm with
  | nil =>
      intro keys hkeys
      have hnil : some ([] : List CanonicalRule3Key) = some keys := by
        simpa only [compileRule3Children] using hkeys
      have hkeysEq : keys = [] := (Option.some.inj hnil).symm
      rw [hkeysEq]
      exact ⟨[], rfl, List.Perm.refl []⟩
  | cons node _ ih =>
      intro keys hkeys
      rw [compileRule3Children_cons] at hkeys
      obtain ⟨key, hkey, hkeys⟩ := Option.bind_eq_some_iff.mp hkeys
      obtain ⟨tailKeys, htail, hsome⟩ := Option.bind_eq_some_iff.mp hkeys
      have hkeysEq : keys = key :: tailKeys := (Option.some.inj hsome).symm
      rw [hkeysEq]
      obtain ⟨otherTail, hotherTail, htailPerm⟩ := ih htail
      refine ⟨key :: otherTail, ?_, htailPerm.cons key⟩
      rw [compileRule3Children_cons, hkey]
      simp only [Option.bind_some]
      rw [hotherTail]
      simp only [Option.bind_some]
  | swap x y tail =>
      intro keys hkeys
      rw [compileRule3Children_cons] at hkeys
      obtain ⟨yKey, hy, hkeys₁⟩ := Option.bind_eq_some_iff.mp hkeys
      rw [compileRule3Children_cons] at hkeys₁
      obtain ⟨middle, hmiddle, houter⟩ := Option.bind_eq_some_iff.mp hkeys₁
      obtain ⟨xKey, hx, hmiddle₂⟩ := Option.bind_eq_some_iff.mp hmiddle
      obtain ⟨tailKeys, htail, hinner⟩ := Option.bind_eq_some_iff.mp hmiddle₂
      have hmiddleEq : middle = xKey :: tailKeys := (Option.some.inj hinner).symm
      rw [hmiddleEq] at houter
      have hkeysEq : keys = yKey :: xKey :: tailKeys :=
        (Option.some.inj houter).symm
      rw [hkeysEq]
      refine ⟨xKey :: yKey :: tailKeys, ?_,
        List.Perm.swap xKey yKey tailKeys⟩
      rw [compileRule3Children_cons, hx]
      simp only [Option.bind_some]
      rw [compileRule3Children_cons, hy]
      simp only [Option.bind_some]
      rw [htail]
      simp only [Option.bind_some]
  | trans _ _ ihFirst ihSecond =>
      intro keys hkeys
      obtain ⟨middleKeys, hmiddle, hfirstPerm⟩ := ihFirst hkeys
      obtain ⟨rightKeys, hright, hsecondPerm⟩ := ihSecond hmiddle
      exact ⟨rightKeys, hright, hfirstPerm.trans hsecondPerm⟩

/-- Compilation failure is invariant under permutation of the node list. -/
private theorem compileRule3Children_none_iff_of_perm
    (compile : CanonicalBranchNode → Option CanonicalRule3Key)
    {left right : List CanonicalBranchNode} (hperm : left.Perm right) :
    compileRule3Children compile left = none ↔
      compileRule3Children compile right = none := by
  constructor
  · intro hleftNone
    cases hright : compileRule3Children compile right with
    | none => rfl
    | some keys =>
        obtain ⟨otherKeys, hother, _⟩ :=
          compileRule3Children_perm_of_perm compile hperm.symm hright
        rw [hleftNone] at hother
        exact absurd hother (by simp)
  · intro hrightNone
    cases hleft : compileRule3Children compile left with
    | none => rfl
    | some keys =>
        obtain ⟨otherKeys, hother, _⟩ :=
          compileRule3Children_perm_of_perm compile hperm hleft
        rw [hrightNone] at hother
        exact absurd hother (by simp)

/-- Pointwise agreement of a projection on the single-node compiler is preserved by the
concrete child-list compiler: the projected compiled key lists agree, and failure agrees with
failure.  This is a same-node-list simulation, so no projected compiler of a different result
type is introduced. -/
private theorem compileRule3Children_map_eq_of_pointwise {γ : Type*}
    (step₁ step₂ : CanonicalBranchNode → Option CanonicalRule3Key)
    (project : CanonicalRule3Key → γ)
    (hpoint : ∀ node, Option.map project (step₁ node) = Option.map project (step₂ node))
    (nodes : List CanonicalBranchNode) :
    Option.map (List.map project) (compileRule3Children step₁ nodes) =
      Option.map (List.map project) (compileRule3Children step₂ nodes) := by
  induction nodes with
  | nil => rfl
  | cons node nodes inductionHypothesis =>
      rw [compileRule3Children_cons step₁ node nodes,
        compileRule3Children_cons step₂ node nodes]
      cases step₁Computed : step₁ node with
      | none =>
          have step₂Computed : step₂ node = none := by
            have agreement := hpoint node
            rw [step₁Computed, Option.map_none] at agreement
            cases computed : step₂ node with
            | none => rfl
            | some key =>
                rw [computed, Option.map_some] at agreement
                cases agreement
          rw [step₂Computed]
          rfl
      | some key₁ =>
          obtain ⟨key₂, step₂Computed, projectedKey⟩ :
              ∃ key₂, step₂ node = some key₂ ∧ project key₁ = project key₂ := by
            have agreement := hpoint node
            rw [step₁Computed, Option.map_some] at agreement
            cases computed : step₂ node with
            | none =>
                rw [computed, Option.map_none] at agreement
                cases agreement
            | some key₂ =>
                rw [computed, Option.map_some] at agreement
                exact ⟨key₂, rfl, Option.some.inj agreement⟩
          rw [step₂Computed]
          simp only [Option.bind_some]
          cases step₁Tail : compileRule3Children step₁ nodes with
          | none =>
              have step₂Tail : compileRule3Children step₂ nodes = none := by
                rw [step₁Tail, Option.map_none] at inductionHypothesis
                cases computed : compileRule3Children step₂ nodes with
                | none => rfl
                | some keys =>
                    rw [computed, Option.map_some] at inductionHypothesis
                    cases inductionHypothesis
              rw [step₂Tail]
              rfl
          | some tailKeys₁ =>
              obtain ⟨tailKeys₂, step₂Tail, projectedTail⟩ :
                  ∃ tailKeys₂, compileRule3Children step₂ nodes = some tailKeys₂ ∧
                    tailKeys₁.map project = tailKeys₂.map project := by
                rw [step₁Tail, Option.map_some] at inductionHypothesis
                cases computed : compileRule3Children step₂ nodes with
                | none =>
                    rw [computed, Option.map_none] at inductionHypothesis
                    cases inductionHypothesis
                | some tailKeys₂ =>
                    rw [computed, Option.map_some] at inductionHypothesis
                    exact ⟨tailKeys₂, rfl, Option.some.inj inductionHypothesis⟩
              rw [step₂Tail]
              simp only [Option.map_some, Option.bind_some, List.map_cons]
              rw [projectedKey, projectedTail]

/-- Compilation under a comparison projection: the option domain is preserved, and successful
runs produce permutation-related projected key lists. -/
private theorem compileRule3Children_projection_dichotomy {γ : Type*}
    (step₁ step₂ : CanonicalBranchNode → Option CanonicalRule3Key)
    (project : CanonicalRule3Key → γ)
    {left right : List CanonicalBranchNode} (hperm : left.Perm right)
    (hpoint : ∀ node, Option.map project (step₁ node) =
      Option.map project (step₂ node)) :
    (compileRule3Children step₁ left = none ↔
        compileRule3Children step₂ right = none) ∧
      (∀ {keys₁ : List CanonicalRule3Key},
        compileRule3Children step₁ left = some keys₁ →
        ∃ keys₂ : List CanonicalRule3Key,
          compileRule3Children step₂ right = some keys₂ ∧
            (keys₁.map project).Perm (keys₂.map project)) := by
  have sameList (nodes : List CanonicalBranchNode) :
      Option.map (List.map project) (compileRule3Children step₁ nodes) =
        Option.map (List.map project) (compileRule3Children step₂ nodes) :=
    compileRule3Children_map_eq_of_pointwise step₁ step₂ project hpoint nodes
  constructor
  · constructor
    · intro leftNone
      have rightLeft : compileRule3Children step₁ right = none :=
        (compileRule3Children_none_iff_of_perm step₁ hperm).mp leftNone
      have agreement := sameList right
      rw [rightLeft, Option.map_none] at agreement
      cases rightComputed : compileRule3Children step₂ right with
      | none => rfl
      | some keys =>
          rw [rightComputed, Option.map_some] at agreement
          cases agreement
    · intro rightNone
      have agreement := sameList right
      cases rightLeft : compileRule3Children step₁ right with
      | none =>
          exact (compileRule3Children_none_iff_of_perm step₁ hperm).mpr rightLeft
      | some keys =>
          rw [rightLeft, Option.map_some] at agreement
          cases rightComputed : compileRule3Children step₂ right with
          | none =>
              rw [rightComputed, Option.map_none] at agreement
              cases agreement
          | some otherKeys =>
              rw [rightComputed] at rightNone
              cases rightNone
  · intro keys₁ leftComputed
    obtain ⟨leftKeys, leftRight, keysPerm⟩ :=
      compileRule3Children_perm_of_perm step₁ hperm leftComputed
    have agreement := sameList right
    rw [leftRight, Option.map_some] at agreement
    cases rightComputed : compileRule3Children step₂ right with
    | none =>
        rw [rightComputed, Option.map_none] at agreement
        cases agreement
    | some keys₂ =>
        rw [rightComputed, Option.map_some] at agreement
        have projectedEq : keys₂.map project = leftKeys.map project :=
          (Option.some.inj agreement).symm
        refine ⟨keys₂, rfl, ?_⟩
        rw [projectedEq]
        exact List.Perm.map project keysPerm

/-! ## Assembly projection congruence -/

/-- Assembling the same root data over two child-key lists with the same comparison-visible
observable list gives the same comparison projection.

The hypothesis is an equality of observable lists (the form produced after sorting); no
provenance field is required to agree. -/
theorem canonicalRule3ComparisonProjection_assembleCanonicalRule3Key_eq
    (root : CanonicalBranchKey)
    (rootObservation : Option CanonicalRule3Observation)
    {sorted₁ sorted₂ : List CanonicalRule3Key}
    (h : sorted₁.map canonicalRule3Observable =
      sorted₂.map canonicalRule3Observable) :
    canonicalRule3ComparisonProjection
        (assembleCanonicalRule3Key root rootObservation sorted₁) =
      canonicalRule3ComparisonProjection
        (assembleCanonicalRule3Key root rootObservation sorted₂) := by
  have hRule1aLayers :
      (sorted₁.map fun key => mapCanonicalAtomicLayers key.constitutional.rule1a) =
        (sorted₂.map fun key => mapCanonicalAtomicLayers key.constitutional.rule1a) := by
    have hmap := congrArg
      (fun observables : List CanonicalRule3Observable =>
        observables.map fun observable => observable.rule1a) h
    simpa only [List.map_map, Function.comp_def,
      canonicalRule3Observable_rule1a] using hmap
  have hRule1bLayers :
      (sorted₁.map fun key => key.constitutional.rule1b) =
        (sorted₂.map fun key => key.constitutional.rule1b) := by
    have hmap := congrArg
      (fun observables : List CanonicalRule3Observable =>
        observables.map fun observable => observable.rule1b) h
    simpa only [List.map_map, Function.comp_def,
      canonicalRule3Observable_rule1b] using hmap
  have hRule2Layers :
      (sorted₁.map fun key => key.constitutional.rule2) =
        (sorted₂.map fun key => key.constitutional.rule2) := by
    have hmap := congrArg
      (fun observables : List CanonicalRule3Observable =>
        observables.map fun observable => observable.rule2) h
    simpa only [List.map_map, Function.comp_def,
      canonicalRule3Observable_rule2] using hmap
  have hRule3Layers :
      (sorted₁.map fun key => key.rule3) =
        (sorted₂.map fun key => key.rule3) := by
    have hmap := congrArg
      (fun observables : List CanonicalRule3Observable =>
        observables.map fun observable => observable.rule3) h
    simpa only [List.map_map, Function.comp_def,
      canonicalRule3Observable_rule3] using hmap
  have hRule1a :
      mapCanonicalAtomicLayers
          (assembleCanonicalRule3Key root rootObservation sorted₁).constitutional.rule1a =
        mapCanonicalAtomicLayers
          (assembleCanonicalRule3Key root rootObservation sorted₂).constitutional.rule1a := by
    have hchildren :
        (sorted₁.map fun key => key.constitutional).map
            (fun child => mapCanonicalAtomicLayers child.rule1a) =
          (sorted₂.map fun key => key.constitutional).map
            (fun child => mapCanonicalAtomicLayers child.rule1a) := by
      simpa only [List.map_map, Function.comp_def] using hRule1aLayers
    simp only [assembleCanonicalRule3Key, assembleCanonicalBranchKey,
      mapCanonicalAtomicLayers_append,
      mapCanonicalAtomicLayers_mergeCanonicalAtomicChildren, hchildren]
  have hRule1b :
      (assembleCanonicalRule3Key root rootObservation sorted₁).constitutional.rule1b =
        (assembleCanonicalRule3Key root rootObservation sorted₂).constitutional.rule1b := by
    have hchildren :
        (sorted₁.map fun key => key.constitutional).map (fun child => child.rule1b) =
          (sorted₂.map fun key => key.constitutional).map (fun child => child.rule1b) := by
      simpa only [List.map_map, Function.comp_def] using hRule1bLayers
    simp only [assembleCanonicalRule3Key, assembleCanonicalBranchKey,
      mergeCanonicalNatChildren_eq_observed, hchildren]
  have hRule2 :
      (assembleCanonicalRule3Key root rootObservation sorted₁).constitutional.rule2 =
        (assembleCanonicalRule3Key root rootObservation sorted₂).constitutional.rule2 := by
    have hchildren :
        (sorted₁.map fun key => key.constitutional).map (fun child => child.rule2) =
          (sorted₂.map fun key => key.constitutional).map (fun child => child.rule2) := by
      simpa only [List.map_map, Function.comp_def] using hRule2Layers
    simp only [assembleCanonicalRule3Key, assembleCanonicalBranchKey,
      mergeCanonicalNatChildren_eq_observed, hchildren]
  have hRule3 :
      (assembleCanonicalRule3Key root rootObservation sorted₁).rule3 =
        (assembleCanonicalRule3Key root rootObservation sorted₂).rule3 := by
    simp only [assembleCanonicalRule3Key, mergeCanonicalRule3NatChildren_eq_observed,
      hRule3Layers]
  have hObservable :
      canonicalRule3Observable
          (assembleCanonicalRule3Key root rootObservation sorted₁) =
        canonicalRule3Observable
          (assembleCanonicalRule3Key root rootObservation sorted₂) :=
    canonicalRule3Observable_eq_of_fields hRule1a hRule1b hRule2 hRule3
  exact canonicalRule3ComparisonProjection_eq_of_fields hObservable (by
    simp only [canonicalRule3ComparisonProjection_complete, assembleCanonicalRule3Key,
      assembleCanonicalBranchKey])

/-! ## Arbitrary-fuel permutation invariance of the concrete builder -/

/-- Pointwise permutations of the child enumerations, with identical node observations, produce
identical comparison projections at every fuel.

Only the comparison-visible projection is claimed: `sourceNodes`, `sourceOccurrences`,
`sourceTree?` and the addressed observation provenance are not required to agree.  The statement
is purely structural and makes no stereo-perception claim. -/
theorem buildCanonicalRule3Key?_map_comparisonProjection_eq_of_perm
    (mol : RawMolecule)
    (children₁ children₂ : CanonicalBranchNode → List CanonicalBranchNode)
    (observe : CanonicalBranchNode → Option (Option CanonicalRule3Observation))
    (hchildren : ∀ node, (children₁ node).Perm (children₂ node))
    (fuel : ℕ) (node : CanonicalBranchNode) :
    (buildCanonicalRule3Key? mol children₁ observe fuel node).map
        canonicalRule3ComparisonProjection =
      (buildCanonicalRule3Key? mol children₂ observe fuel node).map
        canonicalRule3ComparisonProjection := by
  induction fuel generalizing node with
  | zero =>
      unfold buildCanonicalRule3Key?
      cases hobserve : observe node with
      | none => rfl
      | some rootObservation =>
          have hpermHere : (children₁ node).Perm (children₂ node) := hchildren node
          cases hchildNodes₁ : children₁ node with
          | nil =>
              have hpermSymm : (children₂ node).Perm (children₁ node) :=
                hpermHere.symm
              rw [hchildNodes₁] at hpermSymm
              have hchildNodes₂ : children₂ node = [] :=
                List.Perm.eq_nil hpermSymm
              rw [hchildNodes₂]
          | cons child rest =>
              cases hchildNodes₂ : children₂ node with
              | nil =>
                  rw [hchildNodes₁, hchildNodes₂] at hpermHere
                  exact absurd hpermHere (by simp)
              | cons child₂ rest₂ => rfl
  | succ fuel ih =>
      unfold buildCanonicalRule3Key?
      cases hobserve : observe node with
      | none => rfl
      | some rootObservation =>
          have hpermHere : (children₁ node).Perm (children₂ node) := hchildren node
          cases hchildNodes₁ : children₁ node with
          | nil =>
              have hpermSymm : (children₂ node).Perm (children₁ node) :=
                hpermHere.symm
              rw [hchildNodes₁] at hpermSymm
              have hchildNodes₂ : children₂ node = [] :=
                List.Perm.eq_nil hpermSymm
              rw [hchildNodes₂]
          | cons child rest =>
              cases hchildNodes₂ : children₂ node with
              | nil =>
                  rw [hchildNodes₁, hchildNodes₂] at hpermHere
                  exact absurd hpermHere (by simp)
              | cons child₂ rest₂ =>
                  have hpermHere' : (child :: rest).Perm (child₂ :: rest₂) := by
                    simpa only [hchildNodes₁, hchildNodes₂] using hpermHere
                  dsimp only
                  have hpoint : ∀ childNode,
                      Option.map canonicalRule3ComparisonProjection
                          (buildCanonicalRule3Key? mol children₁ observe fuel childNode) =
                        Option.map canonicalRule3ComparisonProjection
                          (buildCanonicalRule3Key? mol children₂ observe fuel childNode) :=
                    fun childNode => ih childNode
                  have hdichotomy := compileRule3Children_projection_dichotomy
                    (fun childNode =>
                      buildCanonicalRule3Key? mol children₁ observe fuel childNode)
                    (fun childNode =>
                      buildCanonicalRule3Key? mol children₂ observe fuel childNode)
                    canonicalRule3ComparisonProjection hpermHere' hpoint
                  cases hkeys₁ : compileRule3Children
                      (fun childNode =>
                        buildCanonicalRule3Key? mol children₁ observe fuel childNode)
                      (child :: rest) with
                  | none =>
                      have hkeys₂ : compileRule3Children
                          (fun childNode =>
                            buildCanonicalRule3Key? mol children₂ observe fuel childNode)
                          (child₂ :: rest₂) = none :=
                        hdichotomy.1.mp hkeys₁
                      simp only [hkeys₂, Option.map_none]
                  | some keys₁ =>
                      obtain ⟨keys₂, hkeys₂, hkeysPerm⟩ := hdichotomy.2 hkeys₁
                      simp only [hkeys₂]
                      have hkeysPermObservable :
                          (keys₁.map canonicalRule3Observable).Perm
                            (keys₂.map canonicalRule3Observable) := by
                        have hmap := List.Perm.map
                          (fun projection : CanonicalRule3ComparisonProjection =>
                            projection.observable) hkeysPerm
                        simpa only [List.map_map, Function.comp_def,
                          canonicalRule3ComparisonProjection_observable] using hmap
                      have hSortedObservable :
                          (sortCanonicalRule3Keys keys₁).map canonicalRule3Observable =
                            (sortCanonicalRule3Keys keys₂).map canonicalRule3Observable :=
                        map_sortCanonicalRule3Keys_observable_eq_of_perm
                          hkeysPermObservable
                      cases hroot : mol.canonicalRootKeyAuthoritative? node true with
                      | none => rfl
                      | some root =>
                          simp only [Option.map_some]
                          exact congrArg some
                            (canonicalRule3ComparisonProjection_assembleCanonicalRule3Key_eq
                              root rootObservation hSortedObservable)

end RawMolecule
end OneCenter
end TetraStereo

/- Kernel trust checks for both public results. -/
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.canonicalRule3ComparisonProjection_assembleCanonicalRule3Key_eq
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.buildCanonicalRule3Key?_map_comparisonProjection_eq_of_perm
