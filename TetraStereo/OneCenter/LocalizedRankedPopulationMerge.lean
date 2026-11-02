import TetraStereo.OneCenter.LocalizedRankedProjectionTransport
import TetraStereo.OneCenter.LocalizedRankedChildPermutation
import TetraStereo.OneCenter.LocalizedCumulativeAssemblyRecovery

set_option autoImplicit false

/-!
# Population transport through hierarchy-ranked label merging

`mergeLocalizedRerootRankedLabelChildren` merges each sibling's `rankedLabels` stacks beneath the
hierarchy-equivalence rank assigned by `localizedRerootRankedChildren`, padding every child with the
empty sphere beyond the end of its own stack.  The Rule-4b population consumed by P-92.5.2.1(b) is
`localizedChiralDescriptorsAtRank` of one merged sphere.

This module proves that the merged per-rank chiral population is invariant in two independent
senses, both quantified over *every* sphere depth and *every* hierarchy rank path:

1. `mergeLocalizedRerootRankedLabelChildren_population_perm_of_forall₂`: pointwise related sibling
   lists carry permutation-equivalent merged populations, where the relation only has to refine
   observable equality and per-depth/per-rank population permutation.
2. `mergeLocalizedRerootRankedLabelChildren_population_perm_of_perm_of_descending`: two descending
   permutations of the same sibling list carry permutation-equivalent merged populations.

The technical core is the *padded* `getD` normal form
`getD_mergeLocalizedRerootRankedLabelChildren`: at every depth the merged sphere is the `flatMap`
of the ranked children's own spheres prefixed by their assigned rank.  Since the padding is by the
empty sphere, no equality of child stack heights is required.  Fixed-rank chiral-population
extraction distributes over that `flatMap`, and a prefixed sphere contributes its child population
at `rank = head :: tail` exactly when the child's assigned rank is `head`.

Scope: these are statements about *fixed-rank* populations only.  They do not assert invariance of
the first occupied chiral rank or of the selected Rule-4b reference; those require the additional
projection invariants supplied elsewhere.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## Fixed-rank extraction through list structure -/

/-- Fixed-rank chiral-descriptor extraction distributes over list append. -/
theorem localizedChiralDescriptorsAtRank_append (rank : List Nat)
    (left right : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    localizedChiralDescriptorsAtRank rank (left ++ right) =
      localizedChiralDescriptorsAtRank rank left ++
        localizedChiralDescriptorsAtRank rank right := by
  rw [localizedChiralDescriptorsAtRank_eq_filterMap rank (left ++ right),
    localizedChiralDescriptorsAtRank_eq_filterMap rank left,
    localizedChiralDescriptorsAtRank_eq_filterMap rank right,
    List.filterMap_append]

/-- Fixed-rank chiral-descriptor extraction distributes over `flatMap`. -/
theorem localizedChiralDescriptorsAtRank_flatMap (rank : List Nat) {α : Type*}
    (blocks : List α)
    (chunk : α → List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    localizedChiralDescriptorsAtRank rank (blocks.flatMap chunk) =
      blocks.flatMap (fun block =>
        localizedChiralDescriptorsAtRank rank (chunk block)) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      rw [List.flatMap_cons, List.flatMap_cons, localizedChiralDescriptorsAtRank_append, ih]

/-! ## Extraction through a rank prefix -/

/-- A sphere prefixed by any rank slot contributes nothing at the empty rank path. -/
theorem localizedChiralDescriptorsAtRank_prefixLayer_nil (slot : Nat)
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    localizedChiralDescriptorsAtRank [] (OfficialRuleMajorKey.prefixLayer slot layer) = [] := by
  rw [localizedChiralDescriptorsAtRank_eq_filterMap []
    (OfficialRuleMajorKey.prefixLayer slot layer)]
  unfold OfficialRuleMajorKey.prefixLayer
  rw [List.filterMap_map, List.filterMap_eq_nil_iff]
  intro entry _
  rcases entry with ⟨address, label⟩
  cases label with
  | none => rfl
  | some label => cases label with
    | pseudoasymmetric descriptor => rfl
    | chiral descriptor => simp [chiralDescriptorAtRank]

/-- A sphere prefixed by rank slot `slot` contributes its child population at rank `head :: tail`
exactly when `slot = head`, and nothing otherwise. -/
theorem localizedChiralDescriptorsAtRank_prefixLayer_cons (slot head : Nat) (tail : List Nat)
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    localizedChiralDescriptorsAtRank (head :: tail)
        (OfficialRuleMajorKey.prefixLayer slot layer) =
      if slot = head then localizedChiralDescriptorsAtRank tail layer else [] := by
  rw [localizedChiralDescriptorsAtRank_eq_filterMap (head :: tail)
    (OfficialRuleMajorKey.prefixLayer slot layer)]
  unfold OfficialRuleMajorKey.prefixLayer
  rw [List.filterMap_map]
  by_cases sameSlot : slot = head
  · subst sameSlot
    rw [if_pos rfl, localizedChiralDescriptorsAtRank_eq_filterMap]
    apply List.filterMap_congr
    intro entry _
    rcases entry with ⟨address, label⟩
    cases label with
    | none => rfl
    | some label => cases label with
      | pseudoasymmetric descriptor => rfl
      | chiral descriptor =>
          by_cases sameAddress : address = tail
          · subst sameAddress
            simp [chiralDescriptorAtRank]
          · have different : (slot :: address) ≠ (slot :: tail) := fun equal =>
              sameAddress (List.cons.inj equal).2
            simp [chiralDescriptorAtRank, sameAddress, different]
  · rw [if_neg sameSlot, List.filterMap_eq_nil_iff]
    intro entry _
    rcases entry with ⟨address, label⟩
    cases label with
    | none => rfl
    | some label => cases label with
      | pseudoasymmetric descriptor => rfl
      | chiral descriptor =>
          have different : (slot :: address) ≠ (head :: tail) := fun equal =>
            sameSlot (List.cons.inj equal).1
          simp [chiralDescriptorAtRank, different]

/-! ## The padded `getD` normal form of the ranked merge -/

/-- Every ranked child's underlying key is a member of the sibling list. -/
private theorem fst_mem_of_mem_localizedRerootRankedChildTail
    (input : CertifiedLocalizedCIPInput)
    (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat) :
    ∀ {children : List input.LocalizedRerootCumulativeRule45Key}
      {pair : input.LocalizedRerootCumulativeRule45Key × Nat},
      pair ∈ input.localizedRerootRankedChildTail previous rank children → pair.1 ∈ children := by
  intro children
  induction children generalizing previous rank with
  | nil =>
      intro pair present
      simp [localizedRerootRankedChildTail] at present
  | cons child rest ih =>
      intro pair present
      rw [localizedRerootRankedChildTail_cons input previous child rank rest] at present
      rcases List.mem_cons.mp present with same | tailPresent
      · rw [same]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem child (ih child _ tailPresent)

/-- Every ranked child's underlying key is a member of the sibling list. -/
private theorem fst_mem_of_mem_localizedRerootRankedChildren
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    ∀ {pair : input.LocalizedRerootCumulativeRule45Key × Nat},
      pair ∈ input.localizedRerootRankedChildren children → pair.1 ∈ children := by
  induction children with
  | nil =>
      intro pair present
      simp [localizedRerootRankedChildren] at present
  | cons child rest ih =>
      intro pair present
      rw [localizedRerootRankedChildren_cons input child rest] at present
      rcases List.mem_cons.mp present with same | tailPresent
      · rw [same]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem child
          (fst_mem_of_mem_localizedRerootRankedChildTail input child 0 tailPresent)

/-- **Padded `getD` normal form.**  At *every* depth — including depths beyond every child's own
stack — the merged ranked-label sphere is the `flatMap` of the ranked children's spheres prefixed by
their assigned rank.  The out-of-range padding of each child is the empty sphere, so no equality of
child stack heights is needed. -/
theorem getD_mergeLocalizedRerootRankedLabelChildren
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (depth : Nat) :
    (input.mergeLocalizedRerootRankedLabelChildren children).getD depth [] =
      (input.localizedRerootRankedChildren children).flatMap
        (fun child =>
          OfficialRuleMajorKey.prefixLayer child.2
            (child.1.rankedLabels.getD depth [])) := by
  unfold mergeLocalizedRerootRankedLabelChildren
  dsimp only
  rw [CumulativeAssembly.getD_map_range]
  by_cases within : depth < input.localizedRerootRankedLabelChildLayerCount children
  · rw [if_pos within]
  · rw [if_neg within]
    have empty :
        (input.localizedRerootRankedChildren children).flatMap
          (fun child =>
            OfficialRuleMajorKey.prefixLayer child.2
              (child.1.rankedLabels.getD depth [])) = [] := by
      rw [List.flatMap_eq_nil_iff]
      intro child member
      have childMem : child.1 ∈ children :=
        fst_mem_of_mem_localizedRerootRankedChildren input children member
      have bounded : child.1.rankedLabels.length ≤
          input.localizedRerootRankedLabelChildLayerCount children :=
        CumulativeAssembly.measure_le_foldl_max
          (fun key : input.LocalizedRerootCumulativeRule45Key =>
            key.rankedLabels.length)
          children child.1 childMem
      have padding : child.1.rankedLabels.getD depth [] = [] :=
        List.getD_eq_default (l := child.1.rankedLabels) (d := []) (by omega)
      show OfficialRuleMajorKey.prefixLayer child.2
        (child.1.rankedLabels.getD depth []) = []
      rw [padding]
      rfl
    exact empty.symm

/-! ## Pointwise flatMap transport -/

/-- Pointwise `Perm`-aligned `flatMap` chunks produce `Perm`-related concatenations. -/
private theorem flatMap_perm_of_forall₂_perm {α β : Type*} (f : α → List β) :
    ∀ {left right : List α},
      List.Forall₂ (fun left right => (f left).Perm (f right)) left right →
        (left.flatMap f).Perm (right.flatMap f) := by
  intro left
  induction left with
  | nil =>
      intro right aligned
      obtain rfl := List.forall₂_nil_left_iff.mp aligned
      exact List.Perm.refl []
  | cons head tail ih =>
      intro right aligned
      rcases List.forall₂_cons_left_iff.mp aligned with
        ⟨other, rest, headPerm, tailAligned, rfl⟩
      rw [List.flatMap_cons, List.flatMap_cons]
      exact headPerm.append (ih tailAligned)

/-! ## The two main transport theorems -/

/-- **Pointwise population transport.**  If two sibling lists are pointwise related by a relation
`R` that refines comparison-visible observable equality and per-depth/per-rank population
permutation, then the merged ranked-label layers have `Perm`-related fixed-rank chiral populations
at every depth and every rank path. -/
theorem mergeLocalizedRerootRankedLabelChildren_population_perm_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (R : input.LocalizedRerootCumulativeRule45Key →
      input.LocalizedRerootCumulativeRule45Key → Prop)
    (observable_eq : ∀ left right, R left right →
      input.localizedRerootCumulativeRule45Observable left =
        input.localizedRerootCumulativeRule45Observable right)
    (population_perm : ∀ left right, R left right →
      ∀ (depth : Nat) (rank : List Nat),
        (localizedChiralDescriptorsAtRank rank
            (left.rankedLabels.getD depth [])).Perm
          (localizedChiralDescriptorsAtRank rank
            (right.rankedLabels.getD depth [])))
    (left right : List input.LocalizedRerootCumulativeRule45Key)
    (aligned : List.Forall₂ R left right) :
    ∀ (depth : Nat) (rank : List Nat),
      (localizedChiralDescriptorsAtRank rank
          ((input.mergeLocalizedRerootRankedLabelChildren left).getD depth [])).Perm
        (localizedChiralDescriptorsAtRank rank
          ((input.mergeLocalizedRerootRankedLabelChildren right).getD depth [])) := by
  intro depth rank
  rw [input.getD_mergeLocalizedRerootRankedLabelChildren left depth,
    input.getD_mergeLocalizedRerootRankedLabelChildren right depth,
    localizedChiralDescriptorsAtRank_flatMap,
    localizedChiralDescriptorsAtRank_flatMap]
  let extract : input.LocalizedRerootCumulativeRule45Key × Nat → List RS :=
    fun child =>
      localizedChiralDescriptorsAtRank rank
        (OfficialRuleMajorKey.prefixLayer child.2
          (child.1.rankedLabels.getD depth []))
  have pointwise :
      List.Forall₂ (fun left right => (extract left).Perm (extract right))
        (input.localizedRerootRankedChildren left)
        (input.localizedRerootRankedChildren right) := by
    refine List.Forall₂.imp (fun first second related => ?_)
      (input.localizedRerootRankedChildren_forall₂_of_relation R observable_eq
        left right aligned)
    rcases related with ⟨rankEq, rel⟩
    show (extract first).Perm (extract second)
    dsimp only [extract]
    cases rank with
    | nil =>
        rw [localizedChiralDescriptorsAtRank_prefixLayer_nil,
          localizedChiralDescriptorsAtRank_prefixLayer_nil]
    | cons head tail =>
        rw [localizedChiralDescriptorsAtRank_prefixLayer_cons,
          localizedChiralDescriptorsAtRank_prefixLayer_cons]
        by_cases sameRank : first.2 = head
        · rw [if_pos sameRank, if_pos (rankEq ▸ sameRank)]
          exact population_perm first.1 second.1 rel depth tail
        · rw [if_neg sameRank, if_neg (fun h => sameRank (rankEq ▸ h))]
  exact flatMap_perm_of_forall₂_perm extract pointwise

/-- **Conjunction form of pointwise population transport.**  The direct hypothesis shape used by
structural inductions over independent cumulative-key derivations: observable equality *and* the
per-depth/per-rank child-population permutation, pointwise along the sibling lists. -/
theorem mergeLocalizedRerootRankedLabelChildren_population_perm_of_forall₂_population
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootCumulativeRule45Key)
    (aligned : List.Forall₂
      (fun left right =>
        input.localizedRerootCumulativeRule45Observable left =
            input.localizedRerootCumulativeRule45Observable right ∧
          ∀ (depth : Nat) (rank : List Nat),
            (localizedChiralDescriptorsAtRank rank
                (left.rankedLabels.getD depth [])).Perm
              (localizedChiralDescriptorsAtRank rank
                (right.rankedLabels.getD depth [])))
      left right) :
    ∀ (depth : Nat) (rank : List Nat),
      (localizedChiralDescriptorsAtRank rank
          ((input.mergeLocalizedRerootRankedLabelChildren left).getD depth [])).Perm
        (localizedChiralDescriptorsAtRank rank
          ((input.mergeLocalizedRerootRankedLabelChildren right).getD depth [])) :=
  input.mergeLocalizedRerootRankedLabelChildren_population_perm_of_forall₂
    (fun left right =>
      input.localizedRerootCumulativeRule45Observable left =
          input.localizedRerootCumulativeRule45Observable right ∧
        ∀ (depth : Nat) (rank : List Nat),
          (localizedChiralDescriptorsAtRank rank
              (left.rankedLabels.getD depth [])).Perm
            (localizedChiralDescriptorsAtRank rank
              (right.rankedLabels.getD depth [])))
    (fun _ _ data => data.1)
    (fun _ _ data => data.2)
    left right aligned

/-- **Descending-permutation population transport.**  Two descending permutations of one sibling
list have `Perm`-related fixed-rank chiral populations in the merged ranked-label layers at every
depth and every rank path.  The descending hypotheses are essential: they make the assigned
hierarchy ranks permutation-invariant. -/
theorem mergeLocalizedRerootRankedLabelChildren_population_perm_of_perm_of_descending
    (input : CertifiedLocalizedCIPInput)
    {left right : List input.LocalizedRerootCumulativeRule45Key}
    (permutation : left.Perm right)
    (leftDescending : input.LocalizedRerootCumulativeRule45KeysDescending left)
    (rightDescending : input.LocalizedRerootCumulativeRule45KeysDescending right) :
    ∀ (depth : Nat) (rank : List Nat),
      (localizedChiralDescriptorsAtRank rank
          ((input.mergeLocalizedRerootRankedLabelChildren left).getD depth [])).Perm
        (localizedChiralDescriptorsAtRank rank
          ((input.mergeLocalizedRerootRankedLabelChildren right).getD depth [])) := by
  intro depth rank
  rw [input.getD_mergeLocalizedRerootRankedLabelChildren left depth,
    input.getD_mergeLocalizedRerootRankedLabelChildren right depth,
    localizedChiralDescriptorsAtRank_flatMap,
    localizedChiralDescriptorsAtRank_flatMap]
  exact List.Perm.flatMap_right
    (fun child =>
      localizedChiralDescriptorsAtRank rank
        (OfficialRuleMajorKey.prefixLayer child.2
          (child.1.rankedLabels.getD depth [])))
    (input.localizedRerootRankedChildren_perm_of_descending permutation leftDescending
      rightDescending)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
