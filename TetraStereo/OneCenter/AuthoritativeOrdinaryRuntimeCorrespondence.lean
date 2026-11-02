import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter


























































/-! ## 1. Node labels and node comparators are mode-erased

The authoritative Rule-1a labelers in `CIPAuthoritativeBranchComparator` are textually the same
computations as the ordinary labelers in `BranchSphereKey`; only the name of the general
maximum-matching fallback changes, and that fallback is itself the same term.  Hence all four
correspondences hold by `rfl`. -/

theorem generalMancudeRule1aLabelAuthoritative?_eq_generalMancudeRule1aLabel?
    (mol : RawMolecule) (attached duplicated : ℕ) :
    mol.generalMancudeRule1aLabelAuthoritative? attached duplicated =
      mol.generalMancudeRule1aLabel? attached duplicated := rfl

theorem mancudeRule1aLabelAuthoritative?_eq_mancudeRule1aLabel?
    (mol : RawMolecule) (attached duplicated : ℕ) :
    mol.mancudeRule1aLabelAuthoritative? attached duplicated =
      mol.mancudeRule1aLabel? attached duplicated := rfl

theorem canonicalRule1aLabelAuthoritative?_eq_canonicalRule1aLabel?
    (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode) :
    mol.canonicalRule1aLabelAuthoritative? node = mol.canonicalRule1aLabel? node := rfl

theorem compareCanonicalNodeRuleAuthoritative?_eq_compareCanonicalNodeRule?
    (mol : RawMolecule) (rule : RawMolecule.CanonicalRuleStage)
    (left right : RawMolecule.CanonicalBranchNode) :
    mol.compareCanonicalNodeRuleAuthoritative? rule left right =
      mol.compareCanonicalNodeRule? rule left right := rfl

/-! ## 2. The framed label layer is mode-erased -/

namespace FrameRuntime

open RawMolecule

/-- `label?` ignores the mode flag: the Rule-1b branch never consults it, and the remaining
branches call the two node comparators, which are definitionally equal. -/
theorem label?_false_eq_true (mol : RawMolecule) (profile : Profile)
    (rule : CanonicalRuleStage) (left right : Cursor) :
    label? mol profile false rule left right = label? mol profile true rule left right := by
  unfold label?
  cases hleft : cursor? mol profile left with
  | none => rfl
  | some ld =>
      cases hright : cursor? mol profile right with
      | none => rfl
      | some rd =>
          cases rule with
          | rule1a =>
              simpa using
                (compareCanonicalNodeRuleAuthoritative?_eq_compareCanonicalNodeRule?
                  mol CanonicalRuleStage.rule1a (left.original mol).node
                  (right.original mol).node).symm
          | rule1b => rfl
          | rule2 =>
              simpa using
                (compareCanonicalNodeRuleAuthoritative?_eq_compareCanonicalNodeRule?
                  mol CanonicalRuleStage.rule2 (left.original mol).node
                  (right.original mol).node).symm

/-- `pairLabels?` inherits mode erasure from `label?` by structural induction. -/
theorem pairLabels?_false_eq_true (mol : RawMolecule) (profile : Profile)
    (rule : CanonicalRuleStage) :
    ∀ (pairs : List (Cursor × Cursor)),
      pairLabels? mol profile false rule pairs = pairLabels? mol profile true rule pairs := by
  intro pairs
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      obtain ⟨left, right⟩ := pair
      simp only [pairLabels?]
      rw [label?_false_eq_true mol profile rule left right]
      cases decisionEq : label? mol profile true rule left right with
      | none => simp
      | some decision =>
          cases decision with
          | eq => simpa using ih
          | lt => simp
          | gt => simp

/-- `throughLabels?` is a fixed three-stage pipeline through `label?`, so mode erasure is
immediate. -/
theorem throughLabels?_false_eq_true (mol : RawMolecule) (profile : Profile)
    (stage : CanonicalRuleStage) (left right : Cursor) :
    throughLabels? mol profile false stage left right =
      throughLabels? mol profile true stage left right := by
  simp only [throughLabels?, label?_false_eq_true]

/-! ## 3. The framed ranking primitive

`ranked?` is the only place in the framed runtime where the two modes select different *data*:
the number of padded child slots.  The ordinary mode pads to three, the authoritative mode pads to
`authoritativeChildSlots = 5` (`CIPAuthoritativeBranchComparator`).  We expose the slot count as a
parameter and prove the take/prefix relation between the two counts.  This is the primitive a
caller-level correspondence proof uses; it mentions no CIP rule. -/

/-- `ranked?` with the slot count made explicit.  This is the body of `ranked?` with the
`if authoritative then authoritativeChildSlots else 3` choice replaced by the argument. -/
def rankedWithSlots? (mol : RawMolecule) (profile : Profile)
    (before : Cursor → Cursor → Option Ordering) (parent : Cursor) (slots : Nat) :
    Option (List Cursor) := do
  let _ ← cursor? mol profile parent
  let children := ((parent.original mol).children mol).map Cursor.actual
  if slots < children.length then none else
  let _ ← children.mapM (cursor? mol profile)
  let sorted ← sort? before children
  let phantom : Cursor := .padding parent
  some (sorted ++ List.replicate (slots - sorted.length) phantom)

theorem ranked?_false_eq_rankedWithSlots?
    (mol : RawMolecule) (profile : Profile)
    (before : Cursor → Cursor → Option Ordering) (parent : Cursor) :
    ranked? mol profile false before parent = rankedWithSlots? mol profile before parent 3 := rfl

theorem ranked?_true_eq_rankedWithSlots?
    (mol : RawMolecule) (profile : Profile)
    (before : Cursor → Cursor → Option Ordering) (parent : Cursor) :
    ranked? mol profile true before parent = rankedWithSlots? mol profile before parent 5 := rfl

theorem insert?_length (before : Cursor → Cursor → Option Ordering) (candidate : Cursor)
    (cursors : List Cursor) (result : List Cursor)
    (computed : insert? before candidate cursors = some result) :
    result.length = cursors.length + 1 := by
  induction cursors generalizing result with
  | nil =>
      simp only [insert?] at computed
      have hres : result = [candidate] := (Option.some.inj computed).symm
      subst result
      rfl
  | cons head tail ih =>
      simp only [insert?] at computed
      dsimp only [Bind.bind] at computed
      cases cmpEq : before candidate head with
      | none => simp [cmpEq] at computed
      | some cmp =>
          cases insertedEq : insert? before candidate tail with
          | none =>
              simp only [cmpEq, insertedEq, Option.bind_some] at computed
              split at computed
              · simp at computed
              · have hres : candidate :: head :: tail = result :=
                  Option.some.inj computed
                subst result
                simp
          | some inserted =>
              have ih' := ih inserted insertedEq
              simp only [cmpEq, insertedEq, Option.bind_some] at computed
              split at computed
              · have hres : head :: inserted = result := by
                  simpa [Option.map_some, Option.some.injEq] using computed
                subst result
                simp only [List.length_cons]
                omega
              · have hres : candidate :: head :: tail = result := by
                  simpa only [Option.some.injEq] using computed
                subst result
                rfl

theorem sort?_length (before : Cursor → Cursor → Option Ordering)
    (cursors : List Cursor) (result : List Cursor)
    (computed : sort? before cursors = some result) :
    result.length = cursors.length := by
  induction cursors generalizing result with
  | nil =>
      simp only [sort?] at computed
      have hres : result = [] := (Option.some.inj computed).symm
      subst result
      rfl
  | cons head tail ih =>
      simp only [sort?] at computed
      dsimp only [Bind.bind] at computed
      cases sortedEq : sort? before tail with
      | none => simp [sortedEq] at computed
      | some sorted =>
          cases insertedEq : insert? before head sorted with
          | none => simp [sortedEq, insertedEq] at computed
          | some inserted =>
              have ih' := ih sorted sortedEq
              have hi := insert?_length before head sorted inserted insertedEq
              simp only [sortedEq, insertedEq, Option.bind_some] at computed
              have hres : inserted = result := Option.some.inj computed
              subst result
              simp only [hi, ih', List.length_cons]

/-- Truncating a wide ranking to a narrower slot count is exactly the narrow ranking, provided the
node fits in the narrow count.  Stated for an actual successful wide run (no output is assumed):
the narrow run returns the same child prefix.  Both calls use the same `before` comparator, so the
statement concerns only the padding/arity layer and applies to every recursive caller that threads
one comparator. -/
theorem rankedWithSlots?_take_eq
    (mol : RawMolecule) (profile : Profile)
    (before : Cursor → Cursor → Option Ordering) (parent : Cursor)
    (small big : Nat) (hsmall : small ≤ big)
    (hchildren : (((parent.original mol).children mol).map Cursor.actual).length ≤ small)
    (sorted : List Cursor)
    (hbig : rankedWithSlots? mol profile before parent big = some sorted) :
    rankedWithSlots? mol profile before parent small = some (sorted.take small) := by
  unfold rankedWithSlots? at hbig ⊢
  dsimp only [Bind.bind] at hbig ⊢
  simp only [if_neg (show ¬ (big < (((parent.original mol).children mol).map Cursor.actual).length)
    by omega)] at hbig
  simp only [if_neg (show ¬ (small < (((parent.original mol).children mol).map Cursor.actual).length)
    by omega)]
  cases hcursor : cursor? mol profile parent with
  | none => simp [hcursor] at hbig
  | some distance =>
      cases hmap : (((parent.original mol).children mol).map Cursor.actual).mapM
          (cursor? mol profile) with
      | none => simp [hcursor, hmap] at hbig
      | some validated =>
          cases hsort :
              sort? before (((parent.original mol).children mol).map Cursor.actual) with
          | none => simp [hcursor, hmap, hsort] at hbig
          | some sortedChildren =>
              simp only [hcursor, hmap, hsort, Option.bind_some, Option.some.injEq] at hbig ⊢
              rw [← hbig]
              have hlen : sortedChildren.length =
                  (((parent.original mol).children mol).map Cursor.actual).length :=
                sort?_length before _ sortedChildren hsort
              have hle : sortedChildren.length ≤ small := by omega
              rw [List.take_append]
              rw [List.take_of_length_le hle]
              rw [List.take_replicate]
              simp only [Nat.min_eq_left (Nat.sub_le_sub_right hsmall sortedChildren.length)]

/-- **Ordinary ranking is the three-element prefix of authoritative ranking** on every node whose
child count fits the ordinary arity.  This is the general commuting lemma for the actual
`ranked?` caller: no rule is inspected. -/
theorem ranked?_false_eq_take_of_true
    (mol : RawMolecule) (profile : Profile)
    (before : Cursor → Cursor → Option Ordering) (parent : Cursor)
    (sorted : List Cursor)
    (htrue : ranked? mol profile true before parent = some sorted)
    (hchildren : (((parent.original mol).children mol).map Cursor.actual).length ≤ 3) :
    ranked? mol profile false before parent = some (sorted.take 3) := by
  rw [ranked?_true_eq_rankedWithSlots?] at htrue
  rw [ranked?_false_eq_rankedWithSlots?]
  exact rankedWithSlots?_take_eq mol profile before parent 3 5 (by omega) hchildren sorted htrue

/-- **Arity mode-split schema.**  For the same molecule, profile, comparator and parent, if the
node has four or more children then the ordinary framed ranking returns `none`, regardless of what
the authoritative side does.  This is a conditional schema on the caller-supplied hypothesis
`4 ≤ children.length`; it does **not** assert that a molecule with such a node exists. -/
theorem ranked?_false_eq_none_of_four_le
    (mol : RawMolecule) (profile : Profile)
    (before : Cursor → Cursor → Option Ordering) (parent : Cursor)
    (hchildren : 4 ≤ (((parent.original mol).children mol).map Cursor.actual).length) :
    ranked? mol profile false before parent = none := by
  rw [ranked?_false_eq_rankedWithSlots?]
  unfold rankedWithSlots?
  dsimp only [Bind.bind]
  cases cursor? mol profile parent with
  | none => rfl
  | some distance =>
      have hlt : 3 < (((parent.original mol).children mol).map Cursor.actual).length := by omega
      simp only [if_pos hlt, Option.bind_some]

/-- Corollary in the form used by a caller: whenever the authoritative ranking succeeds on a node
with at least four children, the ordinary ranking refuses. -/
theorem ranked?_false_eq_none_of_true_some_of_four_le
    (mol : RawMolecule) (profile : Profile)
    (before : Cursor → Cursor → Option Ordering) (parent : Cursor)
    (sorted : List Cursor)
    (_htrue : ranked? mol profile true before parent = some sorted)
    (hchildren : 4 ≤ (((parent.original mol).children mol).map Cursor.actual).length) :
    ranked? mol profile false before parent = none :=
  ranked?_false_eq_none_of_four_le mol profile before parent hchildren

/-! ### The second exact mode split: mixed empty/nonempty Rule-4b shapes

`compareRule4b?` orders the mixed shapes only in authoritative mode; the ordinary mode refuses.
The lemma below records the difference exactly at the caller-visible option level, for the same
molecule, profile, state, fuel and cursors, **conditional** on the two reference-selection
hypotheses `leftEmpty` / `rightSingle`.  It does not construct concrete inputs nor prove that the
selected reference lists arise from any molecule. -/

theorem compareRule4b?_false_none_of_left_empty_right_single
    (mol : RawMolecule) (profile : Profile) (state : OccurrenceAuxState)
    (fuel : Nat) (left right : Cursor) (reference : RS)
    (leftEmpty : rule4bReferences? mol profile state fuel [left] = some [])
    (rightSingle : rule4bReferences? mol profile state fuel [right] = some [reference]) :
    compareRule4b? mol profile false state fuel left right = none ∧
      compareRule4b? mol profile true state fuel left right = some Ordering.lt := by
  constructor
  · simp only [compareRule4b?]
    dsimp only [Bind.bind]
    simp [leftEmpty, rightSingle]
  · simp only [compareRule4b?]
    dsimp only [Bind.bind]
    simp [leftEmpty, rightSingle]

end FrameRuntime







theorem insertOccurrenceTrackedAuthoritative?_eq_of_insertOccurrenceTracked
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (candidate : CanonicalRerootCursor)
    (cursors : List CanonicalRerootCursor) (result : List CanonicalRerootCursor × Nat)
    (computed : insertOccurrenceTracked mol state fuel candidate cursors = some result) :
    insertOccurrenceTrackedAuthoritative? mol state fuel candidate cursors = some result := by
  induction cursors generalizing result with
  | nil =>
      simp only [insertOccurrenceTracked] at computed
      simp only [insertOccurrenceTrackedAuthoritative?]
      exact computed
  | cons head tail ih =>
      simp only [insertOccurrenceTracked] at computed
      dsimp only [Bind.bind] at computed
      cases comparisonEq : compareOccurrenceBranches? mol state fuel candidate head with
      | none => simp [comparisonEq] at computed
      | some decision =>
          have completeEq :
              compareOccurrenceBranchesComplete? mol state fuel candidate head =
                some decision := by
            simp only [compareOccurrenceBranchesComplete?, comparisonEq]
          cases insertedEq : insertOccurrenceTracked mol state fuel candidate tail with
          | none =>
              simp only [comparisonEq, insertedEq, Option.bind_some] at computed
              by_cases hlt : (decision.ordering == Ordering.lt) = true
              · rw [if_pos hlt] at computed
                simp at computed
              · rw [if_neg hlt] at computed
                simp only [insertOccurrenceTrackedAuthoritative?, completeEq]
                dsimp only [Bind.bind]
                simp only [Option.bind_some]
                rw [if_neg hlt]
                exact computed
          | some inserted =>
              have insertedAuthoritative :
                  insertOccurrenceTrackedAuthoritative? mol state fuel candidate tail =
                    some inserted :=
                ih inserted insertedEq
              simp only [comparisonEq, insertedEq, Option.bind_some] at computed
              simp only [insertOccurrenceTrackedAuthoritative?, completeEq,
                insertedAuthoritative]
              dsimp only [Bind.bind]
              simp only [Option.bind_some]
              exact computed

theorem sortOccurrencesTrackedAuthoritative?_eq_of_sortOccurrencesTracked
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (cursors : List CanonicalRerootCursor) (result : List CanonicalRerootCursor × Nat)
    (computed : sortOccurrencesTracked? mol state fuel cursors = some result) :
    sortOccurrencesTrackedAuthoritative? mol state fuel cursors = some result := by
  induction cursors generalizing result with
  | nil =>
      simp only [sortOccurrencesTracked?] at computed
      simp only [sortOccurrencesTrackedAuthoritative?]
      exact computed
  | cons head tail ih =>
      simp only [sortOccurrencesTracked?] at computed
      dsimp only [Bind.bind] at computed
      cases sortedEq : sortOccurrencesTracked? mol state fuel tail with
      | none => simp [sortedEq] at computed
      | some sorted =>
          cases insertedEq : insertOccurrenceTracked mol state fuel head sorted.1 with
          | none => simp [sortedEq, insertedEq] at computed
          | some inserted =>
              have sortedAuthoritative :
                  sortOccurrencesTrackedAuthoritative? mol state fuel tail = some sorted :=
                ih sorted sortedEq
              have insertedAuthoritative :
                  insertOccurrenceTrackedAuthoritative? mol state fuel head sorted.1 =
                    some inserted :=
                insertOccurrenceTrackedAuthoritative?_eq_of_insertOccurrenceTracked
                  mol state fuel head sorted.1 inserted insertedEq
              simp only [sortedEq, insertedEq, Option.bind_some] at computed
              simp only [sortOccurrencesTrackedAuthoritative?]
              dsimp only [Bind.bind]
              rw [sortedAuthoritative]
              simp only [Option.bind_some]
              rw [insertedAuthoritative]
              simpa only [Option.bind_some] using computed

theorem compareOccurrenceAdjacentPairsAuthoritative?_eq_map_of_compareOccurrenceAdjacentPairs
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (cursors : List CanonicalRerootCursor)
    (compared : List (OccurrenceComparedPair mol state fuel))
    (computed : compareOccurrenceAdjacentPairs? mol state fuel cursors = some compared) :
    compareOccurrenceAdjacentPairsAuthoritative? mol state fuel cursors =
      some (compared.map fun comparison => comparison.decision) := by
  induction cursors generalizing compared with
  | nil =>
      simp [compareOccurrenceAdjacentPairs?] at computed
      subst compared
      rfl
  | cons left tail ih =>
      cases tail with
      | nil =>
          simp [compareOccurrenceAdjacentPairs?] at computed
          subst compared
          rfl
      | cons right remaining =>
          simp only [compareOccurrenceAdjacentPairs?] at computed
          cases comparisonEq : compareOccurrenceBranches? mol state fuel left right with
          | none => simp [comparisonEq] at computed
          | some decision =>
              cases deeperEq : compareOccurrenceAdjacentPairs? mol state fuel
                  (right :: remaining) with
              | none => simp [comparisonEq, deeperEq] at computed
              | some deeper =>
                  simp [comparisonEq, deeperEq] at computed
                  subst compared
                  have completeEq :
                      compareOccurrenceBranchesComplete? mol state fuel left right =
                        some decision := by
                    simp only [compareOccurrenceBranchesComplete?, comparisonEq]
                  have deeperAuthoritative := ih deeper deeperEq
                  simp only [compareOccurrenceAdjacentPairsAuthoritative?, completeEq,
                    deeperAuthoritative]
                  rfl

/-- **Legacy conservative extension.**  Every successful ordinary legacy fact is reproduced
verbatim by the authoritative legacy evaluator, at the same state and node. -/
theorem legacyOccurrenceFactAuthoritative?_eq_of_legacyOccurrenceFact
    (mol : RawMolecule) (fuel : Nat) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact)
    (computed : legacyOccurrenceFact? mol fuel state node = some fact) :
    legacyOccurrenceFactAuthoritative? mol fuel state node = some fact := by
  unfold legacyOccurrenceFact? at computed
  dsimp only [Bind.bind] at computed
  simp only [Option.bind_eq_some_iff] at computed
  rcases computed with
    ⟨spec, specEq, parity, parityEq, roots, rootsEq, sorted, sortedEq,
      positions, positionsEq, compared, comparedEq, finalEq⟩
  have sortedAuthoritative :
      sortOccurrencesTrackedAuthoritative? mol state fuel roots = some sorted :=
    sortOccurrencesTrackedAuthoritative?_eq_of_sortOccurrencesTracked
      mol state fuel roots sorted sortedEq
  have comparedAuthoritative :
      compareOccurrenceAdjacentPairsAuthoritative? mol state fuel sorted.1 =
        some (compared.map fun comparison => comparison.decision) :=
    compareOccurrenceAdjacentPairsAuthoritative?_eq_map_of_compareOccurrenceAdjacentPairs
      mol state fuel sorted.1 compared comparedEq
  unfold legacyOccurrenceFactAuthoritative?
  dsimp only [Bind.bind]
  simp only [specEq, parityEq, rootsEq, sortedAuthoritative, positionsEq,
    comparedAuthoritative, Option.bind_some]
  exact finalEq

/-- Public corollary on the legacy branch of the dispatcher: when no generated-real-tree profile
exists, ordinary success transports to the authoritative callback. -/
theorem occurrenceFactAuthoritative?_eq_of_occurrenceFact?_of_profile_none
    (mol : RawMolecule) (fuel : Nat) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact)
    (unavailable : FrameRuntime.profile? mol node = none)
    (computed : occurrenceFact? mol fuel state node = some fact) :
    occurrenceFactAuthoritative? mol fuel state node = some fact := by
  rw [occurrenceFact?_eq_legacy_of_profile_none mol fuel state node unavailable] at computed
  rw [occurrenceFactAuthoritative?_eq_legacy_of_profile_none mol fuel state node unavailable]
  exact legacyOccurrenceFactAuthoritative?_eq_of_legacyOccurrenceFact
    mol fuel state node fact computed

/-! ## 5. Batch discovery commutes

`discoverOccurrenceAuxBatches` is total (`filterMap`, silently dropping unavailable labels) while
`discoverOccurrenceAuxBatchesAuthoritative?` is fail-closed (`mapM`).  On a successful run of the
latter the two produce exactly the same final state *for the same callback*.  This is a general
same-callback commuting primitive: it is independent of the rule family, but it deliberately does
**not** assert equality of the two actual builders, whose callbacks
(`occurrenceFact?` versus `occurrenceFactAuthoritative?`) and failure disciplines differ. -/

theorem filterMap_eq_of_mapM_some {α β : Type*} (f : α → Option β) :
    ∀ (inputs : List α) (outputs : List β),
      inputs.mapM f = some outputs → inputs.filterMap f = outputs := by
  intro inputs
  induction inputs with
  | nil =>
      intro outputs computed
      rw [List.mapM_nil] at computed
      have hout : outputs = [] := Option.some.inj computed.symm
      subst outputs
      rfl
  | cons head tail ih =>
      intro outputs computed
      rw [List.mapM_cons] at computed
      cases headComputed : f head with
      | none => simp [headComputed] at computed
      | some headOut =>
          cases tailComputed : tail.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tailOut =>
              simp [headComputed, tailComputed] at computed
              subst outputs
              rw [List.filterMap_cons_some headComputed, ih tailOut tailComputed]

theorem discoverAuxBatches_ordinary_zero_nil
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (state : OccurrenceAuxState) :
    discoverOccurrenceAuxBatches label? 0 [] state = state := rfl

theorem discoverAuxBatches_ordinary_zero_cons
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (head : RawMolecule.CanonicalBranchNode)
    (tail : List RawMolecule.CanonicalBranchNode) (state : OccurrenceAuxState) :
    discoverOccurrenceAuxBatches label? 0 (head :: tail) state = state := rfl

theorem discoverAuxBatches_ordinary_succ_nil
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (remaining : Nat) (state : OccurrenceAuxState) :
    discoverOccurrenceAuxBatches label? (Nat.succ remaining) [] state = state := rfl

theorem discoverAuxBatches_ordinary_succ_cons
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (remaining : Nat) (head : RawMolecule.CanonicalBranchNode)
    (tail : List RawMolecule.CanonicalBranchNode) (state : OccurrenceAuxState) :
    discoverOccurrenceAuxBatches label? (Nat.succ remaining) (head :: tail) state =
      discoverOccurrenceAuxBatches label? remaining
        ((head :: tail).dropWhile (fun node => node.depth == head.depth))
        (state ++ ((head :: tail).takeWhile (fun node => node.depth == head.depth)).filterMap
          (label? state)) := rfl

theorem discoverAuxBatchesAuthoritative_zero_nil
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (state : OccurrenceAuxState) :
    discoverOccurrenceAuxBatchesAuthoritative? label? 0 [] state = some state := rfl

theorem discoverAuxBatchesAuthoritative_zero_cons
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (head : RawMolecule.CanonicalBranchNode)
    (tail : List RawMolecule.CanonicalBranchNode) (state : OccurrenceAuxState) :
    discoverOccurrenceAuxBatchesAuthoritative? label? 0 (head :: tail) state = none := rfl

theorem discoverAuxBatchesAuthoritative_succ_nil
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (remaining : Nat) (state : OccurrenceAuxState) :
    discoverOccurrenceAuxBatchesAuthoritative? label? (Nat.succ remaining) [] state =
      some state := rfl

theorem discoverAuxBatchesAuthoritative_succ_cons
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (remaining : Nat) (head : RawMolecule.CanonicalBranchNode)
    (tail : List RawMolecule.CanonicalBranchNode) (state : OccurrenceAuxState) :
    discoverOccurrenceAuxBatchesAuthoritative? label? (Nat.succ remaining) (head :: tail) state =
      ((head :: tail).takeWhile (fun node => node.depth == head.depth)).mapM
          (fun node => label? state node) >>=
        (fun batch =>
          discoverOccurrenceAuxBatchesAuthoritative? label? remaining
            ((head :: tail).dropWhile (fun node => node.depth == head.depth))
            (state ++ batch)) := rfl

/-- **Batch discovery commutes.**  A successful fail-closed authoritative run yields exactly the
state of the ordinary total run, for the same callback, fuel, node list and initial state. -/
theorem discoverOccurrenceAuxBatches_eq_of_authoritative
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact) :
    ∀ (fuel : Nat) (nodes : List RawMolecule.CanonicalBranchNode)
      (state final : OccurrenceAuxState),
      discoverOccurrenceAuxBatchesAuthoritative? label? fuel nodes state = some final →
      discoverOccurrenceAuxBatches label? fuel nodes state = final := by
  intro fuel
  induction fuel with
  | zero =>
      intro nodes state final computed
      cases nodes with
      | nil =>
          rw [discoverAuxBatchesAuthoritative_zero_nil] at computed
          rw [discoverAuxBatches_ordinary_zero_nil]
          exact Option.some.inj computed
      | cons head tail =>
          rw [discoverAuxBatchesAuthoritative_zero_cons] at computed
          cases computed
  | succ remaining ih =>
      intro nodes state final computed
      cases nodes with
      | nil =>
          rw [discoverAuxBatchesAuthoritative_succ_nil] at computed
          rw [discoverAuxBatches_ordinary_succ_nil]
          exact Option.some.inj computed
      | cons head tail =>
          rw [discoverAuxBatchesAuthoritative_succ_cons] at computed
          dsimp only [Bind.bind] at computed
          simp only [Option.bind_eq_some_iff] at computed
          rcases computed with ⟨batch, hbatch, hrec⟩
          have hrec' :=
            ih ((head :: tail).dropWhile (fun node => node.depth == head.depth))
              (state ++ batch) final hrec
          rw [discoverAuxBatches_ordinary_succ_cons]
          change discoverOccurrenceAuxBatches label? remaining
            ((head :: tail).dropWhile (fun node => node.depth == head.depth))
            (state ++ ((head :: tail).takeWhile
              (fun node => node.depth == head.depth)).filterMap
                (fun node => label? state node)) = final
          rw [filterMap_eq_of_mapM_some (fun node => label? state node)
            ((head :: tail).takeWhile (fun node => node.depth == head.depth)) batch hbatch]
          exact hrec'

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.generalMancudeRule1aLabelAuthoritative?_eq_generalMancudeRule1aLabel?
assert_kernel_only TetraStereo.OneCenter.mancudeRule1aLabelAuthoritative?_eq_mancudeRule1aLabel?
assert_kernel_only TetraStereo.OneCenter.canonicalRule1aLabelAuthoritative?_eq_canonicalRule1aLabel?
assert_kernel_only TetraStereo.OneCenter.compareCanonicalNodeRuleAuthoritative?_eq_compareCanonicalNodeRule?
assert_kernel_only TetraStereo.OneCenter.FrameRuntime.label?_false_eq_true
assert_kernel_only TetraStereo.OneCenter.FrameRuntime.pairLabels?_false_eq_true
assert_kernel_only TetraStereo.OneCenter.FrameRuntime.throughLabels?_false_eq_true
assert_kernel_only TetraStereo.OneCenter.FrameRuntime.ranked?_false_eq_rankedWithSlots?
assert_kernel_only TetraStereo.OneCenter.FrameRuntime.ranked?_true_eq_rankedWithSlots?
assert_kernel_only TetraStereo.OneCenter.FrameRuntime.insert?_length
assert_kernel_only TetraStereo.OneCenter.FrameRuntime.sort?_length
assert_kernel_only TetraStereo.OneCenter.FrameRuntime.rankedWithSlots?_take_eq
assert_kernel_only TetraStereo.OneCenter.FrameRuntime.ranked?_false_eq_take_of_true
assert_kernel_only TetraStereo.OneCenter.FrameRuntime.ranked?_false_eq_none_of_four_le
assert_kernel_only TetraStereo.OneCenter.FrameRuntime.ranked?_false_eq_none_of_true_some_of_four_le
assert_kernel_only TetraStereo.OneCenter.FrameRuntime.compareRule4b?_false_none_of_left_empty_right_single
assert_kernel_only TetraStereo.OneCenter.insertOccurrenceTrackedAuthoritative?_eq_of_insertOccurrenceTracked
assert_kernel_only TetraStereo.OneCenter.sortOccurrencesTrackedAuthoritative?_eq_of_sortOccurrencesTracked
assert_kernel_only TetraStereo.OneCenter.compareOccurrenceAdjacentPairsAuthoritative?_eq_map_of_compareOccurrenceAdjacentPairs
assert_kernel_only TetraStereo.OneCenter.legacyOccurrenceFactAuthoritative?_eq_of_legacyOccurrenceFact
assert_kernel_only TetraStereo.OneCenter.occurrenceFactAuthoritative?_eq_of_occurrenceFact?_of_profile_none
assert_kernel_only TetraStereo.OneCenter.filterMap_eq_of_mapM_some
assert_kernel_only TetraStereo.OneCenter.discoverAuxBatches_ordinary_zero_nil
assert_kernel_only TetraStereo.OneCenter.discoverAuxBatches_ordinary_zero_cons
assert_kernel_only TetraStereo.OneCenter.discoverAuxBatches_ordinary_succ_nil
assert_kernel_only TetraStereo.OneCenter.discoverAuxBatches_ordinary_succ_cons
assert_kernel_only TetraStereo.OneCenter.discoverAuxBatchesAuthoritative_zero_nil
assert_kernel_only TetraStereo.OneCenter.discoverAuxBatchesAuthoritative_zero_cons
assert_kernel_only TetraStereo.OneCenter.discoverAuxBatchesAuthoritative_succ_nil
assert_kernel_only TetraStereo.OneCenter.discoverAuxBatchesAuthoritative_succ_cons
assert_kernel_only TetraStereo.OneCenter.discoverOccurrenceAuxBatches_eq_of_authoritative
