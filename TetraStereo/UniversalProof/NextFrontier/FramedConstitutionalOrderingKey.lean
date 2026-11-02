import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorOrderingKey

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096







namespace TetraStereo.OneCenter.FramedConstitutionalOrderingKey

open RawMolecule FrameRuntime FramedOrderingKeyCore
open FramedDescriptorOrderingKey (denseNext sparseNext children_terminal terminal_padding
  denseNext_fst denseNext_snd compareLex_append_same_length)

abbrev Pair := Cursor × Cursor

structure Context where
  mol : RawMolecule
  profile : Profile
  authoritative : Bool

def distance (ctx : Context) : Cursor → Nat
  | .actual cursor => (cursor? ctx.mol ctx.profile (.actual cursor)).getD 0
  | .padding parent => distance ctx parent + 1

theorem distance_success (ctx : Context) : ∀ cursor observed,
    cursor? ctx.mol ctx.profile cursor = some observed → distance ctx cursor = observed
  | .actual cursor, observed, computed => by simp [distance, computed]
  | .padding parent, observed, computed => by
      cases parentEq : cursor? ctx.mol ctx.profile parent with
      | none => simp [cursor?, parentEq] at computed
      | some parentDistance =>
          have recursive := distance_success ctx parent parentDistance parentEq
          simpa [cursor?, parentEq, distance, recursive] using computed

def atomicLabel? (ctx : Context) (cursor : Cursor) : Option CIPAtomicLabel :=
  if ctx.authoritative then
    ctx.mol.canonicalRule1aLabelAuthoritative? (cursor.original ctx.mol).node
  else ctx.mol.canonicalRule1aLabel? (cursor.original ctx.mol).node

def atomicLabel (ctx : Context) (cursor : Cursor) : CIPAtomicLabel :=
  (atomicLabel? ctx cursor).getD { numerator := 0, denominator := 1 }

def mass (ctx : Context) (cursor : Cursor) : Nat :=
  match (cursor.original ctx.mol).node.provenance with
  | .realAtom => ctx.mol.atomMassAt (cursor.original ctx.mol).node.atom
  | _ => 0

def compareDistance (left right : Nat) : Ordering :=
  if left < right then .gt else if right < left then .lt else .eq

def compareLabel (ctx : Context) (rule : CanonicalRuleStage) (left right : Cursor) : Ordering :=
  match rule with
  | .rule1a => compareCIPAtomicLabel (atomicLabel ctx left) (atomicLabel ctx right)
  | .rule1b => compareDistance (distance ctx left) (distance ctx right)
  | .rule2 => compare (mass ctx left) (mass ctx right)

theorem label_success (ctx : Context) (rule : CanonicalRuleStage) (left right : Cursor)
    (decision : Ordering)
    (computed : label? ctx.mol ctx.profile ctx.authoritative rule left right = some decision) :
    compareLabel ctx rule left right = decision := by
  cases leftEq : cursor? ctx.mol ctx.profile left with
  | none => simp [label?, leftEq] at computed
  | some ld =>
      cases rightEq : cursor? ctx.mol ctx.profile right with
      | none => simp [label?, leftEq, rightEq] at computed
      | some rd =>
          have leftDistance := distance_success ctx left ld leftEq
          have rightDistance := distance_success ctx right rd rightEq
          cases rule with
          | rule1a =>
              have labels : ((atomicLabel? ctx left).bind (fun a =>
                  (atomicLabel? ctx right).bind (fun b => some (compareCIPAtomicLabel a b)))) = some decision := by
                cases mode : ctx.authoritative with
                | false =>
                    simpa [label?, leftEq, rightEq, mode, atomicLabel?,
                      compareCanonicalNodeRule?] using computed
                | true =>
                    simpa [label?, leftEq, rightEq, mode, atomicLabel?,
                      compareCanonicalNodeRuleAuthoritative?] using computed
              cases l : atomicLabel? ctx left with
              | none => simp [l] at labels
              | some ll =>
                  cases r : atomicLabel? ctx right with
                  | none => simp [l, r] at labels
                  | some rr => simpa [compareLabel, atomicLabel, l, r] using labels
          | rule1b =>
              simpa [label?, leftEq, rightEq, compareLabel, compareDistance,
                leftDistance, rightDistance] using computed
          | rule2 =>
              cases mode : ctx.authoritative with
              | false =>
                  simpa [label?, leftEq, rightEq, mode, compareCanonicalNodeRule?,
                    compareCanonicalNodeRule, compareLabel, mass] using computed
              | true =>
                  simpa [label?, leftEq, rightEq, mode, compareCanonicalNodeRuleAuthoritative?,
                    compareCanonicalNodeRule, compareLabel, mass] using computed

def pairLabels (ctx : Context) (rule : CanonicalRuleStage) (pairs : List Pair) : Ordering :=
  List.compareLex (compareLabel ctx rule) (pairs.map Prod.fst) (pairs.map Prod.snd)

theorem pairLabels_success (ctx : Context) (rule : CanonicalRuleStage) :
    ∀ pairs decision,
    FrameRuntime.pairLabels? ctx.mol ctx.profile ctx.authoritative rule pairs = some decision →
    pairLabels ctx rule pairs = decision
  | [], decision, computed => by simpa [FrameRuntime.pairLabels?, pairLabels] using computed
  | pair :: pairs, decision, computed => by
      cases labelEq : label? ctx.mol ctx.profile ctx.authoritative rule pair.1 pair.2 with
      | none => simp [FrameRuntime.pairLabels?, labelEq] at computed
      | some current =>
          have total := label_success ctx rule pair.1 pair.2 current labelEq
          cases current with
          | lt => simpa [FrameRuntime.pairLabels?, labelEq, pairLabels, List.compareLex, total] using computed
          | gt => simpa [FrameRuntime.pairLabels?, labelEq, pairLabels, List.compareLex, total] using computed
          | eq =>
              have recursive := pairLabels_success ctx rule pairs decision
                (by simpa [FrameRuntime.pairLabels?, labelEq] using computed)
              simpa [pairLabels, List.compareLex, total] using recursive

theorem next_success (ctx : Context) (before : Cursor → Cursor → Option Ordering) :
    ∀ pairs result,
    nextPairs? ctx.mol ctx.profile ctx.authoritative before pairs = some result →
    sparseNext ctx.mol ctx.authoritative before before pairs = result
  | [], result, computed => by simpa [nextPairs?, sparseNext] using computed
  | pair :: pairs, result, computed => by
      cases restEq : nextPairs? ctx.mol ctx.profile ctx.authoritative before pairs with
      | none => simp [nextPairs?, restEq] at computed
      | some rest =>
          have restTotal := next_success ctx before pairs rest restEq
          by_cases terminalEq : terminal ctx.mol pair.1 && terminal ctx.mol pair.2
          · simpa [nextPairs?, sparseNext, restEq, terminalEq, restTotal] using computed
          · cases leftEq : ranked? ctx.mol ctx.profile ctx.authoritative before pair.1 with
            | none => simp [nextPairs?, restEq, terminalEq, leftEq] at computed
            | some left =>
                cases rightEq : ranked? ctx.mol ctx.profile ctx.authoritative before pair.2 with
                | none => simp [nextPairs?, restEq, terminalEq, leftEq, rightEq] at computed
                | some right =>
                    have leftTotal := ranked_success ctx.mol ctx.profile ctx.authoritative before
                      pair.1 left leftEq
                    have rightTotal := ranked_success ctx.mol ctx.profile ctx.authoritative before
                      pair.2 right rightEq
                    simpa [nextPairs?, sparseNext, restEq, terminalEq, leftEq, rightEq,
                      leftTotal, rightTotal, restTotal] using computed

def sparseRule (ctx : Context) (before : Cursor → Cursor → Option Ordering)
    (rule : CanonicalRuleStage) : Nat → List Pair → Ordering
  | 0, pairs => pairLabels ctx rule pairs
  | depth + 1, pairs =>
      (pairLabels ctx rule pairs).then (sparseRule ctx before rule depth
        (sparseNext ctx.mol ctx.authoritative before before pairs))

def denseRule (ctx : Context) (before : Cursor → Cursor → Option Ordering)
    (rule : CanonicalRuleStage) : Nat → List Pair → Ordering
  | 0, pairs => pairLabels ctx rule pairs
  | depth + 1, pairs =>
      (pairLabels ctx rule pairs).then (denseRule ctx before rule depth
        (denseNext ctx.mol ctx.authoritative before before pairs))

@[simp] theorem sparseRule_nil (ctx : Context) (before : Cursor → Cursor → Option Ordering)
    (rule : CanonicalRuleStage) : ∀ depth, sparseRule ctx before rule depth [] = .eq
  | 0 => rfl
  | depth + 1 => by simp [sparseRule, pairLabels, sparseNext, sparseRule_nil, List.compareLex]

theorem rule_success_sparse (ctx : Context) (before : Cursor → Cursor → Option Ordering)
    (rule : CanonicalRuleStage) : ∀ fuel pairs decision,
    compareRule? ctx.mol ctx.profile ctx.authoritative before rule fuel pairs = some decision →
    sparseRule ctx before rule fuel pairs = decision := by
  intro fuel
  induction fuel with
  | zero =>
      intro pairs decision computed
      rw [compareRule?] at computed
      by_cases cap : !ctx.authoritative && defaultBranchWidthCap < pairs.length
      · simp [cap] at computed
      · cases labels : FrameRuntime.pairLabels? ctx.mol ctx.profile ctx.authoritative rule pairs with
        | none => simp [cap, labels] at computed
        | some current =>
            have totalLabels := pairLabels_success ctx rule pairs current labels
            cases current with
            | lt => simpa [cap, labels, sparseRule, totalLabels] using computed
            | gt => simpa [cap, labels, sparseRule, totalLabels] using computed
            | eq =>
                cases nextEq : nextPairs? ctx.mol ctx.profile ctx.authoritative before pairs with
                | none => simp [cap, labels, nextEq] at computed
                | some next =>
                    cases next with
                    | nil => simpa [cap, labels, nextEq, sparseRule, totalLabels] using computed
                    | cons head tail => simp [cap, labels, nextEq] at computed
  | succ fuel ih =>
      intro pairs decision computed
      rw [compareRule?] at computed
      by_cases cap : !ctx.authoritative && defaultBranchWidthCap < pairs.length
      · simp [cap] at computed
      · cases labels : FrameRuntime.pairLabels? ctx.mol ctx.profile ctx.authoritative rule pairs with
        | none => simp [cap, labels] at computed
        | some current =>
            have totalLabels := pairLabels_success ctx rule pairs current labels
            cases current with
            | lt => simpa [cap, labels, sparseRule, totalLabels] using computed
            | gt => simpa [cap, labels, sparseRule, totalLabels] using computed
            | eq =>
                cases nextEq : nextPairs? ctx.mol ctx.profile ctx.authoritative before pairs with
                | none => simp [cap, labels, nextEq] at computed
                | some next =>
                    have totalNext := next_success ctx before pairs next nextEq
                    cases next with
                    | nil => simpa [cap, labels, nextEq, sparseRule, totalLabels, totalNext] using computed
                    | cons head tail =>
                        have recursive : compareRule? ctx.mol ctx.profile ctx.authoritative before rule
                            fuel (head :: tail) = some decision := by
                          simpa [cap, labels, nextEq] using computed
                        simpa [sparseRule, totalLabels, totalNext] using ih (head :: tail) decision recursive

@[simp] theorem atomicLabel_padding (ctx : Context) (cursor : Cursor) :
    atomicLabel ctx (.padding cursor) = { numerator := 0, denominator := 1 } := by
  cases mode : ctx.authoritative with
  | false =>
      simp [atomicLabel, atomicLabel?, mode, Cursor.original, canonicalPhantom,
        canonicalRule1aLabel?]
  | true =>
      simp [atomicLabel, atomicLabel?, mode, Cursor.original, canonicalPhantom,
        canonicalRule1aLabelAuthoritative?]

@[simp] theorem mass_padding (ctx : Context) (cursor : Cursor) : mass ctx (.padding cursor) = 0 := by
  simp [mass, Cursor.original, canonicalPhantom]

theorem compareDistance_eq_implies_eq (left right : Nat)
    (tied : compareDistance left right = .eq) : left = right := by
  by_cases hl : left < right
  · simp [compareDistance, hl] at tied
  · by_cases hr : right < left
    · simp [compareDistance, hl, hr] at tied
    · omega

theorem padding_tied (ctx : Context) (rule : CanonicalRuleStage) (left right : Cursor)
    (tied : compareLabel ctx rule left right = .eq) :
    compareLabel ctx rule (.padding left) (.padding right) = .eq := by
  cases rule with
  | rule1a => simp [compareLabel]
  | rule2 => simp [compareLabel]
  | rule1b =>
      have distances := compareDistance_eq_implies_eq (distance ctx left) (distance ctx right) tied
      simp [compareLabel, distance, distances, compareDistance]

def Silent (ctx : Context) (rule : CanonicalRuleStage) (pair : Pair) : Prop :=
  terminal ctx.mol pair.1 = true ∧ terminal ctx.mol pair.2 = true ∧
    compareLabel ctx rule pair.1 pair.2 = .eq

inductive Erases (ctx : Context) (rule : CanonicalRuleStage) : List Pair → List Pair → Prop
  | nil : Erases ctx rule [] []
  | keep (pair : Pair) {active dense : List Pair} (tail : Erases ctx rule active dense) :
      Erases ctx rule (pair :: active) (pair :: dense)
  | erase (pair : Pair) {active dense : List Pair} (silent : Silent ctx rule pair)
      (tail : Erases ctx rule active dense) : Erases ctx rule active (pair :: dense)

theorem Erases.labels_eq {ctx : Context} {rule : CanonicalRuleStage} {active dense : List Pair}
    (h : Erases ctx rule active dense) : pairLabels ctx rule active = pairLabels ctx rule dense := by
  induction h with
  | nil => rfl
  | keep pair tail ih =>
      unfold pairLabels at ih ⊢
      simp only [List.map_cons, List.compareLex]
      cases compareLabel ctx rule pair.1 pair.2 <;> simp [ih]
  | erase pair silent tail ih =>
      rcases silent with ⟨_, _, tied⟩
      simpa [pairLabels, List.compareLex, tied] using ih

theorem Erases.keep_all {ctx : Context} {rule : CanonicalRuleStage}
    (initial : List Pair) {active dense : List Pair} (h : Erases ctx rule active dense) :
    Erases ctx rule (initial ++ active) (initial ++ dense) := by
  induction initial with
  | nil => exact h
  | cons pair rest ih => exact .keep pair ih

theorem Erases.erase_all {ctx : Context} {rule : CanonicalRuleStage}
    (initial : List Pair) {active dense : List Pair}
    (allSilent : ∀ pair ∈ initial, Silent ctx rule pair) (h : Erases ctx rule active dense) :
    Erases ctx rule active (initial ++ dense) := by
  induction initial with
  | nil => exact h
  | cons pair rest ih =>
      exact .erase pair (allSilent pair (by simp)) (ih (fun p hp => allSilent p (by simp [hp])))

theorem silent_children (ctx : Context) (before : Cursor → Cursor → Option Ordering)
    (rule : CanonicalRuleStage) (pair : Pair) (h : Silent ctx rule pair) :
    ∀ child ∈ denseNext ctx.mol ctx.authoritative before before [pair], Silent ctx rule child := by
  rcases h with ⟨lt, rt, tied⟩
  intro child member
  have lc := children_terminal ctx.mol ctx.authoritative before pair.1 lt
  have rc := children_terminal ctx.mol ctx.authoritative before pair.2 rt
  simp only [denseNext, List.flatMap_singleton, lc, rc] at member
  have shape : child = (.padding pair.1, .padding pair.2) := by
    have normalized : slots ctx.authoritative ≠ 0 ∧ child = (.padding pair.1, .padding pair.2) := by
      simpa using member
    exact normalized.2
  subst child
  exact ⟨terminal_padding _ _, terminal_padding _ _, padding_tied ctx rule pair.1 pair.2 tied⟩

theorem labels_tied (ctx : Context) (rule : CanonicalRuleStage) : ∀ pairs,
    pairLabels ctx rule pairs = .eq → ∀ pair ∈ pairs, compareLabel ctx rule pair.1 pair.2 = .eq
  | [], _, pair, member => by simp at member
  | head :: tail, tied, pair, member => by
      simp only [pairLabels, List.map_cons, List.compareLex] at tied
      cases headEq : compareLabel ctx rule head.1 head.2 with
      | lt => simp [headEq] at tied
      | gt => simp [headEq] at tied
      | eq =>
          rcases List.mem_cons.mp member with rfl | ht
          · exact headEq
          · exact labels_tied ctx rule tail (by simpa [headEq, pairLabels] using tied) pair ht

theorem Erases.next {ctx : Context} {rule : CanonicalRuleStage} {active dense : List Pair}
    (h : Erases ctx rule active dense) (before : Cursor → Cursor → Option Ordering)
    (allTied : ∀ pair ∈ active, compareLabel ctx rule pair.1 pair.2 = .eq) :
    Erases ctx rule (sparseNext ctx.mol ctx.authoritative before before active)
      (denseNext ctx.mol ctx.authoritative before before dense) := by
  induction h with
  | nil => exact .nil
  | erase pair silent tail ih =>
      have rest := ih allTied
      simpa [denseNext] using Erases.erase_all
        (denseNext ctx.mol ctx.authoritative before before [pair])
        (silent_children ctx before rule pair silent) rest
  | keep pair tail ih =>
      have rest := ih (fun p hp => allTied p (by simp [hp]))
      by_cases ht : terminal ctx.mol pair.1 && terminal ctx.mol pair.2
      · have terminals : terminal ctx.mol pair.1 = true ∧ terminal ctx.mol pair.2 = true :=
          by simpa using ht
        have silent : Silent ctx rule pair := ⟨terminals.1, terminals.2, allTied pair (by simp)⟩
        simpa [sparseNext, ht, denseNext] using Erases.erase_all
          (denseNext ctx.mol ctx.authoritative before before [pair])
          (silent_children ctx before rule pair silent) rest
      · simpa [sparseNext, ht, denseNext] using Erases.keep_all
          ((children ctx.mol ctx.authoritative before pair.1).zip
            (children ctx.mol ctx.authoritative before pair.2)) rest

theorem Erases.refl {ctx : Context} {rule : CanonicalRuleStage} : ∀ pairs, Erases ctx rule pairs pairs
  | [] => .nil
  | pair :: pairs => .keep pair (Erases.refl pairs)

theorem sparse_dense_eq (ctx : Context) (before : Cursor → Cursor → Option Ordering)
    (rule : CanonicalRuleStage) : ∀ depth active dense, Erases ctx rule active dense →
    sparseRule ctx before rule depth active = denseRule ctx before rule depth dense
  | 0, active, dense, related => related.labels_eq
  | depth + 1, active, dense, related => by
      have eqLabels := related.labels_eq
      cases hc : pairLabels ctx rule active with
      | lt => simp [sparseRule, denseRule, ← eqLabels, hc]
      | gt => simp [sparseRule, denseRule, ← eqLabels, hc]
      | eq =>
          have nextRelated := related.next before (labels_tied ctx rule active hc)
          have recursive := sparse_dense_eq ctx before rule depth _ _ nextRelated
          simpa [sparseRule, denseRule, ← eqLabels, hc] using recursive

theorem denseRule_frontiers (ctx : Context) (before : Cursor → Cursor → Option Ordering)
    (rule : CanonicalRuleStage) : ∀ depth pairs,
    denseRule ctx before rule depth pairs =
      List.compareLex (compareLabel ctx rule)
        (frontiers ctx.mol ctx.authoritative before depth (pairs.map Prod.fst)).flatten
        (frontiers ctx.mol ctx.authoritative before depth (pairs.map Prod.snd)).flatten
  | 0, pairs => by simp [denseRule, pairLabels, frontiers]
  | depth + 1, pairs => by
      have appendEq := compareLex_append_same_length (compareLabel ctx rule)
        (pairs.map Prod.fst) (pairs.map Prod.snd)
        (frontiers ctx.mol ctx.authoritative before depth
          (next ctx.mol ctx.authoritative before (pairs.map Prod.fst))).flatten
        (frontiers ctx.mol ctx.authoritative before depth
          (next ctx.mol ctx.authoritative before (pairs.map Prod.snd))).flatten (by simp)
      have tail := denseRule_frontiers ctx before rule depth
        (denseNext ctx.mol ctx.authoritative before before pairs)
      rw [denseNext_fst, denseNext_snd] at tail
      simp only [denseRule, frontiers, List.flatten_cons]
      rw [appendEq, tail]
      rfl

private def atomicLabelValue (label : CIPAtomicLabel) : ℚ :=
  (label.numerator : ℚ) / (label.effectiveDenominator : ℚ)

private def compareAtomicLabelValue (left right : CIPAtomicLabel) : Ordering :=
  Ordering.byKey atomicLabelValue (fun x y => compareOfLessAndEq x y) left right

private theorem compareCIPAtomicLabel_eq_compare_value (left right : CIPAtomicLabel) :
    compareCIPAtomicLabel left right = compareAtomicLabelValue left right := by
  unfold compareCIPAtomicLabel compareAtomicLabelValue Ordering.byKey atomicLabelValue
  rw [LinearOrder.compare_eq_compareOfLessAndEq]
  unfold compareOfLessAndEq
  have leftPositive : (0 : ℚ) < left.effectiveDenominator := by
    have positive : 0 < left.effectiveDenominator := by
      simp [CIPAtomicLabel.effectiveDenominator]
    exact_mod_cast positive
  have rightPositive : (0 : ℚ) < right.effectiveDenominator := by
    have positive : 0 < right.effectiveDenominator := by
      simp [CIPAtomicLabel.effectiveDenominator]
    exact_mod_cast positive
  simp only [div_lt_div_iff₀ leftPositive rightPositive,
    div_eq_div_iff leftPositive.ne' rightPositive.ne']
  norm_cast

private local instance rationalCompareTrans :
    Std.TransCmp (fun left right : ℚ => compareOfLessAndEq left right) :=
  Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm
    (fun value => lt_irrefl value)
    (fun {_ _ _} leftMiddle middleRight => lt_trans leftMiddle middleRight)
    (fun notLeftRight notRightLeft =>
      le_antisymm (le_of_not_gt notRightLeft) (le_of_not_gt notLeftRight))

private local instance atomicValueCompareTrans : Std.TransCmp compareAtomicLabelValue := by
  unfold compareAtomicLabelValue
  infer_instance

private theorem compareCIPAtomicLabel_transCmp : Std.TransCmp compareCIPAtomicLabel where
  eq_swap {left right} := by
    rw [compareCIPAtomicLabel_eq_compare_value,
      compareCIPAtomicLabel_eq_compare_value]
    exact Std.OrientedCmp.eq_swap
  isLE_trans {left middle right} leftMiddle middleRight := by
    rw [compareCIPAtomicLabel_eq_compare_value] at leftMiddle middleRight ⊢
    exact Std.TransCmp.isLE_trans leftMiddle middleRight

private theorem compareDistance_eq_flip_compare (left right : ℕ) :
    compareDistance left right = flip compare left right := by
  by_cases leftRight : left < right
  · have compared : compare right left = Ordering.gt := Nat.compare_eq_gt.mpr leftRight
    simp [compareDistance, leftRight, flip, compared]
  · by_cases rightLeft : right < left
    · have compared : compare right left = Ordering.lt := Nat.compare_eq_lt.mpr rightLeft
      simp [compareDistance, leftRight, rightLeft, flip, compared]
    · have equal : left = right := Nat.le_antisymm (Nat.le_of_not_gt rightLeft)
          (Nat.le_of_not_gt leftRight)
      subst right
      simp [compareDistance, flip]

private local instance distanceTrans : Std.TransCmp compareDistance := by
  have comparatorEq : compareDistance = flip compare := by
    funext left right
    exact compareDistance_eq_flip_compare left right
  rw [comparatorEq]
  infer_instance


structure Key where
  rule1a : List CIPAtomicLabel
  rule1b : List Nat
  rule2 : List Nat
  deriving DecidableEq, Repr

def buildAt (ctx : Context) : Nat → Cursor → Key
  | 0, cursor =>
      { rule1a := [atomicLabel ctx cursor]
        rule1b := [distance ctx cursor]
        rule2 := [mass ctx cursor] }
  | fuel + 1, cursor =>
      let before := compareBranch? ctx.mol ctx.profile ctx.authoritative fuel .rule2
      let nodes := (frontiers ctx.mol ctx.authoritative before (fuel + 1) [cursor]).flatten
      { rule1a := nodes.map (atomicLabel ctx)
        rule1b := nodes.map (distance ctx)
        rule2 := nodes.map (mass ctx) }

def buildKey (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (fuel : Nat) (cursor : Cursor) : Key := buildAt ⟨mol, profile, authoritative⟩ fuel cursor

def compareKeyRule (rule : CanonicalRuleStage) (left right : Key) : Ordering :=
  match rule with
  | .rule1a => List.compareLex compareCIPAtomicLabel left.rule1a right.rule1a
  | .rule1b => List.compareLex compareDistance left.rule1b right.rule1b
  | .rule2 => List.compareLex compare left.rule2 right.rule2

def compareKey (left right : Key) : Ordering :=
  compareLex
    (Ordering.byKey Key.rule1a (List.compareLex compareCIPAtomicLabel))
    (compareLex
      (Ordering.byKey Key.rule1b (List.compareLex compareDistance))
      (Ordering.byKey Key.rule2 (List.compareLex compare))) left right

private local instance atomicCompareTrans : Std.TransCmp compareCIPAtomicLabel :=
  compareCIPAtomicLabel_transCmp

theorem compareKey_transCmp : Std.TransCmp compareKey := by
  unfold compareKey
  infer_instance

theorem compareKey_eq (left right : Key) :
    compareKey left right = (compareKeyRule .rule1a left right).then
      ((compareKeyRule .rule1b left right).then (compareKeyRule .rule2 left right)) := rfl

theorem buildAt_zero_rule (ctx : Context) (rule : CanonicalRuleStage) (left right : Cursor) :
    compareKeyRule rule (buildAt ctx 0 left) (buildAt ctx 0 right) = compareLabel ctx rule left right := by
  cases rule <;> simp [compareKeyRule, buildAt, compareLabel,
    List.compareLex_cons_cons, List.compareLex_nil_nil]

theorem listCompareLex_map {alpha beta : Type*}
    (mapValue : alpha → beta) (compareSource : alpha → alpha → Ordering)
    (compareTarget : beta → beta → Ordering)
    (hcompare : ∀ left right,
      compareTarget (mapValue left) (mapValue right) = compareSource left right) :
    ∀ left right,
      List.compareLex compareTarget (left.map mapValue) (right.map mapValue) =
        List.compareLex compareSource left right := by
  intro left
  induction left with
  | nil => intro right; cases right <;> rfl
  | cons head tail ih =>
      intro right
      cases right with
      | nil => rfl
      | cons other others =>
          simp only [List.map_cons, List.compareLex]
          rw [hcompare]
          cases compareSource head other <;> simp [ih]

theorem rule_success_key (ctx : Context) (rankFuel : Nat) (rule : CanonicalRuleStage)
    (left right : Cursor) (decision : Ordering)
    (computed : compareRule? ctx.mol ctx.profile ctx.authoritative
      (compareBranch? ctx.mol ctx.profile ctx.authoritative rankFuel .rule2) rule
      (rankFuel + 1) [(left, right)] = some decision) :
    compareKeyRule rule (buildAt ctx (rankFuel + 1) left) (buildAt ctx (rankFuel + 1) right) = decision := by
  let before := compareBranch? ctx.mol ctx.profile ctx.authoritative rankFuel .rule2
  have sparse := rule_success_sparse ctx before rule (rankFuel + 1) [(left, right)] decision computed
  have dense := sparse_dense_eq ctx before rule (rankFuel + 1) [(left, right)] [(left, right)]
    (Erases.refl [(left, right)])
  have factor := dense.symm.trans sparse
  rw [denseRule_frontiers] at factor
  cases rule with
  | rule1a =>
      simp only [compareKeyRule, buildAt]
      rw [listCompareLex_map _ _ _ (by intro l r; rfl)]
      simpa [compareLabel, before] using factor
  | rule1b =>
      simp only [compareKeyRule, buildAt]
      rw [listCompareLex_map _ _ _ (by intro l r; rfl)]
      simpa [compareLabel, before] using factor
  | rule2 =>
      simp only [compareKeyRule, buildAt]
      rw [listCompareLex_map _ _ _ (by intro l r; rfl)]
      simpa [compareLabel, before] using factor

private def schedule (first second third : Option Ordering) : Option Ordering := do
  let first ← first
  if first != Ordering.eq then return first
  let second ← second
  if second != Ordering.eq then return second
  third

private theorem schedule_success_of_factors
    (first second third : Option Ordering) (a b c : Ordering)
    (ha : ∀ d, first = some d → a = d)
    (hb : ∀ d, second = some d → b = d)
    (hc : ∀ d, third = some d → c = d)
    (decision : Ordering) (computed : schedule first second third = some decision) :
    a.then (b.then c) = decision := by
  cases firstEq : first with
  | none => simp [schedule, firstEq] at computed
  | some firstDecision =>
      have af := ha firstDecision firstEq
      cases firstDecision with
      | lt => simpa [schedule, firstEq, af] using computed
      | gt => simpa [schedule, firstEq, af] using computed
      | eq =>
          cases secondEq : second with
          | none => simp [schedule, firstEq, secondEq] at computed
          | some secondDecision =>
              have bs := hb secondDecision secondEq
              cases secondDecision with
              | lt => simpa [schedule, firstEq, secondEq, af, bs] using computed
              | gt => simpa [schedule, firstEq, secondEq, af, bs] using computed
              | eq =>
                  have thirdEq : third = some decision := by
                    simpa [schedule, firstEq, secondEq] using computed
                  simpa [af, bs] using hc decision thirdEq

private theorem throughLabels_success (ctx : Context) (left right : Cursor) (decision : Ordering)
    (computed : throughLabels? ctx.mol ctx.profile ctx.authoritative .rule2 left right = some decision) :
    (compareLabel ctx .rule1a left right).then
      ((compareLabel ctx .rule1b left right).then (compareLabel ctx .rule2 left right)) = decision := by
  apply schedule_success_of_factors
    (label? ctx.mol ctx.profile ctx.authoritative .rule1a left right)
    (label? ctx.mol ctx.profile ctx.authoritative .rule1b left right)
    (label? ctx.mol ctx.profile ctx.authoritative .rule2 left right)
    (compareLabel ctx .rule1a left right) (compareLabel ctx .rule1b left right)
    (compareLabel ctx .rule2 left right)
    (fun d h => label_success ctx .rule1a left right d h)
    (fun d h => label_success ctx .rule1b left right d h)
    (fun d h => label_success ctx .rule2 left right d h) decision
  simpa [throughLabels?, schedule] using computed

/-- The only premise is the actual successful constitutional computation. -/
theorem branch_success_key (ctx : Context) : ∀ fuel (left right : Cursor) (decision : Ordering),
    compareBranch? ctx.mol ctx.profile ctx.authoritative fuel .rule2 left right = some decision →
    compareKey (buildAt ctx fuel left) (buildAt ctx fuel right) = decision
  | 0, left, right, decision, computed => by
      rw [compareBranch?] at computed
      cases throughEq : throughLabels? ctx.mol ctx.profile ctx.authoritative .rule2 left right with
      | none => simp [throughEq] at computed
      | some current =>
          have factored := throughLabels_success ctx left right current throughEq
          have resultEq : current = decision := by
            simp [throughEq] at computed
            exact computed.2
          rw [compareKey_eq, buildAt_zero_rule, buildAt_zero_rule, buildAt_zero_rule]
          exact factored.trans resultEq
  | fuel + 1, left, right, decision, computed => by
      let before := compareBranch? ctx.mol ctx.profile ctx.authoritative fuel .rule2
      rw [compareKey_eq]
      apply schedule_success_of_factors
        (compareRule? ctx.mol ctx.profile ctx.authoritative before .rule1a (fuel + 1) [(left, right)])
        (compareRule? ctx.mol ctx.profile ctx.authoritative before .rule1b (fuel + 1) [(left, right)])
        (compareRule? ctx.mol ctx.profile ctx.authoritative before .rule2 (fuel + 1) [(left, right)])
        (compareKeyRule .rule1a (buildAt ctx (fuel + 1) left) (buildAt ctx (fuel + 1) right))
        (compareKeyRule .rule1b (buildAt ctx (fuel + 1) left) (buildAt ctx (fuel + 1) right))
        (compareKeyRule .rule2 (buildAt ctx (fuel + 1) left) (buildAt ctx (fuel + 1) right))
        (fun d h => rule_success_key ctx fuel .rule1a left right d h)
        (fun d h => rule_success_key ctx fuel .rule1b left right d h)
        (fun d h => rule_success_key ctx fuel .rule2 left right d h) decision
      simpa [compareBranch?, schedule, before] using computed

/-- Every successful framed constitutional ordering is comparison of two independently compiled
keys in one fixed molecule/profile/mode/fuel context. No endpoint success is synthesized. -/
theorem compareBranch?_success_factors (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (fuel : Nat) (left right : Cursor) (decision : Ordering)
    (computed : compareBranch? mol profile authoritative fuel .rule2 left right = some decision) :
    compareKey (buildKey mol profile authoritative fuel left)
      (buildKey mol profile authoritative fuel right) = decision :=
  branch_success_key ⟨mol, profile, authoritative⟩ fuel left right decision computed

end TetraStereo.OneCenter.FramedConstitutionalOrderingKey
