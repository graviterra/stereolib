import TetraStereo.UniversalProof.NextFrontier.FramedOrderingKeyCore

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace TetraStereo.OneCenter.FramedDescriptorOrderingKey

open RawMolecule FrameRuntime FramedOrderingKeyCore

abbrev Pair := Cursor × Cursor

def priority (mol : RawMolecule) (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) (side : Bool) (cursor : Cursor) : Nat :=
  occurrenceNodePriority state stage side (cursor.original mol)

def pairLabels (mol : RawMolecule) (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) (pairs : List Pair) : Ordering :=
  List.compareLex compare (pairs.map fun p => priority mol state stage true p.1)
    (pairs.map fun p => priority mol state stage false p.2)

theorem pairLabels_eq (mol : RawMolecule) (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) : ∀ pairs,
    compareDescriptorPairLabels mol state stage pairs = pairLabels mol state stage pairs
  | [] => rfl
  | pair :: pairs => by
      simp only [compareDescriptorPairLabels, pairLabels, priority, List.map_cons,
        List.compareLex_cons_cons]
      cases compare (occurrenceNodePriority state stage true (pair.1.original mol))
          (occurrenceNodePriority state stage false (pair.2.original mol)) <;>
        simp [pairLabels_eq mol state stage pairs, pairLabels, priority]

def denseNext (mol : RawMolecule) (authoritative : Bool)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering) (pairs : List Pair) : List Pair :=
  pairs.flatMap fun p => (children mol authoritative beforeLeft p.1).zip
    (children mol authoritative beforeRight p.2)

def sparseNext (mol : RawMolecule) (authoritative : Bool)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering) : List Pair → List Pair
  | [] => []
  | p :: pairs =>
      if terminal mol p.1 && terminal mol p.2 then
        sparseNext mol authoritative beforeLeft beforeRight pairs
      else (children mol authoritative beforeLeft p.1).zip
        (children mol authoritative beforeRight p.2) ++
          sparseNext mol authoritative beforeLeft beforeRight pairs

/-- Erase only validation/refusal branches already excluded by the successful production run. -/
theorem next_success (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering) :
    ∀ pairs result,
      nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs = some result →
      sparseNext mol authoritative beforeLeft beforeRight pairs = result
  | [], result, computed => by simpa [nextDescriptorPairs?, sparseNext] using computed
  | pair :: pairs, result, computed => by
      cases leftValid : cursor? mol profile pair.1 with
      | none => simp [nextDescriptorPairs?, leftValid] at computed
      | some ld =>
          cases rightValid : cursor? mol profile pair.2 with
          | none => simp [nextDescriptorPairs?, leftValid, rightValid] at computed
          | some rd =>
              cases restEq : nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs with
              | none => simp [nextDescriptorPairs?, leftValid, rightValid, restEq] at computed
              | some rest =>
                  have restTotal := next_success mol profile authoritative beforeLeft beforeRight
                    pairs rest restEq
                  by_cases terminalEq : terminal mol pair.1 && terminal mol pair.2
                  · simpa [nextDescriptorPairs?, sparseNext, leftValid, rightValid, restEq,
                      terminalEq, restTotal] using computed
                  · cases leftEq : ranked? mol profile authoritative beforeLeft pair.1 with
                    | none =>
                        simp [nextDescriptorPairs?, leftValid, rightValid, restEq, terminalEq,
                          leftEq] at computed
                    | some left =>
                        cases rightEq : ranked? mol profile authoritative beforeRight pair.2 with
                        | none =>
                            simp [nextDescriptorPairs?, leftValid, rightValid, restEq, terminalEq,
                              leftEq, rightEq] at computed
                        | some right =>
                            have leftTotal := ranked_success mol profile authoritative beforeLeft
                              pair.1 left leftEq
                            have rightTotal := ranked_success mol profile authoritative beforeRight
                              pair.2 right rightEq
                            simpa [nextDescriptorPairs?, sparseNext, leftValid, rightValid,
                              restEq, terminalEq, leftEq, rightEq, leftTotal, rightTotal,
                              restTotal] using computed

def sparseRule (mol : RawMolecule) (authoritative : Bool) (state : OccurrenceAuxState)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering)
    (stage : RawDescriptorRuleStage) : Nat → List Pair → Ordering
  | 0, pairs => pairLabels mol state stage pairs
  | depth + 1, pairs =>
      (pairLabels mol state stage pairs).then
        (sparseRule mol authoritative state beforeLeft beforeRight stage depth
          (sparseNext mol authoritative beforeLeft beforeRight pairs))

def denseRule (mol : RawMolecule) (authoritative : Bool) (state : OccurrenceAuxState)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering)
    (stage : RawDescriptorRuleStage) : Nat → List Pair → Ordering
  | 0, pairs => pairLabels mol state stage pairs
  | depth + 1, pairs =>
      (pairLabels mol state stage pairs).then
        (denseRule mol authoritative state beforeLeft beforeRight stage depth
          (denseNext mol authoritative beforeLeft beforeRight pairs))

@[simp] theorem sparseRule_nil (mol : RawMolecule) (authoritative : Bool)
    (state : OccurrenceAuxState) (beforeLeft beforeRight : Cursor → Cursor → Option Ordering)
    (stage : RawDescriptorRuleStage) : ∀ depth,
    sparseRule mol authoritative state beforeLeft beforeRight stage depth [] = .eq
  | 0 => rfl
  | depth + 1 => by simp [sparseRule, pairLabels, sparseNext, sparseRule_nil]

/-- Actual successful exhaustive descriptor traversal agrees with a total sparse traversal.
No callback transitivity, output, or totality assumption is present. -/
theorem rule_success_sparse (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (beforeLeft beforeRight : Cursor → Cursor → Option Ordering)
    (stage : RawDescriptorRuleStage) : ∀ fuel pairs decision,
    compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight stage fuel pairs =
      some decision →
    sparseRule mol authoritative state beforeLeft beforeRight stage fuel pairs = decision := by
  intro fuel
  induction fuel with
  | zero =>
      intro pairs decision computed
      by_cases cap : !authoritative && defaultBranchWidthCap < pairs.length
      · simp [compareDescriptorRule?, cap] at computed
      · cases valid : validatePairs? mol profile pairs with
        | none => simp [compareDescriptorRule?, compareDescriptorPairLabels?, cap, valid] at computed
        | some checked =>
            cases labels : compareDescriptorPairLabels mol state stage pairs with
            | lt =>
                simpa [compareDescriptorRule?, compareDescriptorPairLabels?, cap, valid, labels,
                  sparseRule, ← pairLabels_eq] using computed
            | gt =>
                simpa [compareDescriptorRule?, compareDescriptorPairLabels?, cap, valid, labels,
                  sparseRule, ← pairLabels_eq] using computed
            | eq =>
                cases nextEq : nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs with
                | none =>
                    simp [compareDescriptorRule?, compareDescriptorPairLabels?, cap, valid, labels,
                      nextEq] at computed
                | some next =>
                    cases next with
                    | nil =>
                        simpa [compareDescriptorRule?, compareDescriptorPairLabels?, cap, valid, labels,
                          nextEq, sparseRule, ← pairLabels_eq] using computed
                    | cons head tail =>
                        simp [compareDescriptorRule?, compareDescriptorPairLabels?, cap, valid, labels,
                          nextEq] at computed
  | succ fuel ih =>
      intro pairs decision computed
      by_cases cap : !authoritative && defaultBranchWidthCap < pairs.length
      · simp [compareDescriptorRule?, cap] at computed
      · cases valid : validatePairs? mol profile pairs with
        | none => simp [compareDescriptorRule?, compareDescriptorPairLabels?, cap, valid] at computed
        | some checked =>
            cases labels : compareDescriptorPairLabels mol state stage pairs with
            | lt =>
                simpa [compareDescriptorRule?, compareDescriptorPairLabels?, cap, valid, labels,
                  sparseRule, ← pairLabels_eq] using computed
            | gt =>
                simpa [compareDescriptorRule?, compareDescriptorPairLabels?, cap, valid, labels,
                  sparseRule, ← pairLabels_eq] using computed
            | eq =>
                cases nextEq : nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs with
                | none =>
                    simp [compareDescriptorRule?, compareDescriptorPairLabels?, cap, valid, labels,
                      nextEq] at computed
                | some next =>
                    have totalNext := next_success mol profile authoritative beforeLeft beforeRight
                      pairs next nextEq
                    cases next with
                    | nil =>
                        simpa [compareDescriptorRule?, compareDescriptorPairLabels?, cap, valid, labels,
                          nextEq, sparseRule, ← pairLabels_eq, totalNext] using computed
                    | cons head tail =>
                        have recursive : compareDescriptorRule? mol profile authoritative state
                            beforeLeft beforeRight stage fuel (head :: tail) = some decision := by
                          simpa [compareDescriptorRule?, compareDescriptorPairLabels?, cap, valid,
                            labels, nextEq] using computed
                        simpa [sparseRule, ← pairLabels_eq, labels, totalNext] using
                          ih (head :: tail) decision recursive

private theorem original_children_nil (mol : RawMolecule) (cursor : CanonicalRerootCursor)
    (h : cursorTerminal mol cursor = true) : cursor.children mol = [] := by
  cases childrenEq : cursor.children mol with
  | nil => rfl
  | cons child children =>
      cases forcedEq : cursor.node.forcedLeaf with
      | false => simp [cursorTerminal, forcedEq, childrenEq] at h
      | true => simp [CanonicalRerootCursor.children, forcedEq] at childrenEq

theorem children_terminal (mol : RawMolecule) (authoritative : Bool)
    (before : Cursor → Cursor → Option Ordering) (cursor : Cursor)
    (h : terminal mol cursor = true) :
    children mol authoritative before cursor = List.replicate (slots authoritative) (.padding cursor) := by
  have empty := original_children_nil mol (cursor.original mol) h
  simp [children, empty, sortTotal]

@[simp] theorem terminal_padding (mol : RawMolecule) (cursor : Cursor) :
    terminal mol (.padding cursor) = true := by
  simp [terminal, Cursor.original, cursorTerminal, canonicalPhantom,
    CanonicalRerootCursor.children, CanonicalBranchNode.forcedLeaf]

@[simp] theorem priority_padding (mol : RawMolecule) (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) (side : Bool) (cursor : Cursor) :
    priority mol state stage side (.padding cursor) = 0 := by
  simp [priority, Cursor.original, occurrenceNodePriority, canonicalPhantom,
    OccurrenceAuxState.factAt?]

def Silent (mol : RawMolecule) (state : OccurrenceAuxState) (stage : RawDescriptorRuleStage)
    (pair : Pair) : Prop :=
  terminal mol pair.1 = true ∧ terminal mol pair.2 = true ∧
    compare (priority mol state stage true pair.1) (priority mol state stage false pair.2) = .eq

inductive Erases (mol : RawMolecule) (state : OccurrenceAuxState) (stage : RawDescriptorRuleStage) :
    List Pair → List Pair → Prop
  | nil : Erases mol state stage [] []
  | keep (pair : Pair) {active dense : List Pair} (tail : Erases mol state stage active dense) :
      Erases mol state stage (pair :: active) (pair :: dense)
  | erase (pair : Pair) {active dense : List Pair} (silent : Silent mol state stage pair)
      (tail : Erases mol state stage active dense) : Erases mol state stage active (pair :: dense)

theorem Erases.labels_eq {mol : RawMolecule} {state : OccurrenceAuxState}
    {stage : RawDescriptorRuleStage} {active dense : List Pair}
    (h : Erases mol state stage active dense) :
    pairLabels mol state stage active = pairLabels mol state stage dense := by
  induction h with
  | nil => rfl
  | keep pair tail ih =>
      unfold pairLabels at ih ⊢
      simp only [List.map_cons, List.compareLex]
      cases compare (priority mol state stage true pair.1)
        (priority mol state stage false pair.2) <;> simp [ih]
  | erase pair silent tail ih =>
      rcases silent with ⟨_, _, tied⟩
      simpa [pairLabels, List.compareLex, tied] using ih

theorem Erases.keep_all {mol : RawMolecule} {state : OccurrenceAuxState}
    {stage : RawDescriptorRuleStage} (initial : List Pair) {active dense : List Pair}
    (h : Erases mol state stage active dense) :
    Erases mol state stage (initial ++ active) (initial ++ dense) := by
  induction initial with
  | nil => exact h
  | cons pair rest ih => exact .keep pair ih

theorem Erases.erase_all {mol : RawMolecule} {state : OccurrenceAuxState}
    {stage : RawDescriptorRuleStage} (initial : List Pair) {active dense : List Pair}
    (allSilent : ∀ pair ∈ initial, Silent mol state stage pair)
    (h : Erases mol state stage active dense) : Erases mol state stage active (initial ++ dense) := by
  induction initial with
  | nil => exact h
  | cons pair rest ih =>
      exact .erase pair (allSilent pair (by simp))
        (ih (fun p hp => allSilent p (by simp [hp])))

theorem silent_children (mol : RawMolecule) (authoritative : Bool) (state : OccurrenceAuxState)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering) (stage : RawDescriptorRuleStage)
    (pair : Pair) (h : Silent mol state stage pair) :
    ∀ child ∈ denseNext mol authoritative beforeLeft beforeRight [pair],
      Silent mol state stage child := by
  rcases h with ⟨lt, rt, _⟩
  intro child member
  have lc := children_terminal mol authoritative beforeLeft pair.1 lt
  have rc := children_terminal mol authoritative beforeRight pair.2 rt
  simp only [denseNext, List.flatMap_singleton, lc, rc] at member
  have shape : child = (.padding pair.1, .padding pair.2) := by
    have normalized : slots authoritative ≠ 0 ∧ child = (.padding pair.1, .padding pair.2) := by
      simpa using member
    exact normalized.2
  subst child
  simp [Silent]

theorem labels_tied (mol : RawMolecule) (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) : ∀ pairs,
    pairLabels mol state stage pairs = .eq → ∀ pair ∈ pairs,
      compare (priority mol state stage true pair.1) (priority mol state stage false pair.2) = .eq
  | [], _, pair, member => by simp at member
  | head :: tail, tied, pair, member => by
      simp only [pairLabels, List.map_cons, List.compareLex] at tied
      cases headEq : compare (priority mol state stage true head.1)
          (priority mol state stage false head.2) with
      | lt => simp [headEq] at tied
      | gt => simp [headEq] at tied
      | eq =>
          rcases List.mem_cons.mp member with rfl | ht
          · exact headEq
          · exact labels_tied mol state stage tail (by simpa [headEq, pairLabels] using tied) pair ht

theorem Erases.next {mol : RawMolecule} {state : OccurrenceAuxState}
    {stage : RawDescriptorRuleStage} {active dense : List Pair}
    (h : Erases mol state stage active dense) (authoritative : Bool)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering)
    (allTied : ∀ pair ∈ active,
      compare (priority mol state stage true pair.1) (priority mol state stage false pair.2) = .eq) :
    Erases mol state stage (sparseNext mol authoritative beforeLeft beforeRight active)
      (denseNext mol authoritative beforeLeft beforeRight dense) := by
  induction h with
  | nil => exact .nil
  | erase pair silent tail ih =>
      have rest := ih allTied
      simpa [denseNext] using Erases.erase_all
        (denseNext mol authoritative beforeLeft beforeRight [pair])
        (silent_children mol authoritative state beforeLeft beforeRight stage pair silent) rest
  | keep pair tail ih =>
      have rest := ih (fun p hp => allTied p (by simp [hp]))
      by_cases ht : terminal mol pair.1 && terminal mol pair.2
      · have terminals : terminal mol pair.1 = true ∧ terminal mol pair.2 = true :=
          by simpa using ht
        have silent : Silent mol state stage pair :=
          ⟨terminals.1, terminals.2, allTied pair (by simp)⟩
        simpa [sparseNext, ht, denseNext] using Erases.erase_all
          (denseNext mol authoritative beforeLeft beforeRight [pair])
          (silent_children mol authoritative state beforeLeft beforeRight stage pair silent) rest
      · simpa [sparseNext, ht, denseNext] using Erases.keep_all
          ((children mol authoritative beforeLeft pair.1).zip
            (children mol authoritative beforeRight pair.2)) rest

theorem Erases.refl {mol : RawMolecule} {state : OccurrenceAuxState}
    {stage : RawDescriptorRuleStage} : ∀ pairs, Erases mol state stage pairs pairs
  | [] => .nil
  | pair :: pairs => .keep pair (Erases.refl pairs)

theorem sparse_dense_eq (mol : RawMolecule) (authoritative : Bool) (state : OccurrenceAuxState)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering) (stage : RawDescriptorRuleStage) :
    ∀ depth active dense, Erases mol state stage active dense →
    sparseRule mol authoritative state beforeLeft beforeRight stage depth active =
      denseRule mol authoritative state beforeLeft beforeRight stage depth dense
  | 0, active, dense, related => related.labels_eq
  | depth + 1, active, dense, related => by
      have eqLabels := related.labels_eq
      cases hc : pairLabels mol state stage active with
      | lt => simp [sparseRule, denseRule, ← eqLabels, hc]
      | gt => simp [sparseRule, denseRule, ← eqLabels, hc]
      | eq =>
          have nextRelated := related.next authoritative beforeLeft beforeRight
            (labels_tied mol state stage active hc)
          have recursive := sparse_dense_eq mol authoritative state beforeLeft beforeRight stage
            depth _ _ nextRelated
          simpa [sparseRule, denseRule, ← eqLabels, hc] using recursive

theorem denseNext_fst (mol : RawMolecule) (authoritative : Bool)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering) : ∀ pairs,
    (denseNext mol authoritative beforeLeft beforeRight pairs).map Prod.fst =
      next mol authoritative beforeLeft (pairs.map Prod.fst)
  | [] => rfl
  | pair :: pairs => by
      simp only [denseNext, List.flatMap_cons, List.map_append, next,
        List.map_cons, List.flatMap_cons]
      rw [List.map_fst_zip (by simp)]
      congr 1
      simpa [denseNext, next] using denseNext_fst mol authoritative beforeLeft beforeRight pairs

theorem denseNext_snd (mol : RawMolecule) (authoritative : Bool)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering) : ∀ pairs,
    (denseNext mol authoritative beforeLeft beforeRight pairs).map Prod.snd =
      next mol authoritative beforeRight (pairs.map Prod.snd)
  | [] => rfl
  | pair :: pairs => by
      simp only [denseNext, List.flatMap_cons, List.map_append, next,
        List.map_cons, List.flatMap_cons]
      rw [List.map_snd_zip (by simp)]
      congr 1
      simpa [denseNext, next] using denseNext_snd mol authoritative beforeLeft beforeRight pairs

theorem compareLex_append_same_length {α : Type*} (cmp : α → α → Ordering) :
    ∀ left right leftTail rightTail, left.length = right.length →
    List.compareLex cmp (left ++ leftTail) (right ++ rightTail) =
      (List.compareLex cmp left right).then (List.compareLex cmp leftTail rightTail)
  | [], [], leftTail, rightTail, _ => rfl
  | leftHead :: left, rightHead :: right, leftTail, rightTail, lengths => by
      simp only [List.length_cons, Nat.succ.injEq] at lengths
      simp only [List.cons_append, List.compareLex]
      cases headEq : cmp leftHead rightHead with
      | lt => simp
      | gt => simp
      | eq =>
          simpa [headEq] using compareLex_append_same_length cmp left right leftTail rightTail lengths

theorem denseRule_frontiers (mol : RawMolecule) (authoritative : Bool)
    (state : OccurrenceAuxState) (beforeLeft beforeRight : Cursor → Cursor → Option Ordering)
    (stage : RawDescriptorRuleStage) : ∀ depth pairs,
    denseRule mol authoritative state beforeLeft beforeRight stage depth pairs =
      List.compareLex compare
        ((frontiers mol authoritative beforeLeft depth (pairs.map Prod.fst)).flatten.map
          (priority mol state stage true))
        ((frontiers mol authoritative beforeRight depth (pairs.map Prod.snd)).flatten.map
          (priority mol state stage false))
  | 0, pairs => by simp [denseRule, pairLabels, frontiers, Function.comp_def]
  | depth + 1, pairs => by
      have appendEq := compareLex_append_same_length (compare : Nat → Nat → Ordering)
        ((pairs.map Prod.fst).map (priority mol state stage true))
        ((pairs.map Prod.snd).map (priority mol state stage false))
        ((frontiers mol authoritative beforeLeft depth
          (next mol authoritative beforeLeft (pairs.map Prod.fst))).flatten.map
            (priority mol state stage true))
        ((frontiers mol authoritative beforeRight depth
          (next mol authoritative beforeRight (pairs.map Prod.snd))).flatten.map
            (priority mol state stage false)) (by simp)
      have tail := denseRule_frontiers mol authoritative state beforeLeft beforeRight stage depth
        (denseNext mol authoritative beforeLeft beforeRight pairs)
      rw [denseNext_fst, denseNext_snd] at tail
      simp only [denseRule, frontiers, List.flatten_cons, List.map_append]
      rw [appendEq, tail]
      simp [pairLabels, Function.comp_def]

abbrev Key := List Nat

def buildKey (mol : RawMolecule) (authoritative : Bool) (state : OccurrenceAuxState)
    (before : Cursor → Cursor → Option Ordering) (fuel : Nat) (stage : RawDescriptorRuleStage)
    (side : Bool) (cursor : Cursor) : Key :=
  (frontiers mol authoritative before fuel [cursor]).flatten.map (priority mol state stage side)

def compareKey : Key → Key → Ordering := List.compareLex compare

theorem compareKey_transCmp : Std.TransCmp compareKey := by
  unfold compareKey
  infer_instance

/-- A successful production descriptor-rule result factors through independently compiled unary
priority keys. The fixed callback parameters may themselves invoke the full production runtime. -/
theorem rule_success_factors (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (beforeLeft beforeRight : Cursor → Cursor → Option Ordering)
    (stage : RawDescriptorRuleStage) (fuel : Nat) (left right : Cursor) (decision : Ordering)
    (computed : compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight stage
      fuel [(left, right)] = some decision) :
    compareKey (buildKey mol authoritative state beforeLeft fuel stage true left)
      (buildKey mol authoritative state beforeRight fuel stage false right) = decision := by
  have sparse := rule_success_sparse mol profile authoritative state beforeLeft beforeRight stage
    fuel [(left, right)] decision computed
  have dense := sparse_dense_eq mol authoritative state beforeLeft beforeRight stage
    fuel [(left, right)] [(left, right)] (Erases.refl [(left, right)])
  rw [denseRule_frontiers] at dense
  exact dense.symm.trans sparse

end TetraStereo.OneCenter.FramedDescriptorOrderingKey
