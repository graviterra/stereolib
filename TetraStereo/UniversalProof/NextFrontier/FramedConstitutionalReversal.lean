import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorLawfulnessRepair

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000









namespace TetraStereo.UniversalProof.NextFrontier.FramedConstitutionalReversal

open TetraStereo.OneCenter
open RawMolecule
open FrameRuntime
open FramedDescriptorLawfulnessRepair

/-! ### Constitutional node labels -/

theorem compareCIPAtomicLabel_swap (left right : CIPAtomicLabel) :
    compareCIPAtomicLabel right left = (compareCIPAtomicLabel left right).swap := by
  unfold compareCIPAtomicLabel
  exact nat_compare_antisymm _ _

theorem distanceOrdering_swap (left right : Nat) :
    (if right < left then Ordering.gt else if left < right then Ordering.lt else Ordering.eq) =
      (if left < right then Ordering.gt else if right < left then Ordering.lt else Ordering.eq).swap := by
  by_cases hlt : left < right
  · have hnot : ¬ right < left := by omega
    simp [hlt, hnot]
  · by_cases hgt : right < left
    · simp [hlt, hgt]
    · simp [hlt, hgt]

theorem compareCanonicalNodeRule_swap (mol : RawMolecule) (rule : CanonicalRuleStage)
    (left right : CanonicalBranchNode) :
    mol.compareCanonicalNodeRule rule right left =
      (mol.compareCanonicalNodeRule rule left right).swap := by
  cases rule with
  | rule1a =>
      exact compareCIPAtomicLabel_swap _ _
  | rule1b =>
      exact distanceOrdering_swap _ _
  | rule2 =>
      unfold compareCanonicalNodeRule
      exact nat_compare_antisymm _ _

theorem compareCanonicalNodeRule?_swap (mol : RawMolecule) (rule : CanonicalRuleStage)
    (left right : CanonicalBranchNode) :
    mol.compareCanonicalNodeRule? rule right left =
      (mol.compareCanonicalNodeRule? rule left right).map Ordering.swap := by
  cases rule with
  | rule1a =>
      simp only [compareCanonicalNodeRule?]
      cases hl : mol.canonicalRule1aLabel? left with
      | none =>
          cases hr : mol.canonicalRule1aLabel? right <;> rfl
      | some leftLabel =>
          cases hr : mol.canonicalRule1aLabel? right with
          | none => rfl
          | some rightLabel =>
              exact congrArg some (compareCIPAtomicLabel_swap leftLabel rightLabel)
  | rule1b =>
      exact congrArg some (compareCanonicalNodeRule_swap mol .rule1b left right)
  | rule2 =>
      exact congrArg some (compareCanonicalNodeRule_swap mol .rule2 left right)

theorem compareCanonicalNodeRuleAuthoritative?_swap
    (mol : RawMolecule) (rule : CanonicalRuleStage) (left right : CanonicalBranchNode) :
    mol.compareCanonicalNodeRuleAuthoritative? rule right left =
      (mol.compareCanonicalNodeRuleAuthoritative? rule left right).map Ordering.swap := by
  cases rule with
  | rule1a =>
      simp only [compareCanonicalNodeRuleAuthoritative?]
      cases hl : mol.canonicalRule1aLabelAuthoritative? left with
      | none =>
          cases hr : mol.canonicalRule1aLabelAuthoritative? right <;> rfl
      | some leftLabel =>
          cases hr : mol.canonicalRule1aLabelAuthoritative? right with
          | none => rfl
          | some rightLabel =>
              exact congrArg some (compareCIPAtomicLabel_swap leftLabel rightLabel)
  | rule1b =>
      exact congrArg some (compareCanonicalNodeRule_swap mol .rule1b left right)
  | rule2 =>
      exact congrArg some (compareCanonicalNodeRule_swap mol .rule2 left right)

/-- The Rule-1b comparison reads the same profile on both sides. Admission failure is symmetric. -/
theorem label?_swap (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (rule : CanonicalRuleStage) (left right : Cursor) :
    label? mol profile authoritative rule right left =
      (label? mol profile authoritative rule left right).map Ordering.swap := by
  unfold label?
  cases hl : cursor? mol profile left with
  | none =>
      cases hr : cursor? mol profile right <;> rfl
  | some ld =>
      cases hr : cursor? mol profile right with
      | none => rfl
      | some rd =>
          cases rule with
          | rule1a =>
              cases authoritative with
              | false => exact compareCanonicalNodeRule?_swap mol .rule1a _ _
              | true => exact compareCanonicalNodeRuleAuthoritative?_swap mol .rule1a _ _
          | rule1b => exact congrArg some (distanceOrdering_swap ld rd)
          | rule2 =>
              cases authoritative with
              | false => exact compareCanonicalNodeRule?_swap mol .rule2 _ _
              | true => exact compareCanonicalNodeRuleAuthoritative?_swap mol .rule2 _ _

/-! ### Paired sphere labels and expansion -/

theorem pairLabels?_swap (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (rule : CanonicalRuleStage) (pairs : List (Cursor × Cursor)) :
    pairLabels? mol profile authoritative rule (pairs.map Prod.swap) =
      (pairLabels? mol profile authoritative rule pairs).map Ordering.swap := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨left, right⟩
      simp only [pairLabels?, List.map_cons, Prod.swap]
      rw [label?_swap mol profile authoritative rule left right, ih]
      cases hc : label? mol profile authoritative rule left right with
      | none => rfl
      | some cmp => cases cmp <;> rfl

/-- The same unary child rankings exchange sides; the callback needs no comparator laws. -/
theorem nextPairs?_swap (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (before : Cursor → Cursor → Option Ordering) (pairs : List (Cursor × Cursor)) :
    nextPairs? mol profile authoritative before (pairs.map Prod.swap) =
      (nextPairs? mol profile authoritative before pairs).map (List.map Prod.swap) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨left, right⟩
      simp only [nextPairs?, List.map_cons, Prod.swap]
      rw [ih]
      cases ht : nextPairs? mol profile authoritative before pairs with
      | none => rfl
      | some rest =>
          simp only [Option.map_some]
          rw [Bool.and_comm (terminal mol right) (terminal mol left)]
          by_cases hterminal : terminal mol left && terminal mol right
          · simp [hterminal]
          · cases hl : ranked? mol profile authoritative before left <;>
              cases hr : ranked? mol profile authoritative before right <;>
              simp [hterminal, List.map_append, List.zip_swap]

/-! ### Exhaustive rule traversal -/

theorem compareRule?_swap (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (before : Cursor → Cursor → Option Ordering) (rule : CanonicalRuleStage) :
    ∀ (fuel : Nat) (pairs : List (Cursor × Cursor)),
      compareRule? mol profile authoritative before rule fuel (pairs.map Prod.swap) =
        (compareRule? mol profile authoritative before rule fuel pairs).map Ordering.swap := by
  intro fuel
  induction fuel with
  | zero =>
      intro pairs
      conv_lhs => rw [compareRule?]
      conv_rhs => rw [compareRule?]
      simp only [List.length_map]
      by_cases hcap : !authoritative && defaultBranchWidthCap < pairs.length
      · simp [hcap]
      · simp only [hcap]
        rw [pairLabels?_swap]
        cases hc : pairLabels? mol profile authoritative rule pairs with
        | none => rfl
        | some cmp =>
            cases cmp with
            | lt => rfl
            | gt => rfl
            | eq =>
                simp only [Option.map_some]
                rw [nextPairs?_swap]
                cases hn : nextPairs? mol profile authoritative before pairs with
                | none => rfl
                | some next => simp
  | succ fuel ih =>
      intro pairs
      conv_lhs => rw [compareRule?]
      conv_rhs => rw [compareRule?]
      simp only [List.length_map]
      by_cases hcap : !authoritative && defaultBranchWidthCap < pairs.length
      · simp [hcap]
      · simp only [hcap]
        rw [pairLabels?_swap]
        cases hc : pairLabels? mol profile authoritative rule pairs with
        | none => rfl
        | some cmp =>
            cases cmp with
            | lt => rfl
            | gt => rfl
            | eq =>
                simp only [Option.map_some]
                rw [nextPairs?_swap]
                cases hn : nextPairs? mol profile authoritative before pairs with
                | none => rfl
                | some next =>
                    cases next with
                    | nil => rfl
                    | cons head tail => simpa using ih (head :: tail)

theorem compareRule?_singleton_swap
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (before : Cursor → Cursor → Option Ordering) (rule : CanonicalRuleStage)
    (fuel : Nat) (left right : Cursor) :
    compareRule? mol profile authoritative before rule fuel [(right, left)] =
      (compareRule? mol profile authoritative before rule fuel [(left, right)]).map Ordering.swap := by
  simpa only [List.map_cons, List.map_nil, Prod.swap] using
    compareRule?_swap mol profile authoritative before rule fuel [(left, right)]

/-! ### Rule-major composition and recursive branches -/

/-- Reversal commutes with the exact Rule-1a/1b/2 short-circuit schedule. -/
theorem throughStages_swap (stage : CanonicalRuleStage)
    (first distance isotope : Option Ordering) :
    (first.map Ordering.swap).bind (fun first =>
      if first != Ordering.eq || stage == CanonicalRuleStage.rule1a then some first else
      (distance.map Ordering.swap).bind (fun distance =>
        if distance != Ordering.eq || stage == CanonicalRuleStage.rule1b then some distance else
        isotope.map Ordering.swap)) =
    (first.bind (fun first =>
      if first != Ordering.eq || stage == CanonicalRuleStage.rule1a then some first else
      distance.bind (fun distance =>
        if distance != Ordering.eq || stage == CanonicalRuleStage.rule1b then some distance else
        isotope))).map Ordering.swap := by
  cases first with
  | none => rfl
  | some first =>
      cases first with
      | lt => rfl
      | gt => rfl
      | eq =>
          cases stage with
          | rule1a => rfl
          | rule1b =>
              cases distance with
              | none => rfl
              | some cmp => cases cmp <;> rfl
          | rule2 =>
              cases distance with
              | none => rfl
              | some cmp => cases cmp <;> rfl

theorem throughLabels?_swap (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (stage : CanonicalRuleStage) (left right : Cursor) :
    throughLabels? mol profile authoritative stage right left =
      (throughLabels? mol profile authoritative stage left right).map Ordering.swap := by
  unfold throughLabels?
  rw [label?_swap mol profile authoritative .rule1a left right,
    label?_swap mol profile authoritative .rule1b left right,
    label?_swap mol profile authoritative .rule2 left right]
  exact throughStages_swap stage _ _ _

/-- Constitutional branch reversal for all stages and fuels, including symmetric refusal.
Recursive sibling sorting uses the same callback after root reversal, so no recursive sorting
law is assumed. -/
theorem compareBranch?_swap (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (fuel : Nat) (stage : CanonicalRuleStage) (left right : Cursor) :
    compareBranch? mol profile authoritative fuel stage right left =
      (compareBranch? mol profile authoritative fuel stage left right).map Ordering.swap := by
  cases fuel with
  | zero =>
      simp only [compareBranch?]
      rw [throughLabels?_swap mol profile authoritative stage left right]
      cases hc : throughLabels? mol profile authoritative stage left right with
      | none => rfl
      | some cmp =>
          cases cmp with
          | lt => rfl
          | gt => rfl
          | eq =>
              rw [Bool.and_comm (terminal mol right) (terminal mol left)]
              cases terminal mol left && terminal mol right <;> rfl
  | succ fuel =>
      simp only [compareBranch?]
      rw [compareRule?_singleton_swap mol profile authoritative
          (compareBranch? mol profile authoritative fuel stage) .rule1a (fuel + 1) left right,
        compareRule?_singleton_swap mol profile authoritative
          (compareBranch? mol profile authoritative fuel stage) .rule1b (fuel + 1) left right,
        compareRule?_singleton_swap mol profile authoritative
          (compareBranch? mol profile authoritative fuel stage) .rule2 (fuel + 1) left right]
      exact throughStages_swap stage _ _ _

/-! ### Discharge the accepted descriptor reversal premise -/

theorem constitutionalAntisymmetric (mol : RawMolecule) (profile : Profile)
    (authoritative : Bool) (fuel : Nat) :
    ConstitutionalAntisymmetric mol profile authoritative fuel := by
  intro f _ stage left right
  exact compareBranch?_swap mol profile authoritative f stage right left

theorem compareDescriptorBranchAt?_swap
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (stage : RawDescriptorRuleStage)
    (left right : Cursor) :
    compareDescriptorBranchAt? mol profile authoritative state fuel (swapStage stage) right left =
      (compareDescriptorBranchAt? mol profile authoritative state fuel stage left right).map
        Ordering.swap := by
  exact FramedDescriptorLawfulnessRepair.compareDescriptorBranchAt?_swap
    mol profile authoritative state fuel stage left right
    (constitutionalAntisymmetric mol profile authoritative fuel)

/-- Complete decision reversal has no constitutional-law premise. Only ordering changes;
`swapOccurrenceComparison` retains the exact pseudo flag and Rule-4c carrier. -/
theorem decisionComplete?_swap
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor) :
    decisionComplete? mol profile authoritative state fuel right left =
      (decisionComplete? mol profile authoritative state fuel left right).map
        swapOccurrenceComparison := by
  exact FramedDescriptorLawfulnessRepair.decisionComplete?_swap
    mol profile authoritative state fuel
    (fun l r => compareBranch?_swap mol profile authoritative fuel .rule2 l r) left right

end TetraStereo.UniversalProof.NextFrontier.FramedConstitutionalReversal
