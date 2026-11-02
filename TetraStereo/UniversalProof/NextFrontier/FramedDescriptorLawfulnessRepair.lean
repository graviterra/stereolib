import TetraStereo.OneCenter.SmilesTetrahedral
import Mathlib.Data.List.Zip

set_option autoImplicit false






namespace TetraStereo.UniversalProof.NextFrontier.FramedDescriptorLawfulnessRepair

open TetraStereo.OneCenter
open RawMolecule
open FrameRuntime

/-! ### The swap stage -/

/-- Swap the two reference arguments of the reference-bearing stages and fix the bare stages. -/
def swapStage : RawDescriptorRuleStage → RawDescriptorRuleStage
  | .rule4a => .rule4a
  | .rule4b left right => .rule4b right left
  | .rule4c => .rule4c
  | .rule5 left right => .rule5 right left

theorem swapStage_involutive (stage : RawDescriptorRuleStage) : swapStage (swapStage stage) = stage := by
  cases stage <;> rfl

theorem swapStage_leftInternal (stage : RawDescriptorRuleStage) :
    (swapStage stage).leftInternal = stage.rightInternal := by
  cases stage <;> rfl

theorem swapStage_rightInternal (stage : RawDescriptorRuleStage) :
    (swapStage stage).rightInternal = stage.leftInternal := by
  cases stage <;> rfl

/-! ### Node priority covariance under stage swap and opposite side -/

theorem occurrenceNodePriority_swapStage (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) (side : Bool) (cursor : CanonicalRerootCursor) :
    occurrenceNodePriority state (swapStage stage) (!side) cursor =
      occurrenceNodePriority state stage side cursor := by
  cases side <;> cases stage <;>
    cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [swapStage, occurrenceNodePriority]

theorem occurrenceNodePriority_swapStage_true (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) (cursor : CanonicalRerootCursor) :
    occurrenceNodePriority state (swapStage stage) true cursor =
      occurrenceNodePriority state stage false cursor :=
  occurrenceNodePriority_swapStage state stage false cursor

theorem occurrenceNodePriority_swapStage_false (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) (cursor : CanonicalRerootCursor) :
    occurrenceNodePriority state (swapStage stage) false cursor =
      occurrenceNodePriority state stage true cursor :=
  occurrenceNodePriority_swapStage state stage true cursor

theorem occurrenceNodePriority_rule4a_side_independent (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) :
    occurrenceNodePriority state .rule4a true cursor = occurrenceNodePriority state .rule4a false cursor := by
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;> rfl

theorem occurrenceNodePriority_rule4c_side_independent (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) :
    occurrenceNodePriority state .rule4c true cursor = occurrenceNodePriority state .rule4c false cursor := by
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;> rfl

/-! ### Primitive antisymmetry of the unary priority order -/

/-- The unary projected-priority comparison is natural-number `compare`, which carries the
`Std.TransCmp` bundle. -/
theorem nat_compare_transCmp : Std.TransCmp (compare : Nat → Nat → Ordering) := inferInstance

theorem nat_compare_antisymm (a b : Nat) : compare a b = (compare b a).swap := by
  letI : Std.TransCmp (compare : Nat → Nat → Ordering) := inferInstance
  exact Std.OrientedCmp.eq_swap

/-- The `.rule4a` comparison reverses under operand swap (its key is side-independent). -/
theorem rule4a_compare_swap (state : OccurrenceAuxState) (l r : CanonicalRerootCursor) :
    compare (occurrenceNodePriority state .rule4a true r) (occurrenceNodePriority state .rule4a false l) =
      (compare (occurrenceNodePriority state .rule4a true l) (occurrenceNodePriority state .rule4a false r)).swap := by
  rw [occurrenceNodePriority_rule4a_side_independent state r,
      occurrenceNodePriority_rule4a_side_independent state l]
  exact nat_compare_antisymm _ _

/-! ### Pure paired-sphere label reversal -/

theorem compareDescriptorPairLabels_swap
    (mol : RawMolecule) (state : OccurrenceAuxState) (stage : RawDescriptorRuleStage)
    (pairs : List (Cursor × Cursor)) :
    compareDescriptorPairLabels mol state (swapStage stage) (pairs.map Prod.swap) =
      (compareDescriptorPairLabels mol state stage pairs).swap := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      cases pair with
      | mk l r =>
          simp only [compareDescriptorPairLabels, List.map_cons, Prod.swap]
          rw [occurrenceNodePriority_swapStage_true state stage (r.original mol),
              occurrenceNodePriority_swapStage_false state stage (l.original mol),
              nat_compare_antisymm
                (occurrenceNodePriority state stage false (r.original mol))
                (occurrenceNodePriority state stage true (l.original mol))]
          cases compare (occurrenceNodePriority state stage true (l.original mol))
              (occurrenceNodePriority state stage false (r.original mol)) with
          | lt => rfl
          | eq => exact ih
          | gt => rfl

/-! ### Checked reversal: validation is symmetric on cursors -/

/-- Validation commutes with pair reversal, including reconstruction of each pair. -/
theorem validatePairs?_map_swap (mol : RawMolecule) (profile : Profile)
    (pairs : List (Cursor × Cursor)) :
    validatePairs? mol profile (pairs.map Prod.swap) =
      (validatePairs? mol profile pairs).map (List.map Prod.swap) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨l, r⟩
      simp only [List.map_cons, Prod.swap, validatePairs?]
      rw [ih]
      cases hl : cursor? mol profile l <;>
        cases hr : cursor? mol profile r <;>
        cases ht : validatePairs? mol profile pairs <;> rfl

/-- The checked pair-label comparison reverses under `pairs.map Prod.swap`. -/
theorem compareDescriptorPairLabels?_swap
    (mol : RawMolecule) (profile : Profile) (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) (pairs : List (Cursor × Cursor)) :
    compareDescriptorPairLabels? mol profile state (swapStage stage) (pairs.map Prod.swap) =
      (compareDescriptorPairLabels? mol profile state stage pairs).map Ordering.swap := by
  unfold compareDescriptorPairLabels?
  rw [validatePairs?_map_swap, compareDescriptorPairLabels_swap]
  cases validatePairs? mol profile pairs <;> simp

/-! ### Rule-4c carrier swaps retain the same senior fact -/

/-- Under `pairs.map Prod.swap`, the Rule-4c witness reverses its `ordering` but retains the
*identical* `carrier?` (the same senior real-atom cursor+fact).  The carrier is never dropped. -/
theorem compareRule4cPairLabelsWithWitness_swap
    (mol : RawMolecule) (state : OccurrenceAuxState) (pairs : List (Cursor × Cursor)) :
    compareRule4cPairLabelsWithWitness mol state (pairs.map Prod.swap) =
      { ordering := (compareRule4cPairLabelsWithWitness mol state pairs).ordering.swap,
        carrier? := (compareRule4cPairLabelsWithWitness mol state pairs).carrier? } := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨l, r⟩
      simp only [compareRule4cPairLabelsWithWitness, List.map_cons, Prod.swap]
      simp only [occurrenceNodePriority_rule4c_side_independent]
      rw [nat_compare_antisymm
        (occurrenceNodePriority state .rule4c false (r.original mol))
        (occurrenceNodePriority state .rule4c false (l.original mol))]
      cases hc : compare (occurrenceNodePriority state .rule4c false (l.original mol))
          (occurrenceNodePriority state .rule4c false (r.original mol)) with
      | lt => rfl
      | eq => exact ih
      | gt => rfl

/-! ### Fuel-0 tie reversal -/

theorem priority_compare_swap
    (state : OccurrenceAuxState) (stage : RawDescriptorRuleStage)
    (left right : CanonicalRerootCursor) :
    compare (occurrenceNodePriority state (swapStage stage) true right)
        (occurrenceNodePriority state (swapStage stage) false left) =
      (compare (occurrenceNodePriority state stage true left)
        (occurrenceNodePriority state stage false right)).swap := by
  rw [occurrenceNodePriority_swapStage_true, occurrenceNodePriority_swapStage_false]
  exact nat_compare_antisymm _ _

theorem descriptorNodeTie_swap
    (mol : RawMolecule) (state : OccurrenceAuxState) (stage : RawDescriptorRuleStage)
    (left right : Cursor) :
    descriptorNodeTie mol state (swapStage stage) right left =
      (descriptorNodeTie mol state stage left right).map Ordering.swap := by
  have hs := priority_compare_swap state stage (left.original mol) (right.original mol)
  simp only [descriptorNodeTie]
  rw [rule4a_compare_swap state (left.original mol) (right.original mol)]
  cases hc : compare (occurrenceNodePriority state .rule4a true (left.original mol))
      (occurrenceNodePriority state .rule4a false (right.original mol)) with
  | lt => rfl
  | gt => rfl
  | eq =>
      cases stage <;> first | rfl | simpa only [swapStage, Option.map_some] using congrArg some hs

/-- Swapping side callbacks reuses the identical unary ranking calls.
No width hypothesis is needed: `List.zip_swap` is unconditional. -/
theorem nextDescriptorPairs?_map_swap
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering)
    (pairs : List (Cursor × Cursor)) :
    nextDescriptorPairs? mol profile authoritative beforeRight beforeLeft (pairs.map Prod.swap) =
      (nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs).map
        (List.map Prod.swap) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨l, r⟩
      simp only [nextDescriptorPairs?, List.map_cons, Prod.swap]
      rw [ih]
      cases hl : cursor? mol profile l <;> cases hr : cursor? mol profile r <;>
        cases ht : nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs <;>
        simp only [Option.map_none, Option.map_some]
      all_goals
        rw [Bool.and_comm (terminal mol r) (terminal mol l)]
        by_cases hterminal : terminal mol l && terminal mol r
        · simp [hterminal]
        · cases hrl : ranked? mol profile authoritative beforeLeft l <;>
            cases hrr : ranked? mol profile authoritative beforeRight r <;>
            simp [hterminal, List.map_append, List.zip_swap]

/-! ### Exhaustive-rule reversal -/

theorem compareDescriptorRule?_swap
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering)
    (stage : RawDescriptorRuleStage) :
    ∀ (fuel : Nat) (pairs : List (Cursor × Cursor)),
      compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft
          (swapStage stage) fuel (pairs.map Prod.swap) =
        (compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight stage fuel
          pairs).map Ordering.swap := by
  intro fuel
  induction fuel with
  | zero =>
      intro pairs
      simp only [compareDescriptorRule?, List.length_map]
      by_cases hcap : !authoritative && RawMolecule.defaultBranchWidthCap < pairs.length
      · simp [hcap]
      · simp only [hcap]
        rw [compareDescriptorPairLabels?_swap]
        cases hc : compareDescriptorPairLabels? mol profile state stage pairs with
        | none => rfl
        | some cmp =>
            cases cmp with
            | lt => rfl
            | gt => rfl
            | eq =>
                simp only [Option.map_some]
                rw [nextDescriptorPairs?_map_swap]
                cases hn : nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs with
                | none => rfl
                | some next => simp
  | succ fuel ih =>
      intro pairs
      simp only [compareDescriptorRule?, List.length_map]
      by_cases hcap : !authoritative && RawMolecule.defaultBranchWidthCap < pairs.length
      · simp [hcap]
      · simp only [hcap]
        rw [compareDescriptorPairLabels?_swap]
        cases hc : compareDescriptorPairLabels? mol profile state stage pairs with
        | none => rfl
        | some cmp =>
            cases cmp with
            | lt => rfl
            | gt => rfl
            | eq =>
                simp only [Option.map_some]
                rw [nextDescriptorPairs?_map_swap]
                cases hn : nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs with
                | none => rfl
                | some next =>
                    cases next with
                    | nil => rfl
                    | cons head tail => simpa using ih (head :: tail)

/-! ### The named constitutional primitive -/

/-- Antisymmetry of the shared-profile constitutional comparator at every fuel level up to `fuel`.
This is the single non-closed primitive obligation: a property of `compareBranch?`, not of any
descriptor output. -/
def ConstitutionalAntisymmetric (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (fuel : Nat) : Prop :=
  ∀ f, f ≤ fuel → ∀ (stage : CanonicalRuleStage) (left right : Cursor),
    compareBranch? mol profile authoritative f stage left right =
      (compareBranch? mol profile authoritative f stage right left).map Ordering.swap

theorem ConstitutionalAntisymmetric.mono {mol : RawMolecule} {profile : Profile}
    {authoritative : Bool} {fuel : Nat} :
    ConstitutionalAntisymmetric mol profile authoritative (fuel + 1) →
      ConstitutionalAntisymmetric mol profile authoritative fuel := by
  intro h f hf stage left right
  exact h f (Nat.le_trans hf (Nat.le_succ _)) stage left right

/-! ### Recursive tied-root reversal -/

/-- The recursively-refined tied-root descriptor comparison reverses under `swapStage` and operand
swap, with the child callbacks exactly exchanged via `leftInternal`/`rightInternal`.
No constitutional law is required for this tied-root statement. -/
theorem compareDescriptorAtTiedRoot?_swap
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) :
    ∀ (fuel : Nat) (stage : RawDescriptorRuleStage) (left right : Cursor),
      compareDescriptorAtTiedRoot? mol profile authoritative state fuel (swapStage stage) right left =
        (compareDescriptorAtTiedRoot? mol profile authoritative state fuel stage left right).map
          Ordering.swap := by
  intro fuel stage left right
  simp only [compareDescriptorAtTiedRoot?]
  rw [swapStage_leftInternal stage, swapStage_rightInternal stage]
  let beforeLeft := compareDescriptorBranchAt? mol profile authoritative state fuel stage.leftInternal
  let beforeRight := compareDescriptorBranchAt? mol profile authoritative state fuel stage.rightInternal
  change
    (match compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft .rule4a
        fuel [(right, left)] with
     | none => none
     | some Ordering.lt => some Ordering.lt
     | some Ordering.gt => some Ordering.gt
     | some Ordering.eq =>
         match swapStage stage with
         | .rule4a => some Ordering.eq
         | .rule4b l r => compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft
             (.rule4b l r) fuel [(right, left)]
         | .rule4c =>
             if state.any (fun fact => !fact.uppercase) then
               compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft .rule4c fuel [(right, left)]
             else some Ordering.eq
         | .rule5 l r =>
             let rule4c :=
               if state.any (fun fact => !fact.uppercase) then
                 compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft .rule4c fuel [(right, left)]
               else some Ordering.eq
             match rule4c with
             | some Ordering.eq => compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft
                 (.rule5 l r) fuel [(right, left)]
             | decision => decision) =
      (match compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4a
          fuel [(left, right)] with
       | none => none
       | some Ordering.lt => some Ordering.lt
       | some Ordering.gt => some Ordering.gt
       | some Ordering.eq =>
           match stage with
           | .rule4a => some Ordering.eq
           | .rule4b l r => compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight
               (.rule4b l r) fuel [(left, right)]
           | .rule4c =>
               if state.any (fun fact => !fact.uppercase) then
                 compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4c fuel [(left, right)]
               else some Ordering.eq
           | .rule5 l r =>
               let rule4c :=
                 if state.any (fun fact => !fact.uppercase) then
                   compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4c fuel [(left, right)]
                 else some Ordering.eq
               match rule4c with
               | some Ordering.eq => compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight
                   (.rule5 l r) fuel [(left, right)]
               | decision => decision).map Ordering.swap
  have h4a : compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft .rule4a
      fuel [(right, left)] =
    (compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4a
      fuel [(left, right)]).map Ordering.swap := by
    simpa [swapStage] using
      (compareDescriptorRule?_swap mol profile authoritative state beforeLeft beforeRight .rule4a
        fuel [(left, right)])
  rw [h4a]
  cases compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4a
      fuel [(left, right)] with
  | none => simp
  | some cmp => cases cmp with
    | lt => rfl
    | gt => rfl
    | eq =>
        cases stage with
        | rule4a => rfl
        | rule4b l r =>
            have hb := compareDescriptorRule?_swap mol profile authoritative state beforeLeft beforeRight
              (.rule4b l r) fuel [(left, right)]
            simpa [swapStage] using hb
        | rule4c =>
            have hc := compareDescriptorRule?_swap mol profile authoritative state beforeLeft beforeRight
              .rule4c fuel [(left, right)]
            simp only [swapStage, List.map_cons, List.map_nil, Prod.swap] at hc
            by_cases hany : state.any (fun fact => !fact.uppercase)
            · simp [hany, swapStage, hc]
            · simp [hany, swapStage]
        | rule5 l r =>
            have hc := compareDescriptorRule?_swap mol profile authoritative state beforeLeft beforeRight
              .rule4c fuel [(left, right)]
            simp only [swapStage, List.map_cons, List.map_nil, Prod.swap] at hc
            have h5 := compareDescriptorRule?_swap mol profile authoritative state beforeLeft beforeRight
              (.rule5 l r) fuel [(left, right)]
            by_cases hany : state.any (fun fact => !fact.uppercase)
            · simp only [hany]
              rw [show compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft .rule4c
                  fuel [(right, left)] =
                  (compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4c
                    fuel [(left, right)]).map Ordering.swap from by simpa [swapStage] using hc]
              cases compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4c
                  fuel [(left, right)] with
              | none => rfl
              | some c4 => cases c4 with
                | lt => rfl
                | gt => rfl
                | eq => simpa [swapStage] using h5
            · simpa [hany, swapStage] using h5

/-! ### Recursive branch reversal -/

/-- The recursively-refined constitutional-plus-descriptor branch comparison reverses under
`swapStage` and operand swap.  The constitutional stage is antisymmetrized by the primitive, and
the descriptor tail is the tied-root structure proved above. -/
theorem compareDescriptorBranchAt?_swap
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) :
    ∀ (fuel : Nat) (stage : RawDescriptorRuleStage) (left right : Cursor),
      ConstitutionalAntisymmetric mol profile authoritative fuel →
      compareDescriptorBranchAt? mol profile authoritative state fuel (swapStage stage) right left =
        (compareDescriptorBranchAt? mol profile authoritative state fuel stage left right).map
          Ordering.swap := by
  intro fuel stage left right hconst
  cases fuel with
  | zero =>
      simp only [compareDescriptorBranchAt?]
      rw [hconst 0 (Nat.le_refl _) .rule2 right left]
      cases compareBranch? mol profile authoritative 0 .rule2 left right with
      | none => simp
      | some cmp => cases cmp with
        | lt => rfl
        | gt => rfl
        | eq => exact descriptorNodeTie_swap mol state stage left right
  | succ fuel =>
      simp only [compareDescriptorBranchAt?]
      rw [hconst (fuel + 1) (Nat.le_refl _) .rule2 right left]
      cases compareBranch? mol profile authoritative (fuel + 1) .rule2 left right with
      | none => simp
      | some cmp => cases cmp with
        | lt => rfl
        | gt => rfl
        | eq =>
            rw [swapStage_leftInternal stage, swapStage_rightInternal stage]
            let beforeLeft := compareDescriptorBranchAt? mol profile authoritative state fuel stage.leftInternal
            let beforeRight := compareDescriptorBranchAt? mol profile authoritative state fuel stage.rightInternal
            change
              (match compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft .rule4a
                  (fuel + 1) [(right, left)] with
               | none => none
               | some Ordering.lt => some Ordering.lt
               | some Ordering.gt => some Ordering.gt
               | some Ordering.eq =>
                   match swapStage stage with
                   | .rule4a => some Ordering.eq
                   | .rule4b l r => compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft
                       (.rule4b l r) (fuel + 1) [(right, left)]
                   | .rule4c => compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft
                       .rule4c (fuel + 1) [(right, left)]
                   | .rule5 l r =>
                       match compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft
                           .rule4c (fuel + 1) [(right, left)] with
                       | some Ordering.eq => compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft
                           (.rule5 l r) (fuel + 1) [(right, left)]
                       | decision => decision) =
                (match compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4a
                    (fuel + 1) [(left, right)] with
                 | none => none
                 | some Ordering.lt => some Ordering.lt
                 | some Ordering.gt => some Ordering.gt
                 | some Ordering.eq =>
                     match stage with
                     | .rule4a => some Ordering.eq
                     | .rule4b l r => compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight
                         (.rule4b l r) (fuel + 1) [(left, right)]
                     | .rule4c => compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight
                         .rule4c (fuel + 1) [(left, right)]
                     | .rule5 l r =>
                         match compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight
                             .rule4c (fuel + 1) [(left, right)] with
                         | some Ordering.eq => compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight
                             (.rule5 l r) (fuel + 1) [(left, right)]
                         | decision => decision).map Ordering.swap
            have h4a : compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft .rule4a
                (fuel + 1) [(right, left)] =
              (compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4a
                (fuel + 1) [(left, right)]).map Ordering.swap := by
              simpa [swapStage] using
                (compareDescriptorRule?_swap mol profile authoritative state beforeLeft beforeRight .rule4a
                  (fuel + 1) [(left, right)])
            rw [h4a]
            cases compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4a
                (fuel + 1) [(left, right)] with
            | none => simp
            | some cmp => cases cmp with
              | lt => rfl
              | gt => rfl
              | eq =>
                  cases stage with
                  | rule4a => rfl
                  | rule4b l r =>
                      have hb := compareDescriptorRule?_swap mol profile authoritative state beforeLeft beforeRight
                        (.rule4b l r) (fuel + 1) [(left, right)]
                      simpa [swapStage] using hb
                  | rule4c =>
                      have hc := compareDescriptorRule?_swap mol profile authoritative state beforeLeft beforeRight
                        .rule4c (fuel + 1) [(left, right)]
                      simpa [swapStage] using hc
                  | rule5 l r =>
                      have hc := compareDescriptorRule?_swap mol profile authoritative state beforeLeft beforeRight
                        .rule4c (fuel + 1) [(left, right)]
                      have h5 := compareDescriptorRule?_swap mol profile authoritative state beforeLeft beforeRight
                        (.rule5 l r) (fuel + 1) [(left, right)]
                      rw [show compareDescriptorRule? mol profile authoritative state beforeRight beforeLeft .rule4c
                          (fuel + 1) [(right, left)] =
                          (compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4c
                            (fuel + 1) [(left, right)]).map Ordering.swap from by simpa [swapStage] using hc]
                      cases compareDescriptorRule? mol profile authoritative state beforeLeft beforeRight .rule4c
                          (fuel + 1) [(left, right)] with
                      | none => rfl
                      | some c4 => cases c4 with
                        | lt => rfl
                        | gt => rfl
                        | eq => simpa [swapStage] using h5

/-! ### Rule-5 application -/

/-- Rule-5 reverses its `ordering` and preserves the `±2` `pseudo` flag under operand swap, via the
self-reference `.rule5 R R` / `.rule5 S S` tied-root reversals. -/
theorem compareRule5?_swap
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) :
    ∀ (fuel : Nat) (left right : Cursor),
      compareRule5? mol profile authoritative state fuel right left =
        (compareRule5? mol profile authoritative state fuel left right).map
          (fun c : RawRule5Comparison => { ordering := c.ordering.swap, pseudo := c.pseudo }) := by
  intro fuel left right
  simp only [compareRule5?]
  have hR := compareDescriptorAtTiedRoot?_swap mol profile authoritative state fuel (.rule5 RS.R RS.R)
    left right
  have hS := compareDescriptorAtTiedRoot?_swap mol profile authoritative state fuel (.rule5 RS.S RS.S)
    left right
  simp only [swapStage] at hR hS
  rw [hR, hS]
  cases compareDescriptorAtTiedRoot? mol profile authoritative state fuel (.rule5 RS.R RS.R)
      left right with
  | none => simp
  | some cmpR => cases cmpR with
    | lt =>
        cases compareDescriptorAtTiedRoot? mol profile authoritative state fuel (.rule5 RS.S RS.S)
            left right with
        | none => simp
        | some cmpS => cases cmpS with
          | lt => rfl
          | eq => rfl
          | gt => rfl
    | gt =>
        cases compareDescriptorAtTiedRoot? mol profile authoritative state fuel (.rule5 RS.S RS.S)
            left right with
        | none => simp
        | some cmpS => cases cmpS with
          | lt => rfl
          | eq => rfl
          | gt => rfl
    | eq =>
        cases compareDescriptorAtTiedRoot? mol profile authoritative state fuel (.rule5 RS.S RS.S)
            left right <;> simp

/-! ### Rule-4b single-reference application -/

/-- The single-reference criterion-(b) branch of `compareRule4b?` reverses under operand swap, once
`rule4bReferences?` has produced the two (unary) reference lists.  The empty/one/two-list shape
branches are symmetric by the authoritative/conservative policy; the single-reference branch is
exactly the tied-root reversal with swapped references. -/
theorem compareRule4b?_single_reference_swap
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : Cursor) (lref rref : RS)
    (hl : rule4bReferences? mol profile state fuel [left] = some [lref])
    (hr : rule4bReferences? mol profile state fuel [right] = some [rref]) :
    compareRule4b? mol profile authoritative state fuel right left =
      (compareRule4b? mol profile authoritative state fuel left right).map Ordering.swap := by
  have hswap := compareDescriptorAtTiedRoot?_swap mol profile authoritative state fuel
    (.rule4b lref rref) left right
  simp only [compareRule4b?, hl, hr]
  simpa [swapStage] using hswap

/-- Reverse the ordering while retaining the exact Rule-4c occurrence witness. -/
def swapRule4cDecision (decision : OccurrenceRule4cDecision) : OccurrenceRule4cDecision :=
  { ordering := decision.ordering.swap, carrier? := decision.carrier? }

theorem compareRule4cPairLabelsWithWitness?_swap
    (mol : RawMolecule) (profile : Profile) (state : OccurrenceAuxState)
    (pairs : List (Cursor × Cursor)) :
    compareRule4cPairLabelsWithWitness? mol profile state (pairs.map Prod.swap) =
      (compareRule4cPairLabelsWithWitness? mol profile state pairs).map swapRule4cDecision := by
  unfold compareRule4cPairLabelsWithWitness?
  rw [validatePairs?_map_swap, compareRule4cPairLabelsWithWitness_swap]
  cases hv : validatePairs? mol profile pairs <;> rfl

/-- Exact checked Rule-4c covariance at every fuel and frontier. -/
theorem compareRule4cWithWitness?_swap
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight : Cursor → Cursor → Option Ordering) :
    ∀ (fuel : Nat) (pairs : List (Cursor × Cursor)),
      compareRule4cWithWitness? mol profile authoritative state beforeRight beforeLeft
          fuel (pairs.map Prod.swap) =
        (compareRule4cWithWitness? mol profile authoritative state beforeLeft beforeRight
          fuel pairs).map swapRule4cDecision := by
  intro fuel
  induction fuel with
  | zero =>
      intro pairs
      simp only [compareRule4cWithWitness?, List.length_map]
      by_cases hcap : !authoritative && RawMolecule.defaultBranchWidthCap < pairs.length
      · simp [hcap]
      · simp only [hcap]
        rw [compareRule4cPairLabelsWithWitness?_swap]
        cases hc : compareRule4cPairLabelsWithWitness? mol profile state pairs with
        | none => rfl
        | some decision =>
            rcases decision with ⟨cmp, carrier⟩
            cases cmp with
            | lt => rfl
            | gt => rfl
            | eq =>
                simp only [Option.map_some, swapRule4cDecision]
                rw [nextDescriptorPairs?_map_swap]
                cases hn : nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs with
                | none => rfl
                | some next => simp [swapRule4cDecision]
  | succ fuel ih =>
      intro pairs
      simp only [compareRule4cWithWitness?, List.length_map]
      by_cases hcap : !authoritative && RawMolecule.defaultBranchWidthCap < pairs.length
      · simp [hcap]
      · simp only [hcap]
        rw [compareRule4cPairLabelsWithWitness?_swap]
        cases hc : compareRule4cPairLabelsWithWitness? mol profile state pairs with
        | none => rfl
        | some decision =>
            rcases decision with ⟨cmp, carrier⟩
            cases cmp with
            | lt => rfl
            | gt => rfl
            | eq =>
                simp only [Option.map_some, swapRule4cDecision]
                rw [nextDescriptorPairs?_map_swap]
                cases hn : nextDescriptorPairs? mol profile authoritative beforeLeft beforeRight pairs with
                | none => rfl
                | some next =>
                    cases next with
                    | nil => rfl
                    | cons head tail => simpa using ih (head :: tail)

/-- Dynamic Rule 4b reverses for all reference shapes, including both two-list
rankings and refusal cases. Unary collection and ranking calls merely exchange sides. -/
theorem compareRule4b?_swap
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : Cursor) :
    compareRule4b? mol profile authoritative state fuel right left =
      (compareRule4b? mol profile authoritative state fuel left right).map Ordering.swap := by
  have hs (lref rref : RS) :
      compareDescriptorAtTiedRoot? mol profile authoritative state fuel
          (.rule4b rref lref) right left =
        (compareDescriptorAtTiedRoot? mol profile authoritative state fuel
          (.rule4b lref rref) left right).map Ordering.swap := by
    simpa only [swapStage] using
      compareDescriptorAtTiedRoot?_swap mol profile authoritative state fuel
        (.rule4b lref rref) left right
  cases hl : rule4bReferences? mol profile state fuel [left] with
  | none =>
      cases hr : rule4bReferences? mol profile state fuel [right] <;>
        simp [compareRule4b?, hl, hr]
  | some ls =>
      cases hr : rule4bReferences? mol profile state fuel [right] with
      | none => simp [compareRule4b?, hl, hr]
      | some rs =>
          simp only [compareRule4b?, hl, hr]
          rcases ls with _ | ⟨l, _ | ⟨l', _ | ⟨l'', ls⟩⟩⟩ <;>
            rcases rs with _ | ⟨r, _ | ⟨r', _ | ⟨r'', rs⟩⟩⟩
          all_goals first
            | exact hs _ _
            | (cases authoritative <;> rfl)
            | skip
          cases hrl : rankRule4bReferences? mol profile authoritative state fuel left [l, l'] with
          | none =>
              cases hrr : rankRule4bReferences? mol profile authoritative state fuel right [r, r'] <;>
                simp [hrl, hrr]
          | some rankedLeft =>
              cases hrr : rankRule4bReferences? mol profile authoritative state fuel right [r, r'] with
              | none => simp [hrl, hrr]
              | some rankedRight =>
                  dsimp only [Bind.bind, Option.bind]
                  simp only [hrl, hrr]
                  rw [hs (rankedLeft.getD 0 RS.R) (rankedRight.getD 0 RS.R),
                    hs (rankedLeft.getD 1 RS.S) (rankedRight.getD 1 RS.S)]
                  cases hf : compareDescriptorAtTiedRoot? mol profile authoritative state fuel
                      (.rule4b (rankedLeft.getD 0 RS.R) (rankedRight.getD 0 RS.R)) left right with
                  | none => rfl
                  | some cmp => cases cmp <;> rfl

/-- Reverse a complete decision while retaining both protocol evidence fields. -/
def swapOccurrenceComparison (decision : OccurrenceComparison) : OccurrenceComparison :=
  { ordering := decision.ordering.swap, pseudo := decision.pseudo,
    rule4cCarrier? := decision.rule4cCarrier? }

/-- Only the actual root constitutional comparison needs a primitive reversal law.
Every nonempty descriptor stage below is covered by the unconditional covariance lemmas. -/
theorem decisionComplete?_swap
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat)
    (hconstitutional : ∀ left right : Cursor,
      compareBranch? mol profile authoritative fuel .rule2 right left =
        (compareBranch? mol profile authoritative fuel .rule2 left right).map Ordering.swap)
    (left right : CanonicalRerootCursor) :
    decisionComplete? mol profile authoritative state fuel right left =
      (decisionComplete? mol profile authoritative state fuel left right).map
        swapOccurrenceComparison := by
  have h4a : compareDescriptorAtTiedRoot? mol profile authoritative state fuel .rule4a
      (.actual right) (.actual left) =
      (compareDescriptorAtTiedRoot? mol profile authoritative state fuel .rule4a
        (.actual left) (.actual right)).map Ordering.swap := by
    simpa only [swapStage] using compareDescriptorAtTiedRoot?_swap mol profile authoritative
      state fuel .rule4a (.actual left) (.actual right)
  have h4b := compareRule4b?_swap mol profile authoritative state fuel (.actual left) (.actual right)
  have h4c :
      compareRule4cWithWitness? mol profile authoritative state
        (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
        (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
        fuel [(.actual right, .actual left)] =
      (compareRule4cWithWitness? mol profile authoritative state
        (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
        (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
        fuel [(.actual left, .actual right)]).map swapRule4cDecision := by
    simpa only [List.map_cons, List.map_nil, Prod.swap] using
      compareRule4cWithWitness?_swap mol profile authoritative state
        (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
        (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
        fuel [(.actual left, .actual right)]
  have h5 := compareRule5?_swap mol profile authoritative state fuel (.actual left) (.actual right)
  unfold decisionComplete?
  rw [hconstitutional (.actual left) (.actual right), h4a, h4b, h4c, h5]
  cases hc : compareBranch? mol profile authoritative fuel .rule2
      (.actual left) (.actual right) with
  | none => rfl
  | some constitutional =>
      cases constitutional with
      | lt => rfl
      | gt => rfl
      | eq =>
          cases hempty : state.isEmpty with
          | true => rfl
          | false =>
              cases ha : compareDescriptorAtTiedRoot? mol profile authoritative state fuel .rule4a
                  (.actual left) (.actual right) with
              | none => rfl
              | some rule4a =>
                  cases rule4a with
                  | lt => rfl
                  | gt => rfl
                  | eq =>
                      cases hb : compareRule4b? mol profile authoritative state fuel
                          (.actual left) (.actual right) with
                      | none => rfl
                      | some rule4b =>
                          cases rule4b with
                          | lt => rfl
                          | gt => rfl
                          | eq =>
                              cases hany : state.any (fun fact => !fact.uppercase) with
                              | false =>
                                  cases hfinal : compareRule5? mol profile authoritative state fuel
                                      (.actual left) (.actual right) with
                                  | none => rfl
                                  | some finalDecision => cases finalDecision; rfl
                              | true =>
                                  cases hw : compareRule4cWithWitness? mol profile authoritative state
                                      (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
                                      (compareDescriptorBranchAt? mol profile authoritative state fuel .rule4c)
                                      fuel [(.actual left, .actual right)] with
                                  | none => rfl
                                  | some witness =>
                                      rcases witness with ⟨ordering, carrier⟩
                                      cases ordering with
                                      | lt => rfl
                                      | gt => rfl
                                      | eq =>
                                          cases hfinal : compareRule5? mol profile authoritative state fuel
                                              (.actual left) (.actual right) with
                                          | none => rfl
                                          | some finalDecision => cases finalDecision; rfl

end TetraStereo.UniversalProof.NextFrontier.FramedDescriptorLawfulnessRepair
