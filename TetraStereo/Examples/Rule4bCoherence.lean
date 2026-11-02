import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.Examples.Rule4bCoherence

open TetraStereo.OneCenter

/-!
Kernel-checked coherence regressions for the positional Rule-4b comparator.

The comparator used to return `eq` immediately when two ligands selected both reference senses
and had textually equal first descriptor populations.  That pair-dependent shortcut made both
strict priority and induced ties non-transitive, even when all three hierarchies had the same
sphere widths.  Rule 4b now compares the complete pair-pattern signatures in every case.
-/

/-- All `R/S` sequences of a fixed length. -/
def senses : ℕ → List (List RS)
  | 0 => [[]]
  | n + 1 => (senses n).flatMap fun tail => [RS.R :: tail, RS.S :: tail]

/-- All ordered positive compositions of a population. -/
def compositions : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 =>
      [n + 1] :: (List.range n).flatMap fun left0 =>
        let left := left0 + 1
        (compositions (n + 1 - left)).map fun rest => left :: rest

/-- All descriptor hierarchies with the supplied sphere widths. -/
def assignmentsForShape : List ℕ → List (List (List RS))
  | [] => [[]]
  | width :: rest =>
      (senses width).flatMap fun layer =>
        (assignmentsForShape rest).map fun layers => layer :: layers

def factsOfLayer (layerIndex : ℕ) (layer : List RS) : List RawDescriptorFact :=
  layer.zipIdx.map fun entry =>
    { atom := 100 * layerIndex + entry.2
      descriptor := entry.1
      uppercase := true }

def factsOfHierarchy (layers : List (List RS)) : List (List RawDescriptorFact) :=
  layers.zipIdx.map fun entry => factsOfLayer entry.2 entry.1

/-- The production positional Rule-4b comparison, restricted to abstract uppercase hierarchies. -/
def compareSenses (left right : List (List RS)) : Ordering :=
  compareRule4bLayerHierarchies (factsOfHierarchy left) (factsOfHierarchy right)

/-- Search one fixed positional shape for a strict-transitivity violation. -/
def strictTransitivityViolationForShape? (shape : List ℕ) :=
  let hierarchies := assignmentsForShape shape
  hierarchies.findSome? fun left =>
    hierarchies.findSome? fun middle =>
      hierarchies.findSome? fun right =>
        if compareSenses left middle == .gt && compareSenses middle right == .gt &&
            compareSenses left right != .gt then
          some (left, middle, right)
        else none

/-- Search one fixed positional shape for a non-transitive Rule-4b tie. -/
def tieTransitivityViolationForShape? (shape : List ℕ) :=
  let hierarchies := assignmentsForShape shape
  hierarchies.findSome? fun left =>
    hierarchies.findSome? fun middle =>
      hierarchies.findSome? fun right =>
        if compareSenses left middle == .eq && compareSenses middle right == .eq &&
            compareSenses left right != .eq then
          some (left, middle, right)
        else none

abbrev Rule4bHierarchy := List (List RawDescriptorFact)

/-- The executable Rule-4b comparator is exactly lexicographic comparison of the two independently
constructed canonical signatures. -/
theorem compareRule4bLayerHierarchies_eq_signature_compare
    (left right : Rule4bHierarchy) :
    compareRule4bLayerHierarchies left right =
      compare (rule4bCanonicalSignature left) (rule4bCanonicalSignature right) :=
  rfl

/-- The weak Rule-4b priority relation induced by the production comparator. -/
def Rule4bLE (left right : Rule4bHierarchy) : Prop :=
  compareRule4bLayerHierarchies left right ≠ .gt

/-- Weak Rule-4b priority is reflexive. -/
theorem rule4bLE_refl (hierarchy : Rule4bHierarchy) :
    Rule4bLE hierarchy hierarchy := by
  simp only [Rule4bLE, compareRule4bLayerHierarchies, Ordering.byKey]
  simp

/-- Weak Rule-4b priority is transitive for arbitrary finite hierarchies. -/
theorem rule4bLE_trans {left middle right : Rule4bHierarchy}
    (leftMiddle : Rule4bLE left middle) (middleRight : Rule4bLE middle right) :
    Rule4bLE left right := by
  unfold Rule4bLE compareRule4bLayerHierarchies Ordering.byKey at leftMiddle middleRight ⊢
  exact Std.TransCmp.le_trans leftMiddle middleRight

/-- Every two Rule-4b hierarchies are comparable by the induced weak priority. -/
theorem rule4bLE_total (left right : Rule4bHierarchy) :
    Rule4bLE left right ∨ Rule4bLE right left := by
  unfold Rule4bLE compareRule4bLayerHierarchies Ordering.byKey
  cases h : compare (rule4bCanonicalSignature left) (rule4bCanonicalSignature right) with
  | lt => exact Or.inl (by simp)
  | eq => exact Or.inl (by simp)
  | gt =>
      exact Or.inr (by
        have reverse :
            compare (rule4bCanonicalSignature right) (rule4bCanonicalSignature left) = .lt :=
          Std.OrientedCmp.gt_iff_lt.mp h
        simp [reverse])

/-- Strict Rule-4b priority is transitive for arbitrary finite hierarchies. -/
theorem compareRule4bLayerHierarchies_gt_trans
    {left middle right : Rule4bHierarchy}
    (leftMiddle : compareRule4bLayerHierarchies left middle = .gt)
    (middleRight : compareRule4bLayerHierarchies middle right = .gt) :
    compareRule4bLayerHierarchies left right = .gt := by
  unfold compareRule4bLayerHierarchies Ordering.byKey at leftMiddle middleRight ⊢
  exact Std.TransCmp.gt_of_gt_of_ge leftMiddle (by simp [middleRight])

/-- Equality returned by Rule 4b is transitive; it is equality of canonical signatures, not
necessarily syntactic equality of the original hierarchy representation. -/
theorem compareRule4bLayerHierarchies_eq_trans
    {left middle right : Rule4bHierarchy}
    (leftMiddle : compareRule4bLayerHierarchies left middle = .eq)
    (middleRight : compareRule4bLayerHierarchies middle right = .eq) :
    compareRule4bLayerHierarchies left right = .eq := by
  unfold compareRule4bLayerHierarchies Ordering.byKey at leftMiddle middleRight ⊢
  apply Std.LawfulEqCmp.compare_eq_iff_eq.mpr
  exact (Std.LawfulEqCmp.compare_eq_iff_eq.mp leftMiddle).trans
    (Std.LawfulEqCmp.compare_eq_iff_eq.mp middleRight)

private def strictA : List (List RS) := [[RS.S, RS.R], [RS.S, RS.R]]
private def strictB : List (List RS) := [[RS.R, RS.S], [RS.S, RS.R]]
private def strictC : List (List RS) := [[RS.S, RS.R], [RS.R, RS.R]]

/-- The former minimal strict cycle is now an ordinary transitive chain. -/
theorem former_strict_violation_is_transitive :
    compareSenses strictA strictB = .gt ∧
      compareSenses strictB strictC = .gt ∧
      compareSenses strictA strictC = .gt := by
  decide

private def tieA : List (List RS) := [[RS.S, RS.R], [RS.R]]
private def tieB : List (List RS) := [[RS.S, RS.R], [RS.S]]
private def tieC : List (List RS) := [[RS.R, RS.S], [RS.R]]

/-- The former non-transitive tie now has a consistent `lt`, `eq`, `lt` outcome. -/
theorem former_tie_violation_is_consistent :
    compareSenses tieA tieB = .lt ∧
      compareSenses tieB tieC = .eq ∧
      compareSenses tieA tieC = .lt := by
  decide

end TetraStereo.Examples.Rule4bCoherence
