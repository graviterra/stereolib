import TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Arbitrary structural permutations and recursive transport

The inverse relabelling is explicit and need not equal the forward relabelling. The structural
laws preserve the original domain, including ring-duplicate provenance and occurrence histories.
The concrete recursion theorems require the existing callback covariance contract; they derive
step covariance and transport the actual generated facts without a supplied outcome or a
generated-label agreement premise.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCompletenessPermutationTransport

open LocalizedChemicalRingRelabel LocalizedChemicalRingSenseTransport
open LocalizedGenericMarkedRecalculation (Geometry mirror)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedReachedFrameNeighbors (SingleBonded)
open LocalizedMarkedOperationEvaluator (Operations underWith)

theorem map_map_inverse {σ τ : Nat → Nat} (inverse : Function.LeftInverse τ σ)
    (xs : List Nat) : (xs.map σ).map τ = xs := by
  rw [List.map_map]
  calc
    _ = xs.map id := List.map_congr_left fun a _ => inverse a
    _ = _ := List.map_id _

theorem mapNode_inverse {σ τ : Nat → Nat} (inverse : Function.LeftInverse τ σ)
    (node : RawMolecule.CanonicalBranchNode) : mapNode τ (mapNode σ node) = node := by
  cases node with
  | mk atom parent history provenance =>
      simp only [mapNode, inverse atom, inverse parent, map_map_inverse inverse]

theorem mapKey_inverse {σ τ : Nat → Nat} (inverse : Function.LeftInverse τ σ)
    (key : CanonicalOccurrenceKey) : mapKey τ (mapKey σ key) = key := by
  cases key
  simp only [mapKey, map_map_inverse inverse]

theorem mapFact_inverse {σ τ : Nat → Nat} (inverse : Function.LeftInverse τ σ)
    (fact : OccurrenceAuxFact) : mapFact τ (mapFact σ fact) = fact := by
  cases fact with
  | mk key atom descriptor uppercase positions =>
      cases key
      simp only [mapFact, inverse atom, map_map_inverse inverse]

theorem pullback_inverse {σ τ : Nat → Nat} (inverse : Function.LeftInverse τ σ)
    (geom : Geometry) : pullback σ (pullback τ geom) = geom := by
  funext atom
  exact congrArg geom (inverse atom)

variable {mol : RawMolecule} {σ : Nat → Nat} {ops : Operations}
  (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed)
  (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
  (cov : Covariant mol ops σ)

include sym wellFormed unique single cov

/-- Generated descriptors transport under arbitrary structural bijections, at every depth. -/
theorem descriptorWith_map (step : Step) (stepMap : StepMap step mol ops σ)
    (depth : Nat) (geom : Geometry) (ctx : Option Nat)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node) :
    descriptorWith step mol ops depth geom [] (ctx.map σ) (mapNode σ node) =
      descriptorWith step mol ops depth (pullback σ geom) [] ctx node := by
  have under : ∀ g r,
      (underWith mol ops g [] (mapNode σ node) (factsWith step mol ops depth) (σ r)).Perm
        ((underWith mol ops (pullback σ g) [] node (factsWith step mol ops depth) r).map
          (mapFact σ)) := fun g r =>
    underWith_map step sym wellFormed unique single cov stepMap depth g node reached r
  unfold descriptorWith
  exact caseFromMirror_congr (stepMap node reached geom ctx _ _ (under geom))
    (stepMap node reached (mirror geom) ctx _ _ (under (mirror geom)))

/-- Concrete immediate-reference generated facts; no independent step-transport premise. -/
theorem facts_map (depth : Nat) (geom : Geometry) (ctx : Option Nat)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node) :
    (LocalizedMarkedOperationEvaluator.facts mol ops depth geom [] (ctx.map σ)
      (mapNode σ node)).Perm
      ((LocalizedMarkedOperationEvaluator.facts mol ops depth (pullback σ geom) [] ctx node).map
        (mapFact σ)) := by
  rw [facts_eq_factsWith]
  exact factsWith_map _ sym wellFormed unique single cov
    (rawStep_map sym wellFormed unique single cov) depth geom ctx node reached

/-- Concrete distant-reference generated facts, with the same structural domain. -/
theorem distant_facts_map (depth : Nat) (geom : Geometry) (ctx : Option Nat)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node) :
    (LocalizedPhysicalMarkedDistantEvaluator.facts mol ops depth geom [] (ctx.map σ)
      (mapNode σ node)).Perm
      ((LocalizedPhysicalMarkedDistantEvaluator.facts mol ops depth (pullback σ geom) [] ctx node).map
        (mapFact σ)) := by
  rw [distant_facts_eq_factsWith]
  exact factsWith_map _ sym wellFormed unique single cov
    (distantStep_map sym wellFormed unique single cov) depth geom ctx node reached

end TetraStereo.OneCenter.LocalizedChemicalRingCompletenessPermutationTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessPermutationTransport.mapNode_inverse
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessPermutationTransport.mapKey_inverse
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessPermutationTransport.mapFact_inverse
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessPermutationTransport.pullback_inverse
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessPermutationTransport.descriptorWith_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessPermutationTransport.facts_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessPermutationTransport.distant_facts_map
