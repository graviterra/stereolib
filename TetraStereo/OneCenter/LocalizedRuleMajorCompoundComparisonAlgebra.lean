import TetraStereo.OneCenter.LocalizedActualRule4bPhysicalComparison
import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingSignature
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! List comparison algebra for exhausting all Rule-4b alternatives before Rule 4c.
The Rule-4c pointwise connection is needed only at positions whose prior comparison ties. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
noncomputable section

theorem compareLex_map_eq_of_prior_tie {R K : Type*}
    (prior cmp : R → R → Ordering) (kcmp : K → K → Ordering) (fL fR : R → K) :
    ∀ left right : List R,
      (∀ x ∈ left, ∀ y ∈ right, prior x y = .eq → cmp x y = kcmp (fL x) (fR y)) →
      List.compareLex prior left right = .eq →
      List.compareLex cmp left right =
        List.compareLex kcmp (left.map fL) (right.map fR)
  | [], [], _, _ => rfl
  | [], _ :: _, _, tied => by cases tied
  | _ :: _, [], _, tied => by cases tied
  | x :: xs, y :: ys, agrees, tied => by
      rw [List.compareLex_cons_cons, Ordering.then_eq_eq] at tied
      simp only [List.map_cons, List.compareLex_cons_cons]
      rw [agrees x (by simp) y (by simp) tied.1,
        compareLex_map_eq_of_prior_tie prior cmp kcmp fL fR xs ys
          (fun a ha b hb => agrees a (List.mem_cons_of_mem x ha)
            b (List.mem_cons_of_mem y hb)) tied.2]

theorem compareLex_then_map_eq {R B C : Type*}
    (cmpB cmpC : R → R → Ordering)
    (independentB : B → B → Ordering) (independentC : C → C → Ordering)
    (bL bR : R → B) (cL cR : R → C) (left right : List R)
    (agreesB : ∀ x ∈ left, ∀ y ∈ right, cmpB x y = independentB (bL x) (bR y))
    (agreesC : ∀ x ∈ left, ∀ y ∈ right, cmpB x y = .eq →
      cmpC x y = independentC (cL x) (cR y)) :
    (List.compareLex cmpB left right).then (List.compareLex cmpC left right) =
      (List.compareLex independentB (left.map bL) (right.map bR)).then
        (List.compareLex independentC (left.map cL) (right.map cR)) := by
  calc
    _ = (List.compareLex cmpB left right).then
        (List.compareLex independentC (left.map cL) (right.map cR)) :=
      then_congr (fun tied => compareLex_map_eq_of_prior_tie cmpB cmpC independentC
        cL cR left right agreesC tied)
    _ = _ := by rw [compareLex_map_eq cmpB independentB bL bR left right agreesB]

end
end TetraStereo.OneCenter.Rule4aTableBridge

namespace TetraStereo.OneCenter.DeclarativeCIP
noncomputable section
open Certificate.CanonicalSphereKey (Key)
universe u

/-- The raw observation-list signature. The only difference from the independent ligand
signature is its harmless singleton empty Rule-4b entry when there are no references. -/
def unmaskedCompletePriorSignatureAt {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom) (W D : Nat) :
    CompletePriorSignature :=
  let selection := referenceSelection molecule descriptorMap unit graph
  let readings := completeReadingsAt molecule descriptorMap unit graph W D
  toLex (selection.countPriority, toLex
    (readings.map (fun key => (ofLex key).1), readings.map (fun key => (ofLex key).2)))

/-- Retaining or suppressing the no-reference dummy Rule-4b entry produces the same order
for every pair of molecular ligands, including heterogeneous reference populations. -/
theorem compare_unmaskedCompletePriorSignature_eq
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (left right : RootedDigraph Atom) (W D : Nat) :
    compare (unmaskedCompletePriorSignatureAt molecule descriptorMap unit left W D)
        (unmaskedCompletePriorSignatureAt molecule descriptorMap unit right W D) =
      compare (completePriorSignatureAt molecule descriptorMap unit left W D)
        (completePriorSignatureAt molecule descriptorMap unit right W D) := by
  unfold unmaskedCompletePriorSignatureAt completePriorSignatureAt
  cases hL : referenceSelection molecule descriptorMap unit left <;>
    cases hR : referenceSelection molecule descriptorMap unit right <;>
    simp only [ReferenceSelection.countPriority, reduceCtorEq, ↓reduceIte]
  all_goals first
    | rfl
    | (simp only [completeReadingsAt, hL, hR, completeReadingAt, List.map_cons,
        List.map_nil, ofLex_toLex]; rfl)

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compareLex_map_eq_of_prior_tie
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compareLex_then_map_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.compare_unmaskedCompletePriorSignature_eq
