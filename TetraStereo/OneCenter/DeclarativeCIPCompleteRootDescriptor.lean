import TetraStereo.OneCenter.DeclarativeCIPCompleteRule5Order
import TetraStereo.OneCenter.PhysicalEnantiomorphicPairCountReindexing
import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Independent final-centre descriptor judgment for complete molecular keys. The order is
characterized mathematically, and letter case counts unordered distinct pairs tied before Rule 5.
No runtime sorter, callback, occurrence cursor or generated-state equation defines this judgment.
Its prior-pair criterion is not asserted here to be physical graph enantiomorphism. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
open CertifiedLocalizedCIPInput
noncomputable section
open scoped Classical

def CompletePriorPair (keys : Fin 4 → CompleteLigandRule5Key) (left right : Fin 4) : Prop :=
  left ≠ right ∧ (ofLex (keys left)).1 = (ofLex (keys right)).1

def completeRule5PairCount (keys : Fin 4 → CompleteLigandRule5Key) : Nat :=
  sourceEnantiomorphicPairCount (CompletePriorPair keys)

def CompleteRootDescriptorJudgment (keys : Fin 4 → CompleteLigandRule5Key)
    (points : Fin 4 → CartesianPoint3) (descriptor : LocalizedAuxiliaryLabel) : Prop :=
  ∃ (order : List (Fin 4)) (raw : RS),
    order.Perm (List.finRange 4) ∧
    order.Pairwise (fun left right => keys right < keys left) ∧
    RationalTetrahedralDescriptor (order.map points) raw ∧
    descriptor = classifyTetrahedralRSPseudo raw (completeRule5PairCount keys)

/-- Optional independent outcome: refusal means that no strict-priority geometric judgment exists. -/
def CompleteRootOutcome (keys : Fin 4 → CompleteLigandRule5Key)
    (points : Fin 4 → CartesianPoint3) (outcome : Option LocalizedAuxiliaryLabel) : Prop :=
  match outcome with
  | none => ¬ ∃ descriptor, CompleteRootDescriptorJudgment keys points descriptor
  | some descriptor => CompleteRootDescriptorJudgment keys points descriptor

/-- A complete-key tie prevents an independent strictly ordered tetrahedral judgment. -/
theorem completeRootDescriptorJudgment_injective
    {keys : Fin 4 → CompleteLigandRule5Key} {points : Fin 4 → CartesianPoint3}
    {descriptor : LocalizedAuxiliaryLabel}
    (judgment : CompleteRootDescriptorJudgment keys points descriptor) :
    Function.Injective keys := by
  obtain ⟨order, _, perm, sorted, _, _⟩ := judgment
  intro i j equal
  by_contra different
  have ordered : order.Pairwise (fun a b => keys a < keys b ∨ keys b < keys a) :=
    sorted.imp fun h => Or.inr h
  have either := ordered.forall (fun _ _ h => h.symm)
    (perm.mem_iff.mpr (List.mem_finRange i))
    (perm.mem_iff.mpr (List.mem_finRange j)) different
  rw [equal] at either
  exact either.elim (lt_irrefl _) (lt_irrefl _)

/-- The independent priority permutation and determinant determine a unique classified letter. -/
theorem completeRootDescriptorJudgment_unique
    {keys : Fin 4 → CompleteLigandRule5Key} {points : Fin 4 → CartesianPoint3}
    {left right : LocalizedAuxiliaryLabel}
    (first : CompleteRootDescriptorJudgment keys points left)
    (second : CompleteRootDescriptorJudgment keys points right) : left = right := by
  obtain ⟨orderL, rawL, permL, sortedL, geometryL, rfl⟩ := first
  obtain ⟨orderR, rawR, permR, sortedR, geometryR, rfl⟩ := second
  have orders : orderL = orderR := by
    apply List.Perm.eq_of_pairwise (fun _ _ _ _ h h' => False.elim (lt_asymm h h'))
      sortedL sortedR (permL.trans permR.symm)
  subst orderR
  have rawEq : rawL = rawR := Option.some.inj
    (((descriptorOfPriorityOrderedPoints?_eq_some_iff _ _).mpr geometryL).symm.trans
      ((descriptorOfPriorityOrderedPoints?_eq_some_iff _ _).mpr geometryR))
  rw [rawEq]

theorem completeRootDescriptorJudgment_lowercase_iff
    {keys : Fin 4 → CompleteLigandRule5Key} {points : Fin 4 → CartesianPoint3}
    {descriptor : LocalizedAuxiliaryLabel}
    (judgment : CompleteRootDescriptorJudgment keys points descriptor) :
    descriptor.IsLowercase ↔ completeRule5PairCount keys = 1 := by
  obtain ⟨_, raw, _, _, _, rfl⟩ := judgment
  exact isLowercase_classify_iff raw _

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeRootDescriptorJudgment_injective
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeRootDescriptorJudgment_unique
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeRootDescriptorJudgment_lowercase_iff
