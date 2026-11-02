import TetraStereo.OneCenter.DeclarativeCIPContextualRule5Order
import TetraStereo.OneCenter.DeclarativeCIPCompleteRootDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Independent descriptor judgments for retained molecular contexts. Each ligand is described
by a rooted molecular expansion, and coordinates may be absent. No executable key, sorter,
occurrence cursor, or runtime state equation defines this judgment. Its letter-case criterion
counts ordinary-prior ties; physical graph enantiomorphism is not asserted here. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
open CertifiedLocalizedCIPInput
noncomputable section
universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

def contextualFrameKeysAt (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) : Fin 4 → CompleteLigandRule5Key :=
  fun slot => contextualCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D

/-- A strict independent ligand order and the actual available coordinates determine the
classified letter. Missing coordinates and degenerate tetrahedra admit no such judgment. -/
def ContextualDescriptorJudgmentAt (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (descriptor : LocalizedAuxiliaryLabel) : Prop :=
  ∃ points : Fin 4 → CartesianPoint3,
    (∀ slot, coordinates slot = some (points slot)) ∧
      CompleteRootDescriptorJudgment
        (contextualFrameKeysAt molecule descriptorMap unit graphs W D) points descriptor

def ContextualOutcomeAt (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (outcome : Option LocalizedAuxiliaryLabel) : Prop :=
  match outcome with
  | some descriptor =>
      ContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D coordinates descriptor
  | none => ¬ ∃ descriptor,
      ContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D coordinates descriptor

theorem contextualFrameKeysAt_iso
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (left right : Fin 4 → RootedDigraph Atom)
    (isos : ∀ slot, RootedDigraph.Iso (left slot) (right slot)) (W D : Nat) :
    contextualFrameKeysAt molecule descriptorMap unit right W D =
      contextualFrameKeysAt molecule descriptorMap unit left W D := by
  funext slot
  exact contextualCompleteLigandRule5KeyAt_iso molecule descriptorMap unit (isos slot) W D

theorem contextualDescriptorJudgmentAt_iso
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (left right : Fin 4 → RootedDigraph Atom)
    (isos : ∀ slot, RootedDigraph.Iso (left slot) (right slot))
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (descriptor : LocalizedAuxiliaryLabel) :
    ContextualDescriptorJudgmentAt molecule descriptorMap unit right W D coordinates descriptor ↔
      ContextualDescriptorJudgmentAt molecule descriptorMap unit left W D coordinates descriptor := by
  unfold ContextualDescriptorJudgmentAt
  rw [contextualFrameKeysAt_iso molecule descriptorMap unit left right isos W D]

theorem contextualOutcomeAt_iso
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (left right : Fin 4 → RootedDigraph Atom)
    (isos : ∀ slot, RootedDigraph.Iso (left slot) (right slot))
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (outcome : Option LocalizedAuxiliaryLabel) :
    ContextualOutcomeAt molecule descriptorMap unit right W D coordinates outcome ↔
      ContextualOutcomeAt molecule descriptorMap unit left W D coordinates outcome := by
  cases outcome with
  | none =>
      simp only [ContextualOutcomeAt,
        contextualDescriptorJudgmentAt_iso molecule descriptorMap unit left right isos]
  | some descriptor =>
      exact contextualDescriptorJudgmentAt_iso molecule descriptorMap unit left right isos
        W D coordinates descriptor

theorem contextualDescriptorJudgmentAt_unique
    {molecule : MoleculeGraph Atom}
    {descriptorMap : DescriptorMap (DetectedOccurrence molecule)}
    {unit : DetectedOccurrence molecule} {graphs : Fin 4 → RootedDigraph Atom}
    {W D : Nat} {coordinates : Fin 4 → Option CartesianPoint3}
    {left right : LocalizedAuxiliaryLabel}
    (first : ContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D coordinates left)
    (second : ContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D coordinates right) :
    left = right := by
  obtain ⟨pointsL, availableL, first⟩ := first
  obtain ⟨pointsR, availableR, second⟩ := second
  have pointsEq : pointsL = pointsR := by
    funext slot
    exact Option.some.inj ((availableL slot).symm.trans (availableR slot))
  subst pointsR
  exact completeRootDescriptorJudgment_unique first second

theorem contextualDescriptorJudgmentAt_lowercase_iff
    {molecule : MoleculeGraph Atom}
    {descriptorMap : DescriptorMap (DetectedOccurrence molecule)}
    {unit : DetectedOccurrence molecule} {graphs : Fin 4 → RootedDigraph Atom}
    {W D : Nat} {coordinates : Fin 4 → Option CartesianPoint3}
    {descriptor : LocalizedAuxiliaryLabel}
    (judgment : ContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D
      coordinates descriptor) :
    descriptor.IsLowercase ↔
      completeRule5PairCount (contextualFrameKeysAt molecule descriptorMap unit graphs W D) = 1 := by
  obtain ⟨_, _, judgment⟩ := judgment
  exact completeRootDescriptorJudgment_lowercase_iff judgment

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualFrameKeysAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualDescriptorJudgmentAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualOutcomeAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualDescriptorJudgmentAt_unique
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualDescriptorJudgmentAt_lowercase_iff
