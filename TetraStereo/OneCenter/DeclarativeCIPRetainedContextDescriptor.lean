import TetraStereo.OneCenter.DeclarativeCIPRetainedCompleteSignatures
import TetraStereo.OneCenter.DeclarativeCIPCompleteRootDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Independent retained-context descriptor judgment.

Each of the four ligands is a rooted graph. Its key is
`retainedCompleteLigandRule5KeyAt` at one shared window `(W, D)`. The judgment is the generic
`CompleteRootDescriptorJudgment`: physical points that match the optional coordinate map, one
strictly descending permutation of those retained keys, and the pseudo-aware letter
`classifyTetrahedralRSPseudo`. `R`, `S`, `r`, and `s` are all admitted by that classifier.
`none` means no such judgment exists, including when a coordinate is missing or the retained
keys are not strictly ordered. This module does not assume a successful sort or a chosen letter.

Letter case counts unordered prior ties of the retained keys (`completeRule5PairCount`). That
count is not a physical enantiomorphic-pair equivalence; no such equivalence is claimed for
rings. The coordinate column read by a final consumer is the certified input's
`spatialPointAt?` at the consumer's ligand atoms. Graph cuts, compound builders, runtime state,
and executable descriptors stay outside this specification.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP
open CertifiedLocalizedCIPInput
noncomputable section
universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Retained complete Rule-5 key of each ligand graph at the shared window. -/
def retainedContextualFrameKeysAt (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) : Fin 4 → CompleteLigandRule5Key :=
  fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D

theorem retainedContextualFrameKeysAt_apply (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) (slot : Fin 4) :
    retainedContextualFrameKeysAt molecule descriptorMap unit graphs W D slot =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D := rfl

/-- A strict retained ligand order and the supplied coordinates determine the classified letter.
Missing coordinates and non-strict retained keys admit no such judgment. -/
def RetainedContextualDescriptorJudgmentAt (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (descriptor : LocalizedAuxiliaryLabel) : Prop :=
  ∃ points : Fin 4 → CartesianPoint3,
    (∀ slot, coordinates slot = some (points slot)) ∧
      CompleteRootDescriptorJudgment
        (retainedContextualFrameKeysAt molecule descriptorMap unit graphs W D) points descriptor

theorem retainedContextualDescriptorJudgmentAt_iff_completeRoot
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (descriptor : LocalizedAuxiliaryLabel) :
    RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D
        coordinates descriptor ↔
      ∃ points : Fin 4 → CartesianPoint3,
        (∀ slot, coordinates slot = some (points slot)) ∧
          CompleteRootDescriptorJudgment
            (retainedContextualFrameKeysAt molecule descriptorMap unit graphs W D)
            points descriptor :=
  Iff.rfl

/-- Optional retained outcome. `none` is refusal: no retained strict-priority geometric
judgment exists. -/
def RetainedContextualOutcomeAt (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (outcome : Option LocalizedAuxiliaryLabel) : Prop :=
  match outcome with
  | some descriptor =>
      RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D
        coordinates descriptor
  | none => ¬ ∃ descriptor,
      RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D
        coordinates descriptor

theorem retainedContextualOutcomeAt_some_iff (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (descriptor : LocalizedAuxiliaryLabel) :
    RetainedContextualOutcomeAt molecule descriptorMap unit graphs W D coordinates
        (some descriptor) ↔
      RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D
        coordinates descriptor := by
  unfold RetainedContextualOutcomeAt
  exact Iff.rfl

theorem retainedContextualOutcomeAt_none_iff (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3) :
    RetainedContextualOutcomeAt molecule descriptorMap unit graphs W D coordinates none ↔
      ¬ ∃ descriptor,
        RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D
          coordinates descriptor := by
  unfold RetainedContextualOutcomeAt
  exact Iff.rfl

/-- When every coordinate is present, the retained outcome is the generic complete-root outcome
at those points and the retained keys. -/
theorem retainedContextualOutcomeAt_iff_completeRootOutcome
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (points : Fin 4 → CartesianPoint3)
    (available : ∀ slot, coordinates slot = some (points slot))
    (outcome : Option LocalizedAuxiliaryLabel) :
    RetainedContextualOutcomeAt molecule descriptorMap unit graphs W D coordinates outcome ↔
      CompleteRootOutcome
        (retainedContextualFrameKeysAt molecule descriptorMap unit graphs W D) points outcome := by
  cases outcome with
  | some descriptor =>
      constructor
      · intro judgment
        obtain ⟨points', available', complete⟩ := judgment
        have pointsEq : points' = points := by
          funext slot
          exact Option.some.inj ((available' slot).symm.trans (available slot))
        subst pointsEq
        exact complete
      · intro complete
        exact ⟨points, available, complete⟩
  | none =>
      constructor
      · intro absent complete
        obtain ⟨descriptor, judgment⟩ := complete
        exact absent ⟨descriptor, points, available, judgment⟩
      · intro absent existsJudgment
        obtain ⟨descriptor, points', available', complete⟩ := existsJudgment
        have pointsEq : points' = points := by
          funext slot
          exact Option.some.inj ((available' slot).symm.trans (available slot))
        subst pointsEq
        exact absent ⟨descriptor, complete⟩

/-- A missing ligand coordinate refuses every retained descriptor. -/
theorem not_exists_retainedContextualDescriptorJudgmentAt_of_missing_coordinate
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (missing : ∃ slot, coordinates slot = none) :
    ¬ ∃ descriptor,
      RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D
        coordinates descriptor := by
  intro existsJudgment
  obtain ⟨_, points, available, _⟩ := existsJudgment
  obtain ⟨slot, slotNone⟩ := missing
  have availableSlot := available slot
  rw [slotNone] at availableSlot
  cases availableSlot

theorem retainedContextualOutcomeAt_none_of_missing_coordinate
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom)
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (missing : ∃ slot, coordinates slot = none) :
    RetainedContextualOutcomeAt molecule descriptorMap unit graphs W D coordinates none :=
  not_exists_retainedContextualDescriptorJudgmentAt_of_missing_coordinate
    molecule descriptorMap unit graphs W D coordinates missing

theorem retainedContextualFrameKeysAt_iso
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (left right : Fin 4 → RootedDigraph Atom)
    (isos : ∀ slot, RootedDigraph.Iso (left slot) (right slot)) (W D : Nat) :
    retainedContextualFrameKeysAt molecule descriptorMap unit right W D =
      retainedContextualFrameKeysAt molecule descriptorMap unit left W D := by
  funext slot
  exact retainedCompleteLigandRule5KeyAt_iso molecule descriptorMap unit (isos slot) W D

theorem retainedContextualDescriptorJudgmentAt_iso
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (left right : Fin 4 → RootedDigraph Atom)
    (isos : ∀ slot, RootedDigraph.Iso (left slot) (right slot))
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (descriptor : LocalizedAuxiliaryLabel) :
    RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit right W D
        coordinates descriptor ↔
      RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit left W D
        coordinates descriptor := by
  unfold RetainedContextualDescriptorJudgmentAt
  rw [retainedContextualFrameKeysAt_iso molecule descriptorMap unit left right isos W D]

theorem retainedContextualOutcomeAt_iso
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (left right : Fin 4 → RootedDigraph Atom)
    (isos : ∀ slot, RootedDigraph.Iso (left slot) (right slot))
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (outcome : Option LocalizedAuxiliaryLabel) :
    RetainedContextualOutcomeAt molecule descriptorMap unit right W D coordinates outcome ↔
      RetainedContextualOutcomeAt molecule descriptorMap unit left W D coordinates outcome := by
  cases outcome with
  | none =>
      simp only [RetainedContextualOutcomeAt,
        retainedContextualDescriptorJudgmentAt_iso molecule descriptorMap unit left right isos]
  | some descriptor =>
      exact retainedContextualDescriptorJudgmentAt_iso molecule descriptorMap unit left right isos
        W D coordinates descriptor

theorem retainedContextualDescriptorJudgmentAt_unique
    {molecule : MoleculeGraph Atom}
    {descriptorMap : DescriptorMap (DetectedOccurrence molecule)}
    {unit : DetectedOccurrence molecule} {graphs : Fin 4 → RootedDigraph Atom}
    {W D : Nat} {coordinates : Fin 4 → Option CartesianPoint3}
    {left right : LocalizedAuxiliaryLabel}
    (first : RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D
      coordinates left)
    (second : RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D
      coordinates right) :
    left = right := by
  obtain ⟨pointsL, availableL, first⟩ := first
  obtain ⟨pointsR, availableR, second⟩ := second
  have pointsEq : pointsL = pointsR := by
    funext slot
    exact Option.some.inj ((availableL slot).symm.trans (availableR slot))
  subst pointsR
  exact completeRootDescriptorJudgment_unique first second

/-- Lowercase is one unordered prior tie among the retained keys. The count is
`completeRule5PairCount`; it is not a physical enantiomorphic-pair relation on the ligand graphs. -/
theorem retainedContextualDescriptorJudgmentAt_lowercase_iff
    {molecule : MoleculeGraph Atom}
    {descriptorMap : DescriptorMap (DetectedOccurrence molecule)}
    {unit : DetectedOccurrence molecule} {graphs : Fin 4 → RootedDigraph Atom}
    {W D : Nat} {coordinates : Fin 4 → Option CartesianPoint3}
    {descriptor : LocalizedAuxiliaryLabel}
    (judgment : RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D
      coordinates descriptor) :
    descriptor.IsLowercase ↔
      completeRule5PairCount
        (retainedContextualFrameKeysAt molecule descriptorMap unit graphs W D) = 1 := by
  obtain ⟨_, _, judgment⟩ := judgment
  exact completeRootDescriptorJudgment_lowercase_iff judgment

/-! The coordinate map a final consumer reads from the certified input. Ligand atoms are supplied
by that consumer; this specification does not invent points or a separate molecule. -/

/-- Optional coordinates of the consumer's four ligand atoms in the certified spatial table.
An atom with no stored position contributes `none`. -/
def retainedContextualSourceCoordinates (input : CertifiedLocalizedCIPInput)
    (ligandAtoms : Fin 4 → input.Atom) : Fin 4 → Option CartesianPoint3 :=
  fun slot => input.spatialPointAt? (ligandAtoms slot)

theorem retainedContextualSourceCoordinates_apply (input : CertifiedLocalizedCIPInput)
    (ligandAtoms : Fin 4 → input.Atom) (slot : Fin 4) :
    retainedContextualSourceCoordinates input ligandAtoms slot =
      input.spatialPointAt? (ligandAtoms slot) := rfl

/-- A retained judgment at the certified spatial table is a generic complete-root judgment at
points actually stored for the consumer's ligand atoms. -/
theorem retainedContextualDescriptorJudgmentAt_source_iff
    (input : CertifiedLocalizedCIPInput)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (graphs : Fin 4 → RootedDigraph input.Atom)
    (W D : Nat) (ligandAtoms : Fin 4 → input.Atom)
    (descriptor : LocalizedAuxiliaryLabel) :
    RetainedContextualDescriptorJudgmentAt input.moleculeGraph descriptorMap unit graphs W D
        (retainedContextualSourceCoordinates input ligandAtoms) descriptor ↔
      ∃ points : Fin 4 → CartesianPoint3,
        (∀ slot, input.SemanticSpatialPointAt (ligandAtoms slot) (points slot)) ∧
          CompleteRootDescriptorJudgment
            (retainedContextualFrameKeysAt input.moleculeGraph descriptorMap unit graphs W D)
            points descriptor := by
  constructor
  · intro judgment
    obtain ⟨points, available, complete⟩ := judgment
    refine ⟨points, fun slot => ?_, complete⟩
    have coordinate := available slot
    rw [retainedContextualSourceCoordinates] at coordinate
    exact (spatialPointAt?_eq_some_iff input (ligandAtoms slot) (points slot)).mp coordinate
  · intro existsPoints
    obtain ⟨points, spatial, complete⟩ := existsPoints
    refine ⟨points, fun slot => ?_, complete⟩
    rw [retainedContextualSourceCoordinates]
    exact (spatialPointAt?_eq_some_iff input (ligandAtoms slot) (points slot)).mpr (spatial slot)

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualFrameKeysAt
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualFrameKeysAt_apply
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedContextualDescriptorJudgmentAt
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualDescriptorJudgmentAt_iff_completeRoot
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedContextualOutcomeAt
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualOutcomeAt_some_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualOutcomeAt_none_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualOutcomeAt_iff_completeRootOutcome
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.not_exists_retainedContextualDescriptorJudgmentAt_of_missing_coordinate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualOutcomeAt_none_of_missing_coordinate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualFrameKeysAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualDescriptorJudgmentAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualOutcomeAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualDescriptorJudgmentAt_unique
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualDescriptorJudgmentAt_lowercase_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualSourceCoordinates
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualSourceCoordinates_apply
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualDescriptorJudgmentAt_source_iff
