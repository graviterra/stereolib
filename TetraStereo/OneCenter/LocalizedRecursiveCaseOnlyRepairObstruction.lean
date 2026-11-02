import TetraStereo.OneCenter.LocalizedReferenceInputMirrorCovariance
import TetraStereo.OneCenter.LocalizedRecursivePhysicalDecisionChecks
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# A case-only repair of the 21-atom false lowercase is not mirror covariant

**Scope.** This module rejects one proposed repair. It is **not** a claim that the current
evaluator violates its descriptor reflection law: on the 21-atom input that law holds
(`decorated_actual_covariant`, an instance of `referenceState_reflectInput_mapOcc`).

**Actual source/mirror pair** (`decorated_source_mirror_pair`). `mirrorReference` is
`reflectInput decReference`, the `x ↦ -x` spatial mirror of the accepted hidden-parity cage
(a different certified input). Facts, all derived from the accepted obstruction and the
cross-input covariance; no output is evaluated:

* both inputs return the same lowercase root descriptor and report it;
* the mirror input's arm states are the source arm states swapped: the arm that reads
  `R` on one input reads `S` on the other;
* the executable source-coordinate pair count is `0` on both inputs; the mirror's configuration
  is `mirrorConfiguration detectedCfg`, and it lies in the original recursive domain with
  physical count `0`.

**No-go.** `caseOnly_noGo`: let `F` be any post-processing of the old outcome and a count.
Suppose the old outcome is fixed by the descriptor reflection (lowercase or `none`) and `F` makes
it uppercase. Then `F` is not equivariant: `F (M out) n ≠ M (F out n)`. Instance: the raw-preserving
case conversion `caseOnlyRepair n = map (classifyTetrahedralRSPseudo ∘ rawLetter · n)`
(`caseOnlyRepair_not_covariant`, and on the actual pair `decorated_caseOnlyRepair_fails`). The
same holds for every count-based `F` (`decorated_caseOnly_noGo`): the old root outcome and the
count coincide on the pair, but any mirror-covariant uppercase repaired output must differ
between them (`decorated_repair_must_separate`).

What the repair must therefore supply is information that separates the two inputs at the root.
On this pair, the opposite arm letters and the coordinates provide distinguishing information.
A repair route to investigate is a
reflection-invariant ordering of the two physically diastereomorphic arms before Rule 5, and the
raw orientation read under that order. Nothing here asserts that pair parity suffices, that a
Rule-6 extension is the unique remedy, or which order chemistry prescribes.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveCaseOnlyRepairObstruction

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference
open FinitePhysicalBranchTransport LocalizedActualPhysicalBranchDecision
open LocalizedPhysicalInputReflection LocalizedReferenceInputMirrorCovariance
open LocalizedRecursiveAuxiliaryPhysicalDomain RootedTetrahedralBranchSymmetry

/-! ## The algebraic no-go -/

/-- The raw sense of a label, ignoring case: the letter a case-only conversion keeps. -/
def rawLetter : LocalizedAuxiliaryLabel → RS
  | .chiral raw => raw
  | .pseudoasymmetric .r => .R
  | .pseudoasymmetric .s => .S

/-- **The rejected shortcut**: keep the old raw letter and reclassify case from a new count. -/
def caseOnlyRepair (count : Nat) (outcome : Option LocalizedAuxiliaryLabel) :
    Option LocalizedAuxiliaryLabel :=
  outcome.map fun label => classifyTetrahedralRSPseudo (rawLetter label) count

theorem reflectUppercase_of_isLowercase {label : LocalizedAuxiliaryLabel}
    (lower : label.IsLowercase) : reflectUppercaseAuxiliaryLabel label = label := by
  cases label with
  | chiral raw => exact False.elim lower
  | pseudoasymmetric raw => rfl

theorem uppercase_ne_reflect (raw : RS) :
    (some (.chiral raw) : Option LocalizedAuxiliaryLabel) ≠
      (some (.chiral raw) : Option LocalizedAuxiliaryLabel).map reflectUppercaseAuxiliaryLabel := by
  cases raw <;> simp [reflectUppercaseAuxiliaryLabel, RS.swap]

/-- **No equivariant uppercase at a reflection-fixed outcome.** If the old outcome is fixed by the
descriptor reflection and a post-processing `F` makes it uppercase at a count, then `F` fails the
mirror action at that count. -/
theorem caseOnly_noGo (F : Option LocalizedAuxiliaryLabel → Nat → Option LocalizedAuxiliaryLabel)
    (outcome : Option LocalizedAuxiliaryLabel) (count : Nat)
    (fixed : outcome.map reflectUppercaseAuxiliaryLabel = outcome)
    (upper : ∃ raw : RS, F outcome count = some (.chiral raw)) :
    F (outcome.map reflectUppercaseAuxiliaryLabel) count ≠
      (F outcome count).map reflectUppercaseAuxiliaryLabel := by
  obtain ⟨raw, upperEq⟩ := upper
  rw [fixed, upperEq]
  exact uppercase_ne_reflect raw

/-- The raw-preserving conversion raises a lowercase label at every count other than `1`. -/
theorem caseOnlyRepair_raises (pseudo : PseudoRS) {count : Nat} (notOne : count ≠ 1) :
    caseOnlyRepair count (some (.pseudoasymmetric pseudo)) =
      some (.chiral (rawLetter (.pseudoasymmetric pseudo))) := by
  simp [caseOnlyRepair, classifyTetrahedralRSPseudo, notOne]

/-- **The raw-preserving case-only conversion is not mirror covariant** at any lowercase outcome
and any count other than `1`. -/
theorem caseOnlyRepair_not_covariant (pseudo : PseudoRS) {count : Nat} (notOne : count ≠ 1) :
    caseOnlyRepair count ((some (.pseudoasymmetric pseudo)).map reflectUppercaseAuxiliaryLabel) ≠
      (caseOnlyRepair count (some (.pseudoasymmetric pseudo))).map
        reflectUppercaseAuxiliaryLabel :=
  caseOnly_noGo (fun outcome count => caseOnlyRepair count outcome) _ count rfl
    ⟨_, caseOnlyRepair_raises pseudo notOne⟩

/-! ## The actual 21-atom source/mirror pair -/

section Decorated

open LocalizedRecursiveAuxiliaryParityDecoration LocalizedRecursiveAuxiliarySuccessfulObstruction
open LocalizedRecursivePhysicalDecisionChecks

/-- The spatial mirror of the accepted 21-atom hidden-parity input. -/
abbrev mirrorReference : LocalizedRuleMajorReference.Input := reflectInput decReference

/-- The mirror input's root occurrence (the image of the source final root occurrence). -/
abbrev mirrorTarget : LocalizedRuleMajorReference.Occurrence mirrorReference := mapOcc decTarget

abbrev sourceCount : Nat :=
  computedPairCount (actualCanonicalMolecule decoratedCertified) (coordinateCfg decoratedCertified)
    decRoot

abbrev mirrorCount : Nat :=
  computedPairCount (actualCanonicalMolecule (reflectedCertified decoratedCertified))
    (coordinateCfg (reflectedCertified decoratedCertified)) decRoot

theorem mirrorTarget_eq_final :
    mirrorReference.certified.localizedFinalOccurrenceExecutable (carrierFuel mirrorReference)
      decRoot = mirrorTarget := rfl

/-- **The actual evaluator satisfies its reflection law on the pair.** -/
theorem decorated_actual_covariant :
    referenceState mirrorReference mirrorTarget =
      (referenceState decReference decTarget).map reflectUppercaseAuxiliaryLabel :=
  referenceState_reflectInput_mapOcc (input := decReference) simple_bonded decTarget

theorem sourceCount_eq_zero : sourceCount = 0 := decorated_coordinate_count_zero

theorem mirrorCount_eq_zero : mirrorCount = 0 :=
  (computedPairCount_coordinateCfg_reflectInput decoratedCertified detectedCfg decRoot
    detectedDomain).trans decorated_coordinate_count_zero

theorem source_root_fixed :
    (referenceState decReference decTarget).map reflectUppercaseAuxiliaryLabel =
      referenceState decReference decTarget := by
  obtain ⟨descriptor, returned⟩ := root_returns
  rw [returned]
  exact congrArg some (reflectUppercase_of_isLowercase (root_returned_isLowercase returned))

/-- **The actual source/mirror pair.** Same lowercase root descriptor and report entry on both
inputs, swapped arm letters, count `0` on both, and the mirror input lies in the original
recursive physical domain for the mirrored configuration with physical count `0`. -/
theorem decorated_source_mirror_pair :
    ∃ descriptor : LocalizedAuxiliaryLabel,
      descriptor.IsLowercase ∧
      referenceState decReference decTarget = some descriptor ∧
      referenceState mirrorReference mirrorTarget = some descriptor ∧
      (decRoot.val.val, some descriptor) ∈ analyze decReference ∧
      (decRoot.val.val, some descriptor) ∈ analyze mirrorReference ∧
      (∃ raw : RS,
        referenceState decReference armTargetA = some (.chiral raw) ∧
        referenceState decReference armTargetB = some (.chiral (RS.swap raw)) ∧
        referenceState mirrorReference (mapOcc armTargetA) = some (.chiral (RS.swap raw)) ∧
        referenceState mirrorReference (mapOcc armTargetB) = some (.chiral raw)) ∧
      sourceCount = 0 ∧ mirrorCount = 0 ∧
      RecursiveAuxiliaryPhysicalDomain (reflectedCertified decoratedCertified)
        (decoratedCertified.detectedMultiCenterMolecule.mirrorConfiguration detectedCfg) decRoot ∧
      physicalEnantiomorphicPairCount decoratedCertified.detectedMultiCenterMolecule
        (decoratedCertified.detectedMultiCenterMolecule.mirrorConfiguration detectedCfg)
        decRoot = 0 := by
  obtain ⟨descriptor, returned⟩ := root_returns
  have lower := root_returned_isLowercase returned
  obtain ⟨raw, stateA⟩ := armA_isChiral
  have stateB := stateB_of_stateA stateA
  have sourceMem : (decRoot.val.val, some descriptor) ∈ analyze decReference := by
    obtain ⟨_, _, _, _, _, _, _, _, _, reported⟩ := successfulFalseLowercase
    obtain ⟨other, otherReturned, _, otherMem⟩ := reported
    rw [returned] at otherReturned
    cases otherReturned
    exact otherMem
  have mapped : (some descriptor).map reflectUppercaseAuxiliaryLabel = some descriptor :=
    congrArg some (reflectUppercase_of_isLowercase lower)
  refine ⟨descriptor, lower, returned, ?_, sourceMem, ?_, ⟨raw, stateA, stateB, ?_, ?_⟩,
    decorated_coordinate_count_zero, mirrorCount_eq_zero,
    domain_reflectInput decoratedCertified detectedCfg decRoot detectedDomain,
    (physicalPairCount_mirrorConfiguration _ detectedCfg decRoot).trans detectedPairCount⟩
  · rw [decorated_actual_covariant, returned]
    exact mapped
  · apply (mem_analyze_reflectInput_iff simple_bonded _ _).mpr
    rw [mapped]
    exact sourceMem
  · exact (referenceState_reflectInput_mapOcc (input := decReference) simple_bonded
      armTargetA).trans (by rw [stateA]; rfl)
  · exact (referenceState_reflectInput_mapOcc (input := decReference) simple_bonded
      armTargetB).trans (by rw [stateB]; cases raw <;> rfl)

/-- **No count-based case repair of the 21-atom root is mirror covariant.** For any
post-processing `F` of the old root outcome and the executable count: if `F` makes the source
root uppercase, then the mirror input's repaired root is not the reflected source repaired
root. -/
theorem decorated_caseOnly_noGo
    (F : Option LocalizedAuxiliaryLabel → Nat → Option LocalizedAuxiliaryLabel)
    (upper : ∃ raw : RS, F (referenceState decReference decTarget) sourceCount =
      some (.chiral raw)) :
    F (referenceState mirrorReference mirrorTarget) mirrorCount ≠
      (F (referenceState decReference decTarget) sourceCount).map
        reflectUppercaseAuxiliaryLabel := by
  rw [decorated_actual_covariant, mirrorCount_eq_zero]
  rw [sourceCount_eq_zero] at upper ⊢
  exact caseOnly_noGo F _ 0 source_root_fixed upper

/-- **The raw-preserving case conversion fails on the actual pair.** -/
theorem decorated_caseOnlyRepair_fails :
    caseOnlyRepair mirrorCount (referenceState mirrorReference mirrorTarget) ≠
      (caseOnlyRepair sourceCount (referenceState decReference decTarget)).map
        reflectUppercaseAuxiliaryLabel := by
  apply decorated_caseOnly_noGo (fun outcome count => caseOnlyRepair count outcome)
  obtain ⟨descriptor, returned⟩ := root_returns
  have lower := root_returned_isLowercase returned
  rw [returned, sourceCount_eq_zero]
  cases descriptor with
  | chiral raw => exact False.elim lower
  | pseudoasymmetric pseudo => exact ⟨_, caseOnlyRepair_raises pseudo (by decide)⟩

/-- **What a covariant repair must separate.** Any repaired root outputs on the source and mirror
inputs that satisfy the mirror action and are uppercase on the source differ, whereas the old
root outcome and the executable count coincide on the two inputs. -/
theorem decorated_repair_must_separate (repairedSource repairedMirror : Option LocalizedAuxiliaryLabel)
    (covariant : repairedMirror = repairedSource.map reflectUppercaseAuxiliaryLabel)
    (upper : ∃ raw : RS, repairedSource = some (.chiral raw)) :
    repairedMirror ≠ repairedSource ∧
      referenceState mirrorReference mirrorTarget = referenceState decReference decTarget ∧
      mirrorCount = sourceCount := by
  refine ⟨?_, decorated_actual_covariant.trans source_root_fixed,
    mirrorCount_eq_zero.trans sourceCount_eq_zero.symm⟩
  obtain ⟨raw, upperEq⟩ := upper
  rw [covariant, upperEq]
  exact (uppercase_ne_reflect raw).symm

end Decorated

end TetraStereo.OneCenter.LocalizedRecursiveCaseOnlyRepairObstruction

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCaseOnlyRepairObstruction.caseOnly_noGo
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCaseOnlyRepairObstruction.caseOnlyRepair_not_covariant
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCaseOnlyRepairObstruction.decorated_actual_covariant
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCaseOnlyRepairObstruction.mirrorCount_eq_zero
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCaseOnlyRepairObstruction.decorated_source_mirror_pair
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCaseOnlyRepairObstruction.decorated_caseOnly_noGo
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCaseOnlyRepairObstruction.decorated_caseOnlyRepair_fails
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCaseOnlyRepairObstruction.decorated_repair_must_separate
