import TetraStereo.OneCenter.CIPAuthoritativeAromaticKekuleNormalizationKernelCertificate

set_option autoImplicit false

namespace TetraStereo.OneCenter.AromaticIntroductionIntakeRegression

open AuthoritativeCIPAromaticKekuleNormalization

/-!
The aromatic intake is also callable on raw molecules without aromatic bonds. A one-atom methane
record isolates the provenance admission boundary from Kekulé search: every earlier structural,
valence, source-mass and normalization condition is satisfied even when its claimed introducing
parent is itself. Checked intake must reject that impossible history. Valid root metadata and the
legacy unknown prefix must continue to succeed. General preservation theorems in the imported
kernel certificate cover all aromatic selections, including their changing bond multiplicities.
-/

def knownRoot : RawMolecule :=
  { atoms := [AtomSpec.aliphatic .C]
    bonds := []
    neighborOrder := [[]]
    introductionPredecessors := [none] }

def legacyUnknown : RawMolecule :=
  { knownRoot with introductionPredecessors := [] }

def selfPredecessor : RawMolecule :=
  { knownRoot with introductionPredecessors := [some 0] }

def overlongPrefix : RawMolecule :=
  { knownRoot with introductionPredecessors := [none, none] }

/-- This record satisfied every condition of the previous aromatic intake boundary. -/
theorem malformed_passes_previous_admission :
    selfPredecessor.WrittenNeighborExact ∧ selfPredecessor.Rule2MassesKnown ∧
      AromaticKekuleNormalizable selfPredecessor := by
  refine ⟨selfPredecessor.writtenNeighborExact?_eq_true_iff.mp (by decide +kernel),
    selfPredecessor.rule2MassesKnown?_eq_true_iff.mp (by decide +kernel), ?_⟩
  exact (normalizeAromaticKekule?_isSome_iff_normalizable selfPredecessor).1
    (by decide +kernel)

theorem valid_root_accepted :
    (normalizeAromaticChemistryCertified? knownRoot).isSome = true := by
  decide +kernel

theorem legacy_unknown_accepted :
    (normalizeRawMoleculeAuthoritativeAromaticCertified? legacyUnknown).isSome = true := by
  decide +kernel

theorem self_predecessor_rejected :
    (normalizeAromaticChemistryCertified? selfPredecessor).isNone = true := by
  decide +kernel

theorem raw_self_predecessor_rejected :
    (normalizeRawMoleculeAuthoritativeAromaticCertified? selfPredecessor).isNone = true := by
  decide +kernel

theorem overlong_prefix_rejected :
    (normalizeRawMoleculeAuthoritativeAromaticCertified? overlongPrefix).isNone = true := by
  decide +kernel

end TetraStereo.OneCenter.AromaticIntroductionIntakeRegression

assert_kernel_only
  TetraStereo.OneCenter.AromaticIntroductionIntakeRegression.malformed_passes_previous_admission
assert_kernel_only TetraStereo.OneCenter.AromaticIntroductionIntakeRegression.valid_root_accepted
assert_kernel_only TetraStereo.OneCenter.AromaticIntroductionIntakeRegression.legacy_unknown_accepted
assert_kernel_only
  TetraStereo.OneCenter.AromaticIntroductionIntakeRegression.self_predecessor_rejected
assert_kernel_only
  TetraStereo.OneCenter.AromaticIntroductionIntakeRegression.raw_self_predecessor_rejected
assert_kernel_only
  TetraStereo.OneCenter.AromaticIntroductionIntakeRegression.overlong_prefix_rejected
