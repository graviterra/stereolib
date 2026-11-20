import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootMirrorSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The accepted 25-atom cyclic double-C3 input receives a lowercase descriptor under the
actual repaired prepared evaluator. Both success and classification follow from physical
facts; auxiliary labels and a root output are never supplied or evaluated wholesale.
This result does not identify the concrete r/s letter. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3Pseudo

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingDoubleC3Physical
open LocalizedChemicalRingDoubleC3Geometry
open LocalizedChemicalRingDoubleC3Domain
open LocalizedPhysicalMarkedParityCompleteness (relativeSign transportedSign relativeSign_eq_iff)
open LocalizedChemicalRingPreparedContextRecursion (preparedAssignCenter?)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

noncomputable section

theorem canonical_exchange_negative (d : canon.Center) :
    relativeSign canon (canonicalCfg true) exchangeAut d = -1 := by
  rcases center_cases d with same | same | same
  · subst d
    have parity : permHandedness (canon.ligandPermAt exchangeAut center0) = -1 := by
      rw [root_local_parity]
      rfl
    rw [relativeSign, transportedSign, center0_fixed, parity]
    have square : canon.configurationSign (canonicalCfg true) center0 *
        canon.configurationSign (canonicalCfg true) center0 = 1 := permHandedness_mul_self _
    calc
      _ = -(canon.configurationSign (canonicalCfg true) center0 *
        canon.configurationSign (canonicalCfg true) center0) := by ring
      _ = -1 := by rw [square]
  · subst d
    have image : canon.centerPerm exchangeAut centerL = centerR := Subtype.ext rfl
    rw [relativeSign, transportedSign, gadget_local_even exchangeAut centerL (by decide),
      image, left_sign, right_sign]
    norm_num
  · subst d
    have image : canon.centerPerm exchangeAut centerR = centerL := Subtype.ext rfl
    rw [relativeSign, transportedSign, gadget_local_even exchangeAut centerR (by decide),
      image, left_sign, right_sign]
    norm_num

def detectedExchange : detected.Aut :=
  Eq.mp (congrArg (fun m : MultiCenterMolecule input.Atom => ↥m.Aut) frameChange_spec) (canon.autReindex frameChange exchangeAut)

theorem detected_exchange_negative (d : detected.Center) :
    relativeSign detected cfg detectedExchange d = -1 := by
  have reindexed (d : (canon.reindexFrames frameChange).Center) :
      relativeSign (canon.reindexFrames frameChange)
        (canon.reindexConfiguration frameChange (canonicalCfg true))
        (canon.autReindex frameChange exchangeAut) d = -1 := by
    rw [relativeSign_eq_iff]
    have h := (MultiCenterMolecule.branchTransportSign_reindexFrames_iff canon frameChange
      (canonicalCfg true) exchangeAut d true).mpr
      (by simpa only [if_pos rfl, transportedSign] using
        ((relativeSign_eq_iff canon (canonicalCfg true) exchangeAut d (-1)).mp
          (canonical_exchange_negative d)))
    simpa only [if_pos rfl, transportedSign] using h
  have transfer {m n : MultiCenterMolecule input.Atom} (same : m = n)
      (configuration : m.Configuration) (e : m.Aut)
      (signs : ∀ d : m.Center, relativeSign m configuration e d = -1) :
      ∀ d : n.Center,
        relativeSign n (Eq.mp (congrArg MultiCenterMolecule.Configuration same) configuration)
          (Eq.mp (congrArg (fun m : MultiCenterMolecule input.Atom => ↥m.Aut) same) e) d = -1 := by
    cases same
    exact signs
  exact transfer frameChange_spec _ _ reindexed d

theorem detected_exchange_fixed :
    (detectedExchange : Equiv.Perm input.Atom) detectedRoot.1 = detectedRoot.1 := by
  have transport {m n : MultiCenterMolecule input.Atom} (same : m = n) (e : m.Aut) :
      ((Eq.mp (congrArg (fun m : MultiCenterMolecule input.Atom => ↥m.Aut) same) e : n.Aut) :
        Equiv.Perm input.Atom) = e := by
    cases same
    rfl
  rw [detectedExchange, transport frameChange_spec]
  rfl

/-- An actual cyclic lowercase assignment with stereochemically dependent non-root centers.
The absolute lowercase letter remains unspecified. -/
theorem root_pseudo : ∃ raw,
    preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) 0 =
      some (.pseudoasymmetric raw) :=
  LocalizedChemicalRingJointPreparedRootMirrorSymmetry.assignCenter_pseudo
    input mol (structure_agreement true) admissible supported single_bonded cfg calibrated
    detectedRoot detectedExchange detected_exchange_fixed detected_exchange_negative
    ⟨0, constant_charge⟩ proper_distinct

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3Pseudo

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3Pseudo.canonical_exchange_negative
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3Pseudo.detected_exchange_negative
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3Pseudo.detected_exchange_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3Pseudo.root_pseudo
