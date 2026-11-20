import TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact spatial reflection of the mirror-paired descriptor constructor.
Uppercase letters swap; lowercase letters are unchanged. This is an operational
identity for every step, without any chemical-correctness premise.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingDescriptorSpatialMirror

open LocalizedChemicalRingSenseTransport LocalizedChemicalRingOrientationInduction
open LocalizedMarkedOperationEvaluator (Operations)
open LocalizedGenericMarkedRecalculation (Geometry mirror caseFromMirror?)

def spatialMirror : LocalizedTetrahedralRSPseudoDescriptor → LocalizedTetrahedralRSPseudoDescriptor
  | .chiral raw => .chiral raw.swap
  | .pseudoasymmetric raw => .pseudoasymmetric raw

theorem spatialMirror_involutive : Function.Involutive spatialMirror := by
  rintro (raw | raw) <;> cases raw <;> rfl

theorem caseFromMirror_swapped (first second : Option RS) :
    caseFromMirror? second first = (caseFromMirror? first second).map spatialMirror := by
  cases first with
  | none => cases second <;> rfl
  | some a =>
      cases second with
      | none => rfl
      | some b => cases a <;> cases b <;> rfl

theorem descriptorWith_spatialMirror (step : Step) (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat)
    (node : RawMolecule.CanonicalBranchNode) :
    descriptorWith step mol ops depth (mirror geom) state ctx node =
      (descriptorWith step mol ops depth geom state ctx node).map spatialMirror := by
  unfold descriptorWith
  rw [mirror_mirror]
  exact caseFromMirror_swapped _ _

end TetraStereo.OneCenter.LocalizedChemicalRingDescriptorSpatialMirror

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDescriptorSpatialMirror.spatialMirror_involutive
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDescriptorSpatialMirror.caseFromMirror_swapped
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDescriptorSpatialMirror.descriptorWith_spatialMirror
