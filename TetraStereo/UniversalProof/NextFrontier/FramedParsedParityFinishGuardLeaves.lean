import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityFinishEqualSupport

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Four actual primitive auxiliary refusal guards, one bounded leaf per equal-arm member. -/
namespace TetraStereo.UniversalProof.FramedParsedParityFinishGuardLeaves
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.FramedParsedParitySchedulerCenter
open TetraStereo.UniversalProof.FramedParsedParitySchedulerLeaves
open TetraStereo.UniversalProof.FramedParsedParityFinishEqualSupport

theorem guard_aa :
    auxiliaryRefusalGate (actualResult .anticlockwise .anticlockwise .anticlockwise)
      (actualMol .anticlockwise .anticlockwise .anticlockwise) (stateD .anticlockwise .anticlockwise .anticlockwise)
      (actualFuel .anticlockwise .anticlockwise .anticlockwise) 1 = true := by
  decide +kernel

theorem guard_ac :
    auxiliaryRefusalGate (actualResult .anticlockwise .clockwise .clockwise)
      (actualMol .anticlockwise .clockwise .clockwise) (stateD .anticlockwise .clockwise .clockwise)
      (actualFuel .anticlockwise .clockwise .clockwise) 1 = true := by
  decide +kernel

theorem guard_ca :
    auxiliaryRefusalGate (actualResult .clockwise .anticlockwise .anticlockwise)
      (actualMol .clockwise .anticlockwise .anticlockwise) (stateD .clockwise .anticlockwise .anticlockwise)
      (actualFuel .clockwise .anticlockwise .anticlockwise) 1 = true := by
  decide +kernel

theorem guard_cc :
    auxiliaryRefusalGate (actualResult .clockwise .clockwise .clockwise)
      (actualMol .clockwise .clockwise .clockwise) (stateD .clockwise .clockwise .clockwise)
      (actualFuel .clockwise .clockwise .clockwise) 1 = true := by
  decide +kernel

theorem equal_refusal_guard (center arm : TetrahedralInputParity) :
    auxiliaryRefusalGate (actualResult center arm arm) (actualMol center arm arm)
      (stateD center arm arm) (actualFuel center arm arm) 1 = true := by
  cases center with
  | clockwise =>
      cases arm with
      | clockwise => exact guard_cc
      | anticlockwise => exact guard_ca
  | anticlockwise =>
      cases arm with
      | clockwise => exact guard_ac
      | anticlockwise => exact guard_aa

end TetraStereo.UniversalProof.FramedParsedParityFinishGuardLeaves
