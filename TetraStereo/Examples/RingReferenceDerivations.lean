import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.Rule6CageAuxiliaries

set_option autoImplicit false
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000
set_option Elab.async false

namespace TetraStereo.Examples.RingReferenceDerivations
open OneCenter Engine LocalizedGenericMarkedRecalculation RingChemicalPriority Recursive
open Rule6CageAuxiliaries (twins twinGeometry spiroPentane)

/-- At the first cage bridgehead, both arms reach atom 4 in the same sphere.
The constitutionally preferred route on arm 6 decides the comparison. -/
theorem bridgehead_route :
    (inspectRingReferenceComparison? twins twinGeometry [0,3] 5 6 4 2).map
      (fun c => (c.verdict.ordering,c.verdict.route?)) = some (.lt,some [6,9,12,4]) := by
  decide +kernel

/-- Every choice at the spiro carbon leaves an equivalent pair. All five
carbons have a certified absence, even with no spatial coordinates. -/
theorem pentane_report :
    (deriveRingReferenceCarbons? spiroPentane (fun _ => none) 1 1).map (·.labels) =
      some ((List.range 5).map (fun i => (i,none))) := by
  decide +kernel

end TetraStereo.Examples.RingReferenceDerivations

assert_kernel_only TetraStereo.Examples.RingReferenceDerivations.bridgehead_route
assert_kernel_only TetraStereo.Examples.RingReferenceDerivations.pentane_report
