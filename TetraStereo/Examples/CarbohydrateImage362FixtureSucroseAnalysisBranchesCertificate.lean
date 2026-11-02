import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseAssignmentsCertificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucroseDescriptorCertificate

open OneCenter

def expectedAnalysisBranches : NormalizedStereoAnalysisBranches :=
  { tetrahedral := expectedAssignments
    ordinaryDoubleBond := []
    coupledDoubleBond := []
    oddCumuleneDoubleBond := []
    extendedAxial := [] }

theorem analysisBranches_ext (left right : NormalizedStereoAnalysisBranches)
    (tetrahedral : left.tetrahedral = right.tetrahedral)
    (ordinaryDoubleBond : left.ordinaryDoubleBond = right.ordinaryDoubleBond)
    (coupledDoubleBond : left.coupledDoubleBond = right.coupledDoubleBond)
    (oddCumuleneDoubleBond : left.oddCumuleneDoubleBond = right.oddCumuleneDoubleBond)
    (extendedAxial : left.extendedAxial = right.extendedAxial) : left = right := by
  cases left
  cases right
  simp_all

/-- The normalized analyzer's five output segments are exact: nine tetrahedral assignments and no
ordinary, coupled, odd-cumulene, or extended-axial assignments. -/
theorem normalizedStereoAnalysisBranches_eq_expected :
    normalizedStereoAnalysisBranches normalized = expectedAnalysisBranches := by
  apply analysisBranches_ext
  · simp only [normalizedStereoAnalysisBranches_tetrahedral]
    change tetrahedralAssignments normalized expanded
      (discoverRawDescriptors normalized expanded fuel) fuel = expectedAssignments
    rw [discoverRawDescriptors_eq_expected]
    exact tetrahedralAssignments_eq_expected
  all_goals rfl

/-- The normalized public analyzer assembles exactly the nine certified Sucrose assignments. -/
theorem analyzeNormalized_eq_expected :
    analyzeNormalized normalized = expectedAssignments := by
  unfold analyzeNormalized
  rw [normalizedStereoAnalysisBranches_eq_expected]
  rfl

end SucroseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
