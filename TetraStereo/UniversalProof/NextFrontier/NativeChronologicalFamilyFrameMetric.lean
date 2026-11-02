import TetraStereo.UniversalProof.NextFrontier.NativeGeneratedPhysicalFrameMetric
import TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeChronologicalFamilyFrameMetric

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain
open TetraStereo.UniversalProof.NativeChronologicalTreeAcyclic
open TetraStereo.UniversalProof.NativeGeneratedPhysicalFrameMetric











/-- At any bounded actual discovery root, the real frame built from a genuine
generated center computes physical graph distance to a genuine real target. -/
theorem family_generated_realDistance_eq_physical_distance
    (ps : List TetrahedralInputParity) {root : Nat}
    (rootBound : root < (familyRaw ps).atomCount)
    {center target : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (targetGenerated : CanonicalCenterTreeNode (familyRaw ps) root target)
    (centerReal : center.provenance = .realAtom)
    (targetReal : target.provenance = .realAtom) :
    (⟨center.history⟩ : CanonicalComparisonFrame.Frame).realDistance target =
      (physicalGraph (familyRaw ps)).dist center.atom target.atom :=
  generated_frame_realDistance_eq_physical_distance
    (familyRaw_chronologicalPhysicalTree ps) rootBound
    centerGenerated targetGenerated centerReal targetReal

/-- The actual import-safe observer returns the physical distance for real
family nodes, rather than a supplied distance or a relabelled discovery node. -/
theorem family_generated_real_observation_eq_physical_distance
    (ps : List TetrahedralInputParity) {root : Nat}
    (rootBound : root < (familyRaw ps).atomCount)
    {center target : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (targetGenerated : CanonicalCenterTreeNode (familyRaw ps) root target)
    (centerReal : center.provenance = .realAtom)
    (targetReal : target.provenance = .realAtom) :
    CanonicalComparisonFrame.observeNode
      (⟨center.history⟩ : CanonicalComparisonFrame.Frame) target =
      some ((physicalGraph (familyRaw ps)).dist center.atom target.atom) := by
  rw [CanonicalComparisonFrame.real_observation _ _ targetReal]
  rw [family_generated_realDistance_eq_physical_distance ps rootBound
    centerGenerated targetGenerated centerReal targetReal]

/-- Changing the discovery root preserves real distance at equal physical
center and target atoms. No equality of their histories or metric is assumed. -/
theorem family_generated_discovery_root_independent
    (ps : List TetrahedralInputParity) {firstRoot secondRoot : Nat}
    (firstBound : firstRoot < (familyRaw ps).atomCount)
    (secondBound : secondRoot < (familyRaw ps).atomCount)
    {firstCenter firstTarget secondCenter secondTarget : CanonicalBranchNode}
    (firstCenterGenerated : CanonicalCenterTreeNode (familyRaw ps) firstRoot firstCenter)
    (firstTargetGenerated : CanonicalCenterTreeNode (familyRaw ps) firstRoot firstTarget)
    (secondCenterGenerated : CanonicalCenterTreeNode (familyRaw ps) secondRoot secondCenter)
    (secondTargetGenerated : CanonicalCenterTreeNode (familyRaw ps) secondRoot secondTarget)
    (firstCenterReal : firstCenter.provenance = .realAtom)
    (firstTargetReal : firstTarget.provenance = .realAtom)
    (secondCenterReal : secondCenter.provenance = .realAtom)
    (secondTargetReal : secondTarget.provenance = .realAtom)
    (sameCenterAtom : firstCenter.atom = secondCenter.atom)
    (sameTargetAtom : firstTarget.atom = secondTarget.atom) :
    (⟨firstCenter.history⟩ : CanonicalComparisonFrame.Frame).realDistance firstTarget =
      (⟨secondCenter.history⟩ : CanonicalComparisonFrame.Frame).realDistance secondTarget :=
  generated_frame_discovery_root_independent
    (familyRaw_chronologicalPhysicalTree ps) firstBound secondBound
    firstCenterGenerated firstTargetGenerated secondCenterGenerated secondTargetGenerated
    firstCenterReal firstTargetReal secondCenterReal secondTargetReal
    sameCenterAtom sameTargetAtom

end TetraStereo.UniversalProof.NativeChronologicalFamilyFrameMetric
