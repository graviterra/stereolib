import TetraStereo.UniversalProof.NextFrontier.NativeRawPathCommonPrefixSplice
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeGeneratedPhysicalFrameMetric
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeGeneratedRealPaths
open TetraStereo.UniversalProof.NativeChronologicalTreeAcyclic
open TetraStereo.UniversalProof.NativeChronologicalTreeSimplePathUniqueness
open TetraStereo.UniversalProof.NativeRawPathCommonPrefixSplice

/-- Any actual supported simple path has physical shortest length, because the raw tree
    entails acyclicity and hence equality with an internally obtained shortest graph path. -/
theorem supported_edgeCount_eq_physical_distance {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {start finish : Nat} {vertices : List Nat}
    (supported : RawSupportedPath mol start finish vertices) :
    edgeCount vertices = (physicalGraph mol).dist start finish := by
  obtain ⟨path, support⟩ := raw_supported_realizes_path supported
  obtain ⟨shortest, simple, shortestLength⟩ := path.val.reachable.exists_path_of_dist
  have same : path = (⟨shortest, simple⟩ : (physicalGraph mol).Path start finish) :=
    (chronological_physicalGraph_acyclic tree).path_unique path ⟨shortest, simple⟩
  have sameLength := congrArg (fun p : (physicalGraph mol).Path start finish => p.val.length) same
  rw [← support]
  simp only [edgeCount, SimpleGraph.Walk.length_support, Nat.add_sub_cancel]
  exact sameLength.trans shortestLength

/-- Actual common-prefix metric equals root-independent physical graph distance for all
    raw-supported root paths; no metric or output equality is supplied as a premise. -/
theorem supported_pair_metric_eq_physical_distance {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root center target : Nat} (p q : List Nat)
    (pPath : RawSupportedPath mol root center p)
    (qPath : RawSupportedPath mol root target q) :
    CanonicalComparisonFrame.pathDistance p q = (physicalGraph mol).dist center target := by
  obtain ⟨splice, supported, edgeMetric⟩ := supported_pair_splice_exists tree p q pPath qPath
  have distance := supported_edgeCount_eq_physical_distance tree supported
  exact edgeMetric.symm.trans distance

/-- Frame history is computed from the actual generated real center, retaining all original
    discovery histories; the result is physical distance at that fixed center atom. -/
theorem generated_frame_realDistance_eq_physical_distance {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {center target : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (targetGenerated : CanonicalCenterTreeNode mol root target)
    (centerReal : center.provenance = .realAtom) (targetReal : target.provenance = .realAtom) :
    (⟨center.history⟩ : CanonicalComparisonFrame.Frame).realDistance target =
      (physicalGraph mol).dist center.atom target.atom := by
  have centerPath := generated_real_root_path rootBound tree.wellFormed centerGenerated centerReal
  have targetPath := generated_real_root_path rootBound tree.wellFormed targetGenerated targetReal
  exact supported_pair_metric_eq_physical_distance tree center.history.reverse target.history.reverse
    centerPath targetPath

/-- Different actual discovery roots give the same computed distance at the same physical
    center and target; neither histories nor desired metric values are assumed equal. -/
theorem generated_frame_discovery_root_independent {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {firstRoot secondRoot : Nat}
    (firstBound : firstRoot < mol.atomCount) (secondBound : secondRoot < mol.atomCount)
    {firstCenter firstTarget secondCenter secondTarget : CanonicalBranchNode}
    (firstCenterGenerated : CanonicalCenterTreeNode mol firstRoot firstCenter)
    (firstTargetGenerated : CanonicalCenterTreeNode mol firstRoot firstTarget)
    (secondCenterGenerated : CanonicalCenterTreeNode mol secondRoot secondCenter)
    (secondTargetGenerated : CanonicalCenterTreeNode mol secondRoot secondTarget)
    (firstCenterReal : firstCenter.provenance = .realAtom)
    (firstTargetReal : firstTarget.provenance = .realAtom)
    (secondCenterReal : secondCenter.provenance = .realAtom)
    (secondTargetReal : secondTarget.provenance = .realAtom)
    (sameCenterAtom : firstCenter.atom = secondCenter.atom)
    (sameTargetAtom : firstTarget.atom = secondTarget.atom) :
    (⟨firstCenter.history⟩ : CanonicalComparisonFrame.Frame).realDistance firstTarget =
      (⟨secondCenter.history⟩ : CanonicalComparisonFrame.Frame).realDistance secondTarget := by
  rw [generated_frame_realDistance_eq_physical_distance tree firstBound
    firstCenterGenerated firstTargetGenerated firstCenterReal firstTargetReal]
  rw [generated_frame_realDistance_eq_physical_distance tree secondBound
    secondCenterGenerated secondTargetGenerated secondCenterReal secondTargetReal]
  rw [sameCenterAtom, sameTargetAtom]

end TetraStereo.UniversalProof.NativeGeneratedPhysicalFrameMetric
