import TetraStereo.OneCenter.LocalizedOccurrenceRule3Through5FixedPoint

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedRule3SpatialRegression

open OneCenter

private def leftEndpoint : CartesianPoint3 := { x := 0, y := 0, z := 0 }
private def rightEndpoint : CartesianPoint3 := { x := 1, y := 0, z := 0 }
private def upperLeftReference : CartesianPoint3 := { x := 0, y := 1, z := 0 }
private def upperRightReference : CartesianPoint3 := { x := 1, y := 1, z := 0 }
private def lowerRightReference : CartesianPoint3 := { x := 1, y := -1, z := 0 }
private def nonplanarRightReference : CartesianPoint3 := { x := 1, y := 1, z := 1 }
private def collinearLeftReference : CartesianPoint3 := { x := -1, y := 0, z := 0 }

/-- Exact coplanar references on the same side of the double-bond axis are `seqcis`. -/
example :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
      upperLeftReference upperRightReference = some OfficialRule3Geometry.seqcis := by
  norm_num [rule3GeometryOfSpatialReferences?, CartesianPoint3.rule3Coplanarity,
    CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
    RationalVector3.cross, RationalVector3.dot, leftEndpoint, rightEndpoint,
    upperLeftReference, upperRightReference]

/-- Exact coplanar references on opposite sides of the axis are `seqtrans`. -/
example :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
      upperLeftReference lowerRightReference = some OfficialRule3Geometry.seqtrans := by
  norm_num [rule3GeometryOfSpatialReferences?, CartesianPoint3.rule3Coplanarity,
    CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
    RationalVector3.cross, RationalVector3.dot, leftEndpoint, rightEndpoint,
    upperLeftReference, lowerRightReference]

/-- A noncoplanar four-point observation is not accepted as double-bond geometry. -/
example :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
      upperLeftReference nonplanarRightReference = none := by
  norm_num [rule3GeometryOfSpatialReferences?, CartesianPoint3.rule3Coplanarity,
    CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
    RationalVector3.cross, RationalVector3.dot, leftEndpoint, rightEndpoint,
    upperLeftReference, nonplanarRightReference]

/-- A reference collinear with the double-bond axis supplies no side. -/
example :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
      collinearLeftReference upperRightReference = none := by
  norm_num [rule3GeometryOfSpatialReferences?, CartesianPoint3.rule3Coplanarity,
    CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
    RationalVector3.cross, RationalVector3.dot, leftEndpoint, rightEndpoint,
    collinearLeftReference, upperRightReference]

#check OneCenter.rule3GeometryOfSpatialReferences?_eq_some_iff
#check OneCenter.CertifiedLocalizedCIPInput.localizedRule3SpatialUnit?_sound
#check OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule3SpatialUnit?_sound
#check OneCenter.CertifiedLocalizedCIPInput.localizedRule3SpatialOccurrenceScan?_sound
#check OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootUncancelledRule3SpatialKey?_sound
#check OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootUncancelledRule3SpatialKeys_transCmp
#check OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRecursiveRule3SpatialKey?_sound
#check OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootRecursiveRule3SpatialKeys_transCmp
#check OneCenter.CertifiedLocalizedCIPInput.sortLocalizedRerootRecursiveRule3SpatialKeys_perm
#check OneCenter.CertifiedLocalizedCIPInput.sortLocalizedRerootRecursiveRule3SpatialKeys_descending
#check OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRecursiveRule3SpatialKey?_constitutional_complete
#check OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRecursiveRule3SpatialKey?_constitutional_sourceAligned
#check OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRecursiveRule3SpatialKey?_rule3Aligned
#check OneCenter.CertifiedLocalizedCIPInput.exists_buildLocalizedRerootRecursiveRule3SpatialKey?_of_budget_le
#check OneCenter.CertifiedLocalizedCIPInput.exists_buildLocalizedRerootRecursiveRule3SpatialKey?_at_twice
#check OneCenter.CertifiedLocalizedCIPInput.localizedRule3PhysicalUnitId_eq_iff
#check OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3CanonicalKeyFrame?_sound
#check OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRule3CanonicalKeyFrameAt_transCmp
#check OneCenter.CertifiedLocalizedCIPInput.buildLocalizedOccurrenceRule3Through5KeyFrame?_sound
#check OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceRule3Through5Keys_transCmp
#check OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceRule3Through5At_ordering
#check OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule3Through5Descriptor?_sound
#check OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
#check OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule3Through5Descriptor?_eq_none_iff_no_canonical
#check OneCenter.CertifiedLocalizedCIPInput.existsUnique_localizedOccurrenceRule3Through5Model
#check OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule3Through5Model_eq_some_implies_declarative

end TetraStereo.Examples.LocalizedRule3SpatialRegression
