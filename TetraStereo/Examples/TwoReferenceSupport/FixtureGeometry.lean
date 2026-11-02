import TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture
import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace FixtureGeometry

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture

/-- Read a numbered point through the certified input API, with the bound discharged from the
fixture's 33-atom inventory. -/
def pointAt (n : Fin 33) : Option CartesianPoint3 :=
  input.certified.spatialPointAt? ⟨n.val, by change n.val < 33; exact n.isLt⟩

theorem pointAt_eq_source_index (n : Fin 33) :
    pointAt n = source.spatial?.bind (fun s => s.positions[n.val]?) := by
  simp [pointAt, CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource,
    certifiedSource]

def atoms4 : List (Fin 33) := [6, 3, 7, 5]
def atoms7 : List (Fin 33) := [10, 9, 4, 8]
def atoms11 : List (Fin 33) := [13, 3, 14, 12]
def atoms14 : List (Fin 33) := [17, 16, 11, 15]
def atoms19 : List (Fin 33) := [21, 18, 22, 20]
def atoms22 : List (Fin 33) := [25, 24, 19, 23]
def atoms26 : List (Fin 33) := [28, 18, 29, 27]
def atoms29 : List (Fin 33) := [32, 31, 26, 30]

/-- The coordinate lookup is performed by `spatialPointAt?`; this helper preserves failure rather
than silently replacing missing or out-of-range points. -/
def pointsAt (order : List (Fin 33)) : Option (List CartesianPoint3) :=
  order.mapM pointAt

def volumeAt (order : List (Fin 33)) : Option ℚ := do
  match ← pointsAt order with
  | [a, b, c, d] => some (CartesianPoint3.orientedVolume a b c d)
  | _ => none

/-- Geometry-only descriptor computed from the same point readback. -/
def descriptorAt (order : List (Fin 33)) : Option RS := do
  let volume ← volumeAt order
  CertifiedLocalizedCIPInput.descriptorOfOrientedVolume? volume

theorem descriptorAt_eq_of_volume (order : List (Fin 33)) (v : ℚ)
    (h : volumeAt order = some v) :
    descriptorAt order = CertifiedLocalizedCIPInput.descriptorOfOrientedVolume? v := by
  simp [descriptorAt, h]

/-- The volume-based helper is exactly the public geometry-only list descriptor on the points
returned by the certified coordinate readback. -/
theorem descriptorAt_eq_priority_ordered_list (order : List (Fin 33)) :
    descriptorAt order = (pointsAt order).bind
      CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? := by
  unfold descriptorAt volumeAt
  cases h : pointsAt order <;> simp
  all_goals
    split <;> simp_all [CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?,
      CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?]

theorem volume4 : volumeAt atoms4 = some (-5205250) := by
  norm_num [volumeAt, pointsAt, pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, atoms4,
    CartesianPoint3.orientedVolume]

theorem volume7 : volumeAt atoms7 = some (-5222963) := by
  norm_num [volumeAt, pointsAt, pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, atoms7,
    CartesianPoint3.orientedVolume]

theorem volume11 : volumeAt atoms11 = some 5196264 := by
  norm_num [volumeAt, pointsAt, pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, atoms11,
    CartesianPoint3.orientedVolume]

theorem volume14 : volumeAt atoms14 = some (-5212558) := by
  norm_num [volumeAt, pointsAt, pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, atoms14,
    CartesianPoint3.orientedVolume]

theorem volume19 : volumeAt atoms19 = some 5205250 := by
  norm_num [volumeAt, pointsAt, pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, atoms19,
    CartesianPoint3.orientedVolume]

theorem volume22 : volumeAt atoms22 = some 5222963 := by
  norm_num [volumeAt, pointsAt, pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, atoms22,
    CartesianPoint3.orientedVolume]

theorem volume26 : volumeAt atoms26 = some (-5196264) := by
  norm_num [volumeAt, pointsAt, pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, atoms26,
    CartesianPoint3.orientedVolume]

theorem volume29 : volumeAt atoms29 = some 5212558 := by
  norm_num [volumeAt, pointsAt, pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, atoms29,
    CartesianPoint3.orientedVolume]

theorem descriptor4 : descriptorAt atoms4 = some RS.R := by
  rw [descriptorAt_eq_of_volume atoms4 _ volume4]
  norm_num [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?]

theorem descriptor7 : descriptorAt atoms7 = some RS.R := by
  rw [descriptorAt_eq_of_volume atoms7 _ volume7]
  norm_num [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?]

theorem descriptor11 : descriptorAt atoms11 = some RS.S := by
  rw [descriptorAt_eq_of_volume atoms11 _ volume11]
  norm_num [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?]

theorem descriptor14 : descriptorAt atoms14 = some RS.R := by
  rw [descriptorAt_eq_of_volume atoms14 _ volume14]
  norm_num [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?]

theorem descriptor19 : descriptorAt atoms19 = some RS.S := by
  rw [descriptorAt_eq_of_volume atoms19 _ volume19]
  norm_num [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?]

theorem descriptor22 : descriptorAt atoms22 = some RS.S := by
  rw [descriptorAt_eq_of_volume atoms22 _ volume22]
  norm_num [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?]

theorem descriptor26 : descriptorAt atoms26 = some RS.R := by
  rw [descriptorAt_eq_of_volume atoms26 _ volume26]
  norm_num [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?]

theorem descriptor29 : descriptorAt atoms29 = some RS.S := by
  rw [descriptorAt_eq_of_volume atoms29 _ volume29]
  norm_num [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?]

theorem priorityList4 : (pointsAt atoms4).bind
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? = some RS.R := by
  rw [← descriptorAt_eq_priority_ordered_list]
  exact descriptor4

theorem priorityList7 : (pointsAt atoms7).bind
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? = some RS.R := by
  rw [← descriptorAt_eq_priority_ordered_list]
  exact descriptor7

theorem priorityList11 : (pointsAt atoms11).bind
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? = some RS.S := by
  rw [← descriptorAt_eq_priority_ordered_list]
  exact descriptor11

theorem priorityList14 : (pointsAt atoms14).bind
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? = some RS.R := by
  rw [← descriptorAt_eq_priority_ordered_list]
  exact descriptor14

theorem priorityList19 : (pointsAt atoms19).bind
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? = some RS.S := by
  rw [← descriptorAt_eq_priority_ordered_list]
  exact descriptor19

theorem priorityList22 : (pointsAt atoms22).bind
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? = some RS.S := by
  rw [← descriptorAt_eq_priority_ordered_list]
  exact descriptor22

theorem priorityList26 : (pointsAt atoms26).bind
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? = some RS.R := by
  rw [← descriptorAt_eq_priority_ordered_list]
  exact descriptor26

theorem priorityList29 : (pointsAt atoms29).bind
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? = some RS.S := by
  rw [← descriptorAt_eq_priority_ordered_list]
  exact descriptor29

end FixtureGeometry

assert_kernel_only FixtureGeometry.volume4
assert_kernel_only FixtureGeometry.volume7
assert_kernel_only FixtureGeometry.volume11
assert_kernel_only FixtureGeometry.volume14
assert_kernel_only FixtureGeometry.volume19
assert_kernel_only FixtureGeometry.volume22
assert_kernel_only FixtureGeometry.volume26
assert_kernel_only FixtureGeometry.volume29
assert_kernel_only FixtureGeometry.descriptor4
assert_kernel_only FixtureGeometry.descriptor7
assert_kernel_only FixtureGeometry.descriptor11
assert_kernel_only FixtureGeometry.descriptor14
assert_kernel_only FixtureGeometry.descriptor19
assert_kernel_only FixtureGeometry.descriptor22
assert_kernel_only FixtureGeometry.descriptor26
assert_kernel_only FixtureGeometry.descriptor29
assert_kernel_only FixtureGeometry.descriptorAt_eq_priority_ordered_list
assert_kernel_only FixtureGeometry.priorityList4
assert_kernel_only FixtureGeometry.priorityList7
assert_kernel_only FixtureGeometry.priorityList11
assert_kernel_only FixtureGeometry.priorityList14
assert_kernel_only FixtureGeometry.priorityList19
assert_kernel_only FixtureGeometry.priorityList22
assert_kernel_only FixtureGeometry.priorityList26
assert_kernel_only FixtureGeometry.priorityList29
