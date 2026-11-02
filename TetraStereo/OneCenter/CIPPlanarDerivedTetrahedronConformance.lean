import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor
import TetraStereo.OneCenter.StereochemicalElements

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact P-92 planar derived-tetrahedron conversion

P-92.1.2.1.3 specifies planar chirality by constructing an ordinary tetrahedron with ranked
vertices `a > b > y > z`.  This file formalizes the exact geometric conversion after those four
chemical roles have been established.  It deliberately does not infer the roles from the older
raw planar record; that perception/priority problem remains a separate upstream obligation.

## Source order and handedness calibration

The P-92 text connects the two in-plane reference atoms `a` and `b` to the in-plane bonded atom
`y` and the out-of-plane atom `z`, and determines the chirality sense by the ordinary rules with
the priority order `a > b > y > z`.  The derived tetrahedron is therefore consumed in exactly that
source order: `a`, `b`, `y`, then the lowest-precedence vertex `z`.  `CartesianPoint3.orientedVolume`
anchors on its fourth argument, so passing `a b y z` places `z` on the side remote from the
preferred viewing side, exactly as the ordinary tetrahedral rule requires.  No geometric point
permutation is inserted, and the affine determinant algebra is untouched.

The ordinary tetrahedral calibration for a descending-priority point sequence in the standard
right-handed frame is: negative oriented volume means `R`, positive oriented volume means `S`
(the fourth, lowest-precedence point lies away from the viewer).  P-92.1.2.1.3 assigns the planar
sense by that same ordinary rule, while the `R ↦ Rₚ`, `S ↦ Sₚ` family conversion is fixed by the
P-92 and P-93 planar vocabulary.  Hence `Rₚ` is the negative-volume side of the derived tetrahedron
and `Sₚ` the positive-volume side.  This sign changes only the descriptor calibration at this
bridge; it does not flip any other planar, axial, helical, or IR-9 descriptor, and it does not
change the oriented-volume or affine-frame algebra.
-/

namespace BlueBookP92.PlanarDerivedTetrahedron

/-- Independent exact meaning of `Rₚ/Sₚ` for the source-ordered derived tetrahedron.

The four points are the P-92 ranked vertices in source order `a > b > y > z`; `z` is the
lowest-precedence vertex and is the oriented-volume anchor.  The calibrated ordinary tetrahedral
reading is negative volume `R` and positive volume `S`, hence negative volume `Rₚ` and positive
volume `Sₚ`. -/
def RationalDescriptor
    (a b y z : CartesianPoint3) (descriptor : PlanarDescriptor) : Prop :=
  match descriptor with
  | .Rp => CartesianPoint3.orientedVolume a b y z < 0
  | .Sp => 0 < CartesianPoint3.orientedVolume a b y z

/-- The source order is consumed unchanged: `Rₚ` is exactly the negative-volume side and `Sₚ`
the positive-volume side of the P-92 derived tetrahedron `a > b > y > z`. -/
theorem RationalDescriptor_Rp_iff_negative_volume (a b y z : CartesianPoint3) :
    RationalDescriptor a b y z .Rp ↔
      CartesianPoint3.orientedVolume a b y z < 0 :=
  Iff.rfl

/-- The source order is consumed unchanged: `Sₚ` is exactly the positive-volume side. -/
theorem RationalDescriptor_Sp_iff_positive_volume (a b y z : CartesianPoint3) :
    RationalDescriptor a b y z .Sp ↔
      0 < CartesianPoint3.orientedVolume a b y z :=
  Iff.rfl

end BlueBookP92.PlanarDerivedTetrahedron

/-- Planar labels are the ordinary tetrahedral chirality result on the P-92 derived tetrahedron. -/
def RS.toPlanarDescriptor : RS → PlanarDescriptor
  | .R => .Rp
  | .S => .Sp

/-- Exact executable descriptor for already identified and ranked source vertices `a>b>y>z`.
The point order is the source order unchanged, with the lowest-precedence `z` as the
oriented-volume anchor.  The branch structure keeps the positive side first and the negative side
second; the descriptors are the calibrated ordinary tetrahedral family (`positive ↦ S ↦ Sₚ`,
`negative ↦ R ↦ Rₚ`). -/
def planarDescriptorOfDerivedTetrahedron?
    (a b y z : CartesianPoint3) : Option PlanarDescriptor :=
  let volume := CartesianPoint3.orientedVolume a b y z
  if 0 < volume then some .Sp
  else if volume < 0 then some .Rp
  else none

/-- The planar executable is literally the ordinary exact tetrahedral chirality rule followed by
the `R ↦ Rₚ`, `S ↦ Sₚ` family conversion required by P-92.  The derived tetrahedron is supplied
in source order, so no permutation or reflection enters this bridge. -/
theorem planarDescriptorOfDerivedTetrahedron?_via_tetrahedral_chirality
    (a b y z : CartesianPoint3) :
    planarDescriptorOfDerivedTetrahedron? a b y z =
      (CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
        (CartesianPoint3.orientedVolume a b y z)).map RS.toPlanarDescriptor := by
  let volume := CartesianPoint3.orientedVolume a b y z
  by_cases positive : 0 < volume
  · have core : CertifiedLocalizedCIPInput.descriptorOfOrientedVolume? volume = some RS.S :=
      (CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?_eq_some_S_iff volume).mpr positive
    rw [core]
    simp [planarDescriptorOfDerivedTetrahedron?, volume, positive, RS.toPlanarDescriptor]
  · by_cases negative : volume < 0
    · have core : CertifiedLocalizedCIPInput.descriptorOfOrientedVolume? volume = some RS.R :=
        (CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?_eq_some_R_iff volume).mpr negative
      rw [core]
      simp [planarDescriptorOfDerivedTetrahedron?, volume, positive, negative, RS.toPlanarDescriptor]
    · have zero : volume = 0 := le_antisymm (not_lt.mp positive) (not_lt.mp negative)
      have core : CertifiedLocalizedCIPInput.descriptorOfOrientedVolume? volume = none :=
        (CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?_eq_none_iff volume).mpr zero
      rw [core]
      simp [planarDescriptorOfDerivedTetrahedron?, volume, positive, negative]

/-- The executable result is exactly the independent sign relation. -/
theorem planarDescriptorOfDerivedTetrahedron?_eq_some_iff
    (a b y z : CartesianPoint3) (descriptor : PlanarDescriptor) :
    planarDescriptorOfDerivedTetrahedron? a b y z = some descriptor ↔
      BlueBookP92.PlanarDerivedTetrahedron.RationalDescriptor a b y z descriptor := by
  let volume := CartesianPoint3.orientedVolume a b y z
  cases descriptor with
  | Rp =>
      unfold planarDescriptorOfDerivedTetrahedron?
        BlueBookP92.PlanarDerivedTetrahedron.RationalDescriptor
      by_cases positive : 0 < volume
      · have notNegative : ¬ volume < 0 := not_lt_of_ge positive.le
        simp [volume, positive, notNegative]
      · rw [if_neg positive]
        by_cases negative : volume < 0 <;> simp [volume, negative]
  | Sp =>
      unfold planarDescriptorOfDerivedTetrahedron?
        BlueBookP92.PlanarDerivedTetrahedron.RationalDescriptor
      by_cases positive : 0 < volume
      · simp [volume, positive]
      · rw [if_neg positive]
        by_cases negative : volume < 0 <;> simp [volume, positive, negative]

/-- Affinely degenerate source vertices produce no planar descriptor, and only those do. -/
theorem planarDescriptorOfDerivedTetrahedron?_eq_none_iff
    (a b y z : CartesianPoint3) :
    planarDescriptorOfDerivedTetrahedron? a b y z = none ↔
      CartesianPoint3.orientedVolume a b y z = 0 := by
  let volume := CartesianPoint3.orientedVolume a b y z
  by_cases positive : 0 < volume
  · simp [planarDescriptorOfDerivedTetrahedron?, volume, positive, ne_of_gt positive]
  · by_cases negative : volume < 0
    · simp [planarDescriptorOfDerivedTetrahedron?, volume, positive, negative,
        ne_of_lt negative]
    · have zero : volume = 0 := le_antisymm (not_lt.mp positive) (not_lt.mp negative)
      simp [planarDescriptorOfDerivedTetrahedron?, volume, zero]

/-- Exchanging the two in-plane priority vertices reverses the exact affine orientation. -/
theorem CartesianPoint3.orientedVolume_swap_first_second
    (a b y z : CartesianPoint3) :
    CartesianPoint3.orientedVolume b a y z =
      -CartesianPoint3.orientedVolume a b y z := by
  simp [CartesianPoint3.orientedVolume]
  ring

/-- Exchanging `a` and `b` reverses `Rₚ/Sₚ` in the independent semantics. -/
theorem planarDerivedTetrahedron_rationalDescriptor_swap_ab
    (a b y z : CartesianPoint3) (descriptor : PlanarDescriptor) :
    BlueBookP92.PlanarDerivedTetrahedron.RationalDescriptor
        b a y z descriptor ↔
      BlueBookP92.PlanarDerivedTetrahedron.RationalDescriptor
        a b y z descriptor.mirror := by
  cases descriptor with
  | Rp =>
      change CartesianPoint3.orientedVolume b a y z < 0 ↔
        0 < CartesianPoint3.orientedVolume a b y z
      rw [CartesianPoint3.orientedVolume_swap_first_second]
      simp
  | Sp =>
      change 0 < CartesianPoint3.orientedVolume b a y z ↔
        CartesianPoint3.orientedVolume a b y z < 0
      rw [CartesianPoint3.orientedVolume_swap_first_second]
      simp

/-- The executable conversion has the same odd-swap behavior. -/
theorem planarDescriptorOfDerivedTetrahedron?_swap_ab
    (a b y z : CartesianPoint3) :
    planarDescriptorOfDerivedTetrahedron? b a y z =
      (planarDescriptorOfDerivedTetrahedron? a b y z).map PlanarDescriptor.mirror := by
  unfold planarDescriptorOfDerivedTetrahedron?
  rw [CartesianPoint3.orientedVolume_swap_first_second]
  let volume := CartesianPoint3.orientedVolume a b y z
  by_cases positive : 0 < volume
  · have swappedNegative : -volume < 0 := neg_neg_of_pos positive
    have notSwappedPositive : ¬ 0 < -volume := not_lt_of_ge swappedNegative.le
    simp [volume, positive, swappedNegative, notSwappedPositive, PlanarDescriptor.mirror]
  · by_cases negative : volume < 0
    · have swappedPositive : 0 < -volume := neg_pos_of_neg negative
      simp [volume, positive, negative, swappedPositive, PlanarDescriptor.mirror]
    · have zero : volume = 0 := le_antisymm (not_lt.mp positive) (not_lt.mp negative)
      simp [volume, zero]

end TetraStereo.OneCenter
