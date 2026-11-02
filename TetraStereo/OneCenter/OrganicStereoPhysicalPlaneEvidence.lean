import TetraStereo.OneCenter.P93CyclicConfiguration
import TetraStereo.OneCenter.CIPFrontier
import TetraStereo.OneCenter.AuthoritativeChemicalInput

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open scoped RealInnerProductSpace InnerProductSpace

/-!
# Physical reference-plane evidence for the P-93 cyclic cis/trans observation

`P93CyclicConfiguration.BlueBookP93.Cyclic.RingPlaneObservation` records three bare `Prop`
fields.  This module adds a source-indexed, real-geometric evidence channel.  The generic
selected-support record stores:

* an explicit real affine reference plane, given by an origin and a *nonzero* oriented normal in
  `EuclideanSpace ℝ (Fin 3)`;
* a real conformation with exactly one point per atom of the full format-neutral
  `SemanticMolecule` (`Fin molecule.atomCount`);
* a chosen, duplicate-free selected ring support and two distinct substituent atoms, all as
  indices of the actual source atom list;
* the signed plane functional at every chosen atom, with strict above/below exclusion and an exact
  in-plane zero.

The generic selected-support record deliberately permits a support of any nonempty size.  The
source ring carrier is a separate, stronger object: `SourceClosedRing` requires at least three
distinct ring atoms and, for every cyclic consecutive pair, a source interaction of covalent or
aromatic kind whose participant list contains both source atom indices.
`PhysicalClosedRingObservation` bundles such a closed ring with source interaction witnesses
attaching each substituent to an actual ring position.  There is no ring-finding algorithm and no
claim that the supplied chosen support is the only or canonical ring.

Nothing is guessed.  In particular this module does **not** construct a mean or least-squares
plane, and it imposes no rationality restriction on the real coordinates.  A supplied reference
plane is a *chosen* datum: it is not part of the record that all ring atoms lie in it.  Actual
coplanarity of the chosen support is a separate, proof-carrying `CoplanarRingEvidence` object, so
a selected support outside the chosen plane is explicitly representable.

The ring side is obtained from the sign of the signed displacement.  The exact signed
characterisations are proved in both directions and are bridged to the existing
`RingSide`/`RelativeRingSide` vocabulary.  Reversing the normals negates both signed displacements:
the cis/trans comparison of the *signs* is invariant under simultaneous orientation reversal, while
the absolute side labels are reversed.  This is the formal statement that the relative cis/trans
observation does not determine absolute orientation.

The legacy `RingPlaneObservation` applicability fields are deliberately not instantiated by this
module.  A reference plane is never identified with a mean plane, and no reentrancy or
applicability proposition is fabricated from a sign.  The only exact vocabulary bridge claimed
here is the geometric one to `RingSide` and `RelativeRingSide`.
-/

/-! ## Ring side and relative cis/trans from real signed displacements -/

namespace BlueBookP93.Cyclic

/-- Classify a signed real displacement.  A nonzero displacement is classified by its sign; a zero
displacement is exactly the on-plane case.  This is a classification of supplied real data, not a
computation of any mean plane. -/
def RingSide.ofSigned (displacement : ℝ) : RingSide :=
  if displacement = 0 then .onMeanPlane
  else if 0 < displacement then .positive
  else .negative

@[simp] theorem RingSide.ofSigned_zero : RingSide.ofSigned 0 = .onMeanPlane := by
  unfold RingSide.ofSigned
  simp

theorem RingSide.ofSigned_pos {displacement : ℝ} (positive : 0 < displacement) :
    RingSide.ofSigned displacement = .positive := by
  unfold RingSide.ofSigned
  rw [if_neg (ne_of_gt positive), if_pos positive]

theorem RingSide.ofSigned_neg {displacement : ℝ} (negative : displacement < 0) :
    RingSide.ofSigned displacement = .negative := by
  unfold RingSide.ofSigned
  rw [if_neg (ne_of_lt negative), if_neg (not_lt.mpr (le_of_lt negative))]

/-- Exact positive classification in both directions. -/
theorem RingSide.ofSigned_eq_positive_iff (displacement : ℝ) :
    RingSide.ofSigned displacement = .positive ↔ 0 < displacement := by
  rcases lt_trichotomy displacement 0 with negative | zero | positive
  · rw [RingSide.ofSigned_neg negative]
    simp [not_lt.mpr (le_of_lt negative)]
  · subst displacement
    simp [RingSide.ofSigned_zero]
  · rw [RingSide.ofSigned_pos positive]
    simp [positive]

/-- Exact negative classification in both directions. -/
theorem RingSide.ofSigned_eq_negative_iff (displacement : ℝ) :
    RingSide.ofSigned displacement = .negative ↔ displacement < 0 := by
  rcases lt_trichotomy displacement 0 with negative | zero | positive
  · rw [RingSide.ofSigned_neg negative]
    simp [negative]
  · subst displacement
    simp [RingSide.ofSigned_zero]
  · rw [RingSide.ofSigned_pos positive]
    simp [not_lt.mpr (le_of_lt positive)]

/-- Exact on-plane classification in both directions. -/
theorem RingSide.ofSigned_eq_onMeanPlane_iff (displacement : ℝ) :
    RingSide.ofSigned displacement = .onMeanPlane ↔ displacement = 0 := by
  rcases lt_trichotomy displacement 0 with negative | zero | positive
  · rw [RingSide.ofSigned_neg negative]
    simp [ne_of_lt negative]
  · subst displacement
    simp [RingSide.ofSigned_zero]
  · rw [RingSide.ofSigned_pos positive]
    simp [ne_of_gt positive]

/-- A displacement is nonzero exactly when its ring side is not the on-plane side. -/
theorem RingSide.ofSigned_ne_onMeanPlane_iff (displacement : ℝ) :
    RingSide.ofSigned displacement ≠ .onMeanPlane ↔ displacement ≠ 0 :=
  not_congr (RingSide.ofSigned_eq_onMeanPlane_iff displacement)

/-- Orientation reversal of a ring side: positive and negative are exchanged, while the exact
on-plane case is fixed.  This is a relabelling of the *sign* channel only. -/
def RingSide.negate : RingSide → RingSide
  | .positive => .negative
  | .negative => .positive
  | .onMeanPlane => .onMeanPlane

@[simp] theorem RingSide.negate_negate (side : RingSide) :
    side.negate.negate = side := by
  cases side <;> rfl

/-- Negating the signed displacement is exactly the orientation reversal of its ring side. -/
@[simp] theorem RingSide.ofSigned_negate (displacement : ℝ) :
    RingSide.ofSigned (-displacement) = (RingSide.ofSigned displacement).negate := by
  rcases lt_trichotomy displacement 0 with negative | zero | positive
  · have positive' : 0 < -displacement := neg_pos.mpr negative
    rw [RingSide.ofSigned_pos positive', RingSide.ofSigned_neg negative]
    rfl
  · subst displacement
    simp [RingSide.ofSigned_zero, RingSide.negate]
  · have negative' : -displacement < 0 := neg_lt_zero.mpr positive
    rw [RingSide.ofSigned_neg negative', RingSide.ofSigned_pos positive]
    rfl

/-- A non-on-plane side is changed by orientation reversal. -/
theorem RingSide.negate_ne_self_of_ne_onMeanPlane {side : RingSide}
    (notOnPlane : side ≠ .onMeanPlane) : side.negate ≠ side := by
  cases side with
  | positive => simp [RingSide.negate]
  | negative => simp [RingSide.negate]
  | onMeanPlane => exact absurd rfl notOnPlane

/-- In particular, a nonzero signed displacement gives a side whose absolute label is reversed by
orientation reversal. -/
theorem RingSide.negate_ne_self_of_ne_zero {displacement : ℝ}
    (nonzero : displacement ≠ 0) :
    (RingSide.ofSigned displacement).negate ≠ RingSide.ofSigned displacement := by
  apply RingSide.negate_ne_self_of_ne_onMeanPlane
  intro onPlane
  exact nonzero ((RingSide.ofSigned_eq_onMeanPlane_iff displacement).mp onPlane)

/-- Exchange the two relative cis/trans descriptors. -/
def CisTrans.swap : CisTrans → CisTrans
  | .cis => .trans
  | .trans => .cis

@[simp] theorem CisTrans.swap_swap (descriptor : CisTrans) :
    descriptor.swap.swap = descriptor := by
  cases descriptor <;> rfl

/-- The relative cis/trans comparison induced by two signed displacements.  It is defined only when
both displacements are nonzero; a zero displacement contributes no cis/trans observation. -/
def relativeCisTransOfSigned (first second : ℝ) : Option CisTrans :=
  match RingSide.ofSigned first, RingSide.ofSigned second with
  | .positive, .positive => some .cis
  | .negative, .negative => some .cis
  | .positive, .negative => some .trans
  | .negative, .positive => some .trans
  | _, _ => none

/-- Exact bridge to the existing `RelativeRingSide` relation: the signed comparison returns exactly
the relative judgment of the two existing ring sides. -/
theorem relativeCisTransOfSigned_eq_some_iff (first second : ℝ) (descriptor : CisTrans) :
    relativeCisTransOfSigned first second = some descriptor ↔
      RelativeRingSide (RingSide.ofSigned first) (RingSide.ofSigned second) descriptor := by
  cases hFirst : RingSide.ofSigned first <;>
    cases hSecond : RingSide.ofSigned second <;>
    cases descriptor <;>
    simp [relativeCisTransOfSigned, hFirst, hSecond, RelativeRingSide]

/-- Exact characterisation of the existing `cis` relation in terms of its two ring-side
arguments. -/
theorem relativeRingSide_cis_iff (first second : RingSide) :
    RelativeRingSide first second .cis ↔
      (first = .positive ∧ second = .positive) ∨
        (first = .negative ∧ second = .negative) := by
  cases first <;> cases second <;> simp [RelativeRingSide]

/-- Exact characterisation of the existing `trans` relation in terms of its two ring-side
arguments. -/
theorem relativeRingSide_trans_iff (first second : RingSide) :
    RelativeRingSide first second .trans ↔
      (first = .positive ∧ second = .negative) ∨
        (first = .negative ∧ second = .positive) := by
  cases first <;> cases second <;> simp [RelativeRingSide]

/-- `cis` on the signed channel is exactly equality of the two signs. -/
theorem relativeCisTransOfSigned_eq_cis_iff (first second : ℝ) :
    relativeCisTransOfSigned first second = some .cis ↔
      (0 < first ∧ 0 < second) ∨ (first < 0 ∧ second < 0) := by
  rw [relativeCisTransOfSigned_eq_some_iff]
  constructor
  · intro relative
    rcases (relativeRingSide_cis_iff _ _).mp relative with
      ⟨positiveFirst, positiveSecond⟩ | ⟨negativeFirst, negativeSecond⟩
    · exact Or.inl
        ⟨(RingSide.ofSigned_eq_positive_iff first).mp positiveFirst,
          (RingSide.ofSigned_eq_positive_iff second).mp positiveSecond⟩
    · exact Or.inr
        ⟨(RingSide.ofSigned_eq_negative_iff first).mp negativeFirst,
          (RingSide.ofSigned_eq_negative_iff second).mp negativeSecond⟩
  · rintro (⟨positiveFirst, positiveSecond⟩ | ⟨negativeFirst, negativeSecond⟩)
    · exact (relativeRingSide_cis_iff _ _).mpr (Or.inl
        ⟨(RingSide.ofSigned_eq_positive_iff first).mpr positiveFirst,
          (RingSide.ofSigned_eq_positive_iff second).mpr positiveSecond⟩)
    · exact (relativeRingSide_cis_iff _ _).mpr (Or.inr
        ⟨(RingSide.ofSigned_eq_negative_iff first).mpr negativeFirst,
          (RingSide.ofSigned_eq_negative_iff second).mpr negativeSecond⟩)

/-- `trans` on the signed channel is exactly opposition of the two signs. -/
theorem relativeCisTransOfSigned_eq_trans_iff (first second : ℝ) :
    relativeCisTransOfSigned first second = some .trans ↔
      (0 < first ∧ second < 0) ∨ (first < 0 ∧ 0 < second) := by
  rw [relativeCisTransOfSigned_eq_some_iff]
  constructor
  · intro relative
    rcases (relativeRingSide_trans_iff _ _).mp relative with
      ⟨positiveFirst, negativeSecond⟩ | ⟨negativeFirst, positiveSecond⟩
    · exact Or.inl
        ⟨(RingSide.ofSigned_eq_positive_iff first).mp positiveFirst,
          (RingSide.ofSigned_eq_negative_iff second).mp negativeSecond⟩
    · exact Or.inr
        ⟨(RingSide.ofSigned_eq_negative_iff first).mp negativeFirst,
          (RingSide.ofSigned_eq_positive_iff second).mp positiveSecond⟩
  · rintro (⟨positiveFirst, negativeSecond⟩ | ⟨negativeFirst, positiveSecond⟩)
    · exact (relativeRingSide_trans_iff _ _).mpr (Or.inl
        ⟨(RingSide.ofSigned_eq_positive_iff first).mpr positiveFirst,
          (RingSide.ofSigned_eq_negative_iff second).mpr negativeSecond⟩)
    · exact (relativeRingSide_trans_iff _ _).mpr (Or.inr
        ⟨(RingSide.ofSigned_eq_negative_iff first).mpr negativeFirst,
          (RingSide.ofSigned_eq_positive_iff second).mpr positiveSecond⟩)

/-- No relative cis/trans observation exists when either signed displacement is zero. -/
theorem relativeCisTransOfSigned_eq_none_iff (first second : ℝ) :
    relativeCisTransOfSigned first second = none ↔
      RingSide.ofSigned first = .onMeanPlane ∨
        RingSide.ofSigned second = .onMeanPlane := by
  cases hFirst : RingSide.ofSigned first <;>
    cases hSecond : RingSide.ofSigned second <;>
    simp [relativeCisTransOfSigned, hFirst, hSecond]

/-- Simultaneous reversal of both normals negates both signed displacements and leaves the
relative cis/trans comparison unchanged.  Only relative orientation is observed. -/
theorem relativeCisTransOfSigned_neg_neg (first second : ℝ) :
    relativeCisTransOfSigned (-first) (-second) =
      relativeCisTransOfSigned first second := by
  cases hFirst : RingSide.ofSigned first <;>
    cases hSecond : RingSide.ofSigned second <;>
    simp [relativeCisTransOfSigned, RingSide.ofSigned_negate, hFirst, hSecond,
      RingSide.negate]

/-- Reversing only one normal swaps cis and trans.  Thus the relative observation is invariant
under simultaneous reversal, not under an independent choice of normal orientation. -/
theorem relativeCisTransOfSigned_neg_first (first second : ℝ) :
    relativeCisTransOfSigned (-first) second =
      (relativeCisTransOfSigned first second).map CisTrans.swap := by
  cases hFirst : RingSide.ofSigned first <;>
    cases hSecond : RingSide.ofSigned second <;>
    simp [relativeCisTransOfSigned, RingSide.ofSigned_negate, hFirst, hSecond,
      RingSide.negate, CisTrans.swap]

end BlueBookP93.Cyclic

open BlueBookP93.Cyclic

/-! ## Real affine reference planes and signed displacement -/

namespace PhysicalPlaneEvidence

/-- The real point type already used by `CIPFrontier.MolecularConformation`. -/
abbrev RealPoint := EuclideanSpace ℝ (Fin 3)

/-- An explicitly supplied real affine plane: an origin together with an oriented *nonzero* normal.
The normal is deliberately not normalized; only its sign structure, hence the oriented side
functional, is used. -/
structure ReferencePlane where
  origin : RealPoint
  normal : RealPoint
  normal_ne_zero : normal ≠ 0

namespace ReferencePlane

/-- Orientation reversal of the plane datum: the normal is negated.  The origin is unchanged. -/
def reverse (plane : ReferencePlane) : ReferencePlane where
  origin := plane.origin
  normal := -plane.normal
  normal_ne_zero := by
    intro negatedZero
    exact plane.normal_ne_zero (by simpa using congrArg Neg.neg negatedZero)

@[simp] theorem reverse_origin (plane : ReferencePlane) :
    plane.reverse.origin = plane.origin := rfl

@[simp] theorem reverse_normal (plane : ReferencePlane) :
    plane.reverse.normal = -plane.normal := rfl

@[simp] theorem reverse_reverse (plane : ReferencePlane) :
    plane.reverse.reverse = plane := by
  cases plane with
  | mk origin normal normal_ne_zero =>
      simp [ReferencePlane.reverse]

end ReferencePlane

namespace ReferencePlane

/-- The oriented signed displacement functional of a plane at a real point.  This is the inner
product with the supplied normal, not divided by the norm; its sign is the physical side datum. -/
def signedDisplacement (plane : ReferencePlane) (point : RealPoint) : ℝ :=
  ⟪point - plane.origin, plane.normal⟫_ℝ

/-- Strictly above the oriented plane. -/
def StrictlyAbove (plane : ReferencePlane) (point : RealPoint) : Prop :=
  0 < signedDisplacement plane point

/-- Strictly below the oriented plane. -/
def StrictlyBelow (plane : ReferencePlane) (point : RealPoint) : Prop :=
  signedDisplacement plane point < 0

/-- Exactly on the plane. -/
def InPlane (plane : ReferencePlane) (point : RealPoint) : Prop :=
  signedDisplacement plane point = 0

end ReferencePlane

open ReferencePlane

@[simp] theorem signedDisplacement_origin (plane : ReferencePlane) :
    signedDisplacement plane plane.origin = 0 := by
  simp [signedDisplacement]

/-- The point one normal step above the origin has displacement equal to the squared norm of the
normal. -/
@[simp] theorem signedDisplacement_origin_add_normal (plane : ReferencePlane) :
    signedDisplacement plane (plane.origin + plane.normal) =
      ⟪plane.normal, plane.normal⟫_ℝ := by
  unfold signedDisplacement
  rw [add_sub_cancel_left]

/-- The point one normal step below the origin has the negated squared norm as displacement. -/
@[simp] theorem signedDisplacement_origin_add_neg_normal (plane : ReferencePlane) :
    signedDisplacement plane (plane.origin + -plane.normal) =
      -⟪plane.normal, plane.normal⟫_ℝ := by
  unfold signedDisplacement
  rw [add_sub_cancel_left]
  simp

/-- Reversing the oriented normal negates the signed displacement at every point. -/
@[simp] theorem signedDisplacement_reverse (plane : ReferencePlane) (point : RealPoint) :
    signedDisplacement plane.reverse point = -signedDisplacement plane point := by
  simp [signedDisplacement, ReferencePlane.reverse]

/-- In-plane membership is unchanged by orientation reversal. -/
@[simp] theorem inPlane_reverse (plane : ReferencePlane) (point : RealPoint) :
    plane.reverse.InPlane point ↔ plane.InPlane point := by
  unfold InPlane
  rw [signedDisplacement_reverse]
  constructor <;> intro zero <;> linarith

/-- Above for the reversed plane is exactly below for the original plane. -/
@[simp] theorem strictlyAbove_reverse (plane : ReferencePlane) (point : RealPoint) :
    plane.reverse.StrictlyAbove point ↔ plane.StrictlyBelow point := by
  unfold StrictlyAbove StrictlyBelow
  rw [signedDisplacement_reverse]
  constructor <;> intro strict <;> linarith

/-- Below for the reversed plane is exactly above for the original plane. -/
@[simp] theorem strictlyBelow_reverse (plane : ReferencePlane) (point : RealPoint) :
    plane.reverse.StrictlyBelow point ↔ plane.StrictlyAbove point := by
  unfold StrictlyAbove StrictlyBelow
  rw [signedDisplacement_reverse]
  constructor <;> intro strict <;> linarith

/-- The three strict/on-plane relations exhaust the real line. -/
theorem above_or_inPlane_or_below (plane : ReferencePlane) (point : RealPoint) :
    plane.StrictlyAbove point ∨ plane.InPlane point ∨ plane.StrictlyBelow point := by
  unfold StrictlyAbove InPlane StrictlyBelow
  rcases lt_trichotomy (signedDisplacement plane point) 0 with negative | zero | positive
  · exact Or.inr (Or.inr negative)
  · exact Or.inr (Or.inl zero)
  · exact Or.inl positive

/-- Above and below are mutually exclusive. -/
theorem not_above_and_below (plane : ReferencePlane) (point : RealPoint) :
    ¬(plane.StrictlyAbove point ∧ plane.StrictlyBelow point) := by
  rintro ⟨above, below⟩
  unfold StrictlyAbove at above
  unfold StrictlyBelow at below
  linarith

/-- Above and in-plane are mutually exclusive. -/
theorem not_above_and_inPlane (plane : ReferencePlane) (point : RealPoint) :
    ¬(plane.StrictlyAbove point ∧ plane.InPlane point) := by
  rintro ⟨above, inPlane⟩
  unfold StrictlyAbove at above
  unfold InPlane at inPlane
  linarith

/-- Below and in-plane are mutually exclusive. -/
theorem not_below_and_inPlane (plane : ReferencePlane) (point : RealPoint) :
    ¬(plane.StrictlyBelow point ∧ plane.InPlane point) := by
  rintro ⟨below, inPlane⟩
  unfold StrictlyBelow at below
  unfold InPlane at inPlane
  linarith

/-- In-plane is exactly the failure of both strict alternatives. -/
theorem inPlane_iff_not_above_and_not_below (plane : ReferencePlane) (point : RealPoint) :
    plane.InPlane point ↔
      ¬ plane.StrictlyAbove point ∧ ¬ plane.StrictlyBelow point := by
  unfold InPlane StrictlyAbove StrictlyBelow
  constructor
  · intro zero
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨notAbove, notBelow⟩
    linarith

/-- No explicit reference plane contains every point: a point displaced by one normal step from the
origin is strictly on the normal side.  This is why support coplanarity cannot be assumed from the
chosen plane datum alone. -/
theorem exists_not_inPlane (plane : ReferencePlane) :
    ∃ point : RealPoint, ¬ plane.InPlane point := by
  refine ⟨plane.origin + plane.normal, ?_⟩
  intro inPlane
  have positive : 0 < ⟪plane.normal, plane.normal⟫_ℝ :=
    real_inner_self_pos.mpr plane.normal_ne_zero
  have zero : ⟪plane.normal, plane.normal⟫_ℝ = 0 := by
    simpa [InPlane, signedDisplacement] using inPlane
  linarith

/-! ## Full source-bound selected-support observation -/

/-- The atom-list position underlying a dependent index of the full semantic molecule. -/
def sourceIndex (molecule : SemanticMolecule) (index : Fin molecule.atomCount) :
    Fin molecule.atoms.length :=
  ⟨index.val, index.isLt⟩

/-- The source atom at a dependent index of the full semantic molecule.  No atom is invented or
dropped: the dependent index is exactly a position in the molecule's atom list. -/
def sourceAtomAt (molecule : SemanticMolecule) (index : Fin molecule.atomCount) : SemanticAtom :=
  molecule.atoms.get (sourceIndex molecule index)

@[simp] theorem sourceAtomAt_mem (molecule : SemanticMolecule)
    (index : Fin molecule.atomCount) :
    sourceAtomAt molecule index ∈ molecule.atoms := by
  simp [sourceAtomAt]

/-- Exact source lookup of the atom at a dependent index. -/
theorem sourceAtomAt_get? (molecule : SemanticMolecule)
    (index : Fin molecule.atomCount) :
    listGet? molecule.atoms (sourceIndex molecule index) =
      some (sourceAtomAt molecule index) := by
  rw [listGet?_eq_some_get molecule.atoms (sourceIndex molecule index)]
  simp [sourceAtomAt]

/-- Physical reference-plane evidence over the full format-neutral semantic molecule.

The record carries the actual real conformation, the actual chosen reference plane, and the actual
source atom indices of the chosen support and of the two substituents.  It never stores a desired
stereodescriptor, and no field is derived from a label that is supposed to be justified by the
geometry.  The chosen support is generic: it may be a singleton, and coplanarity is *not* a field.
Actual coplanarity must be supplied separately as `CoplanarRingEvidence`.  A genuine closed ring
carrier with at least three distinct atoms and source bond witnesses is the separate
`PhysicalClosedRingObservation`. -/
structure PhysicalRingPlaneObservation (molecule : SemanticMolecule) where
  /-- One real point for every atom of the full source molecule. -/
  conformation : MolecularConformation (Fin molecule.atomCount)
  /-- The explicitly supplied oriented reference plane. -/
  plane : ReferencePlane
  /-- The chosen selected support, as actual source atom indices. -/
  ringAtoms : List (Fin molecule.atomCount)
  /-- The chosen support has no repeated source atom. -/
  ringAtoms_nodup : ringAtoms.Nodup
  /-- The chosen support is nonempty. -/
  ringAtoms_nonempty : ringAtoms ≠ []
  /-- The first substituted position, as an actual source atom index. -/
  firstSubstituent : Fin molecule.atomCount
  /-- The second substituted position, as an actual source atom index. -/
  secondSubstituent : Fin molecule.atomCount
  /-- The two substituted positions are distinct. -/
  substituents_distinct : firstSubstituent ≠ secondSubstituent
  /-- The first substituted position is not one of the chosen support atoms. -/
  firstSubstituent_not_ring : firstSubstituent ∉ ringAtoms
  /-- The second substituted position is not one of the chosen support atoms. -/
  secondSubstituent_not_ring : secondSubstituent ∉ ringAtoms

namespace PhysicalRingPlaneObservation

variable {molecule : SemanticMolecule}

/-- The actual real position of a source atom in the supplied conformation. -/
def atomPosition (observation : PhysicalRingPlaneObservation molecule)
    (atom : Fin molecule.atomCount) : RealPoint :=
  observation.conformation atom

/-- The signed reference-plane displacement of a source atom. -/
def signedDisplacementOf (observation : PhysicalRingPlaneObservation molecule)
    (atom : Fin molecule.atomCount) : ℝ :=
  signedDisplacement observation.plane (observation.atomPosition atom)

/-- The signed displacement of the first substituted position. -/
def firstSignedDisplacement (observation : PhysicalRingPlaneObservation molecule) : ℝ :=
  observation.signedDisplacementOf observation.firstSubstituent

/-- The signed displacement of the second substituted position. -/
def secondSignedDisplacement (observation : PhysicalRingPlaneObservation molecule) : ℝ :=
  observation.signedDisplacementOf observation.secondSubstituent

/-- The existing ring side of a chosen source atom, obtained from the sign of its signed
displacement. -/
def atomSide (observation : PhysicalRingPlaneObservation molecule)
    (atom : Fin molecule.atomCount) : RingSide :=
  RingSide.ofSigned (observation.signedDisplacementOf atom)

/-- The existing ring side of the first substituted position. -/
def firstSide (observation : PhysicalRingPlaneObservation molecule) : RingSide :=
  observation.atomSide observation.firstSubstituent

/-- The existing ring side of the second substituted position. -/
def secondSide (observation : PhysicalRingPlaneObservation molecule) : RingSide :=
  observation.atomSide observation.secondSubstituent

/-- The relative cis/trans observation of the two substituted positions.  It is `none` exactly when
one of the signed displacements is zero, so no cis/trans claim is fabricated on a plane. -/
def relativeCisTrans (observation : PhysicalRingPlaneObservation molecule) : Option CisTrans :=
  BlueBookP93.Cyclic.relativeCisTransOfSigned
    observation.firstSignedDisplacement observation.secondSignedDisplacement

@[simp] theorem firstSide_eq_ofSigned (observation : PhysicalRingPlaneObservation molecule) :
    observation.firstSide = RingSide.ofSigned observation.firstSignedDisplacement := rfl

@[simp] theorem secondSide_eq_ofSigned (observation : PhysicalRingPlaneObservation molecule) :
    observation.secondSide = RingSide.ofSigned observation.secondSignedDisplacement := rfl

/-- The first side is positive exactly for a positive signed displacement. -/
theorem firstSide_eq_positive_iff (observation : PhysicalRingPlaneObservation molecule) :
    observation.firstSide = .positive ↔ 0 < observation.firstSignedDisplacement := by
  rw [firstSide_eq_ofSigned]
  exact RingSide.ofSigned_eq_positive_iff _

/-- The first side is negative exactly for a negative signed displacement. -/
theorem firstSide_eq_negative_iff (observation : PhysicalRingPlaneObservation molecule) :
    observation.firstSide = .negative ↔ observation.firstSignedDisplacement < 0 := by
  rw [firstSide_eq_ofSigned]
  exact RingSide.ofSigned_eq_negative_iff _

/-- The first side is on-plane exactly for a zero signed displacement. -/
theorem firstSide_eq_onMeanPlane_iff (observation : PhysicalRingPlaneObservation molecule) :
    observation.firstSide = .onMeanPlane ↔ observation.firstSignedDisplacement = 0 := by
  rw [firstSide_eq_ofSigned]
  exact RingSide.ofSigned_eq_onMeanPlane_iff _

/-- The second side is positive exactly for a positive signed displacement. -/
theorem secondSide_eq_positive_iff (observation : PhysicalRingPlaneObservation molecule) :
    observation.secondSide = .positive ↔ 0 < observation.secondSignedDisplacement := by
  rw [secondSide_eq_ofSigned]
  exact RingSide.ofSigned_eq_positive_iff _

/-- The second side is negative exactly for a negative signed displacement. -/
theorem secondSide_eq_negative_iff (observation : PhysicalRingPlaneObservation molecule) :
    observation.secondSide = .negative ↔ observation.secondSignedDisplacement < 0 := by
  rw [secondSide_eq_ofSigned]
  exact RingSide.ofSigned_eq_negative_iff _

/-- The second side is on-plane exactly for a zero signed displacement. -/
theorem secondSide_eq_onMeanPlane_iff (observation : PhysicalRingPlaneObservation molecule) :
    observation.secondSide = .onMeanPlane ↔ observation.secondSignedDisplacement = 0 := by
  rw [secondSide_eq_ofSigned]
  exact RingSide.ofSigned_eq_onMeanPlane_iff _

/-- A side is non-on-plane exactly when its signed displacement is nonzero. -/
theorem firstSide_ne_onMeanPlane_iff (observation : PhysicalRingPlaneObservation molecule) :
    observation.firstSide ≠ .onMeanPlane ↔ observation.firstSignedDisplacement ≠ 0 := by
  rw [firstSide_eq_ofSigned]
  exact RingSide.ofSigned_ne_onMeanPlane_iff _

/-- A side is non-on-plane exactly when its signed displacement is nonzero. -/
theorem secondSide_ne_onMeanPlane_iff (observation : PhysicalRingPlaneObservation molecule) :
    observation.secondSide ≠ .onMeanPlane ↔ observation.secondSignedDisplacement ≠ 0 := by
  rw [secondSide_eq_ofSigned]
  exact RingSide.ofSigned_ne_onMeanPlane_iff _

/-- Exact bridge to the existing `RelativeRingSide` relation. -/
theorem relativeCisTrans_eq_some_iff (observation : PhysicalRingPlaneObservation molecule)
    (descriptor : CisTrans) :
    observation.relativeCisTrans = some descriptor ↔
      RelativeRingSide observation.firstSide observation.secondSide descriptor := by
  unfold relativeCisTrans
  rw [BlueBookP93.Cyclic.relativeCisTransOfSigned_eq_some_iff]
  rfl

/-- Signed `cis` characterisation in both directions. -/
theorem relativeCisTrans_eq_cis_iff (observation : PhysicalRingPlaneObservation molecule) :
    observation.relativeCisTrans = some .cis ↔
      (0 < observation.firstSignedDisplacement ∧
          0 < observation.secondSignedDisplacement) ∨
        (observation.firstSignedDisplacement < 0 ∧
          observation.secondSignedDisplacement < 0) := by
  simpa [relativeCisTrans] using
    BlueBookP93.Cyclic.relativeCisTransOfSigned_eq_cis_iff
      observation.firstSignedDisplacement observation.secondSignedDisplacement

/-- Signed `trans` characterisation in both directions. -/
theorem relativeCisTrans_eq_trans_iff (observation : PhysicalRingPlaneObservation molecule) :
    observation.relativeCisTrans = some .trans ↔
      (0 < observation.firstSignedDisplacement ∧
          observation.secondSignedDisplacement < 0) ∨
        (observation.firstSignedDisplacement < 0 ∧
          0 < observation.secondSignedDisplacement) := by
  simpa [relativeCisTrans] using
    BlueBookP93.Cyclic.relativeCisTransOfSigned_eq_trans_iff
      observation.firstSignedDisplacement observation.secondSignedDisplacement

/-- The record's chosen support consists of actual source atoms. -/
theorem ringAtom_is_sourceAtom (observation : PhysicalRingPlaneObservation molecule)
    {atom : Fin molecule.atomCount} (_member : atom ∈ observation.ringAtoms) :
    sourceAtomAt molecule atom ∈ molecule.atoms :=
  sourceAtomAt_mem molecule atom

/-- The first substituted position is an actual source atom. -/
theorem firstSubstituent_is_sourceAtom
    (observation : PhysicalRingPlaneObservation molecule) :
    sourceAtomAt molecule observation.firstSubstituent ∈ molecule.atoms :=
  sourceAtomAt_mem molecule observation.firstSubstituent

/-- The second substituted position is an actual source atom. -/
theorem secondSubstituent_is_sourceAtom
    (observation : PhysicalRingPlaneObservation molecule) :
    sourceAtomAt molecule observation.secondSubstituent ∈ molecule.atoms :=
  sourceAtomAt_mem molecule observation.secondSubstituent

/-- The chosen support is coplanar in the supplied reference plane.  This predicate is not a field
of the observation; it is the content of separately supplied coplanarity evidence. -/
def RingSupportInPlane (observation : PhysicalRingPlaneObservation molecule) : Prop :=
  ∀ atom, atom ∈ observation.ringAtoms →
    observation.plane.InPlane (observation.atomPosition atom)

/-- Coplanarity is exactly vanishing of every chosen support displacement. -/
theorem ringSupportInPlane_iff_all_displacements_zero
    (observation : PhysicalRingPlaneObservation molecule) :
    observation.RingSupportInPlane ↔
      ∀ atom, atom ∈ observation.ringAtoms →
        observation.signedDisplacementOf atom = 0 := by
  unfold RingSupportInPlane InPlane signedDisplacementOf
  rfl

/-- A witness that the chosen support is not contained in the chosen reference plane.  This is a
statement about the chosen plane, not an intrinsic claim that the selected support is nonplanar in
every plane. -/
def RingSupportNotInChosenPlane (observation : PhysicalRingPlaneObservation molecule) : Prop :=
  ∃ atom, atom ∈ observation.ringAtoms ∧
    observation.signedDisplacementOf atom ≠ 0

/-- Failure of support coplanarity in the chosen plane is exactly the existence of a selected atom
outside that plane. -/
theorem not_ringSupportInPlane_iff (observation : PhysicalRingPlaneObservation molecule) :
    ¬ observation.RingSupportInPlane ↔ observation.RingSupportNotInChosenPlane := by
  classical
  unfold RingSupportInPlane RingSupportNotInChosenPlane
  constructor
  · intro notCoplanar
    push_neg at notCoplanar
    rcases notCoplanar with ⟨atom, member, notInPlane⟩
    refine ⟨atom, member, ?_⟩
    intro zero
    exact notInPlane (by simpa [InPlane, signedDisplacementOf, atomPosition] using zero)
  · rintro ⟨atom, member, nonzero⟩ coplanar
    exact nonzero
      (by simpa [InPlane, signedDisplacementOf, atomPosition] using coplanar atom member)

/-- Orientation reversal of the whole observation: only the oriented normal is negated.  All actual
coordinates, source indices and the chosen support are preserved. -/
def reversePlane (observation : PhysicalRingPlaneObservation molecule) :
    PhysicalRingPlaneObservation molecule :=
  { observation with plane := observation.plane.reverse }

@[simp] theorem reversePlane_plane (observation : PhysicalRingPlaneObservation molecule) :
    observation.reversePlane.plane = observation.plane.reverse := rfl

@[simp] theorem reversePlane_conformation
    (observation : PhysicalRingPlaneObservation molecule) :
    observation.reversePlane.conformation = observation.conformation := rfl

@[simp] theorem reversePlane_ringAtoms (observation : PhysicalRingPlaneObservation molecule) :
    observation.reversePlane.ringAtoms = observation.ringAtoms := rfl

@[simp] theorem reversePlane_firstSubstituent
    (observation : PhysicalRingPlaneObservation molecule) :
    observation.reversePlane.firstSubstituent = observation.firstSubstituent := rfl

@[simp] theorem reversePlane_secondSubstituent
    (observation : PhysicalRingPlaneObservation molecule) :
    observation.reversePlane.secondSubstituent = observation.secondSubstituent := rfl

@[simp] theorem firstSignedDisplacement_reversePlane
    (observation : PhysicalRingPlaneObservation molecule) :
    observation.reversePlane.firstSignedDisplacement =
      -observation.firstSignedDisplacement := by
  simp [firstSignedDisplacement, signedDisplacementOf, atomPosition, reversePlane]

@[simp] theorem secondSignedDisplacement_reversePlane
    (observation : PhysicalRingPlaneObservation molecule) :
    observation.reversePlane.secondSignedDisplacement =
      -observation.secondSignedDisplacement := by
  simp [secondSignedDisplacement, signedDisplacementOf, atomPosition, reversePlane]

/-- Orientation reversal negates the first ring side. -/
@[simp] theorem firstSide_reversePlane (observation : PhysicalRingPlaneObservation molecule) :
    observation.reversePlane.firstSide = observation.firstSide.negate := by
  simp [firstSide_eq_ofSigned, firstSignedDisplacement_reversePlane]

/-- Orientation reversal negates the second ring side. -/
@[simp] theorem secondSide_reversePlane (observation : PhysicalRingPlaneObservation molecule) :
    observation.reversePlane.secondSide = observation.secondSide.negate := by
  simp [secondSide_eq_ofSigned, secondSignedDisplacement_reversePlane]

/-- Simultaneous reversal of the oriented normal leaves the relative cis/trans observation
unchanged. -/
@[simp] theorem relativeCisTrans_reversePlane
    (observation : PhysicalRingPlaneObservation molecule) :
    observation.reversePlane.relativeCisTrans = observation.relativeCisTrans := by
  unfold relativeCisTrans
  rw [firstSignedDisplacement_reversePlane, secondSignedDisplacement_reversePlane]
  exact BlueBookP93.Cyclic.relativeCisTransOfSigned_neg_neg _ _

/-- Support coplanarity is unchanged by orientation reversal. -/
@[simp] theorem ringSupportInPlane_reversePlane
    (observation : PhysicalRingPlaneObservation molecule) :
    observation.reversePlane.RingSupportInPlane ↔ observation.RingSupportInPlane := by
  constructor
  · rintro reversed atom member
    have member' : atom ∈ observation.reversePlane.ringAtoms := by
      simpa using member
    have reversedAt := reversed atom member'
    have inPlane : observation.plane.reverse.InPlane (observation.atomPosition atom) := by
      simpa [PhysicalRingPlaneObservation.atomPosition] using reversedAt
    exact (inPlane_reverse observation.plane (observation.atomPosition atom)).mp inPlane
  · rintro original atom member
    have originalAt : observation.plane.InPlane (observation.atomPosition atom) :=
      original atom member
    show observation.plane.reverse.InPlane (observation.atomPosition atom)
    exact (inPlane_reverse observation.plane (observation.atomPosition atom)).mpr originalAt

/-- The explicit loss of absolute orientation: if both substituted positions are strictly off the
plane, orientation reversal changes both absolute side labels while preserving the relative
cis/trans observation. -/
theorem planeReversal_flips_absolute_preserves_relative
    (observation : PhysicalRingPlaneObservation molecule)
    (firstNonzero : observation.firstSignedDisplacement ≠ 0)
    (secondNonzero : observation.secondSignedDisplacement ≠ 0) :
    observation.reversePlane.firstSide = observation.firstSide.negate ∧
      observation.reversePlane.secondSide = observation.secondSide.negate ∧
      observation.reversePlane.firstSide ≠ observation.firstSide ∧
      observation.reversePlane.secondSide ≠ observation.secondSide ∧
      observation.reversePlane.relativeCisTrans = observation.relativeCisTrans := by
  have firstFlipped : observation.reversePlane.firstSide ≠ observation.firstSide := by
    rw [firstSide_reversePlane]
    exact RingSide.negate_ne_self_of_ne_onMeanPlane
      ((observation.firstSide_ne_onMeanPlane_iff).mpr firstNonzero)
  have secondFlipped : observation.reversePlane.secondSide ≠ observation.secondSide := by
    rw [secondSide_reversePlane]
    exact RingSide.negate_ne_self_of_ne_onMeanPlane
      ((observation.secondSide_ne_onMeanPlane_iff).mpr secondNonzero)
  exact ⟨firstSide_reversePlane observation, secondSide_reversePlane observation,
    firstFlipped, secondFlipped, relativeCisTrans_reversePlane observation⟩

end PhysicalRingPlaneObservation

/-! ## Source closed-ring carrier and substituent attachments -/

/-- Covalent or aromatic source interactions qualify as ring bonds.  Other interaction kinds are
kept outside the ring-bond channel rather than silently coerced into it. -/
def IsRingBond : SemanticInteractionKind → Prop
  | .unspecifiedCovalent => True
  | .covalent _ => True
  | .aromatic => True
  | _ => False

@[simp] theorem isRingBond_unspecifiedCovalent :
    IsRingBond .unspecifiedCovalent := trivial

@[simp] theorem isRingBond_covalent (bondOrder : ℕ) :
    IsRingBond (.covalent bondOrder) := trivial

@[simp] theorem isRingBond_aromatic :
    IsRingBond .aromatic := trivial

/-- The exact *binary* participant condition for a source interaction: the participant list is
`[left, right]` or `[right, left]`.  A multicenter or delocalized hyperedge with a longer
participant list does not satisfy this condition, so it cannot be flattened into a ring edge. -/
def HasBinaryParticipants (left right : ℕ) (interaction : SemanticInteraction) : Prop :=
  interaction.participants = [left, right] ∨
    interaction.participants = [right, left]

namespace HasBinaryParticipants

variable {left right : ℕ} {interaction : SemanticInteraction}

/-- A binary interaction contains its left endpoint. -/
theorem left_mem (binary : HasBinaryParticipants left right interaction) :
    left ∈ interaction.participants := by
  rcases binary with equal | equal <;> rw [equal] <;> simp

/-- A binary interaction contains its right endpoint. -/
theorem right_mem (binary : HasBinaryParticipants left right interaction) :
    right ∈ interaction.participants := by
  rcases binary with equal | equal <;> rw [equal] <;> simp

/-- A binary interaction has exactly two participants.  This is the formal exclusion of
hyperedge flattening. -/
theorem length_eq_two (binary : HasBinaryParticipants left right interaction) :
    interaction.participants.length = 2 := by
  rcases binary with equal | equal <;> rw [equal] <;> rfl

/-- The participant list itself, retained as an explicit datum. -/
theorem participants_eq (binary : HasBinaryParticipants left right interaction) :
    interaction.participants = [left, right] ∨
      interaction.participants = [right, left] :=
  binary

end HasBinaryParticipants

/-- Cyclic successor on a nonempty finite type of positions. -/
def cycleSucc {n : ℕ} (positive : 0 < n) (index : Fin n) : Fin n :=
  ⟨(index.val + 1) % n, Nat.mod_lt _ positive⟩

/-- The cyclic successor of a position is different from that position when there are at least
two positions.  This guarantees that a closed-ring edge does not degenerate into a self-loop. -/
theorem cycleSucc_ne {n : ℕ} (two : 2 ≤ n) (positive : 0 < n) (index : Fin n) :
    cycleSucc positive index ≠ index := by
  intro equal
  have valueEqual : (index.val + 1) % n = index.val := congrArg Fin.val equal
  have indexLt : index.val < n := index.isLt
  have succLe : index.val + 1 ≤ n := Nat.succ_le_of_lt indexLt
  rcases Nat.lt_or_ge (index.val + 1) n with below | above
  · rw [Nat.mod_eq_of_lt below] at valueEqual
    omega
  · have eqn : index.val + 1 = n := Nat.le_antisymm succLe above
    rw [eqn, Nat.mod_self] at valueEqual
    omega

/-- A source closed ring: at least three distinct ring atoms, and for every cyclic consecutive
pair of ring positions an actual *binary* source covalent or aromatic interaction whose
participant list is exactly the two atom indices.  The binary condition, rather than mere
co-membership, prevents a multicenter hyperedge from being flattened into a ring edge.
The ring is a chosen source-bound certificate; no fitting algorithm is provided or claimed. -/
structure SourceClosedRing (molecule : SemanticMolecule) where
  ringAtoms : List (Fin molecule.atomCount)
  length_ge_three : 3 ≤ ringAtoms.length
  nodup : ringAtoms.Nodup
  bond : ∀ position : Fin ringAtoms.length,
    ∃ interaction : SemanticInteraction,
      interaction ∈ molecule.interactions ∧
        IsRingBond interaction.kind ∧
          HasBinaryParticipants
            (ringAtoms.get position).val
            (ringAtoms.get
              (cycleSucc
                (Nat.lt_of_lt_of_le (by decide : 0 < 3) length_ge_three)
                position)).val
            interaction

namespace SourceClosedRing

variable {molecule : SemanticMolecule}

/-- A closed ring has a positive number of ring positions. -/
theorem length_positive (ring : SourceClosedRing molecule) : 0 < ring.ringAtoms.length :=
  Nat.lt_of_lt_of_le (by decide : 0 < 3) ring.length_ge_three

/-- The chosen ring carrier has at least three distinct source atoms. -/
theorem three_le_length (ring : SourceClosedRing molecule) : 3 ≤ ring.ringAtoms.length :=
  ring.length_ge_three

/-- Every cyclic consecutive pair is joined by an actual binary source ring bond interaction. -/
theorem bond_exists (ring : SourceClosedRing molecule) (position : Fin ring.ringAtoms.length) :
    ∃ interaction : SemanticInteraction,
      interaction ∈ molecule.interactions ∧
        IsRingBond interaction.kind ∧
          HasBinaryParticipants
            (ring.ringAtoms.get position).val
            (ring.ringAtoms.get (cycleSucc ring.length_positive position)).val
            interaction :=
  ring.bond position

/-- Every ring edge has an endpoint in the source interaction's participant list. -/
theorem bond_left_mem (ring : SourceClosedRing molecule) (position : Fin ring.ringAtoms.length) :
    ∃ interaction : SemanticInteraction,
      interaction ∈ molecule.interactions ∧
        IsRingBond interaction.kind ∧
          (ring.ringAtoms.get position).val ∈ interaction.participants := by
  obtain ⟨interaction, mem, kind, binary⟩ := ring.bond position
  exact ⟨interaction, mem, kind, binary.left_mem⟩

/-- Every ring edge has its cyclic successor in the source interaction's participant list. -/
theorem bond_right_mem (ring : SourceClosedRing molecule) (position : Fin ring.ringAtoms.length) :
    ∃ interaction : SemanticInteraction,
      interaction ∈ molecule.interactions ∧
        IsRingBond interaction.kind ∧
          (ring.ringAtoms.get (cycleSucc ring.length_positive position)).val ∈
            interaction.participants := by
  obtain ⟨interaction, mem, kind, binary⟩ := ring.bond position
  exact ⟨interaction, mem, kind, binary.right_mem⟩

/-- Every ring edge is witnessed by an interaction with exactly two participants, so a longer
multicenter hyperedge cannot witness it. -/
theorem bond_length_eq_two (ring : SourceClosedRing molecule)
    (position : Fin ring.ringAtoms.length) :
    ∃ interaction : SemanticInteraction,
      interaction ∈ molecule.interactions ∧
        IsRingBond interaction.kind ∧ interaction.participants.length = 2 := by
  obtain ⟨interaction, mem, kind, binary⟩ := ring.bond position
  exact ⟨interaction, mem, kind, binary.length_eq_two⟩

/-- The cyclic successor of a ring position is never that same position, so no ring edge is a
self-loop. -/
theorem bond_endpoints_distinct (ring : SourceClosedRing molecule)
    (position : Fin ring.ringAtoms.length) :
    ring.ringAtoms.get (cycleSucc ring.length_positive position) ≠
      ring.ringAtoms.get position := by
  intro equal
  have indexEqual : cycleSucc ring.length_positive position = position :=
    ring.nodup.get_inj_iff.mp equal
  exact cycleSucc_ne (Nat.le_trans (by decide : 2 ≤ 3) ring.length_ge_three)
    ring.length_positive position indexEqual

end SourceClosedRing

/-- A source-bound substituent attachment: a ring position drawn from the actual ring atom list,
and a source covalent or aromatic interaction containing both the ring position's and the
substituent's source atom indices. -/
structure SourceRingSubstituentAttachment (molecule : SemanticMolecule)
    (ringAtoms : List (Fin molecule.atomCount))
    (substituent : Fin molecule.atomCount) where
  ringPosition : Fin molecule.atomCount
  ringPosition_mem : ringPosition ∈ ringAtoms
  substituent_not_ring : substituent ∉ ringAtoms
  interaction : SemanticInteraction
  interaction_mem : interaction ∈ molecule.interactions
  interaction_isRingBond : IsRingBond interaction.kind
  binaryParticipants : HasBinaryParticipants ringPosition.val substituent.val interaction

/-- A generic selected-support plane observation together with a source closed-ring carrier and
actual source interaction witnesses attaching each substituent to a ring position. -/
structure PhysicalClosedRingObservation (molecule : SemanticMolecule) where
  observation : PhysicalRingPlaneObservation molecule
  ring : SourceClosedRing molecule
  ring_matches : ring.ringAtoms = observation.ringAtoms
  firstAttachment :
    SourceRingSubstituentAttachment molecule ring.ringAtoms observation.firstSubstituent
  secondAttachment :
    SourceRingSubstituentAttachment molecule ring.ringAtoms observation.secondSubstituent

namespace PhysicalClosedRingObservation

variable {molecule : SemanticMolecule}

/-- The first side is the generic observation's first side. -/
def firstSide (observation : PhysicalClosedRingObservation molecule) : RingSide :=
  observation.observation.firstSide

/-- The second side is the generic observation's second side. -/
def secondSide (observation : PhysicalClosedRingObservation molecule) : RingSide :=
  observation.observation.secondSide

/-- The relative cis/trans observation of the closed-ring record. -/
def relativeCisTrans (observation : PhysicalClosedRingObservation molecule) : Option CisTrans :=
  observation.observation.relativeCisTrans

@[simp] theorem firstSide_def (observation : PhysicalClosedRingObservation molecule) :
    observation.firstSide = observation.observation.firstSide := rfl

@[simp] theorem secondSide_def (observation : PhysicalClosedRingObservation molecule) :
    observation.secondSide = observation.observation.secondSide := rfl

@[simp] theorem relativeCisTrans_def (observation : PhysicalClosedRingObservation molecule) :
    observation.relativeCisTrans = observation.observation.relativeCisTrans := rfl

/-- Exact bridge to the existing `RelativeRingSide` relation for the closed-ring record. -/
theorem relativeCisTrans_eq_some_iff (observation : PhysicalClosedRingObservation molecule)
    (descriptor : CisTrans) :
    observation.relativeCisTrans = some descriptor ↔
      RelativeRingSide observation.firstSide observation.secondSide descriptor := by
  simpa [relativeCisTrans, firstSide, secondSide] using
    PhysicalRingPlaneObservation.relativeCisTrans_eq_some_iff observation.observation descriptor

/-- Coplanarity of the closed ring's own atom list in the chosen plane. -/
def RingSupportInPlane (observation : PhysicalClosedRingObservation molecule) : Prop :=
  observation.observation.RingSupportInPlane

@[simp] theorem ringSupportInPlane_def (observation : PhysicalClosedRingObservation molecule) :
    observation.RingSupportInPlane = observation.observation.RingSupportInPlane := rfl

/-- Coplanarity over the closed ring's own atom list, connected to the generic support. -/
theorem ringSupportInPlane_iff_ring (observation : PhysicalClosedRingObservation molecule) :
    observation.RingSupportInPlane ↔
      ∀ atom, atom ∈ observation.ring.ringAtoms →
        observation.observation.plane.InPlane (observation.observation.atomPosition atom) := by
  unfold RingSupportInPlane PhysicalRingPlaneObservation.RingSupportInPlane
  rw [observation.ring_matches]

/-- The closed ring has at least three distinct atoms. -/
theorem ring_length_ge_three (observation : PhysicalClosedRingObservation molecule) :
    3 ≤ observation.ring.ringAtoms.length :=
  observation.ring.length_ge_three

/-- The closed ring's atom list is duplicate-free. -/
theorem ring_nodup (observation : PhysicalClosedRingObservation molecule) :
    observation.ring.ringAtoms.Nodup :=
  observation.ring.nodup

/-- The first attachment's ring position is an actual ring atom. -/
theorem firstAttachment_ringPosition_mem
    (observation : PhysicalClosedRingObservation molecule) :
    observation.firstAttachment.ringPosition ∈ observation.ring.ringAtoms :=
  observation.firstAttachment.ringPosition_mem

/-- The first attachment's ring position is an actual selected-support atom of the generic
observation. -/
theorem firstAttachment_ringPosition_mem_observation
    (observation : PhysicalClosedRingObservation molecule) :
    observation.firstAttachment.ringPosition ∈ observation.observation.ringAtoms := by
  rw [← observation.ring_matches]
  exact observation.firstAttachment.ringPosition_mem

/-- The first attachment is a source interaction. -/
theorem firstAttachment_interaction_mem
    (observation : PhysicalClosedRingObservation molecule) :
    observation.firstAttachment.interaction ∈ molecule.interactions :=
  observation.firstAttachment.interaction_mem

/-- The first attachment is a covalent or aromatic ring bond. -/
theorem firstAttachment_interaction_isRingBond
    (observation : PhysicalClosedRingObservation molecule) :
    IsRingBond observation.firstAttachment.interaction.kind :=
  observation.firstAttachment.interaction_isRingBond

/-- The first attachment is witnessed by an actual binary participant list. -/
theorem firstAttachment_binaryParticipants
    (observation : PhysicalClosedRingObservation molecule) :
    HasBinaryParticipants observation.firstAttachment.ringPosition.val
      observation.observation.firstSubstituent.val
      observation.firstAttachment.interaction :=
  observation.firstAttachment.binaryParticipants

/-- The first attachment interaction has exactly two participants. -/
theorem firstAttachment_participants_length
    (observation : PhysicalClosedRingObservation molecule) :
    observation.firstAttachment.interaction.participants.length = 2 :=
  (observation.firstAttachment_binaryParticipants).length_eq_two

/-- The ring position participates in the first attachment interaction. -/
theorem firstAttachment_ringParticipates
    (observation : PhysicalClosedRingObservation molecule) :
    observation.firstAttachment.ringPosition.val ∈
      observation.firstAttachment.interaction.participants :=
  (observation.firstAttachment.binaryParticipants).left_mem

/-- The first substituent participates in the first attachment interaction. -/
theorem firstAttachment_substituentParticipates
    (observation : PhysicalClosedRingObservation molecule) :
    observation.observation.firstSubstituent.val ∈
      observation.firstAttachment.interaction.participants :=
  (observation.firstAttachment.binaryParticipants).right_mem

/-- The first substituent is not a ring atom. -/
theorem firstAttachment_substituent_not_ring
    (observation : PhysicalClosedRingObservation molecule) :
    observation.observation.firstSubstituent ∉ observation.ring.ringAtoms :=
  observation.firstAttachment.substituent_not_ring

/-- The second attachment's ring position is an actual ring atom. -/
theorem secondAttachment_ringPosition_mem
    (observation : PhysicalClosedRingObservation molecule) :
    observation.secondAttachment.ringPosition ∈ observation.ring.ringAtoms :=
  observation.secondAttachment.ringPosition_mem

/-- The second attachment's ring position is an actual selected-support atom of the generic
observation. -/
theorem secondAttachment_ringPosition_mem_observation
    (observation : PhysicalClosedRingObservation molecule) :
    observation.secondAttachment.ringPosition ∈ observation.observation.ringAtoms := by
  rw [← observation.ring_matches]
  exact observation.secondAttachment.ringPosition_mem

/-- The second attachment is a source interaction. -/
theorem secondAttachment_interaction_mem
    (observation : PhysicalClosedRingObservation molecule) :
    observation.secondAttachment.interaction ∈ molecule.interactions :=
  observation.secondAttachment.interaction_mem

/-- The second attachment is a covalent or aromatic ring bond. -/
theorem secondAttachment_interaction_isRingBond
    (observation : PhysicalClosedRingObservation molecule) :
    IsRingBond observation.secondAttachment.interaction.kind :=
  observation.secondAttachment.interaction_isRingBond

/-- The second attachment is witnessed by an actual binary participant list. -/
theorem secondAttachment_binaryParticipants
    (observation : PhysicalClosedRingObservation molecule) :
    HasBinaryParticipants observation.secondAttachment.ringPosition.val
      observation.observation.secondSubstituent.val
      observation.secondAttachment.interaction :=
  observation.secondAttachment.binaryParticipants

/-- The second attachment interaction has exactly two participants. -/
theorem secondAttachment_participants_length
    (observation : PhysicalClosedRingObservation molecule) :
    observation.secondAttachment.interaction.participants.length = 2 :=
  (observation.secondAttachment_binaryParticipants).length_eq_two

/-- The ring position participates in the second attachment interaction. -/
theorem secondAttachment_ringParticipates
    (observation : PhysicalClosedRingObservation molecule) :
    observation.secondAttachment.ringPosition.val ∈
      observation.secondAttachment.interaction.participants :=
  (observation.secondAttachment.binaryParticipants).left_mem

/-- The second substituent participates in the second attachment interaction. -/
theorem secondAttachment_substituentParticipates
    (observation : PhysicalClosedRingObservation molecule) :
    observation.observation.secondSubstituent.val ∈
      observation.secondAttachment.interaction.participants :=
  (observation.secondAttachment.binaryParticipants).right_mem

/-- The second substituent is not a ring atom. -/
theorem secondAttachment_substituent_not_ring
    (observation : PhysicalClosedRingObservation molecule) :
    observation.observation.secondSubstituent ∉ observation.ring.ringAtoms :=
  observation.secondAttachment.substituent_not_ring

/-- Orientation reversal of the closed-ring record changes only the oriented normal.  The source
ring and both attachment witnesses are preserved. -/
def reversePlane (observation : PhysicalClosedRingObservation molecule) :
    PhysicalClosedRingObservation molecule where
  observation := observation.observation.reversePlane
  ring := observation.ring
  ring_matches := by simpa using observation.ring_matches
  firstAttachment := observation.firstAttachment
  secondAttachment := observation.secondAttachment

@[simp] theorem reversePlane_observation
    (observation : PhysicalClosedRingObservation molecule) :
    observation.reversePlane.observation = observation.observation.reversePlane := rfl

@[simp] theorem firstSide_reversePlane
    (observation : PhysicalClosedRingObservation molecule) :
    observation.reversePlane.firstSide = observation.firstSide.negate := by
  simp [firstSide]

@[simp] theorem secondSide_reversePlane
    (observation : PhysicalClosedRingObservation molecule) :
    observation.reversePlane.secondSide = observation.secondSide.negate := by
  simp [secondSide]

/-- Orientation reversal preserves the relative cis/trans observation of a closed-ring record. -/
@[simp] theorem relativeCisTrans_reversePlane
    (observation : PhysicalClosedRingObservation molecule) :
    observation.reversePlane.relativeCisTrans = observation.relativeCisTrans := by
  simp [relativeCisTrans]

/-- Orientation reversal preserves coplanarity of the closed ring. -/
@[simp] theorem ringSupportInPlane_reversePlane
    (observation : PhysicalClosedRingObservation molecule) :
    observation.reversePlane.RingSupportInPlane ↔ observation.RingSupportInPlane := by
  simp [RingSupportInPlane]

end PhysicalClosedRingObservation

/-- Actual proof that the chosen support of an observation is contained in its chosen reference
plane.  This is deliberately a separate object: the chosen plane datum alone does not assert that
any selected atom is on it. -/
structure CoplanarRingEvidence {molecule : SemanticMolecule}
    (observation : PhysicalRingPlaneObservation molecule) where
  inPlane : observation.RingSupportInPlane

namespace CoplanarRingEvidence

variable {molecule : SemanticMolecule} {observation : PhysicalRingPlaneObservation molecule}

/-- Coplanarity evidence is exactly the observation's support coplanarity predicate. -/
theorem ringSupportInPlane (evidence : CoplanarRingEvidence observation) :
    observation.RingSupportInPlane :=
  evidence.inPlane

/-- Coplanarity survives orientation reversal of the reference plane. -/
theorem reversePlane (evidence : CoplanarRingEvidence observation) :
    observation.reversePlane.RingSupportInPlane :=
  (PhysicalRingPlaneObservation.ringSupportInPlane_reversePlane observation).mpr evidence.inPlane

end CoplanarRingEvidence

/-! ## Deliberate non-instantiation of the legacy applicability record

`P93CyclicConfiguration.BlueBookP93.Cyclic.RingPlaneObservation` stores the three bare `Prop`
fields `usesMeanPlane`, `firstSubstitutedPositionNotReentrant` and
`secondSubstitutedPositionNotReentrant`.  This module deliberately supplies **no adapter** from
the physical record to that structure.  A chosen reference plane is not a mean plane, and the
non-reentrancy facts are independent chemical conditions that the signed geometry neither
constructs nor refutes.  The exact vocabulary bridge claimed by this module is the geometric one
to `RingSide` and `RelativeRingSide` (`relativeCisTrans_eq_some_iff`), together with the exact
signed characterisations above.  Any future adapter must justify the three legacy propositions
from independently formalised chemical data. -/









/-- A concrete nonzero reference plane: the `xy`-plane through the origin with normal the third
standard basis vector.  It is used only to instantiate the non-vacuity witnesses. -/
def standardPlane : ReferencePlane where
  origin := 0
  normal := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  normal_ne_zero := by
    intro zero
    have coefficientZero : (1 : ℝ) = 0 :=
      (EuclideanSpace.single_eq_zero_iff).mp zero
    norm_num at coefficientZero

namespace Examples

/-- Carbon, only as a source atom identity for the witness molecules. -/
def carbon : PeriodicElement where
  atomicNumber := 6
  positive := by decide
  atMost118 := by decide

/-- A carbon atom with ordinary isotopic composition. -/
def carbonAtom : SemanticAtom := { element := carbon }

/-- A three-atom molecule used for the generic selected-support witnesses.  It intentionally has no
interactions: these witnesses concern the generic support geometry, not a chemical ring. -/
def threeAtomMolecule : SemanticMolecule :=
  { atoms := [carbonAtom, carbonAtom, carbonAtom], interactions := [] }

@[simp] theorem threeAtomMolecule_atomCount : threeAtomMolecule.atomCount = 3 := rfl

/-- The chosen selected-support index `0`. -/
def atom0 : Fin threeAtomMolecule.atomCount := ⟨0, by decide⟩

/-- The first substituted atom index `1`. -/
def atom1 : Fin threeAtomMolecule.atomCount := ⟨1, by decide⟩

/-- The second substituted atom index `2`. -/
def atom2 : Fin threeAtomMolecule.atomCount := ⟨2, by decide⟩

/-- A conformation assigning explicit real points to the three source atoms. -/
def conformation (ringPosition firstPosition secondPosition : RealPoint) :
    MolecularConformation (Fin threeAtomMolecule.atomCount) :=
  fun index =>
    if index.val = 0 then ringPosition
    else if index.val = 1 then firstPosition
    else secondPosition

@[simp] theorem conformation_atom0
    (ringPosition firstPosition secondPosition : RealPoint) :
    conformation ringPosition firstPosition secondPosition atom0 = ringPosition := by
  simp [conformation, atom0]

@[simp] theorem conformation_atom1
    (ringPosition firstPosition secondPosition : RealPoint) :
    conformation ringPosition firstPosition secondPosition atom1 = firstPosition := by
  simp [conformation, atom1]

@[simp] theorem conformation_atom2
    (ringPosition firstPosition secondPosition : RealPoint) :
    conformation ringPosition firstPosition secondPosition atom2 = secondPosition := by
  simp [conformation, atom2]

/-- A generic selected-support witness whose selected atom is the plane origin and whose
substituents lie one normal step above and below it.  The selected support is coplanar and the
relative observation is `trans` for every nonzero reference plane. -/
def coplanarObservation (plane : ReferencePlane) :
    PhysicalRingPlaneObservation threeAtomMolecule where
  conformation :=
    conformation plane.origin (plane.origin + plane.normal)
      (plane.origin + -plane.normal)
  plane := plane
  ringAtoms := [atom0]
  ringAtoms_nodup := by decide
  ringAtoms_nonempty := by decide
  firstSubstituent := atom1
  secondSubstituent := atom2
  substituents_distinct := by decide
  firstSubstituent_not_ring := by decide
  secondSubstituent_not_ring := by decide

@[simp] theorem coplanarObservation_firstSignedDisplacement (plane : ReferencePlane) :
    (coplanarObservation plane).firstSignedDisplacement =
      ⟪plane.normal, plane.normal⟫_ℝ := by
  simp [PhysicalRingPlaneObservation.firstSignedDisplacement,
    PhysicalRingPlaneObservation.signedDisplacementOf,
    PhysicalRingPlaneObservation.atomPosition, coplanarObservation]

@[simp] theorem coplanarObservation_secondSignedDisplacement (plane : ReferencePlane) :
    (coplanarObservation plane).secondSignedDisplacement =
      -⟪plane.normal, plane.normal⟫_ℝ := by
  simp [PhysicalRingPlaneObservation.secondSignedDisplacement,
    PhysicalRingPlaneObservation.signedDisplacementOf,
    PhysicalRingPlaneObservation.atomPosition, coplanarObservation]

/-- The selected support of the generic coplanar witness is actually coplanar. -/
@[simp] theorem coplanarObservation_ringSupportInPlane (plane : ReferencePlane) :
    (coplanarObservation plane).RingSupportInPlane := by
  intro atom member
  rcases List.mem_singleton.mp member with rfl
  simp [PhysicalRingPlaneObservation.atomPosition, InPlane, coplanarObservation]

/-- The first side of the generic coplanar witness is positive. -/
@[simp] theorem coplanarObservation_firstSide (plane : ReferencePlane) :
    (coplanarObservation plane).firstSide = .positive := by
  rw [PhysicalRingPlaneObservation.firstSide_eq_ofSigned,
    coplanarObservation_firstSignedDisplacement]
  exact RingSide.ofSigned_pos (real_inner_self_pos.mpr plane.normal_ne_zero)

/-- The second side of the generic coplanar witness is negative. -/
@[simp] theorem coplanarObservation_secondSide (plane : ReferencePlane) :
    (coplanarObservation plane).secondSide = .negative := by
  have positive : 0 < ⟪plane.normal, plane.normal⟫_ℝ :=
    real_inner_self_pos.mpr plane.normal_ne_zero
  rw [PhysicalRingPlaneObservation.secondSide_eq_ofSigned,
    coplanarObservation_secondSignedDisplacement]
  exact RingSide.ofSigned_neg (by linarith)

/-- The relative observation of the generic coplanar witness is `trans`. -/
@[simp] theorem coplanarObservation_relativeCisTrans (plane : ReferencePlane) :
    (coplanarObservation plane).relativeCisTrans = some .trans := by
  have positive : 0 < ⟪plane.normal, plane.normal⟫_ℝ :=
    real_inner_self_pos.mpr plane.normal_ne_zero
  unfold PhysicalRingPlaneObservation.relativeCisTrans
  rw [coplanarObservation_firstSignedDisplacement,
    coplanarObservation_secondSignedDisplacement]
  unfold BlueBookP93.Cyclic.relativeCisTransOfSigned
  rw [RingSide.ofSigned_pos positive,
    RingSide.ofSigned_neg (by linarith)]

/-- The generic coplanar witness satisfies the legacy `RelativeRingSide.trans` relation exactly. -/
theorem coplanarObservation_relativeRingSide (plane : ReferencePlane) :
    RelativeRingSide (coplanarObservation plane).firstSide
      (coplanarObservation plane).secondSide .trans := by
  rw [coplanarObservation_firstSide, coplanarObservation_secondSide]
  exact trivial

/-- The generic coplanar witness has actual coplanarity evidence. -/
def coplanarEvidence (plane : ReferencePlane) :
    CoplanarRingEvidence (coplanarObservation plane) :=
  ⟨coplanarObservation_ringSupportInPlane plane⟩

/-- A generic selected-support witness with one selected atom one normal step off the chosen plane
origin.  This demonstrates only that the chosen reference plane need not contain a selected atom;
it makes no intrinsic nonplanarity claim about the selected support. -/
def ringAtomOffChosenPlaneObservation (plane : ReferencePlane) :
    PhysicalRingPlaneObservation threeAtomMolecule where
  conformation :=
    conformation (plane.origin + plane.normal) plane.origin
      (plane.origin + -plane.normal)
  plane := plane
  ringAtoms := [atom0]
  ringAtoms_nodup := by decide
  ringAtoms_nonempty := by decide
  firstSubstituent := atom1
  secondSubstituent := atom2
  substituents_distinct := by decide
  firstSubstituent_not_ring := by decide
  secondSubstituent_not_ring := by decide

/-- The chosen reference plane of this generic witness does not contain its selected atom.  This is
the formal refusal to assume that a selected support is coplanar with every chosen plane; it is not
a claim that the support is intrinsically nonplanar. -/
theorem ringAtomOffChosenPlaneObservation_not_ringSupportInPlane
    (plane : ReferencePlane) :
    ¬ (ringAtomOffChosenPlaneObservation plane).RingSupportInPlane := by
  intro coplanar
  have member : atom0 ∈ (ringAtomOffChosenPlaneObservation plane).ringAtoms := by
    show atom0 ∈ [atom0]
    exact List.mem_singleton.mpr rfl
  have zero : signedDisplacement plane (plane.origin + plane.normal) = 0 := by
    simpa [PhysicalRingPlaneObservation.RingSupportInPlane,
      PhysicalRingPlaneObservation.atomPosition, InPlane, ringAtomOffChosenPlaneObservation]
      using coplanar atom0 member
  rw [signedDisplacement_origin_add_normal] at zero
  exact (real_inner_self_pos.mpr plane.normal_ne_zero).ne' zero

/-- There is a generic physical observation whose selected support is coplanar. -/
theorem exists_observation_ringSupportInPlane :
    ∃ (molecule : SemanticMolecule) (observation : PhysicalRingPlaneObservation molecule),
      observation.RingSupportInPlane :=
  ⟨threeAtomMolecule, coplanarObservation standardPlane,
    coplanarObservation_ringSupportInPlane standardPlane⟩

/-- There is a generic physical observation whose chosen reference plane does not contain its
selected atom. -/
theorem exists_observation_ringAtomOffChosenPlane :
    ∃ (molecule : SemanticMolecule) (observation : PhysicalRingPlaneObservation molecule),
      ¬ observation.RingSupportInPlane :=
  ⟨threeAtomMolecule, ringAtomOffChosenPlaneObservation standardPlane,
    ringAtomOffChosenPlaneObservation_not_ringSupportInPlane standardPlane⟩

/-- On the generic coplanar witness, orientation reversal changes both absolute side labels while
keeping the relative `trans` observation. -/
theorem coplanarObservation_orientationReversal (plane : ReferencePlane) :
    (coplanarObservation plane).reversePlane.firstSide = .negative ∧
      (coplanarObservation plane).reversePlane.secondSide = .positive ∧
      (coplanarObservation plane).reversePlane.relativeCisTrans =
        (coplanarObservation plane).relativeCisTrans := by
  constructor
  · rw [PhysicalRingPlaneObservation.firstSide_reversePlane,
      coplanarObservation_firstSide]
    rfl
  constructor
  · rw [PhysicalRingPlaneObservation.secondSide_reversePlane,
      coplanarObservation_secondSide]
    rfl
  · exact PhysicalRingPlaneObservation.relativeCisTrans_reversePlane _

/-! ### Closed-ring five-atom witness -/

/-- A five-atom molecule with a three-membered source ring `0-1-2-0` and two source substituent
bonds `0-3` and `1-4`.  All interactions are explicitly covalent. -/
def fiveAtomMolecule : SemanticMolecule :=
  { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom]
    interactions :=
      [ { participants := [0, 1], kind := .unspecifiedCovalent },
        { participants := [1, 2], kind := .unspecifiedCovalent },
        { participants := [2, 0], kind := .unspecifiedCovalent },
        { participants := [0, 3], kind := .unspecifiedCovalent },
        { participants := [1, 4], kind := .unspecifiedCovalent } ] }

@[simp] theorem fiveAtomMolecule_atomCount : fiveAtomMolecule.atomCount = 5 := rfl

/-- Source atom `0`, a ring position. -/
def fiveAtom0 : Fin fiveAtomMolecule.atomCount := ⟨0, by decide⟩

/-- Source atom `1`, a ring position. -/
def fiveAtom1 : Fin fiveAtomMolecule.atomCount := ⟨1, by decide⟩

/-- Source atom `2`, a ring position. -/
def fiveAtom2 : Fin fiveAtomMolecule.atomCount := ⟨2, by decide⟩

/-- Source atom `3`, the first substituent. -/
def fiveAtom3 : Fin fiveAtomMolecule.atomCount := ⟨3, by decide⟩

/-- Source atom `4`, the second substituent. -/
def fiveAtom4 : Fin fiveAtomMolecule.atomCount := ⟨4, by decide⟩

/-- The first selected ring point: the origin of the standard plane. -/
def fiveRingPoint0 : RealPoint := 0

/-- The second selected ring point: the first standard basis vector. -/
def fiveRingPoint1 : RealPoint := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- The third selected ring point: the second standard basis vector. -/
def fiveRingPoint2 : RealPoint := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)

/-- The first substituent point: one normal step above the standard plane. -/
def fiveAbovePoint : RealPoint := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)

/-- The second substituent point: one normal step below the standard plane. -/
def fiveBelowPoint : RealPoint := EuclideanSpace.single (2 : Fin 3) (-1 : ℝ)

/-- A conformation with five explicit atom positions, one for each source atom. -/
def fiveConformation (ring0 ring1 ring2 above below : RealPoint) :
    MolecularConformation (Fin fiveAtomMolecule.atomCount) :=
  fun index =>
    if index.val = 0 then ring0
    else if index.val = 1 then ring1
    else if index.val = 2 then ring2
    else if index.val = 3 then above
    else below

@[simp] theorem fiveConformation_atom0
    (ring0 ring1 ring2 above below : RealPoint) :
    fiveConformation ring0 ring1 ring2 above below fiveAtom0 = ring0 := by
  simp [fiveConformation, fiveAtom0]

@[simp] theorem fiveConformation_atom1
    (ring0 ring1 ring2 above below : RealPoint) :
    fiveConformation ring0 ring1 ring2 above below fiveAtom1 = ring1 := by
  simp [fiveConformation, fiveAtom1]

@[simp] theorem fiveConformation_atom2
    (ring0 ring1 ring2 above below : RealPoint) :
    fiveConformation ring0 ring1 ring2 above below fiveAtom2 = ring2 := by
  simp [fiveConformation, fiveAtom2]

@[simp] theorem fiveConformation_atom3
    (ring0 ring1 ring2 above below : RealPoint) :
    fiveConformation ring0 ring1 ring2 above below fiveAtom3 = above := by
  simp [fiveConformation, fiveAtom3]

@[simp] theorem fiveConformation_atom4
    (ring0 ring1 ring2 above below : RealPoint) :
    fiveConformation ring0 ring1 ring2 above below fiveAtom4 = below := by
  simp [fiveConformation, fiveAtom4]

/-- The concrete closed-ring observation: the ring `0-1-2-0` is carried by the three distinct,
noncollinear points `0`, `e₀`, `e₁` of the standard plane; the first substituent `3` is one
normal step above the plane, and the second substituent `4` is one normal step below it.
Every ring edge and both substituent attachments carry actual binary source interaction
witnesses. -/
def closedRingObservation : PhysicalClosedRingObservation fiveAtomMolecule where
  observation :=
    { conformation :=
        fiveConformation fiveRingPoint0 fiveRingPoint1 fiveRingPoint2
          fiveAbovePoint fiveBelowPoint
      plane := standardPlane
      ringAtoms := [fiveAtom0, fiveAtom1, fiveAtom2]
      ringAtoms_nodup := by decide
      ringAtoms_nonempty := by decide
      firstSubstituent := fiveAtom3
      secondSubstituent := fiveAtom4
      substituents_distinct := by decide
      firstSubstituent_not_ring := by decide
      secondSubstituent_not_ring := by decide }
  ring :=
    { ringAtoms := [fiveAtom0, fiveAtom1, fiveAtom2]
      length_ge_three := by decide
      nodup := by decide
      bond := by
        intro position
        fin_cases position
        · exact ⟨⟨[0, 1], .unspecifiedCovalent⟩, by decide, trivial,
            by unfold HasBinaryParticipants; decide⟩
        · exact ⟨⟨[1, 2], .unspecifiedCovalent⟩, by decide, trivial,
            by unfold HasBinaryParticipants; decide⟩
        · exact ⟨⟨[2, 0], .unspecifiedCovalent⟩, by decide, trivial,
            by unfold HasBinaryParticipants; decide⟩ }
  ring_matches := rfl
  firstAttachment :=
    { ringPosition := fiveAtom0
      ringPosition_mem := by decide
      substituent_not_ring := by
        show fiveAtom3 ∉
          ([fiveAtom0, fiveAtom1, fiveAtom2] : List (Fin fiveAtomMolecule.atomCount))
        decide
      interaction := ⟨[0, 3], .unspecifiedCovalent⟩
      interaction_mem := by decide
      interaction_isRingBond := trivial
      binaryParticipants := by
        unfold HasBinaryParticipants
        decide }
  secondAttachment :=
    { ringPosition := fiveAtom1
      ringPosition_mem := by decide
      substituent_not_ring := by
        show fiveAtom4 ∉
          ([fiveAtom0, fiveAtom1, fiveAtom2] : List (Fin fiveAtomMolecule.atomCount))
        decide
      interaction := ⟨[1, 4], .unspecifiedCovalent⟩
      interaction_mem := by decide
      interaction_isRingBond := trivial
      binaryParticipants := by
        unfold HasBinaryParticipants
        decide }

@[simp] theorem closedRingObservation_plane :
    closedRingObservation.observation.plane = standardPlane := rfl

@[simp] theorem closedRingObservation_conformation :
    closedRingObservation.observation.conformation =
      fiveConformation fiveRingPoint0 fiveRingPoint1 fiveRingPoint2
        fiveAbovePoint fiveBelowPoint := rfl

@[simp] theorem closedRingObservation_ringAtoms :
    closedRingObservation.observation.ringAtoms =
      [fiveAtom0, fiveAtom1, fiveAtom2] := rfl

@[simp] theorem closedRingObservation_firstSubstituent :
    closedRingObservation.observation.firstSubstituent = fiveAtom3 := rfl

@[simp] theorem closedRingObservation_secondSubstituent :
    closedRingObservation.observation.secondSubstituent = fiveAtom4 := rfl

@[simp] theorem closedRingObservation_ring_ringAtoms :
    closedRingObservation.ring.ringAtoms =
      [fiveAtom0, fiveAtom1, fiveAtom2] := rfl

@[simp] theorem closedRingObservation_firstSignedDisplacement :
    closedRingObservation.observation.firstSignedDisplacement =
      ⟪standardPlane.normal, standardPlane.normal⟫_ℝ := by
  simp [PhysicalRingPlaneObservation.firstSignedDisplacement,
    PhysicalRingPlaneObservation.signedDisplacementOf,
    PhysicalRingPlaneObservation.atomPosition,
    closedRingObservation_plane, closedRingObservation_conformation,
    closedRingObservation_firstSubstituent, fiveConformation, fiveAtom3,
    fiveAbovePoint, standardPlane, signedDisplacement]

@[simp] theorem closedRingObservation_secondSignedDisplacement :
    closedRingObservation.observation.secondSignedDisplacement =
      -⟪standardPlane.normal, standardPlane.normal⟫_ℝ := by
  have innerValue : ⟪(EuclideanSpace.single (2 : Fin 3) (-1 : ℝ)),
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))⟫_ℝ = -1 := by
    rw [EuclideanSpace.inner_single_right]
    simp [EuclideanSpace.single_apply]
  simp [PhysicalRingPlaneObservation.secondSignedDisplacement,
    PhysicalRingPlaneObservation.signedDisplacementOf,
    PhysicalRingPlaneObservation.atomPosition,
    closedRingObservation_plane, closedRingObservation_conformation,
    closedRingObservation_secondSubstituent, fiveConformation, fiveAtom4,
    fiveBelowPoint, standardPlane, signedDisplacement]
  exact innerValue

/-- A concrete noncollinearity certificate for an ordered triple of points: the first two points
are distinct, and the third does not lie on the line through them. -/
def RingPointsNoncollinear (first second third : RealPoint) : Prop :=
  second ≠ first ∧ ¬ ∃ scale : ℝ, third - first = scale • (second - first)

/-- The three selected ring points are distinct and noncollinear. -/
theorem fiveRingPoints_noncollinear :
    RingPointsNoncollinear fiveRingPoint0 fiveRingPoint1 fiveRingPoint2 := by
  constructor
  · intro equal
    have zero : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) = 0 := by
      rw [fiveRingPoint0, fiveRingPoint1] at equal
      exact equal
    have coefficient : (1 : ℝ) = 0 := (EuclideanSpace.single_eq_zero_iff).mp zero
    norm_num at coefficient
  · rintro ⟨scale, equal⟩
    have coordinate := congrArg (fun point : RealPoint => point (1 : Fin 3)) equal
    simp [fiveRingPoint0, fiveRingPoint1, fiveRingPoint2,
      EuclideanSpace.single_apply] at coordinate

/-- The actual ring atom positions of the closed-ring witness are noncollinear. -/
theorem closedRingObservation_ringPoints_noncollinear :
    RingPointsNoncollinear
      (closedRingObservation.observation.atomPosition fiveAtom0)
      (closedRingObservation.observation.atomPosition fiveAtom1)
      (closedRingObservation.observation.atomPosition fiveAtom2) := by
  simpa [PhysicalRingPlaneObservation.atomPosition, closedRingObservation_conformation,
    fiveConformation, fiveAtom0, fiveAtom1, fiveAtom2] using fiveRingPoints_noncollinear

/-- The three ring positions lie in the chosen standard plane. -/
@[simp] theorem closedRingObservation_ringSupportInPlane :
    closedRingObservation.RingSupportInPlane := by
  intro atom member
  have member' : atom ∈ [fiveAtom0, fiveAtom1, fiveAtom2] := by
    simpa using member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member'
  rcases member' with rfl | rfl | rfl
  · simp [PhysicalRingPlaneObservation.atomPosition, closedRingObservation_conformation,
      InPlane, signedDisplacement, fiveConformation, fiveAtom0, fiveRingPoint0,
      standardPlane]
  · simp [PhysicalRingPlaneObservation.atomPosition, closedRingObservation_conformation,
      InPlane, signedDisplacement, fiveConformation, fiveAtom1, fiveRingPoint1,
      standardPlane, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  · simp [PhysicalRingPlaneObservation.atomPosition, closedRingObservation_conformation,
      InPlane, signedDisplacement, fiveConformation, fiveAtom2, fiveRingPoint2,
      standardPlane, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

/-- The first side of the closed-ring witness is positive. -/
@[simp] theorem closedRingObservation_firstSide :
    closedRingObservation.firstSide = .positive := by
  unfold PhysicalClosedRingObservation.firstSide
  rw [PhysicalRingPlaneObservation.firstSide_eq_ofSigned,
    closedRingObservation_firstSignedDisplacement]
  exact RingSide.ofSigned_pos (real_inner_self_pos.mpr standardPlane.normal_ne_zero)

/-- The second side of the closed-ring witness is negative. -/
@[simp] theorem closedRingObservation_secondSide :
    closedRingObservation.secondSide = .negative := by
  have positive : 0 < ⟪standardPlane.normal, standardPlane.normal⟫_ℝ :=
    real_inner_self_pos.mpr standardPlane.normal_ne_zero
  unfold PhysicalClosedRingObservation.secondSide
  rw [PhysicalRingPlaneObservation.secondSide_eq_ofSigned,
    closedRingObservation_secondSignedDisplacement]
  exact RingSide.ofSigned_neg (by linarith)

/-- The relative observation of the closed-ring witness is `trans`. -/
@[simp] theorem closedRingObservation_relativeCisTrans :
    closedRingObservation.relativeCisTrans = some .trans := by
  have positive : 0 < ⟪standardPlane.normal, standardPlane.normal⟫_ℝ :=
    real_inner_self_pos.mpr standardPlane.normal_ne_zero
  unfold PhysicalClosedRingObservation.relativeCisTrans
  unfold PhysicalRingPlaneObservation.relativeCisTrans
  rw [closedRingObservation_firstSignedDisplacement,
    closedRingObservation_secondSignedDisplacement]
  unfold BlueBookP93.Cyclic.relativeCisTransOfSigned
  rw [RingSide.ofSigned_pos positive,
    RingSide.ofSigned_neg (by linarith)]

/-- The closed-ring witness satisfies the existing `RelativeRingSide.trans` relation exactly. -/
theorem closedRingObservation_relativeRingSide :
    RelativeRingSide closedRingObservation.firstSide
      closedRingObservation.secondSide .trans := by
  rw [closedRingObservation_firstSide, closedRingObservation_secondSide]
  exact trivial

/-- The closed-ring witness supplies actual coplanarity evidence for its generic observation. -/
def closedRingObservationEvidence :
    CoplanarRingEvidence closedRingObservation.observation :=
  ⟨closedRingObservation_ringSupportInPlane⟩

/-- On the closed-ring witness, orientation reversal changes both absolute side labels while
keeping the relative `trans` observation. -/
theorem closedRingObservation_orientationReversal :
    closedRingObservation.reversePlane.firstSide = .negative ∧
      closedRingObservation.reversePlane.secondSide = .positive ∧
      closedRingObservation.reversePlane.relativeCisTrans =
        closedRingObservation.relativeCisTrans := by
  constructor
  · rw [PhysicalClosedRingObservation.firstSide_reversePlane,
      closedRingObservation_firstSide]
    rfl
  constructor
  · rw [PhysicalClosedRingObservation.secondSide_reversePlane,
      closedRingObservation_secondSide]
    rfl
  · exact PhysicalClosedRingObservation.relativeCisTrans_reversePlane _

/-- A genuine closed-ring physical observation exists, with a coplanar three-atom ring and both
substituent attachments backed by source interactions. -/
theorem exists_closedRingObservation_with_coplanar_ring :
    ∃ (molecule : SemanticMolecule) (observation : PhysicalClosedRingObservation molecule),
      observation.RingSupportInPlane :=
  ⟨fiveAtomMolecule, closedRingObservation, closedRingObservation_ringSupportInPlane⟩

/-- The concrete closed-ring witness has noncollinear ring positions. -/
theorem exists_closedRingObservation_with_noncollinear_ring :
    ∃ (molecule : SemanticMolecule) (observation : PhysicalClosedRingObservation molecule)
      (first second third : Fin molecule.atomCount),
      RingPointsNoncollinear (observation.observation.atomPosition first)
        (observation.observation.atomPosition second)
        (observation.observation.atomPosition third) :=
  ⟨fiveAtomMolecule, closedRingObservation, fiveAtom0, fiveAtom1, fiveAtom2,
    closedRingObservation_ringPoints_noncollinear⟩

/-- A genuine closed-ring physical observation exists whose relative observation is `trans`. -/
theorem exists_closedRingObservation_trans :
    ∃ (molecule : SemanticMolecule) (observation : PhysicalClosedRingObservation molecule),
      observation.relativeCisTrans = some .trans :=
  ⟨fiveAtomMolecule, closedRingObservation, closedRingObservation_relativeCisTrans⟩

/-- The concrete closed-ring witness has three distinct ring atoms, a duplicate-free ring list,
binary source interactions for every ring edge, and binary source interaction witnesses for both
substituent attachments. -/
theorem closedRingObservation_source_carrier :
    3 ≤ closedRingObservation.ring.ringAtoms.length ∧
      closedRingObservation.ring.ringAtoms.Nodup ∧
      (∀ position : Fin closedRingObservation.ring.ringAtoms.length,
        ∃ interaction : SemanticInteraction,
          interaction ∈ fiveAtomMolecule.interactions ∧
            IsRingBond interaction.kind ∧
              HasBinaryParticipants
                (closedRingObservation.ring.ringAtoms.get position).val
                (closedRingObservation.ring.ringAtoms.get
                  (cycleSucc
                    (Nat.lt_of_lt_of_le (by decide : 0 < 3)
                      closedRingObservation.ring.length_ge_three)
                    position)).val
                interaction) ∧
      closedRingObservation.firstAttachment.interaction ∈
        fiveAtomMolecule.interactions ∧
      closedRingObservation.firstAttachment.ringPosition ∈
        closedRingObservation.ring.ringAtoms ∧
      HasBinaryParticipants
        closedRingObservation.firstAttachment.ringPosition.val
        closedRingObservation.observation.firstSubstituent.val
        closedRingObservation.firstAttachment.interaction ∧
      closedRingObservation.firstAttachment.interaction.participants.length = 2 ∧
      closedRingObservation.secondAttachment.interaction ∈
        fiveAtomMolecule.interactions ∧
      closedRingObservation.secondAttachment.ringPosition ∈
        closedRingObservation.ring.ringAtoms ∧
      HasBinaryParticipants
        closedRingObservation.secondAttachment.ringPosition.val
        closedRingObservation.observation.secondSubstituent.val
        closedRingObservation.secondAttachment.interaction ∧
      closedRingObservation.secondAttachment.interaction.participants.length = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PhysicalClosedRingObservation.ring_length_ge_three _
  · exact PhysicalClosedRingObservation.ring_nodup _
  · exact closedRingObservation.ring.bond
  · exact PhysicalClosedRingObservation.firstAttachment_interaction_mem _
  · exact PhysicalClosedRingObservation.firstAttachment_ringPosition_mem _
  · exact PhysicalClosedRingObservation.firstAttachment_binaryParticipants _
  · exact PhysicalClosedRingObservation.firstAttachment_participants_length _
  · exact PhysicalClosedRingObservation.secondAttachment_interaction_mem _
  · exact PhysicalClosedRingObservation.secondAttachment_ringPosition_mem _
  · exact PhysicalClosedRingObservation.secondAttachment_binaryParticipants _
  · exact PhysicalClosedRingObservation.secondAttachment_participants_length _

end Examples

end PhysicalPlaneEvidence

end

end TetraStereo.OneCenter
