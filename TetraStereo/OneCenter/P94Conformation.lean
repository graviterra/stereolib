import TetraStereo.OneCenter.Basic
import Mathlib.NumberTheory.Real.Irrational

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent IUPAC P-94 conformation semantics

This module transcribes the mathematical cores of P-94.1--P-94.3 without calling the production
analyzer.  Exact real degree values are used at the authority boundary; restricting the carrier
to rationals would exclude ordinary geometries with irrational torsion angles.  The conformational
angle classification is a relation, not a tie-broken function: the source's inclusive “within
±30°” language makes boundary angles members of both adjacent named regions.
-/

namespace BlueBookP94

/-! ## P-94.1: conformation -/

/-- Equivalence closure of rotations about formally single bonds. -/
inductive InterconvertibleBySingleBondRotations {State : Type*}
    (singleBondRotation : State → State → Prop) : State → State → Prop where
  | refl (state) : InterconvertibleBySingleBondRotations singleBondRotation state state
  | step {first second} (rotation : singleBondRotation first second) :
      InterconvertibleBySingleBondRotations singleBondRotation first second
  | symm {first second}
      (path : InterconvertibleBySingleBondRotations singleBondRotation first second) :
      InterconvertibleBySingleBondRotations singleBondRotation second first
  | trans {first second third}
      (firstSecond : InterconvertibleBySingleBondRotations singleBondRotation first second)
      (secondThird : InterconvertibleBySingleBondRotations singleBondRotation second third) :
      InterconvertibleBySingleBondRotations singleBondRotation first third

namespace InterconvertibleBySingleBondRotations

variable {State : Type*} {rotation : State → State → Prop}

theorem reflexive : Reflexive (InterconvertibleBySingleBondRotations rotation) :=
  .refl

theorem symmetric : Symmetric (InterconvertibleBySingleBondRotations rotation) :=
  fun _ _ path => .symm path

theorem transitive : Transitive (InterconvertibleBySingleBondRotations rotation) :=
  fun _ _ _ firstSecond secondThird => .trans firstSecond secondThird

end InterconvertibleBySingleBondRotations

/-- Two distinct spatial arrangements are conformers when formally-single-bond rotations
interconvert them. -/
def AreConformers {State : Type*} (singleBondRotation : State → State → Prop)
    (first second : State) : Prop :=
  first ≠ second ∧ InterconvertibleBySingleBondRotations singleBondRotation first second

/-! ## P-94.2: torsion angle -/

/-- Principal signed torsion angle in degrees.  The viewing orientation and selected front/rear
atoms are part of the observation that constructs this value. -/
structure TorsionAngle where
  degrees : ℝ
  lowerBound : (-180 : ℝ) ≤ degrees
  upperBound : degrees ≤ 180

namespace TorsionAngle

@[ext] theorem ext {left right : TorsionAngle} (degrees : left.degrees = right.degrees) :
    left = right := by
  cases left
  cases right
  simp_all

def magnitude (angle : TorsionAngle) : ℝ := |angle.degrees|

theorem magnitude_nonnegative (angle : TorsionAngle) : 0 ≤ angle.magnitude :=
  abs_nonneg _

theorem magnitude_le_180 (angle : TorsionAngle) : angle.magnitude ≤ 180 := by
  exact abs_le.mpr ⟨angle.lowerBound, angle.upperBound⟩

def ofReal (degrees : ℝ) (lowerBound : (-180 : ℝ) ≤ degrees)
    (upperBound : degrees ≤ 180) : TorsionAngle :=
  { degrees := degrees, lowerBound := lowerBound, upperBound := upperBound }

@[simp] theorem ofReal_degrees (degrees : ℝ) (lowerBound : (-180 : ℝ) ≤ degrees)
    (upperBound : degrees ≤ 180) :
    (ofReal degrees lowerBound upperBound).degrees = degrees :=
  rfl

theorem every_bounded_real_representable (degrees : ℝ)
    (lowerBound : (-180 : ℝ) ≤ degrees) (upperBound : degrees ≤ 180) :
    ∃ angle : TorsionAngle, angle.degrees = degrees :=
  ⟨ofReal degrees lowerBound upperBound, rfl⟩

def ofRat (degrees : ℚ) (lowerBound : (-180 : ℚ) ≤ degrees)
    (upperBound : degrees ≤ 180) : TorsionAngle :=
  ofReal (degrees : ℝ) (by exact_mod_cast lowerBound) (by exact_mod_cast upperBound)

@[simp] theorem ofRat_degrees (degrees : ℚ) (lowerBound : (-180 : ℚ) ≤ degrees)
    (upperBound : degrees ≤ 180) :
    (ofRat degrees lowerBound upperBound).degrees = (degrees : ℝ) :=
  rfl

/-- A concrete angle that the former rational carrier could not represent. -/
noncomputable def sqrtTwo : TorsionAngle :=
  ofReal (Real.sqrt 2) (by
    have nonnegative := Real.sqrt_nonneg 2
    linarith) (by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2])

@[simp] theorem sqrtTwo_degrees : sqrtTwo.degrees = Real.sqrt 2 :=
  rfl

theorem sqrtTwo_irrational : Irrational sqrtTwo.degrees := by
  simpa using irrational_sqrt_two

theorem sqrtTwo_ne_ratCast (degrees : ℚ) : sqrtTwo.degrees ≠ (degrees : ℝ) := by
  intro equal
  exact sqrtTwo_irrational ⟨degrees, equal.symm⟩

end TorsionAngle

inductive RotationSense where
  | clockwise
  | anticlockwise
  deriving DecidableEq, Repr

/-- P-94.2.1 sign convention after fixing which selected bond is rotated toward the rear bond. -/
def SignAgreesWithRotation (angle : TorsionAngle) (sense : RotationSense) : Prop :=
  match sense with
  | .clockwise => 0 < angle.degrees
  | .anticlockwise => angle.degrees < 0

def RationalSignAgreesWithRotation (degrees : ℚ) (sense : RotationSense) : Prop :=
  match sense with
  | .clockwise => 0 < degrees
  | .anticlockwise => degrees < 0

theorem signAgreesWithRotation_ofRat_iff (degrees : ℚ)
    (lowerBound : (-180 : ℚ) ≤ degrees) (upperBound : degrees ≤ 180)
    (sense : RotationSense) :
    SignAgreesWithRotation (TorsionAngle.ofRat degrees lowerBound upperBound) sense ↔
      RationalSignAgreesWithRotation degrees sense := by
  cases sense <;> norm_num [SignAgreesWithRotation, RationalSignAgreesWithRotation]

inductive TorsionParticipant (Atom : Type*) where
  | atom (value : Atom)
  | lonePair (center : Atom)
  | duplicateAtom (original : Atom)
  deriving DecidableEq, Repr

/-- The P-94.2.2 vocabulary explicitly admits lone-pair phantoms and multiple-bond duplicate atoms
to the same sequence-rule selection relation as ordinary atoms. -/
structure SelectedTorsionFrame (Atom : Type*) where
  front : TorsionParticipant Atom
  rear : TorsionParticipant Atom
  angle : TorsionAngle

/-- One selectable atom/group on one end of the torsion axis.  Smaller sequence priority numbers
are senior; `identityClass` represents chemical identity for criteria (2) and (3). -/
structure TorsionCandidate where
  sequencePriority : ℕ
  identityClass : ℕ
  /-- Magnitude produced with the already selected group at the other end. -/
  resultingMagnitude : ℝ

namespace TorsionCandidate

def AllDifferent (candidates : List TorsionCandidate) : Prop :=
  (candidates.map TorsionCandidate.identityClass).Nodup

def IsOnlyUnique (candidates : List TorsionCandidate) (selected : TorsionCandidate) : Prop :=
  (candidates.map TorsionCandidate.identityClass).count selected.identityClass = 1 ∧
  ∀ candidate ∈ candidates,
    (candidates.map TorsionCandidate.identityClass).count candidate.identityClass = 1 →
      candidate.identityClass = selected.identityClass

def AllIdentical (candidates : List TorsionCandidate) : Prop :=
  ∀ first ∈ candidates, ∀ second ∈ candidates,
    first.identityClass = second.identityClass

/-- P-94.2.1's ordered selection criteria.  The three disjuncts correspond to: all different and
CIP-senior; exactly one identity class unique; all identical and smallest torsion magnitude. -/
def SelectedByP94Criteria (candidates : List TorsionCandidate)
    (selected : TorsionCandidate) : Prop :=
  selected ∈ candidates ∧
  ((AllDifferent candidates ∧
      ∀ candidate ∈ candidates, selected.sequencePriority ≤ candidate.sequencePriority) ∨
    (¬AllDifferent candidates ∧ IsOnlyUnique candidates selected) ∨
    (AllIdentical candidates ∧
      ∀ candidate ∈ candidates, selected.resultingMagnitude ≤ candidate.resultingMagnitude))

end TorsionCandidate

inductive ConformationalClass where
  | synperiplanar
  | synclinal
  | anticlinal
  | antiperiplanar
  deriving DecidableEq, Repr

/-- P-94.2.1's four regions, centered at 0°, ±60°, ±120°, and ±180° with a ±30° tolerance. -/
def ClassifiedAs (angle : TorsionAngle) : ConformationalClass → Prop
  | .synperiplanar => angle.magnitude ≤ 30
  | .synclinal => 30 ≤ angle.magnitude ∧ angle.magnitude ≤ 90
  | .anticlinal => 90 ≤ angle.magnitude ∧ angle.magnitude ≤ 150
  | .antiperiplanar => 150 ≤ angle.magnitude ∧ angle.magnitude ≤ 180

def RationalClassifiedAs (degrees : ℚ) : ConformationalClass → Prop
  | .synperiplanar => |degrees| ≤ 30
  | .synclinal => 30 ≤ |degrees| ∧ |degrees| ≤ 90
  | .anticlinal => 90 ≤ |degrees| ∧ |degrees| ≤ 150
  | .antiperiplanar => 150 ≤ |degrees| ∧ |degrees| ≤ 180

theorem classifiedAs_ofRat_iff (degrees : ℚ)
    (lowerBound : (-180 : ℚ) ≤ degrees) (upperBound : degrees ≤ 180)
    (classification : ConformationalClass) :
    ClassifiedAs (TorsionAngle.ofRat degrees lowerBound upperBound) classification ↔
      RationalClassifiedAs degrees classification := by
  cases classification <;>
    simp only [ClassifiedAs, RationalClassifiedAs, TorsionAngle.magnitude,
      TorsionAngle.ofRat_degrees] <;>
    rw [← Rat.cast_abs] <;>
    norm_cast

theorem sqrtTwo_classified_synperiplanar :
    ClassifiedAs TorsionAngle.sqrtTwo .synperiplanar := by
  rw [ClassifiedAs]
  simp only [TorsionAngle.magnitude, TorsionAngle.sqrtTwo_degrees,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

theorem every_torsionAngle_classified (angle : TorsionAngle) :
    ∃ classification, ClassifiedAs angle classification := by
  by_cases atMost30 : angle.magnitude ≤ 30
  · exact ⟨.synperiplanar, atMost30⟩
  by_cases atMost90 : angle.magnitude ≤ 90
  · exact ⟨.synclinal, le_of_lt (lt_of_not_ge atMost30), atMost90⟩
  by_cases atMost150 : angle.magnitude ≤ 150
  · exact ⟨.anticlinal, le_of_lt (lt_of_not_ge atMost90), atMost150⟩
  · exact ⟨.antiperiplanar, le_of_lt (lt_of_not_ge atMost150), angle.magnitude_le_180⟩

/-- The source's inclusive intervals overlap at 30°, 90°, and 150°.  This theorem records the
30° case so that an implementation cannot silently claim the authority relation is a function. -/
theorem thirty_degrees_has_two_classes :
    let angle : TorsionAngle :=
      { degrees := 30, lowerBound := by norm_num, upperBound := by norm_num }
    ClassifiedAs angle .synperiplanar ∧ ClassifiedAs angle .synclinal := by
  norm_num [ClassifiedAs, TorsionAngle.magnitude]

/-! ## P-94.3.1: acyclic conformational descriptors -/

def Eclipsed (angle : TorsionAngle) : Prop := angle.degrees = 0

/-- Context needed for the source's variational definition of `staggered`.  The separation
functional is supplied by exact geometry; it measures distance from the nearest eclipsed form. -/
structure StaggeredContext where
  admissible : TorsionAngle → Prop
  separationFromNearestEclipsed : TorsionAngle → ℝ
  allLigandsIdentical : Prop

def IsStaggered (context : StaggeredContext) (candidate : TorsionAngle) : Prop :=
  context.allLigandsIdentical ∧ context.admissible candidate ∧
  ∀ other, context.admissible other →
    context.separationFromNearestEclipsed other ≤
      context.separationFromNearestEclipsed candidate

/-- “Gauche” and “skew” have the same denotation as synclinal; `synclinal` is the preferred name. -/
def GaucheOrSkew (angle : TorsionAngle) : Prop :=
  ClassifiedAs angle .synclinal

theorem gaucheOrSkew_iff_synclinal (angle : TorsionAngle) :
    GaucheOrSkew angle ↔ ClassifiedAs angle .synclinal :=
  Iff.rfl

inductive ConjugatedSystemKind where
  | twoDoubleBondsSeparatedBySingleBond
  | nAlkylAmide
  | other
  deriving DecidableEq, Repr

inductive SCisTrans where
  | sCis
  | sTrans
  deriving DecidableEq, Repr

/-- P-94.3.1.3: `s-cis`/`s-trans` apply only to two conjugated double bonds about their intervening
single bond; their meanings are synperiplanar/antiperiplanar. -/
def SCisTransApplies (system : ConjugatedSystemKind) (angle : TorsionAngle) : SCisTrans → Prop
  | .sCis => system = .twoDoubleBondsSeparatedBySingleBond ∧
      ClassifiedAs angle .synperiplanar
  | .sTrans => system = .twoDoubleBondsSeparatedBySingleBond ∧
      ClassifiedAs angle .antiperiplanar

theorem sCis_not_applicable_to_nAlkylAmide (angle : TorsionAngle) :
    ¬SCisTransApplies .nAlkylAmide angle .sCis := by
  simp [SCisTransApplies]

/-- P-94.3.1.2 observation for `R₃C-C(Y)=X`. -/
structure TrigonalConformationObservation where
  isR3CCYXGrouping : Prop
  xToSomeR : TorsionAngle
  doubleBondBisectsRCRAngle : Prop

def IsBisectingConformation (observation : TrigonalConformationObservation) : Prop :=
  observation.isR3CCYXGrouping ∧
  ClassifiedAs observation.xToSomeR .antiperiplanar ∧
  observation.doubleBondBisectsRCRAngle

def IsEclipsingConformation (observation : TrigonalConformationObservation) : Prop :=
  observation.isR3CCYXGrouping ∧
  ClassifiedAs observation.xToSomeR .synperiplanar

/-! ## P-94.3.2: alicyclic ring conformations -/

inductive PlaneSide where
  | onPlane
  | positive
  | negative
  deriving DecidableEq, Repr

def OppositeSides : PlaneSide → PlaneSide → Prop
  | .positive, .negative | .negative, .positive => True
  | _, _ => False

def SameOffPlaneSide : PlaneSide → PlaneSide → Prop
  | .positive, .positive | .negative, .negative => True
  | _, _ => False

/-- P-94.3.2.1: four atoms of a five-membered ring lie in a plane and one lies outside it. -/
def IsEnvelope (sides : List PlaneSide) : Prop :=
  sides.length = 5 ∧ sides.count .onPlane = 4

/-- Carbohydrate five-membered-ring twist geometry (2-Carb-7.3): three adjacent ring atoms
define the reference plane and the remaining two atoms lie on opposite sides.  A cyclic offset is
handled by rotating the ring traversal before constructing this side list. -/
def IsCarbohydrateFiveRingTwist (sides : List PlaneSide) : Prop :=
  sides.length = 5 ∧
    ∃ firstExoplanar secondExoplanar,
      sides[0]? = some .onPlane ∧
      sides[1]? = some .onPlane ∧
      sides[2]? = some .onPlane ∧
      sides[3]? = some firstExoplanar ∧
      sides[4]? = some secondExoplanar ∧
      OppositeSides firstExoplanar secondExoplanar

/-- The source-defined five-ring twist has exactly three planar positions at its chosen offset,
so it cannot simultaneously be the four-planar-atom envelope form. -/
theorem carbohydrateFiveRingTwist_not_envelope (sides : List PlaneSide)
    (twist : IsCarbohydrateFiveRingTwist sides) : ¬IsEnvelope sides := by
  intro envelope
  rcases twist with
    ⟨lengthFive, firstExoplanar, secondExoplanar,
      side0, side1, side2, side3, side4, opposite⟩
  rcases sides with _ | ⟨first, tail1⟩
  · simp at lengthFive
  rcases tail1 with _ | ⟨second, tail2⟩
  · simp at lengthFive
  rcases tail2 with _ | ⟨third, tail3⟩
  · simp at lengthFive
  rcases tail3 with _ | ⟨fourth, tail4⟩
  · simp at lengthFive
  rcases tail4 with _ | ⟨fifth, rest⟩
  · simp at lengthFive
  have restLength : rest.length = 0 := by simpa using lengthFive
  have restNil : rest = [] := List.length_eq_zero_iff.mp restLength
  subst rest
  simp at side0 side1 side2 side3 side4
  subst first
  subst second
  subst third
  subst fourth
  subst fifth
  cases firstExoplanar <;> cases secondExoplanar <;>
    simp_all [OppositeSides, IsEnvelope]

/-- Plane-side form of the P-94.3.2.2 six-ring definitions.  Positions are numbered 1--6 in list
order; atoms 1, 2, 4, and 5 define the witness plane. -/
def SixRingReferencePlane (sides : List PlaneSide) : Prop :=
  sides.length = 6 ∧
  sides[0]? = some .onPlane ∧ sides[1]? = some .onPlane ∧
  sides[3]? = some .onPlane ∧ sides[4]? = some .onPlane

def IsChair (sides : List PlaneSide) : Prop :=
  SixRingReferencePlane sides ∧
  ∃ side3 side6,
    sides[2]? = some side3 ∧ sides[5]? = some side6 ∧ OppositeSides side3 side6

def IsBoat (sides : List PlaneSide) : Prop :=
  SixRingReferencePlane sides ∧
  ∃ side3 side6,
    sides[2]? = some side3 ∧ sides[5]? = some side6 ∧ SameOffPlaneSide side3 side6

theorem chair_not_boat (sides : List PlaneSide) (chair : IsChair sides) :
    ¬IsBoat sides := by
  rintro ⟨_, side3, side6, side3At, side6At, same⟩
  rcases chair.2 with ⟨chair3, chair6, chair3At, chair6At, opposite⟩
  have eq3 : side3 = chair3 := by simpa [side3At] using chair3At
  have eq6 : side6 = chair6 := by simpa [side6At] using chair6At
  subst side3
  subst side6
  cases chair3 <;> cases chair6 <;> simp [OppositeSides, SameOffPlaneSide] at opposite same

/-- P-94.3.2.3: a monounsaturated six-ring with the two atoms remote from the double bond on
opposite sides of its witness plane. -/
structure HalfChairObservation where
  ringSize : ℕ
  doubleBondCount : ℕ
  firstRemoteSide : PlaneSide
  secondRemoteSide : PlaneSide

def IsHalfChair (observation : HalfChairObservation) : Prop :=
  observation.ringSize = 6 ∧
  observation.doubleBondCount = 1 ∧
  OppositeSides observation.firstRemoteSide observation.secondRemoteSide

/-- A weak consequence of the P-94.3.2.2 twist definition: the candidate lies in the same
single-bond-rotation equivalence component as two distinct boats.  This predicate deliberately
retains its historical name for compatibility, but it is not by itself the authoritative twist
criterion because equivalence closure forgets whether the candidate actually occurs on a
boat-to-boat path. -/
def IsTwistOnBoatInterconversion {State : Type*}
    (singleBondRotation : State → State → Prop)
    (isBoatState : State → Prop) (candidate : State) : Prop :=
  ∃ firstBoat secondBoat,
    firstBoat ≠ secondBoat ∧
    isBoatState firstBoat ∧
    isBoatState secondBoat ∧
    InterconvertibleBySingleBondRotations singleBondRotation firstBoat candidate ∧
    InterconvertibleBySingleBondRotations singleBondRotation candidate secondBoat

/-- One physical direct-rotation edge, independent of which endpoint the supplied relation names
first.  A caller may orient its direct-rotation ledger either way without changing path meaning. -/
def DirectRotationStep {State : Type*}
    (singleBondRotation : State → State → Prop) (first second : State) : Prop :=
  singleBondRotation first second ∨ singleBondRotation second first

theorem directRotationStep_symmetric {State : Type*}
    (singleBondRotation : State → State → Prop) :
    Symmetric (DirectRotationStep singleBondRotation) := by
  intro first second direct
  rcases direct with forward | reverse
  · exact Or.inr forward
  · exact Or.inl reverse

theorem directRotationStep_reverseRelation_iff {State : Type*}
    (singleBondRotation : State → State → Prop) (first second : State) :
    DirectRotationStep singleBondRotation first second ↔
      DirectRotationStep (fun left right => singleBondRotation right left) first second := by
  constructor <;> intro direct <;> rcases direct with forward | reverse
  · exact Or.inr forward
  · exact Or.inl reverse
  · exact Or.inr forward
  · exact Or.inl reverse

/-- A nonempty finite ordered path whose adjacent states differ by one asserted formally-single-
bond rotation.  Unlike the equivalence closure above, this object retains traversal order while
`DirectRotationStep` makes each physical edge invariant under ledger orientation. -/
inductive DirectedRotationPath {State : Type*}
    (singleBondRotation : State → State → Prop) : List State → Prop where
  | singleton (state : State) : DirectedRotationPath singleBondRotation [state]
  | cons {first second : State} {rest : List State}
      (direct : DirectRotationStep singleBondRotation first second)
      (tail : DirectedRotationPath singleBondRotation (second :: rest)) :
      DirectedRotationPath singleBondRotation (first :: second :: rest)

namespace DirectedRotationPath

/-- A directed rotation path supplies the corresponding P-94.1 interconversion relation between
its first and last states. -/
theorem interconvertible_head_last {State : Type*}
    {singleBondRotation : State → State → Prop} {states : List State}
    (path : DirectedRotationPath singleBondRotation states)
    {first last : State}
    (firstAt : states.head? = some first)
    (lastAt : states.getLast? = some last) :
    InterconvertibleBySingleBondRotations singleBondRotation first last := by
  induction path generalizing first last with
  | singleton state =>
      simp at firstAt lastAt
      subst first
      subst last
      exact .refl state
  | @cons firstState secondState rest direct tail inductionHypothesis =>
      have firstEq : firstState = first := by simpa using firstAt
      subst first
      have firstSecond :
          InterconvertibleBySingleBondRotations singleBondRotation firstState secondState := by
        rcases direct with forward | reverse
        · exact .step forward
        · exact .symm (.step reverse)
      apply InterconvertibleBySingleBondRotations.trans firstSecond
      apply inductionHypothesis
      · rfl
      · simpa using lastAt

end DirectedRotationPath

/-- Authoritative finite path meaning of the P-94.3.2.2 phrase “the conformation passed through
in the interconversion of two boat forms”.  Besides distinct state identifiers, the two endpoint
boats must satisfy the caller's explicit conformation-distinguishability relation.  The candidate
is the shared endpoint of two ordered legs, is strictly different from both endpoint families,
and occurs once on the combined simple path.  The separate chair exclusion prevents the former
equivalence-component false positive. -/
def ExplicitTwistOnBoatInterconversion {State : Type*}
    (singleBondRotation : State → State → Prop)
    (endpointConformationsDistinct : State → State → Prop)
    (isBoatState isChairState : State → Prop) (candidate : State)
    (firstLeg secondLeg : List State) : Prop :=
  ∃ firstBoat secondBoat,
    firstBoat ≠ secondBoat ∧
    endpointConformationsDistinct firstBoat secondBoat ∧
    isBoatState firstBoat ∧
    isBoatState secondBoat ∧
    ¬isBoatState candidate ∧
    ¬isChairState candidate ∧
    firstLeg.head? = some firstBoat ∧
    firstLeg.getLast? = some candidate ∧
    secondLeg.head? = some candidate ∧
    secondLeg.getLast? = some secondBoat ∧
    DirectedRotationPath singleBondRotation firstLeg ∧
    DirectedRotationPath singleBondRotation secondLeg ∧
    (firstLeg ++ secondLeg.tail).Nodup

/-- The authoritative ordered-path criterion implies the older equivalence-component
consequence.  The converse is false in general and is not used for descriptor support. -/
theorem explicitTwistOnBoatInterconversion_implies_weak {State : Type*}
    {singleBondRotation : State → State → Prop}
    {endpointConformationsDistinct : State → State → Prop}
    {isBoatState isChairState : State → Prop} {candidate : State}
    {firstLeg secondLeg : List State}
    (explicit : ExplicitTwistOnBoatInterconversion singleBondRotation
      endpointConformationsDistinct isBoatState isChairState candidate firstLeg secondLeg) :
    IsTwistOnBoatInterconversion singleBondRotation isBoatState candidate := by
  rcases explicit with
    ⟨firstBoat, secondBoat, distinct, _conformationsDistinct,
      firstBoatIsBoat, secondBoatIsBoat,
      _candidateNotBoat, _candidateNotChair, firstHead, firstLast,
      secondHead, secondLast, firstPath, secondPath, _nodup⟩
  exact ⟨firstBoat, secondBoat, distinct, firstBoatIsBoat, secondBoatIsBoat,
    firstPath.interconvertible_head_last firstHead firstLast,
    secondPath.interconvertible_head_last secondHead secondLast⟩

/-- Adjacent side entries alternate between the two off-plane witness planes. -/
def AlternatingOffPlane : List PlaneSide → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      OppositeSides first second ∧ AlternatingOffPlane (second :: rest)

/-- P-94.3.2.4.  `symmetricallyEquivalent` is an explicit geometry/group-action witness left for
the perception layer; it is not inferred from an alternating cartoon. -/
def IsCrown (sides : List PlaneSide) (symmetricallyEquivalent : Prop) : Prop :=
  8 ≤ sides.length ∧ Even sides.length ∧ AlternatingOffPlane sides ∧ symmetricallyEquivalent

private def TubPattern (sides : List PlaneSide) : Prop :=
  sides.length = 8 ∧
  sides[0]? = some .onPlane ∧ sides[1]? = some .onPlane ∧
  sides[4]? = some .onPlane ∧ sides[5]? = some .onPlane ∧
  ∃ offSide,
    (offSide = .positive ∨ offSide = .negative) ∧
    sides[2]? = some offSide ∧ sides[3]? = some offSide ∧
    sides[6]? = some offSide ∧ sides[7]? = some offSide

/-- P-94.3.2.5, allowing any cyclic choice of the first member of the diametrically opposite
bond pair. -/
def IsTub (sides : List PlaneSide) : Prop :=
  ∃ offset, TubPattern (sides.rotate offset)

inductive BridgeheadDirection where
  | inward
  | outward
  deriving DecidableEq, Repr

/-- P-94.3.2.6 observation of one identified bridgehead site.  Retaining molecule atom IDs keeps
opposite directions on different sites from being conflated into an in-out pair. -/
structure InOutObservation (Framework : Type*) where
  framework : Framework
  bridgehead : ℕ
  directedParticipant : TorsionParticipant ℕ
  bridgeLongEnough : Prop
  direction : BridgeheadDirection

/-- P-94.3.2.6: identical sufficiently long-bridged frameworks observed at the same bridgehead
and the same directed exocyclic atom or lone pair form an in-out pair exactly when their
directions differ. -/
def AreInOutIsomers {Framework : Type*}
    (first second : InOutObservation Framework) : Prop :=
  first.framework = second.framework ∧
  first.bridgehead = second.bridgehead ∧
  first.directedParticipant = second.directedParticipant ∧
  first.bridgeLongEnough ∧ second.bridgeLongEnough ∧
  first.direction ≠ second.direction

end BlueBookP94

end TetraStereo.OneCenter
