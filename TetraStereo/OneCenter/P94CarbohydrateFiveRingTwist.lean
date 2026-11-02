import TetraStereo.OneCenter.P94CoordinateRingWitnessDiscovery

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94CarbohydrateFiveRingTwist

open CoordinateRing

/-!
# Carbohydrate-specific five-membered twist geometry

P-94.3.2.2 delegates the carbohydrate convention.  The carbohydrate recommendation gives an
exact geometric rule: three adjacent ring atoms define the reference plane and the other two lie
on opposite sides.  This module searches every cyclic offset and every noncollinear plane spanned
by actual ring coordinates.

Applicability is intentionally separate from graph geometry.  The present raw molecule has no
semantic annotation saying that a ring is being named in carbohydrate stereochemistry, so an
independent finite authority supplies exactly those molecule-local units.  The analyzer validates
and exhausts that authority; it does not classify every five-membered ring as a carbohydrate.
-/

/-! ## Finite independent applicability authority -/

structure IndependentCarbohydrateFiveRingAuthority where
  Applies : RawMolecule → P94ConformationUnit → Prop
  units : RawMolecule → Finset P94ConformationUnit
  mem_units_iff : ∀ molecule unit, unit ∈ units molecule ↔ Applies molecule unit
  applies_kind : ∀ molecule unit, Applies molecule unit →
    unit.kind = .fiveMemberedRing
  applies_valid : ∀ molecule unit, Applies molecule unit → unit.ValidFor molecule

def scheduledCarbohydrateFiveRingUnits
    (authority : IndependentCarbohydrateFiveRingAuthority) (molecule : RawMolecule) :
    Finset P94ConformationUnit :=
  authority.units molecule

theorem mem_scheduledCarbohydrateFiveRingUnits_iff
    (authority : IndependentCarbohydrateFiveRingAuthority) (molecule : RawMolecule)
    (unit : P94ConformationUnit) :
    unit ∈ scheduledCarbohydrateFiveRingUnits authority molecule ↔
      authority.Applies molecule unit :=
  authority.mem_units_iff molecule unit

/-! ## Exact geometry at one cyclic offset and reference plane -/

private def carbohydrateFiveRingTwistRecord
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (molecule : RawMolecule) (unit : P94ConformationUnit) (sides : List PlaneSide) :
    CoordinateRingEvidence :=
  .ringPlane
    { unit := unit
      sides := sides
      saturatedCyclic := False
      symmetricallyEquivalent := False
      carbohydrateFiveRing := authority.Applies molecule unit }

def CoordinateCarbohydrateFiveRingTwistEvidenceJudgment
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (offset : ℕ) (plane : ExactPlane)
    (output : CoordinateRingEvidence) : Prop :=
  authority.Applies molecule unit ∧
    ∃ sides,
      RingSidesOfPlane spatial (unit.atoms.rotate offset) plane sides ∧
      IsCarbohydrateFiveRingTwist sides ∧
      output = carbohydrateFiveRingTwistRecord authority molecule unit sides

private theorem coordinateCarbohydrateFiveRingTwistEvidenceJudgment_functional
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (offset : ℕ) (plane : ExactPlane) :
    ∀ left right,
      CoordinateCarbohydrateFiveRingTwistEvidenceJudgment authority molecule spatial
        unit offset plane left →
      CoordinateCarbohydrateFiveRingTwistEvidenceJudgment authority molecule spatial
        unit offset plane right →
      left = right := by
  rintro left right ⟨_, leftSides, leftJudged, _, rfl⟩
    ⟨_, rightSides, rightJudged, _, rfl⟩
  have equal := RingSidesOfPlane.unique spatial
    (unit.atoms.rotate offset) plane leftJudged rightJudged
  subst rightSides
  rfl

private noncomputable def specificationChoice? {Alpha : Type*}
    (predicate : Alpha → Prop) : Option Alpha := by
  classical
  exact if present : ∃ value, predicate value then some (Classical.choose present) else none

private theorem specificationChoice?_eq_some_iff {Alpha : Type*}
    (predicate : Alpha → Prop)
    (functional : ∀ left right, predicate left → predicate right → left = right)
    (value : Alpha) :
    specificationChoice? predicate = some value ↔ predicate value := by
  classical
  by_cases present : ∃ candidate, predicate candidate
  · have chosen : predicate (Classical.choose present) := Classical.choose_spec present
    constructor
    · intro computed
      have equal : Classical.choose present = value := by
        simpa [specificationChoice?, present] using computed
      simpa [← equal] using chosen
    · intro judged
      have equal := functional (Classical.choose present) value chosen judged
      simp [specificationChoice?, present, equal]
  · constructor
    · intro computed
      simp [specificationChoice?, present] at computed
    · intro judged
      exact False.elim (present ⟨value, judged⟩)

noncomputable def coordinateCarbohydrateFiveRingTwistEvidence?
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (offset : ℕ) (plane : ExactPlane) :
    Option CoordinateRingEvidence :=
  specificationChoice?
    (CoordinateCarbohydrateFiveRingTwistEvidenceJudgment
      authority molecule spatial unit offset plane)

theorem coordinateCarbohydrateFiveRingTwistEvidence?_eq_some_iff
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (offset : ℕ) (plane : ExactPlane)
    (output : CoordinateRingEvidence) :
    coordinateCarbohydrateFiveRingTwistEvidence?
        authority molecule spatial unit offset plane = some output ↔
      CoordinateCarbohydrateFiveRingTwistEvidenceJudgment
        authority molecule spatial unit offset plane output :=
  specificationChoice?_eq_some_iff _
    (coordinateCarbohydrateFiveRingTwistEvidenceJudgment_functional
      authority molecule spatial unit offset plane) output

theorem coordinateCarbohydrateFiveRingTwistEvidenceJudgment_supports
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (offset : ℕ) (plane : ExactPlane)
    (output : CoordinateRingEvidence)
    (judged : CoordinateCarbohydrateFiveRingTwistEvidenceJudgment
      authority molecule spatial unit offset plane output) :
    output.unit.ValidFor molecule ∧ output.MolecularRolesValid molecule ∧
      output.Supports .twist := by
  rcases judged with ⟨applies, sides, sidesJudged, twist, rfl⟩
  have kind := authority.applies_kind molecule unit applies
  have valid := authority.applies_valid molecule unit applies
  refine ⟨valid, ?_, ?_⟩
  · simp [carbohydrateFiveRingTwistRecord,
      P94ConformationEvidence.MolecularRolesValid, kind]
  · apply (p94CarbohydrateFiveRingTwistSupport_iff
      (State := Unit) (Framework := Unit) _).mpr
    exact ⟨kind, by simpa using sidesJudged.length_eq, applies, twist⟩

/-! ## Exhaustive offset and plane discovery -/

def CanonicalCarbohydrateFiveRingTwistOffsetJudgment
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (offset : ℕ) (output : CoordinateRingEvidence) : Prop :=
  CanonicalRingSearchJudgment spatial (unit.atoms.rotate offset) candidatePlanes
    (CoordinateCarbohydrateFiveRingTwistEvidenceJudgment
      authority molecule spatial unit offset) output

def AutomaticCarbohydrateFiveRingTwistEvidenceJudgment
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (output : CoordinateRingEvidence) : Prop :=
  CanonicalFirst
    (CanonicalCarbohydrateFiveRingTwistOffsetJudgment authority molecule spatial unit)
    (List.range unit.atoms.length) output

noncomputable def automaticCarbohydrateFiveRingTwistEvidence?
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) : Option CoordinateRingEvidence :=
  firstSuccess?
    (fun offset => canonicalRingSearch? spatial (unit.atoms.rotate offset) candidatePlanes
      (coordinateCarbohydrateFiveRingTwistEvidence?
        authority molecule spatial unit offset))
    (List.range unit.atoms.length)

theorem automaticCarbohydrateFiveRingTwistEvidence?_eq_some_iff
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (output : CoordinateRingEvidence) :
    automaticCarbohydrateFiveRingTwistEvidence? authority molecule spatial unit =
        some output ↔
      AutomaticCarbohydrateFiveRingTwistEvidenceJudgment
        authority molecule spatial unit output := by
  exact firstSuccess?_eq_some_iff
    (fun offset => canonicalRingSearch? spatial (unit.atoms.rotate offset) candidatePlanes
      (coordinateCarbohydrateFiveRingTwistEvidence?
        authority molecule spatial unit offset))
    (CanonicalCarbohydrateFiveRingTwistOffsetJudgment authority molecule spatial unit)
    (fun offset candidate => canonicalRingSearch?_eq_some_iff spatial
      (unit.atoms.rotate offset) candidatePlanes
      (coordinateCarbohydrateFiveRingTwistEvidence?
        authority molecule spatial unit offset)
      (CoordinateCarbohydrateFiveRingTwistEvidenceJudgment
        authority molecule spatial unit offset)
      (fun plane result =>
        coordinateCarbohydrateFiveRingTwistEvidence?_eq_some_iff
          authority molecule spatial unit offset plane result)
      candidate)
    (List.range unit.atoms.length) output

theorem automaticCarbohydrateFiveRingTwistEvidence?_eq_none_iff
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) :
    automaticCarbohydrateFiveRingTwistEvidence? authority molecule spatial unit = none ↔
      ¬∃ output,
        AutomaticCarbohydrateFiveRingTwistEvidenceJudgment
          authority molecule spatial unit output := by
  constructor
  · intro computed ⟨output, judged⟩
    have someComputed := (automaticCarbohydrateFiveRingTwistEvidence?_eq_some_iff
      authority molecule spatial unit output).mpr judged
    rw [computed] at someComputed
    contradiction
  · intro absent
    cases computed : automaticCarbohydrateFiveRingTwistEvidence?
        authority molecule spatial unit with
    | none => rfl
    | some output =>
        exact False.elim (absent ⟨output,
          (automaticCarbohydrateFiveRingTwistEvidence?_eq_some_iff
            authority molecule spatial unit output).mp computed⟩)

theorem automaticCarbohydrateFiveRingTwistEvidenceJudgment_supports
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (output : CoordinateRingEvidence)
    (judged : AutomaticCarbohydrateFiveRingTwistEvidenceJudgment
      authority molecule spatial unit output) :
    output.unit.ValidFor molecule ∧ output.MolecularRolesValid molecule ∧
      output.Supports .twist := by
  rcases judged.witness with ⟨offset, _offsetPresent, offsetJudged⟩
  rcases offsetJudged with ⟨_points, _pointsJudged, planeSelected⟩
  rcases planeSelected.witness with ⟨plane, _planePresent, planeJudged⟩
  exact coordinateCarbohydrateFiveRingTwistEvidenceJudgment_supports
    authority molecule spatial unit offset plane output planeJudged

/-! ## Exact public reporting for one unit -/

noncomputable def automaticCarbohydrateFiveRingTwistAssignments
    (certified : CertifiedChemistryNormalizationResult)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    List P94ConformationAssignment :=
  match automaticCarbohydrateFiveRingTwistEvidence?
      authority certified.result.parsed spatial unit with
  | none => []
  | some output => certified.analyzeP94Conformation [output]

theorem automaticCarbohydrateFiveRingTwistAssignments_mem_iff
    (certified : CertifiedChemistryNormalizationResult)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (assignment : P94ConformationAssignment) :
    assignment ∈ automaticCarbohydrateFiveRingTwistAssignments
        certified authority spatial unit ↔
      ∃ output,
        AutomaticCarbohydrateFiveRingTwistEvidenceJudgment authority
          certified.result.parsed spatial unit output ∧
        IndependentP94ConformationAssignment certified.result.parsed [output] assignment := by
  classical
  cases computed : automaticCarbohydrateFiveRingTwistEvidence?
      authority certified.result.parsed spatial unit with
  | none =>
      constructor
      · intro present
        unfold automaticCarbohydrateFiveRingTwistAssignments at present
        rw [computed] at present
        simp at present
      · rintro ⟨output, judged, _⟩
        have someComputed := (automaticCarbohydrateFiveRingTwistEvidence?_eq_some_iff
          authority certified.result.parsed spatial unit output).mpr judged
        rw [computed] at someComputed
        contradiction
  | some output =>
      constructor
      · intro present
        have analyzedPresent : assignment ∈ certified.analyzeP94Conformation [output] := by
          unfold automaticCarbohydrateFiveRingTwistAssignments at present
          rw [computed] at present
          exact present
        exact ⟨output,
          (automaticCarbohydrateFiveRingTwistEvidence?_eq_some_iff
            authority certified.result.parsed spatial unit output).mp computed,
          (mem_analyzeP94Conformation_iff_independent
            certified [output] assignment).mp analyzedPresent⟩
      · rintro ⟨other, judged, independent⟩
        have otherComputed := (automaticCarbohydrateFiveRingTwistEvidence?_eq_some_iff
          authority certified.result.parsed spatial unit other).mpr judged
        rw [computed] at otherComputed
        have equal : output = other := Option.some.inj otherComputed
        subst other
        have analyzedPresent := (mem_analyzeP94Conformation_iff_independent
          certified [output] assignment).mpr independent
        unfold automaticCarbohydrateFiveRingTwistAssignments
        rw [computed]
        exact analyzedPresent

theorem automaticCarbohydrateFiveRingTwistAssignments_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    (automaticCarbohydrateFiveRingTwistAssignments
      certified authority spatial unit).Nodup := by
  classical
  cases computed : automaticCarbohydrateFiveRingTwistEvidence?
      authority certified.result.parsed spatial unit with
  | none =>
      unfold automaticCarbohydrateFiveRingTwistAssignments
      rw [computed]
      simp
  | some output =>
      unfold automaticCarbohydrateFiveRingTwistAssignments
      rw [computed]
      exact analyzeP94Conformation_nodup certified [output]

theorem automaticCarbohydrateFiveRingTwistAssignment_count_eq_one_iff
    (certified : CertifiedChemistryNormalizationResult)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (assignment : P94ConformationAssignment) :
    List.count assignment
        (automaticCarbohydrateFiveRingTwistAssignments
          certified authority spatial unit) = 1 ↔
      ∃ output,
        AutomaticCarbohydrateFiveRingTwistEvidenceJudgment authority
          certified.result.parsed spatial unit output ∧
        IndependentP94ConformationAssignment certified.result.parsed [output] assignment := by
  rw [← automaticCarbohydrateFiveRingTwistAssignments_mem_iff]
  constructor
  · intro countOne
    by_contra absent
    have countZero := List.count_eq_zero_of_not_mem absent
    omega
  · exact List.count_eq_one_of_mem
      (automaticCarbohydrateFiveRingTwistAssignments_nodup
        certified authority spatial unit)

/-! ## Deduplicated molecule-level carbohydrate twist report -/

noncomputable def molecularCarbohydrateFiveRingTwistAssignments
    (certified : CertifiedChemistryNormalizationResult)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (spatial : SpatialConfiguration) : List P94ConformationAssignment :=
  ((scheduledCarbohydrateFiveRingUnits authority certified.result.parsed).toList.flatMap
    (automaticCarbohydrateFiveRingTwistAssignments certified authority spatial)).dedup

def IndependentMolecularCarbohydrateFiveRingTwistAssignment
    (molecule : RawMolecule) (authority : IndependentCarbohydrateFiveRingAuthority)
    (spatial : SpatialConfiguration) (assignment : P94ConformationAssignment) : Prop :=
  ∃ unit, authority.Applies molecule unit ∧
    ∃ output,
      AutomaticCarbohydrateFiveRingTwistEvidenceJudgment
        authority molecule spatial unit output ∧
      IndependentP94ConformationAssignment molecule [output] assignment

theorem molecularCarbohydrateFiveRingTwistAssignments_mem_iff
    (certified : CertifiedChemistryNormalizationResult)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (spatial : SpatialConfiguration) (assignment : P94ConformationAssignment) :
    assignment ∈ molecularCarbohydrateFiveRingTwistAssignments
        certified authority spatial ↔
      IndependentMolecularCarbohydrateFiveRingTwistAssignment
        certified.result.parsed authority spatial assignment := by
  classical
  simp only [molecularCarbohydrateFiveRingTwistAssignments, List.mem_dedup,
    List.mem_flatMap, Finset.mem_toList]
  constructor
  · rintro ⟨unit, unitPresent, assignmentPresent⟩
    rcases (automaticCarbohydrateFiveRingTwistAssignments_mem_iff
      certified authority spatial unit assignment).mp assignmentPresent with
      ⟨output, judged, independent⟩
    exact ⟨unit,
      (mem_scheduledCarbohydrateFiveRingUnits_iff
        authority certified.result.parsed unit).mp unitPresent,
      output, judged, independent⟩
  · rintro ⟨unit, applies, output, judged, independent⟩
    exact ⟨unit,
      (mem_scheduledCarbohydrateFiveRingUnits_iff
        authority certified.result.parsed unit).mpr applies,
      (automaticCarbohydrateFiveRingTwistAssignments_mem_iff
        certified authority spatial unit assignment).mpr
        ⟨output, judged, independent⟩⟩

theorem molecularCarbohydrateFiveRingTwistAssignments_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (spatial : SpatialConfiguration) :
    (molecularCarbohydrateFiveRingTwistAssignments certified authority spatial).Nodup := by
  classical
  exact List.nodup_dedup _

theorem molecularCarbohydrateFiveRingTwistAssignment_count_eq_one_iff
    (certified : CertifiedChemistryNormalizationResult)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (spatial : SpatialConfiguration) (assignment : P94ConformationAssignment) :
    List.count assignment
        (molecularCarbohydrateFiveRingTwistAssignments certified authority spatial) = 1 ↔
      IndependentMolecularCarbohydrateFiveRingTwistAssignment
        certified.result.parsed authority spatial assignment := by
  rw [← molecularCarbohydrateFiveRingTwistAssignments_mem_iff]
  constructor
  · intro countOne
    by_contra absent
    have countZero := List.count_eq_zero_of_not_mem absent
    omega
  · exact List.count_eq_one_of_mem
      (molecularCarbohydrateFiveRingTwistAssignments_nodup
        certified authority spatial)

theorem molecularCarbohydrateFiveRingTwistAssignment_count_eq_zero_iff
    (certified : CertifiedChemistryNormalizationResult)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (spatial : SpatialConfiguration) (assignment : P94ConformationAssignment) :
    List.count assignment
        (molecularCarbohydrateFiveRingTwistAssignments certified authority spatial) = 0 ↔
      ¬IndependentMolecularCarbohydrateFiveRingTwistAssignment
        certified.result.parsed authority spatial assignment := by
  rw [List.count_eq_zero, molecularCarbohydrateFiveRingTwistAssignments_mem_iff]

end BlueBookP94.P94CarbohydrateFiveRingTwist
end TetraStereo.OneCenter
