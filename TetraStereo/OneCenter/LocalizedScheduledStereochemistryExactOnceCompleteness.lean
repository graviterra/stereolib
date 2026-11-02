import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialAssignmentCompleteness
import TetraStereo.OneCenter.LocalizedOddCumuleneAssignmentCompleteness
import TetraStereo.OneCenter.LocalizedOrdinaryMonocyclicAssignmentCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Exact-once assembly for the four-family localized scheduled result

The four source analyzers retain distinct canonical physical units.  This file closes the list
assembly seam: each family has exact membership in the public disjoint sum, the complete public
list is duplicate-free, and its projection to canonical physical units is duplicate-free.  Thus
every emitted physical unit has literal multiplicity one in the actual scheduled result, not only
in an isolated family analyzer.
-/

/-! ## Missing local structural lemmas -/

/-- The canonical localized tetrahedral-center carrier is duplicate-free. -/
theorem canonicalTetrahedralCenters_nodup
    (input : CertifiedLocalizedCIPInput) :
    input.canonicalTetrahedralCenters.Nodup := by
  unfold canonicalTetrahedralCenters
  apply List.Nodup.map
  · intro left right equal
    apply Subtype.ext
    exact congrArg
      (fun center : input.TetrahedralCenter => center.1) equal
  · exact (Finset.sort_nodup input.tetrahedralCenterSet
      (fun left right => left ≤ right)).attach

/-- A successful scheduled tetrahedral call retains exactly its canonical source center. -/
theorem localizedScheduledTetrahedralSpatialAssignmentAt?_center
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter)
    (assignment : input.LocalizedScheduledTetrahedralSpatialAssignment fuel)
    (computed : input.localizedScheduledTetrahedralSpatialAssignmentAt?
      fuel center = some assignment) :
    assignment.center = center := by
  unfold localizedScheduledTetrahedralSpatialAssignmentAt? at computed
  cases stateComputed :
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
        (input.localizedFinalOccurrence fuel center) with
  | none => simp [stateComputed] at computed
  | some descriptor =>
      simp [stateComputed] at computed
      subst assignment
      rfl

/-- Scheduled tetrahedral list membership is exactly the retained-center local computation. -/
theorem mem_analyzeLocalizedScheduledTetrahedralSpatial_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedScheduledTetrahedralSpatialAssignment fuel) :
    assignment ∈ input.analyzeLocalizedScheduledTetrahedralSpatial fuel ↔
      input.localizedScheduledTetrahedralSpatialAssignmentAt?
        fuel assignment.center = some assignment := by
  classical
  constructor
  · intro present
    rw [analyzeLocalizedScheduledTetrahedralSpatial, List.mem_filterMap] at present
    obtain ⟨center, _centerPresent, emitted⟩ := present
    cases resultComputed : input.localizedScheduledTetrahedralSpatialAssignmentAt?
        fuel center with
    | none => simp [resultComputed] at emitted
    | some result =>
        simp [resultComputed] at emitted
        subst assignment
        rw [input.localizedScheduledTetrahedralSpatialAssignmentAt?_center
          fuel center result resultComputed]
        exact resultComputed
  · intro emitted
    rw [analyzeLocalizedScheduledTetrahedralSpatial, List.mem_filterMap]
    exact ⟨assignment.center,
      (input.mem_canonicalTetrahedralCenters_iff assignment.center).mpr
        assignment.center.2,
      by simp [emitted]⟩

/-- The scheduled tetrahedral branch is duplicate-free. -/
theorem analyzeLocalizedScheduledTetrahedralSpatial_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.analyzeLocalizedScheduledTetrahedralSpatial fuel).Nodup := by
  classical
  unfold analyzeLocalizedScheduledTetrahedralSpatial
  apply input.canonicalTetrahedralCenters_nodup.filterMap
  intro left right assignment leftComputed rightComputed
  have leftCenter := input.localizedScheduledTetrahedralSpatialAssignmentAt?_center
    fuel left assignment leftComputed
  have rightCenter := input.localizedScheduledTetrahedralSpatialAssignmentAt?_center
    fuel right assignment rightComputed
  exact leftCenter.symm.trans rightCenter

/-- Projecting scheduled tetrahedral assignments to physical centers remains duplicate-free. -/
theorem analyzeLocalizedScheduledTetrahedralSpatial_centers_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    ((input.analyzeLocalizedScheduledTetrahedralSpatial fuel).map
      LocalizedScheduledTetrahedralSpatialAssignment.center).Nodup := by
  classical
  apply (input.analyzeLocalizedScheduledTetrahedralSpatial_nodup fuel).map_on
  intro left leftPresent right rightPresent sameCenter
  have leftComputed :=
    (input.mem_analyzeLocalizedScheduledTetrahedralSpatial_iff fuel left).mp leftPresent
  have rightComputed :=
    (input.mem_analyzeLocalizedScheduledTetrahedralSpatial_iff fuel right).mp rightPresent
  rw [sameCenter] at leftComputed
  exact Option.some.inj (leftComputed.symm.trans rightComputed)

/-- The state-parameterized even-axial branch is duplicate-free. -/
theorem analyzeLocalizedEvenCumuleneAxialWithState_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) :
    (input.analyzeLocalizedEvenCumuleneAxialWithState fuel state).Nodup := by
  classical
  unfold analyzeLocalizedEvenCumuleneAxialWithState
  apply input.localizedEvenAxialChains_nodup.attach.filterMap
  intro left right assignment leftComputed rightComputed
  have leftAxis := input.localizedEvenAxialSpatialAssignmentAtWithState?_axis
    fuel state left assignment leftComputed
  have rightAxis := input.localizedEvenAxialSpatialAssignmentAtWithState?_axis
    fuel state right assignment rightComputed
  exact leftAxis.symm.trans rightAxis

/-- The scheduled even-axial branch is duplicate-free. -/
theorem analyzeLocalizedEvenCumuleneAxial_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.analyzeLocalizedEvenCumuleneAxial fuel).Nodup :=
  input.analyzeLocalizedEvenCumuleneAxialWithState_nodup fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)

/-- Projecting scheduled even-axial assignments to canonical axes remains duplicate-free. -/
theorem analyzeLocalizedEvenCumuleneAxial_axes_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    ((input.analyzeLocalizedEvenCumuleneAxial fuel).map
      LocalizedEvenAxialSpatialAssignment.axis).Nodup := by
  classical
  apply (input.analyzeLocalizedEvenCumuleneAxial_nodup fuel).map_on
  intro left leftPresent right rightPresent sameAxis
  have leftComputed :=
    (input.mem_analyzeLocalizedEvenCumuleneAxialWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) left).mp
        leftPresent
  have rightComputed :=
    (input.mem_analyzeLocalizedEvenCumuleneAxialWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) right).mp
        rightPresent
  rw [sameAxis] at leftComputed
  exact Option.some.inj (leftComputed.symm.trans rightComputed)

/-- Projecting scheduled odd-cumulene assignments to canonical axes remains duplicate-free. -/
theorem analyzeLocalizedOddCumuleneEZ_axes_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    ((input.analyzeLocalizedOddCumuleneEZ fuel).map
      LocalizedOddCumuleneEZSpatialAssignment.axis).Nodup := by
  classical
  apply (input.analyzeLocalizedOddCumuleneEZ_nodup fuel).map_on
  intro left leftPresent right rightPresent sameAxis
  have leftComputed :=
    (input.mem_analyzeLocalizedOddCumuleneEZWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) left).mp
        leftPresent
  have rightComputed :=
    (input.mem_analyzeLocalizedOddCumuleneEZWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) right).mp
        rightPresent
  rw [sameAxis] at leftComputed
  exact Option.some.inj (leftComputed.symm.trans rightComputed)

/-! ## Exact public family membership -/

theorem tetrahedral_mem_analyzeLocalizedScheduledStereochemistry_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedScheduledTetrahedralSpatialAssignment fuel) :
    LocalizedScheduledStereochemicalAssignment.tetrahedral assignment ∈
        input.analyzeLocalizedScheduledStereochemistry fuel ↔
      assignment ∈ input.analyzeLocalizedScheduledTetrahedralSpatial fuel := by
  simp [analyzeLocalizedScheduledStereochemistry]

theorem evenAxial_mem_analyzeLocalizedScheduledStereochemistry_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel) :
    LocalizedScheduledStereochemicalAssignment.evenAxial assignment ∈
        input.analyzeLocalizedScheduledStereochemistry fuel ↔
      assignment ∈ input.analyzeLocalizedEvenCumuleneAxial fuel := by
  simp [analyzeLocalizedScheduledStereochemistry]

theorem ordinaryMonocyclicEZ_mem_analyzeLocalizedScheduledStereochemistry_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel) :
    LocalizedScheduledStereochemicalAssignment.ordinaryMonocyclicEZ assignment ∈
        input.analyzeLocalizedScheduledStereochemistry fuel ↔
      assignment ∈ input.analyzeLocalizedOrdinaryMonocyclicEZ fuel := by
  simp [analyzeLocalizedScheduledStereochemistry]

theorem oddCumuleneEZ_mem_analyzeLocalizedScheduledStereochemistry_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel) :
    LocalizedScheduledStereochemicalAssignment.oddCumuleneEZ assignment ∈
        input.analyzeLocalizedScheduledStereochemistry fuel ↔
      assignment ∈ input.analyzeLocalizedOddCumuleneEZ fuel := by
  simp [analyzeLocalizedScheduledStereochemistry]

/-! ## Global duplicate-freedom and exact physical units -/

/-- The complete four-family scheduled descriptor list is duplicate-free. -/
theorem analyzeLocalizedScheduledStereochemistry_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.analyzeLocalizedScheduledStereochemistry fuel).Nodup := by
  classical
  simp only [analyzeLocalizedScheduledStereochemistry, List.nodup_append]
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · exact (input.analyzeLocalizedScheduledTetrahedralSpatial_nodup fuel).map
      (by intro left right equal; cases equal; rfl)
  · exact (input.analyzeLocalizedEvenCumuleneAxial_nodup fuel).map
      (by intro left right equal; cases equal; rfl)
  · intro left leftPresent right rightPresent equal
    simp only [List.mem_map] at leftPresent rightPresent
    rcases leftPresent with ⟨leftSource, _leftSourcePresent, leftIdentity⟩
    rcases rightPresent with ⟨rightSource, _rightSourcePresent, rightIdentity⟩
    subst left
    subst right
    contradiction
  · exact (input.analyzeLocalizedOrdinaryMonocyclicEZ_nodup fuel).map
      (by intro left right equal; cases equal; rfl)
  · intro left leftPresent right rightPresent equal
    simp only [List.mem_append, List.mem_map] at leftPresent
    rcases leftPresent with
      (⟨leftSource, _leftSourcePresent, leftIdentity⟩ |
       ⟨leftSource, _leftSourcePresent, leftIdentity⟩)
    · subst left
      simp only [List.mem_map] at rightPresent
      rcases rightPresent with ⟨rightSource, _rightSourcePresent, rightIdentity⟩
      subst right
      contradiction
    · subst left
      simp only [List.mem_map] at rightPresent
      rcases rightPresent with ⟨rightSource, _rightSourcePresent, rightIdentity⟩
      subst right
      contradiction
  · exact (input.analyzeLocalizedOddCumuleneEZ_nodup fuel).map
      (by intro left right equal; cases equal; rfl)
  · intro left leftPresent right rightPresent equal
    simp only [List.mem_append, List.mem_map] at leftPresent
    rcases leftPresent with
      ((⟨leftSource, _leftSourcePresent, leftIdentity⟩ |
        ⟨leftSource, _leftSourcePresent, leftIdentity⟩) |
       ⟨leftSource, _leftSourcePresent, leftIdentity⟩)
    · subst left
      simp only [List.mem_map] at rightPresent
      rcases rightPresent with ⟨rightSource, _rightSourcePresent, rightIdentity⟩
      subst right
      contradiction
    · subst left
      simp only [List.mem_map] at rightPresent
      rcases rightPresent with ⟨rightSource, _rightSourcePresent, rightIdentity⟩
      subst right
      contradiction
    · subst left
      simp only [List.mem_map] at rightPresent
      rcases rightPresent with ⟨rightSource, _rightSourcePresent, rightIdentity⟩
      subst right
      contradiction

/-- Disjoint canonical physical-unit identity for the four scheduled descriptor families. -/
inductive LocalizedScheduledStereochemicalPhysicalUnit
    (input : CertifiedLocalizedCIPInput) where
  | tetrahedral (center : input.TetrahedralCenter)
  | evenAxial (axis : input.LocalizedEvenAxialChain)
  | ordinaryMonocyclicEZ (bond : input.LocalizedCanonicalDoubleBond)
  | oddCumuleneEZ (axis : input.LocalizedOddCumuleneChain)
  deriving DecidableEq

/-- Forget a scheduled descriptor payload while retaining its exact canonical physical unit. -/
def LocalizedScheduledStereochemicalAssignment.physicalUnit
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (assignment : input.LocalizedScheduledStereochemicalAssignment fuel) :
    input.LocalizedScheduledStereochemicalPhysicalUnit :=
  match assignment with
  | .tetrahedral source => .tetrahedral source.center
  | .evenAxial source => .evenAxial source.axis
  | .ordinaryMonocyclicEZ source => .ordinaryMonocyclicEZ source.bond
  | .oddCumuleneEZ source => .oddCumuleneEZ source.axis

/-- The complete public result cannot duplicate any canonical physical stereogenic unit. -/
theorem analyzeLocalizedScheduledStereochemistry_physicalUnits_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    ((input.analyzeLocalizedScheduledStereochemistry fuel).map
      LocalizedScheduledStereochemicalAssignment.physicalUnit).Nodup := by
  classical
  simp only [analyzeLocalizedScheduledStereochemistry, List.map_append, List.map_map,
    Function.comp_def, LocalizedScheduledStereochemicalAssignment.physicalUnit,
    List.nodup_append]
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using
      (input.analyzeLocalizedScheduledTetrahedralSpatial_centers_nodup fuel).map
        (by
          intro left right equal
          exact LocalizedScheduledStereochemicalPhysicalUnit.tetrahedral.inj equal)
  · simpa [List.map_map, Function.comp_def] using
      (input.analyzeLocalizedEvenCumuleneAxial_axes_nodup fuel).map
        (by
          intro left right equal
          exact LocalizedScheduledStereochemicalPhysicalUnit.evenAxial.inj equal)
  · intro left leftPresent right rightPresent equal
    simp only [List.mem_map] at leftPresent rightPresent
    rcases leftPresent with ⟨leftSource, _leftPresent, leftIdentity⟩
    rcases rightPresent with ⟨rightSource, _rightPresent, rightIdentity⟩
    subst left
    subst right
    contradiction
  · simpa [List.map_map, Function.comp_def] using
      (input.analyzeLocalizedOrdinaryMonocyclicEZ_bonds_nodup fuel).map
        (by
          intro left right equal
          exact LocalizedScheduledStereochemicalPhysicalUnit.ordinaryMonocyclicEZ.inj equal)
  · intro left leftPresent right rightPresent equal
    simp only [List.mem_append, List.mem_map] at leftPresent
    rcases leftPresent with
      (⟨leftSource, _leftPresent, leftIdentity⟩ |
       ⟨leftSource, _leftPresent, leftIdentity⟩)
    · subst left
      simp only [List.mem_map] at rightPresent
      rcases rightPresent with ⟨rightSource, _rightPresent, rightIdentity⟩
      subst right
      contradiction
    · subst left
      simp only [List.mem_map] at rightPresent
      rcases rightPresent with ⟨rightSource, _rightPresent, rightIdentity⟩
      subst right
      contradiction
  · simpa [List.map_map, Function.comp_def] using
      (input.analyzeLocalizedOddCumuleneEZ_axes_nodup fuel).map
        (by
          intro left right equal
          exact LocalizedScheduledStereochemicalPhysicalUnit.oddCumuleneEZ.inj equal)
  · intro left leftPresent right rightPresent equal
    simp only [List.mem_append, List.mem_map] at leftPresent
    rcases leftPresent with
      ((⟨leftSource, _leftPresent, leftIdentity⟩ |
        ⟨leftSource, _leftPresent, leftIdentity⟩) |
       ⟨leftSource, _leftPresent, leftIdentity⟩)
    · subst left
      simp only [List.mem_map] at rightPresent
      rcases rightPresent with ⟨rightSource, _rightPresent, rightIdentity⟩
      subst right
      contradiction
    · subst left
      simp only [List.mem_map] at rightPresent
      rcases rightPresent with ⟨rightSource, _rightPresent, rightIdentity⟩
      subst right
      contradiction
    · subst left
      simp only [List.mem_map] at rightPresent
      rcases rightPresent with ⟨rightSource, _rightPresent, rightIdentity⟩
      subst right
      contradiction

/-- Every public scheduled assignment's exact physical unit occurs literally once. -/
theorem scheduledStereochemicalAssignment_physicalUnit_count_eq_one
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedScheduledStereochemicalAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedScheduledStereochemistry fuel) :
    List.count assignment.physicalUnit
      ((input.analyzeLocalizedScheduledStereochemistry fuel).map
        LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  exact List.count_eq_one_of_mem
    (input.analyzeLocalizedScheduledStereochemistry_physicalUnits_nodup fuel)
    (List.mem_map.mpr ⟨assignment, present, rfl⟩)

/-- A tetrahedral family member's canonical center occurs once in the complete public result. -/
theorem tetrahedral_physicalUnit_count_eq_one_of_mem
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedScheduledTetrahedralSpatialAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedScheduledTetrahedralSpatial fuel) :
    List.count (.tetrahedral assignment.center)
      ((input.analyzeLocalizedScheduledStereochemistry fuel).map
        LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  exact input.scheduledStereochemicalAssignment_physicalUnit_count_eq_one fuel
    (.tetrahedral assignment)
    ((input.tetrahedral_mem_analyzeLocalizedScheduledStereochemistry_iff
      fuel assignment).mpr present)

/-- An even-axial family member's canonical axis occurs once in the complete public result. -/
theorem evenAxial_physicalUnit_count_eq_one_of_mem
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedEvenCumuleneAxial fuel) :
    List.count (.evenAxial assignment.axis)
      ((input.analyzeLocalizedScheduledStereochemistry fuel).map
        LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  exact input.scheduledStereochemicalAssignment_physicalUnit_count_eq_one fuel
    (.evenAxial assignment)
    ((input.evenAxial_mem_analyzeLocalizedScheduledStereochemistry_iff
      fuel assignment).mpr present)

/-- An ordinary-monocyclic family member's canonical bond occurs once in the public result. -/
theorem ordinaryMonocyclicEZ_physicalUnit_count_eq_one_of_mem
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedOrdinaryMonocyclicEZ fuel) :
    List.count (.ordinaryMonocyclicEZ assignment.bond)
      ((input.analyzeLocalizedScheduledStereochemistry fuel).map
        LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  exact input.scheduledStereochemicalAssignment_physicalUnit_count_eq_one fuel
    (.ordinaryMonocyclicEZ assignment)
    ((input.ordinaryMonocyclicEZ_mem_analyzeLocalizedScheduledStereochemistry_iff
      fuel assignment).mpr present)

/-- An odd-cumulene family member's canonical axis occurs once in the complete public result. -/
theorem oddCumuleneEZ_physicalUnit_count_eq_one_of_mem
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedOddCumuleneEZ fuel) :
    List.count (.oddCumuleneEZ assignment.axis)
      ((input.analyzeLocalizedScheduledStereochemistry fuel).map
        LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  exact input.scheduledStereochemicalAssignment_physicalUnit_count_eq_one fuel
    (.oddCumuleneEZ assignment)
    ((input.oddCumuleneEZ_mem_analyzeLocalizedScheduledStereochemistry_iff
      fuel assignment).mpr present)

/-! ## Direct transport from successful local computations -/

/-- A successful scheduled tetrahedral computation yields exact-once center coverage in the
complete four-family result. -/
theorem localizedScheduledTetrahedral_success_physicalUnit_count_eq_one
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter)
    (assignment : input.LocalizedScheduledTetrahedralSpatialAssignment fuel)
    (computed : input.localizedScheduledTetrahedralSpatialAssignmentAt?
      fuel center = some assignment) :
    List.count (.tetrahedral center)
      ((input.analyzeLocalizedScheduledStereochemistry fuel).map
        LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  have retained := input.localizedScheduledTetrahedralSpatialAssignmentAt?_center
    fuel center assignment computed
  have present : assignment ∈
      input.analyzeLocalizedScheduledTetrahedralSpatial fuel :=
    (input.mem_analyzeLocalizedScheduledTetrahedralSpatial_iff fuel assignment).mpr (by
      rw [retained]
      exact computed)
  simpa [retained] using
    input.tetrahedral_physicalUnit_count_eq_one_of_mem fuel assignment present

/-- A successful scheduled even-cumulene computation yields exact-once canonical-axis coverage
in the complete four-family result. -/
theorem localizedEvenAxial_success_physicalUnit_count_eq_one
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain)
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel)
    (computed : input.localizedEvenAxialSpatialAssignmentAtWithState? fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) axis =
        some assignment) :
    List.count (.evenAxial axis)
      ((input.analyzeLocalizedScheduledStereochemistry fuel).map
        LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  have retained := input.localizedEvenAxialSpatialAssignmentAtWithState?_axis fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
    axis assignment computed
  have present : assignment ∈ input.analyzeLocalizedEvenCumuleneAxial fuel :=
    (input.mem_analyzeLocalizedEvenCumuleneAxialWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) assignment).mpr (by
        rw [retained]
        exact computed)
  simpa [retained] using
    input.evenAxial_physicalUnit_count_eq_one_of_mem fuel assignment present

/-- A successful scheduled ordinary-monocyclic computation yields exact-once canonical-bond
coverage in the complete four-family result. -/
theorem localizedOrdinaryMonocyclicEZ_success_publicPhysicalUnit_count_eq_one
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond)
    (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel)
    (computed : input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState? fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) bond =
        some assignment) :
    List.count (.ordinaryMonocyclicEZ bond)
      ((input.analyzeLocalizedScheduledStereochemistry fuel).map
        LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  have retained := input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_bond fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
    bond assignment computed
  have present : assignment ∈ input.analyzeLocalizedOrdinaryMonocyclicEZ fuel :=
    (input.mem_analyzeLocalizedOrdinaryMonocyclicEZWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) assignment).mpr (by
        rw [retained]
        exact computed)
  simpa [retained] using
    input.ordinaryMonocyclicEZ_physicalUnit_count_eq_one_of_mem fuel assignment present

/-- Cursor-free ordinary-monocyclic chemical readiness yields one independently conforming
assignment in the complete four-family public list, with literal public physical-unit count one. -/
theorem every_dependencyResolved_localizedOrdinaryMonocyclicEZ_public_exactly_once
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond)
    (evidence : input.LocalizedOrdinaryMonocyclicProductionDependencyEvidenceWithState fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) bond) :
    ∃ assignment,
      LocalizedScheduledStereochemicalAssignment.ordinaryMonocyclicEZ assignment ∈
          input.analyzeLocalizedScheduledStereochemistry fuel ∧
        input.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignment fuel assignment ∧
        List.count (.ordinaryMonocyclicEZ bond)
          ((input.analyzeLocalizedScheduledStereochemistry fuel).map
            LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  obtain ⟨assignment, retained, familyPresent, derived, _familyCount⟩ :=
    input.every_dependencyResolved_localizedOrdinaryMonocyclicEZ_occurs_exactly_once
      fuel bond evidence
  exact ⟨assignment,
    (input.ordinaryMonocyclicEZ_mem_analyzeLocalizedScheduledStereochemistry_iff
      fuel assignment).mpr familyPresent,
    derived,
    by simpa [retained] using
      input.ordinaryMonocyclicEZ_physicalUnit_count_eq_one_of_mem
        fuel assignment familyPresent⟩

/-- A successful scheduled odd-cumulene computation yields exact-once canonical-axis coverage
in the complete four-family result. -/
theorem localizedOddCumuleneEZ_success_physicalUnit_count_eq_one
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedOddCumuleneChain)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel)
    (computed : input.localizedOddCumuleneEZSpatialAssignmentAtWithState? fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) axis =
        some assignment) :
    List.count (.oddCumuleneEZ axis)
      ((input.analyzeLocalizedScheduledStereochemistry fuel).map
        LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  have retained := input.localizedOddCumuleneEZSpatialAssignmentAtWithState?_axis fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
    axis assignment computed
  have present : assignment ∈ input.analyzeLocalizedOddCumuleneEZ fuel :=
    (input.mem_analyzeLocalizedOddCumuleneEZWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) assignment).mpr (by
        rw [retained]
        exact computed)
  simpa [retained] using
    input.oddCumuleneEZ_physicalUnit_count_eq_one_of_mem fuel assignment present

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
