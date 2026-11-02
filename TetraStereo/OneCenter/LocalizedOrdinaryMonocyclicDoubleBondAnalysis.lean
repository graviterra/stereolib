import TetraStereo.OneCenter.LocalizedCyclicDoubleBondDescriptor
import TetraStereo.OneCenter.LocalizedCyclicCumuleneAuthorityAnalysis
import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialAnalysis
import TetraStereo.OneCenter.LocalizedOddCumuleneAnalysis
import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3FuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecule-wide ordinary-monocyclic double-bond analysis

Every physical order-two bond is represented once by the canonical lower-to-higher atom-root
occurrence. Whole-molecule exact monocycle perception is applied before cumulative-chain
classification, so cycloalkenes whose ring closes through single bonds receive the P-91/P-93
omission or required-`E/Z` policy. Required assignments use the same decreasing descriptor-bearing
Rules-1a--5 endpoint-frame builder as the scheduled tetrahedral and axial paths.
-/

namespace CertifiedLocalizedCIPInput

/-- One final ordinary-monocyclic `E/Z` assignment, retaining its unique canonical physical bond
and the complete production result/certificate payload. -/
structure LocalizedOrdinaryMonocyclicEZSpatialAssignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  bond : input.LocalizedCanonicalDoubleBond
  result : input.LocalizedRule3OrdinaryMonocyclicEZResult fuel

/-- Analyze one canonical physical double bond against an arbitrary complete auxiliary state. -/
noncomputable def localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond) :
    Option (input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel) :=
  let target := input.localizedAtomRootOccurrence fuel bond.1.1
  let occurrence := input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond
  let view := input.localizedDependencyView state target
  (input.localizedRule3OrdinaryMonocyclicEZWith?
      target occurrence view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view
          (localizedDescriptorBearingRule3EvaluationFuel fuel))).map fun result =>
    { bond, result }

/-- Independent meaning of a state-parameterized molecule-wide cyclic assignment. -/
def DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignmentWithState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel) : Prop :=
  let target := input.localizedAtomRootOccurrence fuel assignment.bond.1.1
  let occurrence :=
    input.localizedCanonicalDoubleBondFirstChildOccurrence fuel assignment.bond
  let view := input.localizedDependencyView state target
  input.DeclarativeLocalizedRule3OrdinaryMonocyclicEZWith
    target occurrence view
      (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view
        (localizedDescriptorBearingRule3EvaluationFuel fuel))
      assignment.result

/-- A successful one-bond analysis retains exactly the canonical bond supplied to it. -/
theorem localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_bond
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond)
    (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel)
    (computed : input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?
      fuel state bond = some assignment) :
    assignment.bond = bond := by
  unfold localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState? at computed
  dsimp only at computed
  cases resultComputed : input.localizedRule3OrdinaryMonocyclicEZWith?
      (input.localizedAtomRootOccurrence fuel bond.1.1)
      (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond)
      (input.localizedDependencyView state
        (input.localizedAtomRootOccurrence fuel bond.1.1))
      (input.buildLocalizedDescriptorBearingRule3Frame?
        (input.localizedAtomRootOccurrence fuel bond.1.1)
        (input.localizedDependencyView state
          (input.localizedAtomRootOccurrence fuel bond.1.1))
        (localizedDescriptorBearingRule3EvaluationFuel fuel)) with
  | none => simp [resultComputed] at computed
  | some result =>
      simp [resultComputed] at computed
      subst assignment
      rfl

/-- Every emitted one-bond assignment has exact physical topology, whole-molecule monocycle
policy, complete endpoint priorities, rational geometry, and independent P-93 `E/Z` meaning. -/
theorem localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_sound
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond)
    (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel)
    (computed : input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?
      fuel state bond = some assignment) :
    input.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignmentWithState
      fuel state assignment := by
  unfold localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState? at computed
  dsimp only at computed
  let target := input.localizedAtomRootOccurrence fuel bond.1.1
  let occurrence := input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond
  let view := input.localizedDependencyView state target
  let frameOf := input.buildLocalizedDescriptorBearingRule3Frame?
    target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
  cases resultComputed : input.localizedRule3OrdinaryMonocyclicEZWith?
      target occurrence view frameOf with
  | none => simp [target, occurrence, view, frameOf, resultComputed] at computed
  | some result =>
      simp [target, occurrence, view, frameOf, resultComputed] at computed
      subst assignment
      exact input.localizedRule3OrdinaryMonocyclicEZWith?_sound
        target occurrence view frameOf
        (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view
          (localizedDescriptorBearingRule3EvaluationFuel fuel))
        (fun cursors frame frameComputed =>
          input.buildLocalizedDescriptorBearingRule3Frame?_sound
            target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
              cursors frame frameComputed)
        result resultComputed

/-- A canonical bond belonging to a multi-bond cumulative frame cannot be emitted by the ordinary
per-bond monocycle analyzer.  Its configuration remains owned by the even/odd cumulene path. -/
theorem localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_eq_none_of_cumulated
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond)
    (axis : input.LocalizedRule3CumulatedEndpointCursorFrame fuel)
    (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel fuel)
      (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond) = some axis)
    (cumulated : axis.doubleBondCount ≠ 1) :
    input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?
      fuel state bond = none := by
  have routedNone :=
    input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?_eq_none_of_cumulated
      (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond)
      axis axisComputed cumulated
  simp [localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?,
    localizedRule3OrdinaryMonocyclicEZWith?, routedNone]

/-- A canonical occurrence with no complete terminal-start cumulative frame cannot emit through
the ordinary per-bond monocycle analyzer. -/
theorem localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_eq_none_of_no_axis
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond)
    (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel fuel)
      (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond) = none) :
    input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?
      fuel state bond = none := by
  have routedNone :=
    input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?_eq_none_of_no_axis
      (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond) axisComputed
  simp [localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?,
    localizedRule3OrdinaryMonocyclicEZWith?, routedNone]

/-- Whole-molecule ordinary-monocyclic analysis against a supplied auxiliary state. -/
noncomputable def analyzeLocalizedOrdinaryMonocyclicEZWithState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) :
    List (input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel) :=
  input.localizedCanonicalDoubleBondPairs.attach.filterMap fun bond =>
    input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState? fuel state bond

/-- Exact membership in the state-parameterized whole-molecule cyclic analyzer. -/
theorem mem_analyzeLocalizedOrdinaryMonocyclicEZWithState_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel) :
    assignment ∈ input.analyzeLocalizedOrdinaryMonocyclicEZWithState fuel state ↔
      input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?
        fuel state assignment.bond = some assignment := by
  classical
  constructor
  · intro present
    rw [analyzeLocalizedOrdinaryMonocyclicEZWithState, List.mem_filterMap] at present
    obtain ⟨bond, _bondPresent, emitted⟩ := present
    cases resultComputed : input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?
        fuel state bond with
    | none => simp [resultComputed] at emitted
    | some result =>
        simp [resultComputed] at emitted
        subst assignment
        rw [input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_bond
          fuel state bond result resultComputed]
        exact resultComputed
  · intro emitted
    rw [analyzeLocalizedOrdinaryMonocyclicEZWithState, List.mem_filterMap]
    exact ⟨assignment.bond, by simp, by simp [emitted]⟩

/-- Every member of the state-parameterized whole-molecule cyclic list is independently sound. -/
theorem analyzeLocalizedOrdinaryMonocyclicEZWithState_member_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel)
    (present : assignment ∈
      input.analyzeLocalizedOrdinaryMonocyclicEZWithState fuel state) :
    input.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignmentWithState
      fuel state assignment :=
  input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_sound
    fuel state assignment.bond assignment
      ((input.mem_analyzeLocalizedOrdinaryMonocyclicEZWithState_iff
        fuel state assignment).mp present)

/-- Scheduled molecule-wide ordinary-monocyclic `E/Z` analyzer. -/
noncomputable def analyzeLocalizedOrdinaryMonocyclicEZ
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    List (input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel) :=
  input.analyzeLocalizedOrdinaryMonocyclicEZWithState fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)

/-- Independent meaning under the canonical causal Rules-1a--5 scheduler state. -/
def DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel) : Prop :=
  input.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignmentWithState fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) assignment

/-- Every final cyclic `E/Z` emitted by the scheduled whole-molecule path is independently
correct from molecular topology through final descriptor. -/
theorem analyzeLocalizedOrdinaryMonocyclicEZ_member_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedOrdinaryMonocyclicEZ fuel) :
    input.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignment fuel assignment :=
  input.analyzeLocalizedOrdinaryMonocyclicEZWithState_member_conforms fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
    assignment present

/-! ## Enlarged scheduled public result -/

/-- Currently integrated scheduled final families, now including ordinary monocyclic `E/Z`. -/
inductive LocalizedScheduledStereochemicalAssignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  | tetrahedral (assignment : input.LocalizedScheduledTetrahedralSpatialAssignment fuel)
  | evenAxial (assignment : input.LocalizedEvenAxialSpatialAssignment fuel)
  | ordinaryMonocyclicEZ
      (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel)
  | oddCumuleneEZ
      (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel)

/-- One public list for all currently integrated scheduled descriptor families. -/
noncomputable def analyzeLocalizedScheduledStereochemistry
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    List (input.LocalizedScheduledStereochemicalAssignment fuel) :=
  (input.analyzeLocalizedScheduledTetrahedralSpatial fuel).map
      LocalizedScheduledStereochemicalAssignment.tetrahedral ++
    (input.analyzeLocalizedEvenCumuleneAxial fuel).map
      LocalizedScheduledStereochemicalAssignment.evenAxial ++
    (input.analyzeLocalizedOrdinaryMonocyclicEZ fuel).map
      LocalizedScheduledStereochemicalAssignment.ordinaryMonocyclicEZ ++
    (input.analyzeLocalizedOddCumuleneEZ fuel).map
      LocalizedScheduledStereochemicalAssignment.oddCumuleneEZ

/-- Independent family-disjoint meaning of the enlarged scheduled public result. -/
inductive DeclarativeLocalizedScheduledStereochemicalAssignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedScheduledStereochemicalAssignment fuel → Prop
  | tetrahedral {assignment}
      (derived : input.DeclarativeLocalizedScheduledTetrahedralSpatialAssignment
        fuel assignment) :
      input.DeclarativeLocalizedScheduledStereochemicalAssignment fuel
        (.tetrahedral assignment)
  | evenAxial {assignment}
      (derived : input.DeclarativeLocalizedEvenAxialSpatialAssignment fuel assignment) :
      input.DeclarativeLocalizedScheduledStereochemicalAssignment fuel
        (.evenAxial assignment)
  | ordinaryMonocyclicEZ {assignment}
      (derived : input.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignment
        fuel assignment) :
      input.DeclarativeLocalizedScheduledStereochemicalAssignment fuel
        (.ordinaryMonocyclicEZ assignment)
  | oddCumuleneEZ {assignment}
      (derived : input.DeclarativeLocalizedOddCumuleneEZSpatialAssignment
        fuel assignment) :
      input.DeclarativeLocalizedScheduledStereochemicalAssignment fuel
        (.oddCumuleneEZ assignment)

/-- Every descriptor in the enlarged final scheduled list conforms to its independent family
specification. -/
theorem analyzeLocalizedScheduledStereochemistry_member_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedScheduledStereochemicalAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedScheduledStereochemistry fuel) :
    input.DeclarativeLocalizedScheduledStereochemicalAssignment fuel assignment := by
  rw [analyzeLocalizedScheduledStereochemistry, List.mem_append] at present
  rcases present with old | odd
  · rw [List.mem_append] at old
    rcases old with older | cyclic
    · rw [List.mem_append] at older
      rcases older with tetrahedral | axial
      · rw [List.mem_map] at tetrahedral
        rcases tetrahedral with ⟨source, sourcePresent, identity⟩
        subst assignment
        exact .tetrahedral
          (input.analyzeLocalizedScheduledTetrahedralSpatial_member_conforms
            fuel source sourcePresent)
      · rw [List.mem_map] at axial
        rcases axial with ⟨source, sourcePresent, identity⟩
        subst assignment
        exact .evenAxial
          (input.analyzeLocalizedEvenCumuleneAxial_member_conforms
            fuel source sourcePresent)
    · rw [List.mem_map] at cyclic
      rcases cyclic with ⟨source, sourcePresent, identity⟩
      subst assignment
      exact .ordinaryMonocyclicEZ
        (input.analyzeLocalizedOrdinaryMonocyclicEZ_member_conforms
          fuel source sourcePresent)
  · rw [List.mem_map] at odd
    rcases odd with ⟨source, sourcePresent, identity⟩
    subst assignment
    exact .oddCumuleneEZ
      (input.analyzeLocalizedOddCumuleneEZ_member_conforms
        fuel source sourcePresent)

/-! ## Public analysis entries retaining recognized nonassignment boundaries -/

/-- Public scheduled output with an explicit branch for recognized fully cyclic cumulenes that
lie outside the transcribed P-93 open-terminal descriptor provisions.  Descriptor assignments
remain a separate constructor, so this type cannot confuse a boundary report with an emitted
stereodescriptor. -/
inductive LocalizedScheduledStereochemicalAnalysisEntry
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  | descriptorAssignment
      (assignment : input.LocalizedScheduledStereochemicalAssignment fuel)
  | fullyCyclicCumuleneBoundary
      (boundary : input.LocalizedFullyCyclicCumuleneAuthorityBoundary)

/-- Public scheduled analysis enriched with every exact fully cyclic cumulene authority
boundary. -/
noncomputable def analyzeLocalizedScheduledStereochemistryWithAuthorityBoundaries
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    List (input.LocalizedScheduledStereochemicalAnalysisEntry fuel) :=
  (input.analyzeLocalizedScheduledStereochemistry fuel).map
      LocalizedScheduledStereochemicalAnalysisEntry.descriptorAssignment ++
    input.analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries.map
      LocalizedScheduledStereochemicalAnalysisEntry.fullyCyclicCumuleneBoundary

/-- Independent disjoint meaning of an enriched public analysis entry. -/
inductive DeclarativeLocalizedScheduledStereochemicalAnalysisEntry
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedScheduledStereochemicalAnalysisEntry fuel → Prop
  | descriptorAssignment {assignment}
      (derived : input.DeclarativeLocalizedScheduledStereochemicalAssignment
        fuel assignment) :
      input.DeclarativeLocalizedScheduledStereochemicalAnalysisEntry fuel
        (.descriptorAssignment assignment)
  | fullyCyclicCumuleneBoundary {boundary}
      (derived : input.DeclarativeLocalizedFullyCyclicCumuleneAuthorityBoundary boundary) :
      input.DeclarativeLocalizedScheduledStereochemicalAnalysisEntry fuel
        (.fullyCyclicCumuleneBoundary boundary)

/-- Every descriptor or recognized nonassignment boundary in the enriched public output has its
independent family meaning. -/
theorem analyzeLocalizedScheduledStereochemistryWithAuthorityBoundaries_member_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (entry : input.LocalizedScheduledStereochemicalAnalysisEntry fuel)
    (present : entry ∈
      input.analyzeLocalizedScheduledStereochemistryWithAuthorityBoundaries fuel) :
    input.DeclarativeLocalizedScheduledStereochemicalAnalysisEntry fuel entry := by
  rw [analyzeLocalizedScheduledStereochemistryWithAuthorityBoundaries,
    List.mem_append] at present
  rcases present with assignmentPresent | boundaryPresent
  · rw [List.mem_map] at assignmentPresent
    rcases assignmentPresent with ⟨assignment, sourcePresent, identity⟩
    subst entry
    exact .descriptorAssignment
      (input.analyzeLocalizedScheduledStereochemistry_member_conforms
        fuel assignment sourcePresent)
  · rw [List.mem_map] at boundaryPresent
    rcases boundaryPresent with ⟨boundary, sourcePresent, identity⟩
    subst entry
    exact .fullyCyclicCumuleneBoundary
      (input.analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries_member_conforms
        boundary sourcePresent)

/-- The enriched output contains a fully cyclic boundary exactly when that boundary satisfies
the independent all-double-component and P-93 non-applicability relation. -/
theorem fullyCyclicCumuleneBoundary_mem_scheduledAnalysis_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (boundary : input.LocalizedFullyCyclicCumuleneAuthorityBoundary) :
    LocalizedScheduledStereochemicalAnalysisEntry.fullyCyclicCumuleneBoundary boundary ∈
        input.analyzeLocalizedScheduledStereochemistryWithAuthorityBoundaries fuel ↔
      input.DeclarativeLocalizedFullyCyclicCumuleneAuthorityBoundary boundary := by
  classical
  simp [analyzeLocalizedScheduledStereochemistryWithAuthorityBoundaries,
    input.mem_analyzeLocalizedFullyCyclicCumuleneAuthorityBoundaries_iff]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
