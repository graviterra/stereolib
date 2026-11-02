import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialDescriptor
import TetraStereo.OneCenter.LocalizedOccurrenceDescriptorBearingRule3Through5FixedPoint
import TetraStereo.OneCenter.P93AcyclicConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecule-wide localized even-cumulene axial analysis

This module closes the carrier-to-descriptor integration boundary for open even cumulenes.  Each
independently perceived canonical axis supplies an actual terminal-root occurrence and its real
zero-copy first-axis child.  The complete occurrence-local Rules-1a--5 evaluator then ranks both
terminal substituent pairs using the causal descriptor-bearing fixed-point state, and exact
rational spatial evidence determines `Rₐ` or `Sₐ`.

The analyzer remains deliberately fail-closed: an axis with tied terminal priorities, absent
semantic coordinates, or zero axial chirality measure emits no assignment.
-/

/-! ## P-93.4.2.2 preferred descriptor conversion -/

/-- Production conversion from the internally proved axial CIP descriptor to the descriptor
family preferred by P-93.4.2.2 for preferred IUPAC names.  This is intentionally separate from
the P-93 reference conversion so that their agreement is a theorem rather than a definition. -/
def AxialDescriptor.toPreferredP93 : AxialDescriptor → BlueBookP93.Acyclic.Descriptor
  | .Ra => .M
  | .Sa => .P

/-- Embed the production `Rₐ/Sₐ` value into the independent P-93 descriptor universe. -/
def AxialDescriptor.toGeneralP93 : AxialDescriptor → BlueBookP93.Acyclic.Descriptor
  | .Ra => .Ra
  | .Sa => .Sa

/-- The production conversion agrees exactly with the independently transcribed axial
correspondence in P-92.1.2.2.3 and P-93.4.2.2. -/
theorem AxialDescriptor.toPreferredP93_conforms (descriptor : AxialDescriptor) :
    BlueBookP93.Acyclic.EvenCumuleneAxialDescriptorCorrespondence
      descriptor.toGeneralP93 descriptor.toPreferredP93 := by
  cases descriptor <;> trivial

/-- The production conversion also agrees extensionally with the independent executable P-93
conversion, including its explicit `Option` domain boundary. -/
theorem AxialDescriptor.toPreferredP93_exact (descriptor : AxialDescriptor) :
    BlueBookP93.Acyclic.preferredEvenCumuleneAxialDescriptor?
        descriptor.toGeneralP93 =
      some descriptor.toPreferredP93 := by
  cases descriptor <;> rfl

/-- Every preferred descriptor emitted by the production conversion is applicable to an even
cumulene and recommended in a preferred IUPAC name. -/
theorem AxialDescriptor.toPreferredP93_recommended (descriptor : AxialDescriptor) :
    BlueBookP93.Acyclic.DescriptorApplies
        .evenDoubleBondCumulene descriptor.toPreferredP93 ∧
      BlueBookP93.Acyclic.DescriptorRecommended
        .preferredIUPACName .evenDoubleBondCumulene descriptor.toPreferredP93 := by
  exact BlueBookP93.Acyclic.preferredEvenCumuleneAxialDescriptor?_recommended
    descriptor.toGeneralP93 descriptor.toPreferredP93 descriptor.toPreferredP93_exact

namespace CertifiedLocalizedCIPInput

open DeclarativeCIP

/-- The canonical causal auxiliary state for descriptor-bearing localized Rules 1a--5. -/
noncomputable def localizedDescriptorBearingRule3Through5SchedulerState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedAuxiliaryState fuel :=
  OccurrenceScheduler.decode
    (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel))
    (@input.LocalizedDepthDependency fuel)
    (OccurrenceScheduler.closure
      (input.localizedAuxiliaryOccurrenceSystem
        (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel))
      (@input.LocalizedDepthDependency fuel))

/-- The canonical scheduler state is a model of the independently specified descriptor-bearing
Rules-1a--5 occurrence semantics. -/
theorem localizedDescriptorBearingRule3Through5SchedulerState_cipModel
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)).CIPModel
        (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) := by
  exact input.localizedOccurrenceDescriptorBearingRule3Through5SchedulerClosure_cipModel fuel

/-- Public molecule-wide axial result, retaining the exact perceived chain that generated it. -/
structure LocalizedEvenAxialSpatialAssignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  axis : input.LocalizedEvenAxialChain
  result : input.LocalizedEvenCumuleneAxialResult fuel

/-- Analyze one perceived canonical even axis against an arbitrary complete auxiliary state. -/
noncomputable def localizedEvenAxialSpatialAssignmentAtWithState?
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedEvenAxialChain) :
    Option (input.LocalizedEvenAxialSpatialAssignment fuel) :=
  let target := input.localizedEvenAxialRootOccurrence fuel axis
  let occurrence := input.localizedEvenAxialFirstChildOccurrence fuel axis
  (input.localizedEvenCumuleneAxialAssignment? target occurrence
      (input.localizedDependencyView state target)).map fun result =>
    { axis, result }

/-- Independent meaning of a one-axis result: complete perceived topology, complete endpoint
Rules-1a--5 keys under the restricted state view, and exact P-92 axial geometry. -/
def DeclarativeLocalizedEvenAxialSpatialAssignmentWithState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel) : Prop :=
  let target := input.localizedEvenAxialRootOccurrence fuel assignment.axis
  let occurrence := input.localizedEvenAxialFirstChildOccurrence fuel assignment.axis
  input.DeclarativeLocalizedEvenCumuleneAxialAssignment
    target occurrence (input.localizedDependencyView state target) assignment.result

/-- A successful one-axis call retains exactly the perceived axis supplied to it. -/
theorem localizedEvenAxialSpatialAssignmentAtWithState?_axis
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedEvenAxialChain)
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel)
    (computed : input.localizedEvenAxialSpatialAssignmentAtWithState?
      fuel state axis = some assignment) :
    assignment.axis = axis := by
  unfold localizedEvenAxialSpatialAssignmentAtWithState? at computed
  dsimp only at computed
  cases resultComputed : input.localizedEvenCumuleneAxialAssignment?
      (input.localizedEvenAxialRootOccurrence fuel axis)
      (input.localizedEvenAxialFirstChildOccurrence fuel axis)
      (input.localizedDependencyView state
        (input.localizedEvenAxialRootOccurrence fuel axis)) with
  | none => simp [resultComputed] at computed
  | some result =>
      simp [resultComputed] at computed
      subst assignment
      rfl

/-- Every one-axis emitted result satisfies the independent topology, priority, and geometry
specification. -/
theorem localizedEvenAxialSpatialAssignmentAtWithState?_sound
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedEvenAxialChain)
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel)
    (computed : input.localizedEvenAxialSpatialAssignmentAtWithState?
      fuel state axis = some assignment) :
    input.DeclarativeLocalizedEvenAxialSpatialAssignmentWithState
      fuel state assignment := by
  unfold localizedEvenAxialSpatialAssignmentAtWithState? at computed
  dsimp only at computed
  cases resultComputed : input.localizedEvenCumuleneAxialAssignment?
      (input.localizedEvenAxialRootOccurrence fuel axis)
      (input.localizedEvenAxialFirstChildOccurrence fuel axis)
      (input.localizedDependencyView state
        (input.localizedEvenAxialRootOccurrence fuel axis)) with
  | none => simp [resultComputed] at computed
  | some result =>
      simp [resultComputed] at computed
      subst assignment
      exact input.localizedEvenCumuleneAxialAssignment?_sound
        (input.localizedEvenAxialRootOccurrence fuel axis)
        (input.localizedEvenAxialFirstChildOccurrence fuel axis)
        (input.localizedDependencyView state
          (input.localizedEvenAxialRootOccurrence fuel axis))
        result resultComputed

/-- Whole-molecule analysis of every perceived canonical open even axis against a supplied
auxiliary state. -/
noncomputable def analyzeLocalizedEvenCumuleneAxialWithState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) :
    List (input.LocalizedEvenAxialSpatialAssignment fuel) :=
  input.localizedEvenAxialChains.attach.filterMap fun axis =>
    input.localizedEvenAxialSpatialAssignmentAtWithState? fuel state axis

/-- Exact membership in the state-parameterized whole-molecule axial analyzer. -/
theorem mem_analyzeLocalizedEvenCumuleneAxialWithState_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel) :
    assignment ∈ input.analyzeLocalizedEvenCumuleneAxialWithState fuel state ↔
      input.localizedEvenAxialSpatialAssignmentAtWithState?
        fuel state assignment.axis = some assignment := by
  constructor
  · intro present
    rw [analyzeLocalizedEvenCumuleneAxialWithState, List.mem_filterMap] at present
    obtain ⟨axis, _axisPresent, emitted⟩ := present
    cases resultComputed : input.localizedEvenAxialSpatialAssignmentAtWithState?
        fuel state axis with
    | none => simp [resultComputed] at emitted
    | some result =>
        simp [resultComputed] at emitted
        subst assignment
        rw [input.localizedEvenAxialSpatialAssignmentAtWithState?_axis
          fuel state axis result resultComputed]
        exact resultComputed
  · intro emitted
    rw [analyzeLocalizedEvenCumuleneAxialWithState, List.mem_filterMap]
    refine ⟨assignment.axis, ?_, ?_⟩
    · simp
    · simp [emitted]

/-- Every member of the state-parameterized whole-molecule result list is independently sound. -/
theorem analyzeLocalizedEvenCumuleneAxialWithState_member_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel)
    (present : assignment ∈
      input.analyzeLocalizedEvenCumuleneAxialWithState fuel state) :
    input.DeclarativeLocalizedEvenAxialSpatialAssignmentWithState
      fuel state assignment :=
  input.localizedEvenAxialSpatialAssignmentAtWithState?_sound fuel state
    assignment.axis assignment
    ((input.mem_analyzeLocalizedEvenCumuleneAxialWithState_iff
      fuel state assignment).mp present)

/-- Molecule-wide even-cumulene axial analyzer using the canonical causal
descriptor-bearing Rules-1a--5 scheduler state. -/
noncomputable def analyzeLocalizedEvenCumuleneAxial
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    List (input.LocalizedEvenAxialSpatialAssignment fuel) :=
  input.analyzeLocalizedEvenCumuleneAxialWithState fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)

/-- Independent meaning of an assignment emitted by the canonical scheduled analyzer. -/
def DeclarativeLocalizedEvenAxialSpatialAssignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel) : Prop :=
  input.DeclarativeLocalizedEvenAxialSpatialAssignmentWithState fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) assignment

/-- Every final `Rₐ/Sₐ` emitted by the scheduled whole-molecule path has independently
proved chain topology, Rules-1a--5 priorities, and exact rational geometry. -/
theorem analyzeLocalizedEvenCumuleneAxial_member_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedEvenCumuleneAxial fuel) :
    input.DeclarativeLocalizedEvenAxialSpatialAssignment fuel assignment := by
  exact input.analyzeLocalizedEvenCumuleneAxialWithState_member_conforms fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
    assignment present

/-! ## P-93.4.2.2 preferred `M/P` reporting -/

/-- A preferred-P93 result retains the complete proved production assignment.  Its public
descriptor accessor exposes `M/P`; the underlying `Rₐ/Sₐ` remains available as the independently
proved CIP geometry certificate rather than being discarded. -/
structure LocalizedEvenAxialPreferredP93Assignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  source : input.LocalizedEvenAxialSpatialAssignment fuel

namespace LocalizedEvenAxialPreferredP93Assignment

/-- The canonical perceived axis retained by a preferred-P93 assignment. -/
def axis {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (assignment : input.LocalizedEvenAxialPreferredP93Assignment fuel) :
    input.LocalizedEvenAxialChain :=
  assignment.source.axis

/-- P-93.4.2.2 preferred descriptor derived from the proved production `Rₐ/Sₐ`. -/
def descriptor {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (assignment : input.LocalizedEvenAxialPreferredP93Assignment fuel) :
    BlueBookP93.Acyclic.Descriptor :=
  assignment.source.result.assignment.descriptor.toPreferredP93

end LocalizedEvenAxialPreferredP93Assignment

/-- Wrap one proved axial assignment for preferred-IUPAC-name reporting. -/
def LocalizedEvenAxialSpatialAssignment.toPreferredP93
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (assignment : input.LocalizedEvenAxialSpatialAssignment fuel) :
    input.LocalizedEvenAxialPreferredP93Assignment fuel :=
  { source := assignment }

/-- Independent meaning of a preferred-P93 result: the retained production assignment satisfies
the full topology/Rules-1a--5/geometry relation, and its reported `M/P` is the independently
specified P-93 equivalent of that proved `Rₐ/Sₐ`. -/
def DeclarativeLocalizedEvenAxialPreferredP93Assignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedEvenAxialPreferredP93Assignment fuel) : Prop :=
  input.DeclarativeLocalizedEvenAxialSpatialAssignment fuel assignment.source ∧
    BlueBookP93.Acyclic.EvenCumuleneAxialDescriptorCorrespondence
      assignment.source.result.assignment.descriptor.toGeneralP93
      assignment.descriptor ∧
    BlueBookP93.Acyclic.DescriptorRecommended
      .preferredIUPACName .evenDoubleBondCumulene assignment.descriptor

/-- Preferred-IUPAC-name view of every scheduled open-even-cumulene result. -/
noncomputable def analyzeLocalizedEvenCumuleneAxialPreferredP93
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    List (input.LocalizedEvenAxialPreferredP93Assignment fuel) :=
  (input.analyzeLocalizedEvenCumuleneAxial fuel).map
    LocalizedEvenAxialSpatialAssignment.toPreferredP93

/-- Exact membership in the preferred-P93 view: it neither adds nor drops a successful axial
production result. -/
theorem mem_analyzeLocalizedEvenCumuleneAxialPreferredP93_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedEvenAxialPreferredP93Assignment fuel) :
    assignment ∈ input.analyzeLocalizedEvenCumuleneAxialPreferredP93 fuel ↔
      assignment.source ∈ input.analyzeLocalizedEvenCumuleneAxial fuel := by
  rw [analyzeLocalizedEvenCumuleneAxialPreferredP93, List.mem_map]
  constructor
  · rintro ⟨source, sourcePresent, identity⟩
    cases assignment
    simp only [LocalizedEvenAxialSpatialAssignment.toPreferredP93] at identity
    cases identity
    exact sourcePresent
  · intro sourcePresent
    exact ⟨assignment.source, sourcePresent, by cases assignment; rfl⟩

/-- Every final preferred `M/P` emitted by the scheduled whole-molecule path is backed by the
complete independent topology, priority, and geometry proof for its source `Rₐ/Sₐ`, and by the
independently transcribed P-93 descriptor correspondence and recommendation. -/
theorem analyzeLocalizedEvenCumuleneAxialPreferredP93_member_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedEvenAxialPreferredP93Assignment fuel)
    (present : assignment ∈ input.analyzeLocalizedEvenCumuleneAxialPreferredP93 fuel) :
    input.DeclarativeLocalizedEvenAxialPreferredP93Assignment fuel assignment := by
  refine ⟨
    input.analyzeLocalizedEvenCumuleneAxial_member_conforms fuel assignment.source
      ((input.mem_analyzeLocalizedEvenCumuleneAxialPreferredP93_iff fuel assignment).mp present),
    assignment.source.result.assignment.descriptor.toPreferredP93_conforms,
    ?_⟩
  exact assignment.source.result.assignment.descriptor.toPreferredP93_recommended.2

/-! ## Scheduled tetrahedral and axial public slice -/

/-- One final tetrahedral assignment read from the same canonical descriptor-bearing scheduler
state used by the axial endpoint compiler. -/
structure LocalizedScheduledTetrahedralSpatialAssignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  center : input.TetrahedralCenter
  descriptor : LocalizedAuxiliaryLabel

/-- Analyze one perceived tetrahedral center by reading its distinguished final occurrence in the
canonical causal state. -/
noncomputable def localizedScheduledTetrahedralSpatialAssignmentAt?
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter) :
    Option (input.LocalizedScheduledTetrahedralSpatialAssignment fuel) :=
  ((input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
    (input.localizedFinalOccurrence fuel center)).map fun descriptor =>
      { center, descriptor }

/-- Independent meaning of a scheduled final tetrahedral assignment. -/
def DeclarativeLocalizedScheduledTetrahedralSpatialAssignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedScheduledTetrahedralSpatialAssignment fuel) : Prop :=
  let state := input.localizedDescriptorBearingRule3Through5SchedulerState fuel
  let target := input.localizedFinalOccurrence fuel assignment.center
  input.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
    target (input.localizedDependencyView state target) assignment.descriptor

/-- Every scheduled tetrahedral result has the independent recursive Rules-1a--5 and exact
geometry meaning. -/
theorem localizedScheduledTetrahedralSpatialAssignmentAt?_sound
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter)
    (assignment : input.LocalizedScheduledTetrahedralSpatialAssignment fuel)
    (computed : input.localizedScheduledTetrahedralSpatialAssignmentAt?
      fuel center = some assignment) :
    input.DeclarativeLocalizedScheduledTetrahedralSpatialAssignment
      fuel assignment := by
  unfold localizedScheduledTetrahedralSpatialAssignmentAt? at computed
  cases stateComputed :
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
        (input.localizedFinalOccurrence fuel center) with
  | none => simp [stateComputed] at computed
  | some descriptor =>
      simp [stateComputed] at computed
      subst assignment
      exact input.localizedOccurrenceDescriptorBearingRule3Through5Model_eq_some_implies_declarative
        (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
        (input.localizedDescriptorBearingRule3Through5SchedulerState_cipModel fuel)
        (input.localizedFinalOccurrence fuel center) descriptor stateComputed

/-- Whole-molecule scheduled tetrahedral branch. -/
noncomputable def analyzeLocalizedScheduledTetrahedralSpatial
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    List (input.LocalizedScheduledTetrahedralSpatialAssignment fuel) :=
  input.canonicalTetrahedralCenters.filterMap fun center =>
    input.localizedScheduledTetrahedralSpatialAssignmentAt? fuel center

/-- Every assignment in the scheduled tetrahedral branch has independent final-descriptor
semantics. -/
theorem analyzeLocalizedScheduledTetrahedralSpatial_member_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedScheduledTetrahedralSpatialAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedScheduledTetrahedralSpatial fuel) :
    input.DeclarativeLocalizedScheduledTetrahedralSpatialAssignment
      fuel assignment := by
  rw [analyzeLocalizedScheduledTetrahedralSpatial, List.mem_filterMap] at present
  obtain ⟨center, _centerPresent, emitted⟩ := present
  cases resultComputed : input.localizedScheduledTetrahedralSpatialAssignmentAt?
      fuel center with
  | none => simp [resultComputed] at emitted
  | some result =>
      simp [resultComputed] at emitted
      subst assignment
      exact input.localizedScheduledTetrahedralSpatialAssignmentAt?_sound
        fuel center result resultComputed

/-- The currently integrated scheduled production slice.  Its name is intentionally explicit:
other P-92/P-93 descriptor families are not silently claimed by this sum. -/
inductive LocalizedScheduledTetrahedralAndEvenAxialAssignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  | tetrahedral (assignment : input.LocalizedScheduledTetrahedralSpatialAssignment fuel)
  | evenAxial (assignment : input.LocalizedEvenAxialSpatialAssignment fuel)

/-- One public list for the integrated scheduled tetrahedral and open-even-cumulene branches. -/
noncomputable def analyzeLocalizedScheduledTetrahedralAndEvenAxial
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    List (input.LocalizedScheduledTetrahedralAndEvenAxialAssignment fuel) :=
  (input.analyzeLocalizedScheduledTetrahedralSpatial fuel).map
      LocalizedScheduledTetrahedralAndEvenAxialAssignment.tetrahedral ++
    (input.analyzeLocalizedEvenCumuleneAxial fuel).map
      LocalizedScheduledTetrahedralAndEvenAxialAssignment.evenAxial

/-- Independent disjoint-family meaning of the currently integrated scheduled production slice. -/
inductive DeclarativeLocalizedScheduledTetrahedralAndEvenAxialAssignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedScheduledTetrahedralAndEvenAxialAssignment fuel → Prop
  | tetrahedral {assignment}
      (derived : input.DeclarativeLocalizedScheduledTetrahedralSpatialAssignment
        fuel assignment) :
      input.DeclarativeLocalizedScheduledTetrahedralAndEvenAxialAssignment fuel
        (.tetrahedral assignment)
  | evenAxial {assignment}
      (derived : input.DeclarativeLocalizedEvenAxialSpatialAssignment fuel assignment) :
      input.DeclarativeLocalizedScheduledTetrahedralAndEvenAxialAssignment fuel
        (.evenAxial assignment)

/-- Every emitted result in the mixed scheduled slice is independently correct for its family. -/
theorem analyzeLocalizedScheduledTetrahedralAndEvenAxial_member_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedScheduledTetrahedralAndEvenAxialAssignment fuel)
    (present : assignment ∈
      input.analyzeLocalizedScheduledTetrahedralAndEvenAxial fuel) :
    input.DeclarativeLocalizedScheduledTetrahedralAndEvenAxialAssignment
      fuel assignment := by
  rw [analyzeLocalizedScheduledTetrahedralAndEvenAxial, List.mem_append] at present
  rcases present with tetrahedral | axial
  · rw [List.mem_map] at tetrahedral
    rcases tetrahedral with ⟨source, sourcePresent, assignmentIdentity⟩
    subst assignment
    exact .tetrahedral
      (input.analyzeLocalizedScheduledTetrahedralSpatial_member_conforms
        fuel source sourcePresent)
  · rw [List.mem_map] at axial
    rcases axial with ⟨source, sourcePresent, assignmentIdentity⟩
    subst assignment
    exact .evenAxial
      (input.analyzeLocalizedEvenCumuleneAxial_member_conforms
        fuel source sourcePresent)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
