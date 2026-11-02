import TetraStereo.OneCenter.LocalizedOddCumulenePerception
import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialAnalysis
import TetraStereo.OneCenter.LocalizedRule3CumulatedDescriptor
import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3FuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecule-wide planar odd-cumulene `E/Z` analysis

P-93.4.2.3 treats an odd cumulene as one planar extended double-bond system.  This module joins
the canonical molecule-wide odd-chain carrier to the occurrence-local descriptor-bearing
Rules-1a--5 endpoint compiler.  Exact rational terminal geometry is converted to the independent
P-93 relation: senior terminal ligands together give `Z`, and senior terminal ligands opposite
give `E`.

The analyzer is fail-closed.  Tied terminal priorities, missing coordinates, degenerate geometry,
branching, cyclic closure, or insufficient occurrence traversal fuel emit no final descriptor.
-/

/-! ## Independent P-93 geometry bridge -/

/-- Production Rule-3 geometry refines the independently transcribed P-93.4.2.3 terminal-ligand
geometry.  `nonstereogenic` has no value in the independent stereogenic geometry domain. -/
def Rule3GeometryRefinesOddCumuleneTerminalGeometry
    (geometry : OfficialRule3Geometry)
    (terminalGeometry : BlueBookP93.Acyclic.OddCumuleneTerminalGeometry) : Prop :=
  match geometry, terminalGeometry with
  | .seqcis, .together | .seqtrans, .opposite => True
  | _, _ => False

/-- Convert only stereogenic production geometry into the independent odd-cumulene domain. -/
def oddCumuleneTerminalGeometryOfRule3? :
    OfficialRule3Geometry →
      Option BlueBookP93.Acyclic.OddCumuleneTerminalGeometry
  | .seqcis => some .together
  | .seqtrans => some .opposite
  | .nonstereogenic => none

theorem oddCumuleneTerminalGeometryOfRule3?_eq_some_iff
    (geometry : OfficialRule3Geometry)
    (terminalGeometry : BlueBookP93.Acyclic.OddCumuleneTerminalGeometry) :
    oddCumuleneTerminalGeometryOfRule3? geometry = some terminalGeometry ↔
      Rule3GeometryRefinesOddCumuleneTerminalGeometry geometry terminalGeometry := by
  cases geometry <;> cases terminalGeometry <;>
    simp [oddCumuleneTerminalGeometryOfRule3?,
      Rule3GeometryRefinesOddCumuleneTerminalGeometry]

/-- Final production-to-authority odd-cumulene descriptor conversion. -/
def oddCumuleneEZDescriptorOfRule3?
    (geometry : OfficialRule3Geometry) :
    Option BlueBookP93.Acyclic.Descriptor := do
  let terminalGeometry ← oddCumuleneTerminalGeometryOfRule3? geometry
  BlueBookP93.Acyclic.oddCumuleneEZDescriptor? terminalGeometry

/-- The final conversion succeeds exactly when production geometry refines an independent
terminal geometry and the independent P-93.4.2.3 relation assigns the emitted descriptor. -/
theorem oddCumuleneEZDescriptorOfRule3?_eq_some_iff
    (geometry : OfficialRule3Geometry)
    (descriptor : BlueBookP93.Acyclic.Descriptor) :
    oddCumuleneEZDescriptorOfRule3? geometry = some descriptor ↔
      ∃ terminalGeometry,
        Rule3GeometryRefinesOddCumuleneTerminalGeometry geometry terminalGeometry ∧
        BlueBookP93.Acyclic.OddCumuleneEZAssignment terminalGeometry descriptor := by
  constructor
  · intro computed
    unfold oddCumuleneEZDescriptorOfRule3? at computed
    cases terminalComputed : oddCumuleneTerminalGeometryOfRule3? geometry with
    | none => simp [terminalComputed] at computed
    | some terminalGeometry =>
        exact ⟨terminalGeometry,
          (oddCumuleneTerminalGeometryOfRule3?_eq_some_iff
            geometry terminalGeometry).mp terminalComputed,
          (BlueBookP93.Acyclic.oddCumuleneEZDescriptor?_eq_some_iff
            terminalGeometry descriptor).mp (by
              simpa [terminalComputed] using computed)⟩
  · rintro ⟨terminalGeometry, refines, assigned⟩
    have terminalComputed :=
      (oddCumuleneTerminalGeometryOfRule3?_eq_some_iff
        geometry terminalGeometry).mpr refines
    have descriptorComputed :=
      (BlueBookP93.Acyclic.oddCumuleneEZDescriptor?_eq_some_iff
        terminalGeometry descriptor).mpr assigned
    simp [oddCumuleneEZDescriptorOfRule3?, terminalComputed, descriptorComputed]

@[simp] theorem oddCumuleneEZDescriptorOfRule3?_nonstereogenic :
    oddCumuleneEZDescriptorOfRule3? .nonstereogenic = none :=
  rfl

namespace CertifiedLocalizedCIPInput

open DeclarativeCIP

/-! ## Occurrence-local final descriptor -/

/-- Final odd-cumulene result retaining the complete topology, endpoint-key, and exact spatial
source certificate from which its public `E/Z` descriptor was derived. -/
structure LocalizedRule3OddCumuleneEZResult
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  source : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel
  descriptor : BlueBookP93.Acyclic.Descriptor

/-- Run the complete occurrence-local odd-cumulene compiler and convert only stereogenic terminal
geometry to the independent P-93.4.2.3 `E/Z` value. -/
noncomputable def localizedRule3OddCumuleneEZWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3OddCumuleneEZResult carrierFuel) := do
  let source ← input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
    target occurrence view rule3FrameOf
  let descriptor ← oddCumuleneEZDescriptorOfRule3? source.unit.geometry
  some { source, descriptor }

/-- A successful final `E/Z` conversion retains exactly the complete descriptor-bearing source
result produced by the occurrence-local odd-cumulene compiler. -/
theorem localizedRule3OddCumuleneEZWith?_source
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (result : input.LocalizedRule3OddCumuleneEZResult carrierFuel)
    (computed : input.localizedRule3OddCumuleneEZWith?
      target occurrence view rule3FrameOf = some result) :
    input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf = some result.source := by
  unfold localizedRule3OddCumuleneEZWith? at computed
  cases sourceComputed :
      input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf with
  | none => simp [sourceComputed] at computed
  | some source =>
      cases descriptorComputed :
          oddCumuleneEZDescriptorOfRule3? source.unit.geometry with
      | none => simp [sourceComputed, descriptorComputed] at computed
      | some descriptor =>
          simp [sourceComputed, descriptorComputed] at computed
          subst result
          simp

/-- Independent meaning of a final occurrence-local odd-cumulene result. -/
def DeclarativeLocalizedRule3OddCumuleneEZWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (result : input.LocalizedRule3OddCumuleneEZResult carrierFuel) : Prop :=
  input.DeclarativeLocalizedRule3OddCumuleneDescriptorBearingSpatialUnitWith
      target occurrence view Rule3FrameMeaning result.source ∧
    ∃ terminalGeometry,
      Rule3GeometryRefinesOddCumuleneTerminalGeometry
        result.source.unit.geometry terminalGeometry ∧
      BlueBookP93.Acyclic.OddCumuleneEZAssignment
        terminalGeometry result.descriptor ∧
      BlueBookP93.Acyclic.DescriptorRecommended .preferredIUPACName
        .oddDoubleBondCumulene result.descriptor

/-- Every emitted occurrence-local odd-cumulene `E/Z` value satisfies the independent complete
topology, priority, exact geometry, and P-93.4.2.3 descriptor relation. -/
theorem localizedRule3OddCumuleneEZWith?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (result : input.LocalizedRule3OddCumuleneEZResult carrierFuel)
    (computed : input.localizedRule3OddCumuleneEZWith?
      target occurrence view rule3FrameOf = some result) :
    input.DeclarativeLocalizedRule3OddCumuleneEZWith
      target occurrence view Rule3FrameMeaning result := by
  unfold localizedRule3OddCumuleneEZWith? at computed
  cases sourceComputed :
      input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf with
  | none => simp [sourceComputed] at computed
  | some source =>
      cases descriptorComputed :
          oddCumuleneEZDescriptorOfRule3? source.unit.geometry with
      | none => simp [sourceComputed, descriptorComputed] at computed
      | some descriptor =>
          simp [sourceComputed, descriptorComputed] at computed
          subst result
          obtain ⟨terminalGeometry, refines, assigned⟩ :=
            (oddCumuleneEZDescriptorOfRule3?_eq_some_iff
              source.unit.geometry descriptor).mp descriptorComputed
          have recommended :=
            BlueBookP93.Acyclic.oddCumuleneEZDescriptor?_recommended
              terminalGeometry descriptor
              ((BlueBookP93.Acyclic.oddCumuleneEZDescriptor?_eq_some_iff
                terminalGeometry descriptor).mpr assigned)
          exact ⟨
            input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_sound
              target occurrence view rule3FrameOf Rule3FrameMeaning rule3FrameSound
              source sourceComputed,
            terminalGeometry, refines, assigned, recommended.2⟩

/-! ## Molecule-wide scheduled analysis -/

/-- Repackage the root of a canonical molecule-wide odd chain as the family-neutral occurrence
carrier root. -/
noncomputable def localizedOddCumuleneAxialRoot
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain) : input.LocalizedAxialRoot :=
  ⟨axis.1.root,
    (input.mem_localizedAxialRootCandidates_iff axis.1.root).mpr
      (input.mem_localizedOddCumuleneChains_implies_declarative
        axis.1 axis.2).1.1⟩

/-- Public molecule-wide odd-cumulene assignment, retaining the exact canonical physical chain
that generated its final descriptor. -/
structure LocalizedOddCumuleneEZSpatialAssignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  axis : input.LocalizedOddCumuleneChain
  result : input.LocalizedRule3OddCumuleneEZResult fuel

/-- Analyze one canonical molecule-wide odd chain against an arbitrary complete auxiliary state. -/
noncomputable def localizedOddCumuleneEZSpatialAssignmentAtWithState?
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedOddCumuleneChain) :
    Option (input.LocalizedOddCumuleneEZSpatialAssignment fuel) :=
  let axialRoot := input.localizedOddCumuleneAxialRoot axis
  let target := input.localizedAxialRootOccurrence fuel axialRoot
  let occurrence := input.localizedAxialRootFirstChildOccurrence fuel axialRoot
  let view := input.localizedDependencyView state target
  (input.localizedRule3OddCumuleneEZWith? target occurrence view
      (input.buildLocalizedDescriptorBearingRule3Frame? target view
        (localizedDescriptorBearingRule3EvaluationFuel fuel))).map fun result =>
    { axis, result }

/-- Independent meaning of a state-parameterized molecule-wide odd-cumulene assignment.  The
occurrence target is definitionally anchored at the retained canonical chain's terminal root. -/
def DeclarativeLocalizedOddCumuleneEZSpatialAssignmentWithState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel) : Prop :=
  let axialRoot := input.localizedOddCumuleneAxialRoot assignment.axis
  let target := input.localizedAxialRootOccurrence fuel axialRoot
  let occurrence := input.localizedAxialRootFirstChildOccurrence fuel axialRoot
  let view := input.localizedDependencyView state target
  input.DeclarativeLocalizedOddCumuleneChainFrame assignment.axis.1 ∧
    input.DeclarativeLocalizedRule3OddCumuleneEZWith
      target occurrence view
        (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view
          (localizedDescriptorBearingRule3EvaluationFuel fuel))
      assignment.result

/-- A successful one-axis call retains exactly the canonical odd chain supplied to it. -/
theorem localizedOddCumuleneEZSpatialAssignmentAtWithState?_axis
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedOddCumuleneChain)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel)
    (computed : input.localizedOddCumuleneEZSpatialAssignmentAtWithState?
      fuel state axis = some assignment) :
    assignment.axis = axis := by
  unfold localizedOddCumuleneEZSpatialAssignmentAtWithState? at computed
  dsimp only at computed
  let axialRoot := input.localizedOddCumuleneAxialRoot axis
  let target := input.localizedAxialRootOccurrence fuel axialRoot
  let occurrence := input.localizedAxialRootFirstChildOccurrence fuel axialRoot
  let view := input.localizedDependencyView state target
  let frameOf := input.buildLocalizedDescriptorBearingRule3Frame?
    target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
  cases resultComputed : input.localizedRule3OddCumuleneEZWith?
      target occurrence view frameOf with
  | none => simp [axialRoot, target, occurrence, view, frameOf,
      resultComputed] at computed
  | some result =>
      simp [axialRoot, target, occurrence, view, frameOf,
        resultComputed] at computed
      subst assignment
      rfl

/-- Every emitted one-axis assignment has independent molecule-wide chain topology and complete
occurrence-local topology, Rules-1a--5 priorities, rational geometry, and final P-93 `E/Z`
meaning. -/
theorem localizedOddCumuleneEZSpatialAssignmentAtWithState?_sound
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedOddCumuleneChain)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel)
    (computed : input.localizedOddCumuleneEZSpatialAssignmentAtWithState?
      fuel state axis = some assignment) :
    input.DeclarativeLocalizedOddCumuleneEZSpatialAssignmentWithState
      fuel state assignment := by
  unfold localizedOddCumuleneEZSpatialAssignmentAtWithState? at computed
  dsimp only at computed
  let axialRoot := input.localizedOddCumuleneAxialRoot axis
  let target := input.localizedAxialRootOccurrence fuel axialRoot
  let occurrence := input.localizedAxialRootFirstChildOccurrence fuel axialRoot
  let view := input.localizedDependencyView state target
  let frameOf := input.buildLocalizedDescriptorBearingRule3Frame?
    target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
  cases resultComputed : input.localizedRule3OddCumuleneEZWith?
      target occurrence view frameOf with
  | none => simp [axialRoot, target, occurrence, view, frameOf,
      resultComputed] at computed
  | some result =>
      simp [axialRoot, target, occurrence, view, frameOf,
        resultComputed] at computed
      subst assignment
      exact ⟨
        input.mem_localizedOddCumuleneChains_implies_declarative axis.1 axis.2,
        input.localizedRule3OddCumuleneEZWith?_sound
          target occurrence view frameOf
          (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view
            (localizedDescriptorBearingRule3EvaluationFuel fuel))
          (fun cursors frame frameComputed =>
            input.buildLocalizedDescriptorBearingRule3Frame?_sound
              target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
              cursors frame frameComputed)
          result resultComputed⟩

/-- Whole-molecule odd-cumulene analysis against a supplied auxiliary state. -/
noncomputable def analyzeLocalizedOddCumuleneEZWithState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) :
    List (input.LocalizedOddCumuleneEZSpatialAssignment fuel) :=
  input.localizedOddCumuleneChains.attach.filterMap fun axis =>
    input.localizedOddCumuleneEZSpatialAssignmentAtWithState? fuel state axis

/-- Exact membership in the state-parameterized whole-molecule odd-cumulene analyzer. -/
theorem mem_analyzeLocalizedOddCumuleneEZWithState_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel) :
    assignment ∈ input.analyzeLocalizedOddCumuleneEZWithState fuel state ↔
      input.localizedOddCumuleneEZSpatialAssignmentAtWithState?
        fuel state assignment.axis = some assignment := by
  classical
  constructor
  · intro present
    rw [analyzeLocalizedOddCumuleneEZWithState, List.mem_filterMap] at present
    obtain ⟨axis, _axisPresent, emitted⟩ := present
    cases resultComputed : input.localizedOddCumuleneEZSpatialAssignmentAtWithState?
        fuel state axis with
    | none => simp [resultComputed] at emitted
    | some result =>
        simp [resultComputed] at emitted
        subst assignment
        rw [input.localizedOddCumuleneEZSpatialAssignmentAtWithState?_axis
          fuel state axis result resultComputed]
        exact resultComputed
  · intro emitted
    rw [analyzeLocalizedOddCumuleneEZWithState, List.mem_filterMap]
    exact ⟨assignment.axis, by simp, by simp [emitted]⟩

/-- Every state-parameterized whole-molecule odd-cumulene result is independently sound. -/
theorem analyzeLocalizedOddCumuleneEZWithState_member_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedOddCumuleneEZWithState fuel state) :
    input.DeclarativeLocalizedOddCumuleneEZSpatialAssignmentWithState
      fuel state assignment :=
  input.localizedOddCumuleneEZSpatialAssignmentAtWithState?_sound
    fuel state assignment.axis assignment
      ((input.mem_analyzeLocalizedOddCumuleneEZWithState_iff
        fuel state assignment).mp present)

/-- Scheduled molecule-wide planar odd-cumulene `E/Z` analyzer. -/
noncomputable def analyzeLocalizedOddCumuleneEZ
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    List (input.LocalizedOddCumuleneEZSpatialAssignment fuel) :=
  input.analyzeLocalizedOddCumuleneEZWithState fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)

/-- Independent meaning under the canonical causal Rules-1a--5 scheduler state. -/
def DeclarativeLocalizedOddCumuleneEZSpatialAssignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel) : Prop :=
  input.DeclarativeLocalizedOddCumuleneEZSpatialAssignmentWithState fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) assignment

/-- Every final odd-cumulene `E/Z` emitted by the scheduled molecule-wide path is independently
correct from maximal physical-chain perception through final P-93.4.2.3 descriptor assignment. -/
theorem analyzeLocalizedOddCumuleneEZ_member_conforms
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel)
    (present : assignment ∈ input.analyzeLocalizedOddCumuleneEZ fuel) :
    input.DeclarativeLocalizedOddCumuleneEZSpatialAssignment fuel assignment :=
  input.analyzeLocalizedOddCumuleneEZWithState_member_conforms fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
    assignment present

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
