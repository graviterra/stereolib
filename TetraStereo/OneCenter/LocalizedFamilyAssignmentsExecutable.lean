import TetraStereo.OneCenter.LocalizedOrdinaryMonocyclicDoubleBondAnalysis
import TetraStereo.OneCenter.LocalizedOriginalRule3WithChildren
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableChildSlots

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Executable even-axis topology selection, with the original complete parity check. -/
def localizedEvenCumuleneEndpointCursorFrameExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat} (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option (input.LocalizedRule3CumulatedEndpointCursorFrame fuel) := do
  let frame ← input.localizedRule3CumulatedEndpointCursorFrameExec? traversalFuel occurrence
  if _even : 1 < frame.doubleBondCount ∧ Even frame.doubleBondCount then some frame else none

theorem localizedEvenCumuleneEndpointCursorFrameExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {fuel : Nat} (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.localizedEvenCumuleneEndpointCursorFrameExec? traversalFuel occurrence =
      input.localizedEvenCumuleneEndpointCursorFrame? traversalFuel occurrence := by
  simp only [localizedEvenCumuleneEndpointCursorFrameExec?, localizedEvenCumuleneEndpointCursorFrame?,
    localizedRule3CumulatedEndpointCursorFrameExec?_eq_original]

/-- Exact axial assignment from fully ranked terminal frames and molecular coordinates. -/
def localizedAxialAssignmentOfEndpointFramesExec?
    (input : CertifiedLocalizedCIPInput) (axisStart axisEnd : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame) :
    Option (AxialAssignment input.Atom) := do
  let (startHigh, startLow) ← input.localizedAxialEndpointPair? startFrame
  let (endHigh, endLow) ← input.localizedAxialEndpointPair? endFrame
  let axisStartPoint ← input.spatialPointAt? axisStart
  let axisEndPoint ← input.spatialPointAt? axisEnd
  let startHighPoint ← input.spatialPointAt? startHigh
  let endHighPoint ← input.spatialPointAt? endHigh
  let descriptor ← axialDescriptorOfSpatialReferences?
    axisStartPoint axisEndPoint startHighPoint endHighPoint
  some
    { unit := { axisStart, axisEnd, startHigh, startLow, endHigh, endLow }
      descriptor }

theorem localizedAxialAssignmentOfEndpointFramesExec?_eq_original
    (input : CertifiedLocalizedCIPInput) (axisStart axisEnd : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame) :
    input.localizedAxialAssignmentOfEndpointFramesExec? axisStart axisEnd startFrame endFrame =
      input.localizedAxialAssignmentOfEndpointFrames? axisStart axisEnd startFrame endFrame := rfl

def localizedEvenCumuleneAxialAssignmentWithExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedEvenCumuleneAxialResult fuel) := do
  let topology ← input.localizedEvenCumuleneEndpointCursorFrameExec?
    (input.localizedRule3CumulatedTraversalFuel fuel) occurrence
  let leftCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
    target view callback topology.initial.left topology.initial.right topology.initial.leftCursor
  let rightCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
    target view callback topology.right topology.rightPartner topology.rightCursor
  let assignment ← input.localizedAxialAssignmentOfEndpointFramesExec?
    topology.initial.left topology.right leftCompilation.endpointFrame rightCompilation.endpointFrame
  some { topology, leftCompilation, rightCompilation, assignment }

theorem localizedEvenCumuleneAxialAssignmentWithExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame) :
    input.localizedEvenCumuleneAxialAssignmentWithExec? target occurrence view callback =
      input.localizedEvenCumuleneAxialAssignmentWith? target occurrence view callback := by
  simp only [localizedEvenCumuleneAxialAssignmentWithExec?, localizedEvenCumuleneAxialAssignmentWith?,
    localizedEvenCumuleneEndpointCursorFrameExec?_eq_original,
    ← buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?,
    localizedAxialAssignmentOfEndpointFramesExec?_eq_original]

private theorem frameFunction_eq (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (budget : Nat) :
    OriginalWithChildren.buildLocalizedDescriptorBearingRule3FrameExec? input
      (input.localizedRerootChildrenFromCarrier? (input.localizedOccurrenceCarrier fuel)) target view budget =
        input.buildLocalizedDescriptorBearingRule3Frame? target view budget := by
  funext cursors
  exact OriginalWithChildren.frame_eq_original input _
    (fun cursor => input.localizedRerootChildrenFromCarrier?_eq_executable cursor)
    target view budget cursors

def localizedEvenCumuleneAxialAssignmentExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) : Option (input.LocalizedEvenCumuleneAxialResult fuel) :=
  input.localizedEvenCumuleneAxialAssignmentWithExec? target occurrence view
    (OriginalWithChildren.buildLocalizedDescriptorBearingRule3FrameExec? input
      (input.localizedRerootChildrenFromCarrier? (input.localizedOccurrenceCarrier fuel)) target view
      (localizedEvenCumuleneAxialRule3EvaluationFuel fuel))

theorem localizedEvenCumuleneAxialAssignmentExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedEvenCumuleneAxialAssignmentExec? target occurrence view =
      input.localizedEvenCumuleneAxialAssignment? target occurrence view := by
  simp only [localizedEvenCumuleneAxialAssignmentExec?, localizedEvenCumuleneAxialAssignment?,
    localizedEvenCumuleneAxialAssignmentWithExec?_eq_original,
    frameFunction_eq]

def localizedRule3OddCumuleneEZWithExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3OddCumuleneEZResult fuel) := do
  let source ← input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
    target occurrence view callback
  let descriptor ← oddCumuleneEZDescriptorOfRule3? source.unit.geometry
  some { source, descriptor }

theorem localizedRule3OddCumuleneEZWithExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame) :
    input.localizedRule3OddCumuleneEZWithExec? target occurrence view callback =
      input.localizedRule3OddCumuleneEZWith? target occurrence view callback := by
  simp only [localizedRule3OddCumuleneEZWithExec?, localizedRule3OddCumuleneEZWith?,
    localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?_eq_original]

/-- Plain root records and first-child slots retain the canonical family topology. -/
def localizedEvenAxialRootOccurrenceExec (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) : input.LocalizedCIPOccurrence fuel :=
  input.localizedAtomRootOccurrenceExecutable fuel axis.1.root.terminal

theorem localizedEvenAxialRootOccurrenceExec_eq (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    input.localizedEvenAxialRootOccurrenceExec fuel axis = input.localizedEvenAxialRootOccurrence fuel axis :=
  Subtype.ext rfl

def localizedOddCumuleneAxialRootExec (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain) : input.LocalizedAxialRoot :=
  ⟨axis.1.root, (input.mem_localizedAxialRootCandidates_iff axis.1.root).mpr
    (input.mem_localizedOddCumuleneChains_implies_declarative axis.1 axis.2).1.1⟩

theorem localizedOddCumuleneAxialRootExec_eq (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain) :
    input.localizedOddCumuleneAxialRootExec axis = input.localizedOddCumuleneAxialRoot axis := rfl

def localizedAxialRootOccurrenceExec (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedAxialRoot) : input.LocalizedCIPOccurrence fuel :=
  input.localizedAtomRootOccurrenceExecutable fuel axis.1.terminal

theorem localizedAxialRootOccurrenceExec_eq (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedAxialRoot) :
    input.localizedAxialRootOccurrenceExec fuel axis = input.localizedAxialRootOccurrence fuel axis :=
  Subtype.ext rfl

/-- Exact executable family interfaces consume any supplied auxiliary state. Their independent
meaning remains relative to that state; no old-scheduler identity is asserted. -/
def localizedEvenAxialSpatialAssignmentAtWithStateExec?
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedEvenAxialChain) : Option (input.LocalizedEvenAxialSpatialAssignment fuel) :=
  let target := input.localizedEvenAxialRootOccurrenceExec fuel axis
  let occurrence := input.localizedEvenAxialFirstChildOccurrenceExec fuel axis
  (input.localizedEvenCumuleneAxialAssignmentExec? target occurrence
    (input.localizedDependencyView state target)).map fun result => { axis, result }

theorem localizedEvenAxialSpatialAssignmentAtWithStateExec?_eq_original
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedEvenAxialChain) :
    input.localizedEvenAxialSpatialAssignmentAtWithStateExec? fuel state axis =
      input.localizedEvenAxialSpatialAssignmentAtWithState? fuel state axis := by
  simp only [localizedEvenAxialSpatialAssignmentAtWithStateExec?, localizedEvenAxialSpatialAssignmentAtWithState?,
    localizedEvenAxialFirstChildOccurrenceExec_eq,
    localizedEvenCumuleneAxialAssignmentExec?_eq_original]
  rfl

def localizedOddCumuleneEZSpatialAssignmentAtWithStateExec?
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedOddCumuleneChain) : Option (input.LocalizedOddCumuleneEZSpatialAssignment fuel) :=
  let axialRoot := input.localizedOddCumuleneAxialRootExec axis
  let target := input.localizedAxialRootOccurrenceExec fuel axialRoot
  let occurrence := input.localizedAxialRootFirstChildOccurrenceExec fuel axialRoot
  let view := input.localizedDependencyView state target
  (input.localizedRule3OddCumuleneEZWithExec? target occurrence view
    (OriginalWithChildren.buildLocalizedDescriptorBearingRule3FrameExec? input
      (input.localizedRerootChildrenFromCarrier? (input.localizedOccurrenceCarrier fuel)) target view
      (localizedDescriptorBearingRule3EvaluationFuel fuel))).map fun result => { axis, result }

theorem localizedOddCumuleneEZSpatialAssignmentAtWithStateExec?_eq_original
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedOddCumuleneChain) :
    input.localizedOddCumuleneEZSpatialAssignmentAtWithStateExec? fuel state axis =
      input.localizedOddCumuleneEZSpatialAssignmentAtWithState? fuel state axis := by
  simp only [localizedOddCumuleneEZSpatialAssignmentAtWithStateExec?, localizedOddCumuleneEZSpatialAssignmentAtWithState?,
    localizedOddCumuleneAxialRootExec_eq,
    localizedAxialRootFirstChildOccurrenceExec_eq, localizedRule3OddCumuleneEZWithExec?_eq_original,
    frameFunction_eq]
  rfl

def localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithStateExec?
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond) : Option (input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel) :=
  let target := input.localizedAtomRootOccurrenceExecutable fuel bond.1.1
  let occurrence := input.localizedCanonicalDoubleBondFirstChildOccurrenceExec fuel bond
  let view := input.localizedDependencyView state target
  (input.localizedRule3OrdinaryMonocyclicEZWithExec? target occurrence view
    (OriginalWithChildren.buildLocalizedDescriptorBearingRule3FrameExec? input
      (input.localizedRerootChildrenFromCarrier? (input.localizedOccurrenceCarrier fuel)) target view
      (localizedDescriptorBearingRule3EvaluationFuel fuel))).map fun result => { bond, result }

theorem localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithStateExec?_eq_original
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond) :
    input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithStateExec? fuel state bond =
      input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState? fuel state bond := by
  simp only [localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithStateExec?, localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?,
    localizedCanonicalDoubleBondFirstChildOccurrenceExec_eq,
    localizedRule3OrdinaryMonocyclicEZWithExec?_eq_original,
    frameFunction_eq]
  rfl

theorem localizedEvenAxialSpatialAssignmentAtWithStateExec?_sound
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (state : input.LocalizedAuxiliaryState fuel)
    (unit : input.LocalizedEvenAxialChain) (assignment : input.LocalizedEvenAxialSpatialAssignment fuel)
    (computed : input.localizedEvenAxialSpatialAssignmentAtWithStateExec? fuel state unit = some assignment) :
    input.DeclarativeLocalizedEvenAxialSpatialAssignmentWithState fuel state assignment := by
  rw [input.localizedEvenAxialSpatialAssignmentAtWithStateExec?_eq_original] at computed
  exact input.localizedEvenAxialSpatialAssignmentAtWithState?_sound fuel state unit assignment computed

theorem localizedOddCumuleneEZSpatialAssignmentAtWithStateExec?_sound
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (state : input.LocalizedAuxiliaryState fuel)
    (unit : input.LocalizedOddCumuleneChain) (assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel)
    (computed : input.localizedOddCumuleneEZSpatialAssignmentAtWithStateExec? fuel state unit = some assignment) :
    input.DeclarativeLocalizedOddCumuleneEZSpatialAssignmentWithState fuel state assignment := by
  rw [input.localizedOddCumuleneEZSpatialAssignmentAtWithStateExec?_eq_original] at computed
  exact input.localizedOddCumuleneEZSpatialAssignmentAtWithState?_sound fuel state unit assignment computed

theorem localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithStateExec?_sound
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (state : input.LocalizedAuxiliaryState fuel)
    (unit : input.LocalizedCanonicalDoubleBond) (assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel)
    (computed : input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithStateExec? fuel state unit = some assignment) :
    input.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignmentWithState fuel state assignment := by
  rw [input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithStateExec?_eq_original] at computed
  exact input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_sound fuel state unit assignment computed

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
