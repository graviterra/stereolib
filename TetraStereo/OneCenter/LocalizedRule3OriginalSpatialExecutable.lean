import TetraStereo.OneCenter.LocalizedCyclicCumulenePerceptionExecutable
import TetraStereo.OneCenter.LocalizedRule3CumulatedChainExecutable
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitExecutable
import TetraStereo.OneCenter.LocalizedCyclicDoubleBondDescriptor
import TetraStereo.OneCenter.LocalizedRule3CumulatedDescriptor

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! Executable twins of the original eager endpoint/spatial/cyclic routing path.
Every equality preserves the original optional result, including all refusals. -/

def localizedRule3DescriptorBearingSpatialUnitExec?
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame) :
    Option input.LocalizedRule3DescriptorBearingSpatialUnitResult :=
  if input.moleculeGraph.bond left right = 2 then
    let leftPriority := input.localizedRule3EndpointPriority leftFrame
    let rightPriority := input.localizedRule3EndpointPriority rightFrame
    match leftPriority, rightPriority with
    | .nonstereogenic, _ | _, .nonstereogenic =>
        some { leftPriority, rightPriority, geometry := .nonstereogenic }
    | .senior leftReference, .senior rightReference => do
        let leftPoint ← input.spatialPointAt? left
        let rightPoint ← input.spatialPointAt? right
        let leftReferencePoint ← input.spatialPointAt? leftReference
        let rightReferencePoint ← input.spatialPointAt? rightReference
        let geometry ← rule3GeometryOfSpatialReferences? leftPoint rightPoint
          leftReferencePoint rightReferencePoint
        some { leftPriority, rightPriority, geometry }
  else none

theorem localizedRule3DescriptorBearingSpatialUnitExec?_eq_original
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame) :
    input.localizedRule3DescriptorBearingSpatialUnitExec? left right leftFrame rightFrame = input.localizedRule3DescriptorBearingSpatialUnit? left right leftFrame rightFrame := by
  rfl

def localizedRule3ExtendedDescriptorBearingSpatialUnitExec?
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame) :
    Option input.LocalizedRule3DescriptorBearingSpatialUnitResult :=
  let leftPriority := input.localizedRule3EndpointPriority leftFrame
  let rightPriority := input.localizedRule3EndpointPriority rightFrame
  match leftPriority, rightPriority with
  | .nonstereogenic, _ | _, .nonstereogenic =>
      some { leftPriority, rightPriority, geometry := .nonstereogenic }
  | .senior leftReference, .senior rightReference => do
      let leftPoint ← input.spatialPointAt? left
      let rightPoint ← input.spatialPointAt? right
      let leftReferencePoint ← input.spatialPointAt? leftReference
      let rightReferencePoint ← input.spatialPointAt? rightReference
      let geometry ← rule3GeometryOfSpatialReferences? leftPoint rightPoint
        leftReferencePoint rightReferencePoint
      some { leftPriority, rightPriority, geometry }

theorem localizedRule3ExtendedDescriptorBearingSpatialUnitExec?_eq_original
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame) :
    input.localizedRule3ExtendedDescriptorBearingSpatialUnitExec? left right leftFrame rightFrame = input.localizedRule3ExtendedDescriptorBearingSpatialUnit? left right leftFrame rightFrame := by
  rfl

def localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel) := do
  let topology ← input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence
  let leftCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
    target view rule3FrameOf topology.left topology.right topology.leftCursor
  let rightCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
    target view rule3FrameOf topology.right topology.left topology.rightCursor
  let unit ← input.localizedRule3DescriptorBearingSpatialUnitExec?
    topology.left topology.right
    leftCompilation.endpointFrame rightCompilation.endpointFrame
  some { topology, leftCompilation, rightCompilation, unit }

theorem localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec? target occurrence view rule3FrameOf = input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith? target occurrence view rule3FrameOf := by
  simp only [localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?, localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?,
    localizedRule3PhysicalEndpointCursorFrameExec?_eq_original,
    ← buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?,
    localizedRule3DescriptorBearingSpatialUnitExec?_eq_original]

def localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel) := do
  let topology ← input.localizedRule3OddCumuleneEndpointCursorFrameExec?
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence
  let leftCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
    target view rule3FrameOf topology.initial.left topology.initial.right
      topology.initial.leftCursor
  let rightCompilation ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
    target view rule3FrameOf topology.right topology.rightPartner topology.rightCursor
  let unit ← input.localizedRule3ExtendedDescriptorBearingSpatialUnitExec?
    topology.initial.left topology.right
    leftCompilation.endpointFrame rightCompilation.endpointFrame
  some { topology, leftCompilation, rightCompilation, unit }

theorem localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec? target occurrence view rule3FrameOf = input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith? target occurrence view rule3FrameOf := by
  simp only [localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?, localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?,
    localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original,
    ← buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?,
    localizedRule3ExtendedDescriptorBearingSpatialUnitExec?_eq_original]

def localizedRule3RingClosureMoleculeRouteExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3RingClosureMoleculeRoute carrierFuel) := do
  let entry ← input.localizedRule3CumulatedAxisEntryExec? occurrence
  match entry with
  | .ringClosure initial closure =>
      match input.localizedCyclicCumuleneComponentContainingExec? initial.left with
      | none => some (.ordinaryCyclicDoubleBondSystem initial closure)
      | some component => some (.fullyCyclicCumulene initial closure component)
  | .terminalStart _ | .internal _ _ | .branched _ _ _ _ => none

theorem localizedRule3RingClosureMoleculeRouteExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedRule3RingClosureMoleculeRouteExec? occurrence = input.localizedRule3RingClosureMoleculeRoute? occurrence := by
  simp only [localizedRule3RingClosureMoleculeRouteExec?, localizedRule3RingClosureMoleculeRoute?,
    localizedRule3CumulatedAxisEntryExec?_eq_original,
    localizedCyclicCumuleneComponentContainingExec?_eq_original]
  rfl

def localizedRule3CyclicAuthorityRouteExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3CyclicAuthorityRoute carrierFuel) := do
  let moleculeRoute ← input.localizedRule3RingClosureMoleculeRouteExec? occurrence
  match moleculeRoute with
  | .fullyCyclicCumulene initial closure component =>
      some (.fullyCyclicCumulene initial closure component)
  | .ordinaryCyclicDoubleBondSystem initial closure =>
      match input.localizedMonocyclicDoubleBondAtExec? initial.left initial.right with
      | none => some (.ordinaryNonmonocyclic initial closure)
      | some carrier =>
          let doubleBondCount := input.localizedDoubleBondCountIn carrier.ring
          match BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy
              carrier.ring.card doubleBondCount with
          | none =>
              some (.ordinaryMonocyclicPolicyGap
                initial closure carrier doubleBondCount)
          | some policy =>
              some (.ordinaryMonocyclicPolicy initial closure
                { carrier, doubleBondCount, policy })

theorem localizedRule3CyclicAuthorityRouteExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedRule3CyclicAuthorityRouteExec? occurrence = input.localizedRule3CyclicAuthorityRoute? occurrence := by
  simp only [localizedRule3CyclicAuthorityRouteExec?, localizedRule3CyclicAuthorityRoute?,
    localizedRule3RingClosureMoleculeRouteExec?_eq_original,
    localizedMonocyclicDoubleBondAtExec?_eq_original]
  rfl

def localizedRule3OrdinaryMonocyclicPolicyAtOccurrenceExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3OrdinaryMonocyclicPolicyAtOccurrenceResult carrierFuel) := do
  let axis ← input.localizedRule3CumulatedEndpointCursorFrameExec?
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence
  if ordinary : axis.doubleBondCount = 1 then
    let policyResult ←
      input.localizedMonocyclicDoubleBondPolicyAtExec? axis.initial.left axis.initial.right
    some { axis, ordinary, policyResult }
  else none

theorem localizedRule3OrdinaryMonocyclicPolicyAtOccurrenceExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrenceExec? occurrence = input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence? occurrence := by
  simp only [localizedRule3OrdinaryMonocyclicPolicyAtOccurrenceExec?, localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?,
    localizedRule3CumulatedEndpointCursorFrameExec?_eq_original,
    localizedMonocyclicDoubleBondPolicyAtExec?_eq_original]

def localizedRule3OrdinaryMonocyclicEZWithExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3OrdinaryMonocyclicEZResult carrierFuel) := do
  let routed ← input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrenceExec? occurrence
  match routed.policyResult.policy with
  | .permanentlyOmit => none
  | .requireEZ => do
      let leftCompilation ←
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
          target view rule3FrameOf routed.initial.left routed.initial.right
            routed.initial.leftCursor
      let rightCompilation ←
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
          target view rule3FrameOf routed.initial.right routed.initial.left
            routed.initial.rightCursor
      let unit ← input.localizedRule3DescriptorBearingSpatialUnitExec?
        routed.initial.left routed.initial.right leftCompilation.endpointFrame
          rightCompilation.endpointFrame
      let cyclicGeometry ← monocyclicSeniorLigandGeometryOfRule3? unit.geometry
      let descriptor ← BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?
        routed.policyResult.carrier.ring.card routed.policyResult.doubleBondCount
          cyclicGeometry
      some
        { axis := routed.axis
          ordinary := routed.ordinary
          policyResult := routed.policyResult
          leftCompilation
          rightCompilation
          unit
          descriptor }

theorem localizedRule3OrdinaryMonocyclicEZWithExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    input.localizedRule3OrdinaryMonocyclicEZWithExec? target occurrence view rule3FrameOf = input.localizedRule3OrdinaryMonocyclicEZWith? target occurrence view rule3FrameOf := by
  simp only [localizedRule3OrdinaryMonocyclicEZWithExec?, localizedRule3OrdinaryMonocyclicEZWith?,
    localizedRule3OrdinaryMonocyclicPolicyAtOccurrenceExec?_eq_original,
    ← buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?,
    localizedRule3DescriptorBearingSpatialUnitExec?_eq_original]
  rfl

def localizedRule3RequiredMonocyclicEZWithExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel) := do
  let route ← input.localizedRule3CyclicAuthorityRouteExec? occurrence
  match route with
  | .ordinaryMonocyclicPolicy initial closure policyResult =>
      match policyResult.policy with
      | .permanentlyOmit => none
      | .requireEZ => do
          let leftCompilation ←
            input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
              target view rule3FrameOf initial.left initial.right initial.leftCursor
          let rightCompilation ←
            input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
              target view rule3FrameOf initial.right initial.left initial.rightCursor
          let unit ← input.localizedRule3DescriptorBearingSpatialUnitExec?
            initial.left initial.right leftCompilation.endpointFrame
              rightCompilation.endpointFrame
          let cyclicGeometry ← monocyclicSeniorLigandGeometryOfRule3? unit.geometry
          let descriptor ← BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?
            policyResult.carrier.ring.card policyResult.doubleBondCount cyclicGeometry
          some
            { initial
              closure
              policyResult
              leftCompilation
              rightCompilation
              unit
              descriptor }
  | .fullyCyclicCumulene _ _ _
  | .ordinaryMonocyclicPolicyGap _ _ _ _
  | .ordinaryNonmonocyclic _ _ => none

theorem localizedRule3RequiredMonocyclicEZWithExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    input.localizedRule3RequiredMonocyclicEZWithExec? target occurrence view rule3FrameOf = input.localizedRule3RequiredMonocyclicEZWith? target occurrence view rule3FrameOf := by
  simp only [localizedRule3RequiredMonocyclicEZWithExec?, localizedRule3RequiredMonocyclicEZWith?,
    localizedRule3CyclicAuthorityRouteExec?_eq_original,
    ← buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?,
    localizedRule3DescriptorBearingSpatialUnitExec?_eq_original]
  rfl

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
