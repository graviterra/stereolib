import TetraStereo.OneCenter.LocalizedOrdinaryEndpointParity
import TetraStereo.OneCenter.LocalizedOrdinaryAcyclicTopology

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OrdinaryPlanar

abbrev FrameMeaning (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :=
  input.DeclarativeLocalizedDescriptorBearingRule3Frame target view
    (localizedDescriptorBearingRule3EvaluationFuel fuel)

/-- One endpoint retains its exact occurrence compilation and the decisive parity. -/
structure Endpoint (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (atom partner : input.Atom) (cursor : input.LocalizedRerootCursor fuel) where
  frame : input.LocalizedRule3OccurrenceEndpointKeyFrame fuel
  compiled : input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith target view
    (FrameMeaning input target view) atom partner cursor frame
  selection : Selection input
  selected : SelectionMeaning input frame.endpointFrame selection

def endpoint? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (readerExact : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (atom partner : input.Atom) (cursor : input.LocalizedRerootCursor fuel) :
    Option (Endpoint input target view atom partner cursor) :=
  let callback := OriginalWithChildren.buildLocalizedDescriptorBearingRule3FrameExec? input
    readChildren target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
  match computed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
      target view callback atom partner cursor with
  | none => none
  | some frame =>
    match select? input frame.endpointFrame with
    | none => none
    | some selection => some
        { frame, selection := selection.val, selected := selection.property
          compiled := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
            target view callback (FrameMeaning input target view)
            (fun cursors result frameComputed =>
              input.buildLocalizedDescriptorBearingRule3Frame?_sound target view
                (localizedDescriptorBearingRule3EvaluationFuel fuel) cursors result
                ((OriginalWithChildren.frame_eq_original input readChildren readerExact
                  target view _ cursors).symm.trans frameComputed))
            atom partner cursor frame
            ((input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
              target view callback atom partner cursor).trans computed) }

/-- Exact molecular point lookups and the independent rational spatial relation. -/
structure Geometry (input : CertifiedLocalizedCIPInput)
    (left right leftReference rightReference : input.Atom) where
  value : OfficialRule3Geometry
  meaning : ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint,
    input.spatialPointAt? left = some leftPoint ∧
    input.spatialPointAt? right = some rightPoint ∧
    input.spatialPointAt? leftReference = some leftReferencePoint ∧
    input.spatialPointAt? rightReference = some rightReferencePoint ∧
    RationalRule3SpatialGeometry leftPoint rightPoint leftReferencePoint rightReferencePoint value

def geometry? (input : CertifiedLocalizedCIPInput)
    (left right leftReference rightReference : input.Atom) :
    Option (Geometry input left right leftReference rightReference) :=
  match leftComputed : input.spatialPointAt? left with
  | none => none
  | some leftPoint =>
    match rightComputed : input.spatialPointAt? right with
    | none => none
    | some rightPoint =>
      match leftReferenceComputed : input.spatialPointAt? leftReference with
      | none => none
      | some leftReferencePoint =>
        match rightReferenceComputed : input.spatialPointAt? rightReference with
        | none => none
        | some rightReferencePoint =>
          match computed : rule3GeometryOfSpatialReferences?
              leftPoint rightPoint leftReferencePoint rightReferencePoint with
          | none => none
          | some value => some
              { value
                meaning := ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
                  leftComputed, rightComputed, leftReferenceComputed, rightReferenceComputed,
                  (rule3GeometryOfSpatialReferences?_eq_some_iff _ _ _ _ value).mp computed⟩ }

abbrev target (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :=
  input.localizedAtomRootOccurrenceExecutable fuel bond.1.1

abbrev dependencyView (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) (bond : input.LocalizedCanonicalDoubleBond) :=
  input.localizedDependencyView state (target input fuel bond)

/-- A data-derived ordinary acyclic result. Every field is tied to this physical bond and the
supplied auxiliary state; the outcome retains the ordinary/enantiomorphic family distinction. -/
structure Assignment (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) (bond : input.LocalizedCanonicalDoubleBond) where
  topology : Topology input fuel bond
  left : Endpoint input (target input fuel bond) (dependencyView input fuel state bond)
    topology.axis.initial.left topology.axis.initial.right topology.axis.initial.leftCursor
  right : Endpoint input (target input fuel bond) (dependencyView input fuel state bond)
    topology.axis.right topology.axis.rightPartner topology.axis.rightCursor
  geometry : Geometry input bond.1.1 bond.1.2 left.selection.reference right.selection.reference
  outcome : StereoOutcome
  outcomeMeaning : AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBondPlanarOutcomeJudgment
    left.selection.enantiomorphic right.selection.enantiomorphic geometry.value outcome

def assignment? (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) (bond : input.LocalizedCanonicalDoubleBond) :
    Option (Assignment input fuel state bond) := do
  let topology ← topology? input fuel bond
  let readChildren := input.localizedRerootChildrenFromCarrier? (input.localizedOccurrenceCarrier fuel)
  let left ← endpoint? input readChildren
    (fun cursor => input.localizedRerootChildrenFromCarrier?_eq_executable cursor)
    (target input fuel bond) (dependencyView input fuel state bond)
    topology.axis.initial.left topology.axis.initial.right topology.axis.initial.leftCursor
  let right ← endpoint? input readChildren
    (fun cursor => input.localizedRerootChildrenFromCarrier?_eq_executable cursor)
    (target input fuel bond) (dependencyView input fuel state bond)
    topology.axis.right topology.axis.rightPartner topology.axis.rightCursor
  let geometry ← geometry? input bond.1.1 bond.1.2 left.selection.reference right.selection.reference
  match computed : AuthoritativeChemicalInput.aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
      left.selection.enantiomorphic right.selection.enantiomorphic geometry.value with
  | none => none
  | some outcome =>
      return {
        topology := topology
        left := left
        right := right
        geometry := geometry
        outcome := outcome
        outcomeMeaning := (AuthoritativeChemicalInput.aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?_eq_some_iff
          _ _ _ _).mp computed }

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OrdinaryPlanar
