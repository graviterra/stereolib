import TetraStereo.OneCenter.LocalizedRerootShortCircuitRule3Key
import TetraStereo.OneCenter.LocalizedOccurrenceFiniteCarrier
import TetraStereo.OneCenter.LocalizedRule3OmissionCertificate

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- A strict constitutional comparison determines this endpoint for every dependency view and frame
callback. The runtime constructor checks atomic roots first, then complete constitutional keys. -/
structure LocalizedRule3StrictEndpointCertificate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpoint partner : input.Atom) (cursor : input.LocalizedRerootCursor fuel) where
  result : input.LocalizedRule3ShortCircuitEndpointResult
  computed : ∀ (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) callback,
    input.localizedRule3ShortCircuitEndpointPriorityExec?
      target view callback endpoint partner cursor = some result

def localizedRule3StrictEndpointCertificate?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpoint partner : input.Atom) (cursor : input.LocalizedRerootCursor fuel) :
    Option (input.LocalizedRule3StrictEndpointCertificate endpoint partner cursor) :=
  match candidates : input.localizedRule3ExplicitSubstituents endpoint partner with
  | [first, second] =>
      match firstComputed : input.localizedRule3ReferenceCursorExec? cursor first with
      | none => none
      | some firstCursor =>
          match secondComputed : input.localizedRule3ReferenceCursorExec? cursor second with
          | none => none
          | some secondCursor =>
              match strict : input.compareLocalizedRerootCursorConstitutionalRoot
                  firstCursor secondCursor with
              | .eq =>
                  match constitutional : input.compareLocalizedConstitutionalCursors?
                      firstCursor secondCursor with
                  | some .gt => some
                      { result := { priority := .senior first, firstCandidate := first }
                        computed := fun target view callback =>
                          input.localizedRule3ShortCircuitEndpointPriorityExec?_constitutional_gt
                            target view callback endpoint partner first second cursor candidates
                            firstCursor secondCursor firstComputed secondComputed strict constitutional }
                  | some .lt => some
                      { result := { priority := .senior second, firstCandidate := first }
                        computed := fun target view callback =>
                          input.localizedRule3ShortCircuitEndpointPriorityExec?_constitutional_lt
                            target view callback endpoint partner first second cursor candidates
                            firstCursor secondCursor firstComputed secondComputed strict constitutional }
                  | _ => none
              | .gt => some
                  { result := { priority := .senior first, firstCandidate := first }
                    computed := fun target view callback =>
                      input.localizedRule3ShortCircuitEndpointPriorityExec?_strict_gt
                        target view callback endpoint partner first second cursor candidates
                        firstCursor secondCursor firstComputed secondComputed strict }
              | .lt => some
                  { result := { priority := .senior second, firstCandidate := first }
                    computed := fun target view callback =>
                      input.localizedRule3ShortCircuitEndpointPriorityExec?_strict_lt
                        target view callback endpoint partner first second cursor candidates
                        firstCursor secondCursor firstComputed secondComputed strict }
  | _ => none

/-- Finite local evidence that this occurrence's node reader never demands a recursive frame.
Its output still observes the caller's physical-unit exclusion list. -/
structure LocalizedRule3CallbackFreeNodeCertificate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) where
  observation : List input.LocalizedRule3PhysicalUnitId →
    Option input.LocalizedRule3SpatialNodeResult
  computed : ∀ (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) callback excluded,
    input.localizedRule3ShortCircuitNodeWithExec?
      target occurrence view callback excluded = some (observation excluded)

/-- Construct local readiness without invoking any recursive stereo frame. Geometric
nodes must have an ordinary route, two strict constitutional endpoint comparisons and successful exact
geometry. Structural nodes and topology-determined omission routes need no geometry. -/
def localizedRule3CallbackFreeNodeCertificate?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option (input.LocalizedRule3CallbackFreeNodeCertificate occurrence) :=
  if edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence then
    match routed : input.localizedRule3OrdinaryRouteCertificate? occurrence with
    | none =>
        match input.localizedRule3OmissionCertificate? occurrence with
        | none => none
        | some omission => some
            { observation := fun _ => none
              computed := omission.computed }
    | some _ =>
        match topologyComputed : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
        | none => none
        | some topology =>
            match input.localizedRule3StrictEndpointCertificate?
                topology.left topology.right topology.leftCursor with
            | none => none
            | some left =>
                match input.localizedRule3StrictEndpointCertificate?
                    topology.right topology.left topology.rightCursor with
                | none => none
                | some right =>
                    match unitComputed : input.localizedRule3ShortCircuitSpatialUnit?
                        topology.left topology.right left.result right.result with
                    | none => none
                    | some unit =>
                        let spatial : input.LocalizedRule3ShortCircuitSpatialResult fuel :=
                          { topology, leftEndpoint := left.result,
                            rightEndpoint := right.result, unit }
                        let observed := input.localizedRule3ShortCircuitSpatialObservation spatial
                        some
                          { observation := fun excluded =>
                              if excluded.contains observed.physicalUnitId
                                then none else some observed
                            computed := by
                              intro target view callback excluded
                              have success : input.localizedRule3ShortCircuitSpatialUnitWithExec?
                                  target occurrence view callback = some spatial := by
                                simp [localizedRule3ShortCircuitSpatialUnitWithExec?,
                                  topologyComputed, left.computed target view callback,
                                  right.computed target view callback, unitComputed, spatial]
                              simp [localizedRule3ShortCircuitNodeWithExec?, routed,
                                success, observed] }
  else some
    { observation := fun _ => none
      computed := by
        intro target view callback excluded
        simp [localizedRule3ShortCircuitNodeWithExec?,
          localizedRule3OrdinaryRouteCertificate?,
          localizedDescriptorBearingRule3NodeWithExec?, edge] }

/-- An automatically checked carrier-wide readiness witness. It assumes no completed key,
descriptor, auxiliary assignment, or successful recursive callback. -/
structure LocalizedRule3CallbackFreeCarrierCertificate
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) : Type where
  ready : ∀ occurrence : input.LocalizedCIPOccurrence fuel,
    ∃ certificate, input.localizedRule3CallbackFreeNodeCertificate? occurrence = some certificate

def localizedRule3CallbackFreeCarrierCertificate?
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    Option (input.LocalizedRule3CallbackFreeCarrierCertificate fuel) :=
  if tested : (input.localizedOccurrenceCarrier fuel).all (fun occurrence =>
      (input.localizedRule3CallbackFreeNodeCertificate? occurrence).isSome) = true then
    some
      { ready := by
          intro occurrence
          have has := (List.all_eq_true.mp tested) occurrence
            (input.localizedOccurrenceCarrier_complete fuel occurrence)
          cases computed : input.localizedRule3CallbackFreeNodeCertificate? occurrence with
          | none => simp [computed] at has
          | some certificate => exact ⟨certificate, rfl⟩ }
  else none

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
