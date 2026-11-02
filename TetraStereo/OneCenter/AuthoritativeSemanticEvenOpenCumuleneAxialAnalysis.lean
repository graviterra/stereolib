import TetraStereo.OneCenter.AuthoritativeSemanticOddOpenCumuleneSpatialAnalysis
import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Source-canonical even-open-cumulene axial analysis

The exhaustive source-level even-open-cumulene carrier list is joined here to the same concrete
Rules-1a--5 auxiliary fixed point used by the tetrahedral, ordinary-double-bond, and odd-cumulene
analyzers.  Exact rational source coordinates determine `Rₐ/Sₐ`; no descriptor is supplied by
the caller.
-/

/-- One final source-indexed axial even-open-cumulene assignment. -/
structure AromaticCanonicalEvenOpenCumuleneAxialAssignment
    (source : AuthoritativeChemicalInput) where
  unit : List source.AromaticCanonicalAtom
  terminals : source.AromaticCanonicalOpenCumuleneTerminals
  startReference : source.AromaticCanonicalAtom
  endReference : source.AromaticCanonicalAtom
  descriptor : AxialDescriptor
  deriving DecidableEq

/-- Analyze one canonical even-open-cumulene physical unit. -/
noncomputable def aromaticCanonicalEvenOpenCumuleneAxialAssignment?
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalEvenOpenCumuleneAxialAssignment := do
  let terminals ← source.aromaticCanonicalOpenCumuleneTerminals? unit
  let startFrame ←
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
      carrierFuel terminals.left terminals.leftPartner
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel terminals.left)
      (2 * (carrierFuel + 1))
  let endFrame ←
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
      carrierFuel terminals.right terminals.rightPartner
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel terminals.right)
      (2 * (carrierFuel + 1))
  let startSelection ←
    source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? startFrame
  let endSelection ←
    source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? endFrame
  let axisStartPoint ← source.aromaticCanonicalSpatialPointAt? terminals.left
  let axisEndPoint ← source.aromaticCanonicalSpatialPointAt? terminals.right
  let startReferencePoint ←
    source.aromaticCanonicalSpatialPointAt? startSelection.reference
  let endReferencePoint ←
    source.aromaticCanonicalSpatialPointAt? endSelection.reference
  let descriptor ← axialDescriptorOfSpatialReferences?
    axisStartPoint axisEndPoint startReferencePoint endReferencePoint
  some {
    unit
    terminals
    startReference := startSelection.reference
    endReference := endSelection.reference
    descriptor
  }

/-- Independent topology, endpoint Rules-1a--5, Rule-5 parity, exact-coordinate, and axial
descriptor meaning of a final even-open-cumulene assignment. -/
def DeclarativeAromaticCanonicalEvenOpenCumuleneAxialAssignment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) : Prop :=
  assignment.unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits ∧
    source.DeclarativeAromaticCanonicalOpenCumuleneTerminals
      assignment.unit assignment.terminals ∧
    ∃ startFrame endFrame startSelection endSelection
        axisStartPoint axisEndPoint startReferencePoint endReferencePoint,
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel assignment.terminals.left assignment.terminals.leftPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel assignment.terminals.left)
        (2 * (carrierFuel + 1)) startFrame ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel assignment.terminals.right assignment.terminals.rightPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel assignment.terminals.right)
        (2 * (carrierFuel + 1)) endFrame ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        startFrame startSelection ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        endFrame endSelection ∧
      assignment.startReference = startSelection.reference ∧
      assignment.endReference = endSelection.reference ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        assignment.terminals.left axisStartPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        assignment.terminals.right axisEndPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        startSelection.reference startReferencePoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        endSelection.reference endReferencePoint ∧
      RationalAxialSpatialDescriptor axisStartPoint axisEndPoint
        startReferencePoint endReferencePoint assignment.descriptor

set_option maxHeartbeats 1000000 in
/-- Every emitted even-open-cumulene descriptor has independent exhaustive topology, terminal
Rules-1a--5 priorities, Rule-5 parity, exact source coordinates, and rational P-92 axial
descriptor meaning. -/
theorem aromaticCanonicalEvenOpenCumuleneAxialAssignment?_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment)
    (computed : source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
      carrierFuel ruleFuel unit = some assignment) :
    source.DeclarativeAromaticCanonicalEvenOpenCumuleneAxialAssignment
      carrierFuel ruleFuel assignment := by
  unfold aromaticCanonicalEvenOpenCumuleneAxialAssignment? at computed
  cases terminalsComputed : source.aromaticCanonicalOpenCumuleneTerminals? unit with
  | none => simp [terminalsComputed] at computed
  | some terminals =>
    cases startFrameComputed :
        source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel terminals.left terminals.leftPartner
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel terminals.left)
          (2 * (carrierFuel + 1)) with
    | none => simp [terminalsComputed, startFrameComputed] at computed
    | some startFrame =>
      cases endFrameComputed :
          source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
            carrierFuel terminals.right terminals.rightPartner
            (source.aromaticCanonicalConcreteDependencyViewAt
              carrierFuel ruleFuel terminals.right)
            (2 * (carrierFuel + 1)) with
      | none =>
          simp [terminalsComputed, startFrameComputed, endFrameComputed] at computed
      | some endFrame =>
        cases startSelectionComputed :
            source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?
              startFrame with
        | none =>
            simp [terminalsComputed, startFrameComputed, endFrameComputed,
              startSelectionComputed] at computed
        | some startSelection =>
          cases endSelectionComputed :
              source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?
                endFrame with
          | none =>
              simp [terminalsComputed, startFrameComputed, endFrameComputed,
                endSelectionComputed] at computed
          | some endSelection =>
            cases axisStartPointComputed :
                source.aromaticCanonicalSpatialPointAt? terminals.left with
            | none =>
                simp [terminalsComputed, startFrameComputed, endFrameComputed,
                  axisStartPointComputed] at computed
            | some axisStartPoint =>
              cases axisEndPointComputed :
                  source.aromaticCanonicalSpatialPointAt? terminals.right with
              | none =>
                  simp [terminalsComputed, startFrameComputed, endFrameComputed,
                    axisStartPointComputed, axisEndPointComputed] at computed
              | some axisEndPoint =>
                cases startReferencePointComputed :
                    source.aromaticCanonicalSpatialPointAt?
                      startSelection.reference with
                | none =>
                    simp [terminalsComputed, startFrameComputed, endFrameComputed,
                      startSelectionComputed, endSelectionComputed,
                      axisStartPointComputed, axisEndPointComputed,
                      startReferencePointComputed] at computed
                | some startReferencePoint =>
                  cases endReferencePointComputed :
                      source.aromaticCanonicalSpatialPointAt?
                        endSelection.reference with
                  | none =>
                      simp [terminalsComputed, startFrameComputed, endFrameComputed,
                        endSelectionComputed,
                        axisStartPointComputed, axisEndPointComputed,
                        endReferencePointComputed] at computed
                  | some endReferencePoint =>
                    cases descriptorComputed : axialDescriptorOfSpatialReferences?
                        axisStartPoint axisEndPoint startReferencePoint
                          endReferencePoint with
                    | none =>
                        simp [terminalsComputed, startFrameComputed,
                          endFrameComputed, startSelectionComputed,
                          endSelectionComputed, axisStartPointComputed,
                          axisEndPointComputed, startReferencePointComputed,
                          endReferencePointComputed, descriptorComputed] at computed
                    | some descriptor =>
                      simp [terminalsComputed, startFrameComputed,
                        endFrameComputed, startSelectionComputed,
                        endSelectionComputed, axisStartPointComputed,
                        axisEndPointComputed, startReferencePointComputed,
                        endReferencePointComputed, descriptorComputed] at computed
                      subst assignment
                      exact ⟨owner,
                        (source.aromaticCanonicalOpenCumuleneTerminals?_eq_some_iff
                          unit terminals).mp terminalsComputed,
                        startFrame, endFrame, startSelection, endSelection,
                        axisStartPoint, axisEndPoint, startReferencePoint,
                        endReferencePoint,
                        source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
                          carrierFuel terminals.left terminals.leftPartner
                          (source.aromaticCanonicalConcreteDependencyViewAt
                            carrierFuel ruleFuel terminals.left)
                          (2 * (carrierFuel + 1)) startFrame startFrameComputed,
                        source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
                          carrierFuel terminals.right terminals.rightPartner
                          (source.aromaticCanonicalConcreteDependencyViewAt
                            carrierFuel ruleFuel terminals.right)
                          (2 * (carrierFuel + 1)) endFrame endFrameComputed,
                        source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_sound
                          startFrame startSelection startSelectionComputed,
                        source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_sound
                          endFrame endSelection endSelectionComputed,
                        rfl, rfl,
                        (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                          terminals.left axisStartPoint).mp axisStartPointComputed,
                        (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                          terminals.right axisEndPoint).mp axisEndPointComputed,
                        (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                          startSelection.reference startReferencePoint).mp
                            startReferencePointComputed,
                        (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                          endSelection.reference endReferencePoint).mp
                            endReferencePointComputed,
                        (axialDescriptorOfSpatialReferences?_eq_some_iff
                          axisStartPoint axisEndPoint startReferencePoint
                            endReferencePoint descriptor).mp descriptorComputed⟩

/-- Whole-molecule analysis of every canonical even-open-cumulene physical unit. -/
noncomputable def analyzeAromaticCanonicalEvenOpenCumuleneAxial
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalEvenOpenCumuleneAxialAssignment :=
  source.aromaticCanonicalEvenOpenCumuleneUnits.filterMap fun unit =>
    source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
      carrierFuel ruleFuel unit

/-- Exact executable membership of the whole even-open-cumulene analyzer. -/
theorem mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) :
    assignment ∈ source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
        carrierFuel ruleFuel ↔
      ∃ unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits,
        source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
          carrierFuel ruleFuel unit = some assignment := by
  rw [analyzeAromaticCanonicalEvenOpenCumuleneAxial, List.mem_filterMap]

/-- Every whole-molecule even-open-cumulene result satisfies the independent source topology,
priority, parity, coordinate, and axial descriptor judgment. -/
theorem analyzeAromaticCanonicalEvenOpenCumuleneAxial_member_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment)
    (present : assignment ∈ source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
      carrierFuel ruleFuel) :
    source.DeclarativeAromaticCanonicalEvenOpenCumuleneAxialAssignment
      carrierFuel ruleFuel assignment := by
  obtain ⟨unit, owner, emitted⟩ :=
    (source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
      carrierFuel ruleFuel assignment).mp present
  exact source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_sound
    carrierFuel ruleFuel unit owner assignment emitted

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
