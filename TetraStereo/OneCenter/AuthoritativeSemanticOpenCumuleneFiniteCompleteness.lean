import TetraStereo.OneCenter.AuthoritativeSemanticEvenOpenCumuleneAxialAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Finite-fuel chemical completeness for source-canonical open cumulenes

The readiness predicates below contain chemical dependency, strict-priority, and nondegenerate
coordinate evidence, but no premise asserting success of an executable recursive builder.  The
existing finite occurrence bound constructs both endpoint Rules-1a--5 frames; exact selector and
geometry theorems then construct the final descriptor.
-/

/-!
## Finite totality of canonical open-cumulene units

The readiness records below always quantify over a caller-chosen `terminals` witness together
with the proof that the canonical unit computes that witness.  Nothing above established that a
canonical unit admits any terminal witness at all.  A member of the exhaustive list has at least
two atoms only because reversal normalization is length-preserving, and that fact was not
recorded.  Without it the terminal half of the readiness record could be vacuous for a unit whose
own chemical Rules-1a--5, selection and geometry evidence exists.

The lemmas here close that finite-totality boundary: reversal normalization preserves length, and
every retained odd or even open-cumulene unit therefore has a computed terminal pair.  The
open-cumulene family has at least three atoms, so the length-two maximal path is exactly an
individual double bond and never routed as a cumulene.  The `terminals` field of the
finite-completeness evidence is thus derived from canonical ownership rather than supplied
independently by the caller.
-/

/-- A nonempty list has a computed head.  Stated over an arbitrary element type so that every
call site below determines the list syntactically instead of leaving the element universe as a
metavariable. -/
private theorem exists_head?_of_length_pos
    {α : Type*} {atoms : List α} (positive : 0 < atoms.length) :
    ∃ head, atoms.head? = some head := by
  cases atoms with
  | nil => simp at positive
  | cons head tail => exact ⟨head, rfl⟩

/-- Reversal normalization chooses only the original orientation or its reversal, so it preserves
the physical atom count of a canonical cumulene path. -/
theorem aromaticCanonicalNormalizeCumulenePath_length
    {source : AuthoritativeChemicalInput}
    (path : List source.AromaticCanonicalAtom) :
    (aromaticCanonicalNormalizeCumulenePath path).length = path.length := by
  unfold aromaticCanonicalNormalizeCumulenePath
  cases headObserved : path.head? with
  | none => simp
  | some first =>
      cases lastObserved : path.getLast? with
      | none => simp
      | some last =>
          by_cases ordered : first ≤ last <;>
            simp [ordered, List.length_reverse]

/-- Terminal extraction is total on every path of at least two atoms. -/
theorem exists_aromaticCanonicalOpenCumuleneTerminals?_of_two_le_length
    (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom)
    (length : 2 ≤ path.length) :
    ∃ terminals, source.aromaticCanonicalOpenCumuleneTerminals? path = some terminals := by
  obtain ⟨left, leftComputed⟩ :=
    exists_head?_of_length_pos (atoms := path) (by omega : 0 < path.length)
  obtain ⟨leftPartner, leftPartnerComputed⟩ :=
    exists_head?_of_length_pos (atoms := path.tail) (by rw [List.length_tail]; omega)
  obtain ⟨right, rightComputed⟩ :=
    exists_head?_of_length_pos (atoms := path.reverse) (by rw [List.length_reverse]; omega)
  obtain ⟨rightPartner, rightPartnerComputed⟩ :=
    exists_head?_of_length_pos (atoms := path.reverse.tail)
      (by rw [List.length_tail, List.length_reverse]; omega)
  refine ⟨{ left := left
            leftPartner := leftPartner
            rightPartner := rightPartner
            right := right }, ?_⟩
  exact (source.aromaticCanonicalOpenCumuleneTerminals?_eq_some_iff path _).mpr
    ⟨leftComputed, leftPartnerComputed, rightComputed, rightPartnerComputed⟩

/-- Every exhaustively perceived open-cumulene unit computes a terminal pair; the caller supplied
`terminals` field is therefore determined by membership rather than independently witnessed. -/
theorem exists_aromaticCanonicalOpenCumuleneTerminals?_of_mem_openCumuleneUnits
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOpenCumuleneUnits route) :
    ∃ terminals, source.aromaticCanonicalOpenCumuleneTerminals? unit = some terminals := by
  obtain ⟨path, valid, normalized⟩ :=
    (source.mem_aromaticCanonicalOpenCumuleneUnits_iff route unit).mp owner
  have unitBound : 2 ≤ unit.length := by
    rw [← normalized, aromaticCanonicalNormalizeCumulenePath_length]
    exact valid.1.1
  exact exists_aromaticCanonicalOpenCumuleneTerminals?_of_two_le_length source unit unitBound

/-- Odd-route corollary: every canonical odd-open-cumulene carrier computes its terminals. -/
theorem exists_aromaticCanonicalOpenCumuleneTerminals?_of_mem_oddOpenCumuleneUnits
    (source : AuthoritativeChemicalInput)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits) :
    ∃ terminals, source.aromaticCanonicalOpenCumuleneTerminals? unit = some terminals :=
  source.exists_aromaticCanonicalOpenCumuleneTerminals?_of_mem_openCumuleneUnits
    .oddOpenCumulene unit owner

/-- Even-route corollary: every canonical even-open-cumulene carrier computes its terminals. -/
theorem exists_aromaticCanonicalOpenCumuleneTerminals?_of_mem_evenOpenCumuleneUnits
    (source : AuthoritativeChemicalInput)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits) :
    ∃ terminals, source.aromaticCanonicalOpenCumuleneTerminals? unit = some terminals :=
  source.exists_aromaticCanonicalOpenCumuleneTerminals?_of_mem_openCumuleneUnits
    .evenOpenCumulene unit owner

/-- A routed odd open cumulene spans at least three atoms: a two-atom maximal path is exactly one
ordinary double bond and is never routed to the odd-open-cumulene family. -/
theorem aromaticCanonicalOddOpenCumuleneUnits_length_ge_three
    (source : AuthoritativeChemicalInput)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits) :
    3 ≤ unit.length := by
  obtain ⟨path, valid, normalized⟩ :=
    (source.mem_aromaticCanonicalOddOpenCumuleneUnits_iff unit).mp owner
  obtain ⟨_nonempty, applies⟩ := valid.2.2.2
  change (path.length - 1 ≠ 1) ∧ Odd (path.length - 1) at applies
  have countNeOne : path.length - 1 ≠ 1 := applies.1
  have lengthLower : 2 ≤ path.length := valid.1.1
  have pathLower : 3 ≤ path.length := by omega
  rw [← normalized, aromaticCanonicalNormalizeCumulenePath_length]
  exact pathLower

/-- A routed even open cumulene spans at least three atoms; the length-two maximal path is the
individual-double-bond route, not a cumulene. -/
theorem aromaticCanonicalEvenOpenCumuleneUnits_length_ge_three
    (source : AuthoritativeChemicalInput)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits) :
    3 ≤ unit.length := by
  obtain ⟨path, valid, normalized⟩ :=
    (source.mem_aromaticCanonicalEvenOpenCumuleneUnits_iff unit).mp owner
  obtain ⟨_nonempty, applies⟩ := valid.2.2.2
  change (path.length - 1 ≠ 1) ∧ ¬ Odd (path.length - 1) at applies
  have countNeOne : path.length - 1 ≠ 1 := applies.1
  have lengthLower : 2 ≤ path.length := valid.1.1
  have pathLower : 3 ≤ path.length := by omega
  rw [← normalized, aromaticCanonicalNormalizeCumulenePath_length]
  exact pathLower

/-- Independent readiness evidence sufficient to compile one odd-open-cumulene carrier. -/
structure AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals) : Prop where
  owner : unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits
  terminalsDerived : source.DeclarativeAromaticCanonicalOpenCumuleneTerminals
    unit terminals
  leftDependencies :
    source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5DependenciesResolved
      carrierFuel terminals.left terminals.leftPartner
  rightDependencies :
    source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5DependenciesResolved
      carrierFuel terminals.right terminals.rightPartner
  leftSelectable : ∀ frame,
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel terminals.left terminals.leftPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel terminals.left)
        (2 * (carrierFuel + 1)) frame →
      ∃ selection,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          frame selection
  rightSelectable : ∀ frame,
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel terminals.right terminals.rightPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel terminals.right)
        (2 * (carrierFuel + 1)) frame →
      ∃ selection,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          frame selection
  spatiallyNondegenerate :
    ∀ (leftFrame rightFrame :
        source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
      (leftSelection rightSelection :
        source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection carrierFuel),
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        leftFrame leftSelection →
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          rightFrame rightSelection →
      ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint geometry,
        source.SemanticAromaticCanonicalSpatialPointAt terminals.left leftPoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt terminals.right rightPoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt
          leftSelection.reference leftReferencePoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt
          rightSelection.reference rightReferencePoint ∧
        RationalRule3SpatialGeometry leftPoint rightPoint
          leftReferencePoint rightReferencePoint geometry ∧
        geometry ≠ OfficialRule3Geometry.nonstereogenic

/-- Every independently ready odd-open-cumulene carrier emits at the uniform finite bound. -/
theorem exists_aromaticCanonicalOddOpenCumuleneSpatialAssignment_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals)
    (evidence : source.AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence
      carrierFuel ruleFuel unit terminals) :
    ∃ assignment,
      source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
        carrierFuel ruleFuel unit = some assignment := by
  have terminalsComputed :=
    (source.aromaticCanonicalOpenCumuleneTerminals?_eq_some_iff
      unit terminals).mpr evidence.terminalsDerived
  obtain ⟨leftFrame, leftFrameComputed⟩ :=
    source.exists_buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame_at_twice
      carrierFuel terminals.left terminals.leftPartner
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel terminals.left)
      evidence.leftDependencies
  obtain ⟨rightFrame, rightFrameComputed⟩ :=
    source.exists_buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame_at_twice
      carrierFuel terminals.right terminals.rightPartner
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel terminals.right)
      evidence.rightDependencies
  have leftFrameDerived :=
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
      carrierFuel terminals.left terminals.leftPartner
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel terminals.left)
      (2 * (carrierFuel + 1)) leftFrame leftFrameComputed
  have rightFrameDerived :=
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
      carrierFuel terminals.right terminals.rightPartner
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel terminals.right)
      (2 * (carrierFuel + 1)) rightFrame rightFrameComputed
  obtain ⟨leftSelection, leftSelectionDerived⟩ :=
    evidence.leftSelectable leftFrame leftFrameDerived
  obtain ⟨rightSelection, rightSelectionDerived⟩ :=
    evidence.rightSelectable rightFrame rightFrameDerived
  have leftSelectionComputed :=
    (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff_declarative
      leftFrame leftSelection).mpr leftSelectionDerived
  have rightSelectionComputed :=
    (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff_declarative
      rightFrame rightSelection).mpr rightSelectionDerived
  obtain ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint, geometry,
      leftPointDerived, rightPointDerived, leftReferencePointDerived,
      rightReferencePointDerived, geometryDerived, geometryNondegenerate⟩ :=
    evidence.spatiallyNondegenerate leftFrame rightFrame leftSelection rightSelection
      leftSelectionDerived rightSelectionDerived
  have leftPointComputed :=
    (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
      terminals.left leftPoint).mpr leftPointDerived
  have rightPointComputed :=
    (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
      terminals.right rightPoint).mpr rightPointDerived
  have leftReferencePointComputed :=
    (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
      leftSelection.reference leftReferencePoint).mpr leftReferencePointDerived
  have rightReferencePointComputed :=
    (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
      rightSelection.reference rightReferencePoint).mpr rightReferencePointDerived
  have geometryComputed :=
    (rule3GeometryOfSpatialReferences?_eq_some_iff
      leftPoint rightPoint leftReferencePoint rightReferencePoint geometry).mpr
        geometryDerived
  obtain ⟨outcome, outcomeComputed⟩ :
      ∃ outcome, aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
        leftSelection.enantiomorphic rightSelection.enantiomorphic geometry =
          some outcome := by
    cases geometry with
    | nonstereogenic => contradiction
    | seqcis =>
        cases leftSelection.enantiomorphic <;> cases rightSelection.enantiomorphic <;>
          simp [aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?]
    | seqtrans =>
        cases leftSelection.enantiomorphic <;> cases rightSelection.enantiomorphic <;>
          simp [aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?]
  refine ⟨{
      unit
      terminals
      leftReference := leftSelection.reference
      rightReference := rightSelection.reference
      geometry
      outcome
    }, ?_⟩
  simp [aromaticCanonicalOddOpenCumuleneSpatialAssignment?, terminalsComputed,
    leftFrameComputed, rightFrameComputed, leftSelectionComputed,
    rightSelectionComputed, leftPointComputed, rightPointComputed,
    leftReferencePointComputed, rightReferencePointComputed,
    geometryComputed, outcomeComputed]

/-- Odd-route completeness and correctness hold for the same emitted assignment. -/
theorem exists_aromaticCanonicalOddOpenCumuleneSpatialAssignment_and_judgment_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals)
    (evidence : source.AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence
      carrierFuel ruleFuel unit terminals) :
    ∃ assignment,
      source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
          carrierFuel ruleFuel unit = some assignment ∧
        source.DeclarativeAromaticCanonicalOddOpenCumuleneSpatialAssignment
          carrierFuel ruleFuel assignment := by
  obtain ⟨assignment, computed⟩ :=
    source.exists_aromaticCanonicalOddOpenCumuleneSpatialAssignment_of_dependencies
      carrierFuel ruleFuel unit terminals evidence
  exact ⟨assignment, computed,
    source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_sound
      carrierFuel ruleFuel unit evidence.owner assignment computed⟩

/-- Independent readiness evidence sufficient to compile one even-open-cumulene carrier. -/
structure AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals) : Prop where
  owner : unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits
  terminalsDerived : source.DeclarativeAromaticCanonicalOpenCumuleneTerminals
    unit terminals
  startDependencies :
    source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5DependenciesResolved
      carrierFuel terminals.left terminals.leftPartner
  endDependencies :
    source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5DependenciesResolved
      carrierFuel terminals.right terminals.rightPartner
  startSelectable : ∀ frame,
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel terminals.left terminals.leftPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel terminals.left)
        (2 * (carrierFuel + 1)) frame →
      ∃ selection,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          frame selection
  endSelectable : ∀ frame,
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel terminals.right terminals.rightPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel terminals.right)
        (2 * (carrierFuel + 1)) frame →
      ∃ selection,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          frame selection
  spatiallyNondegenerate :
    ∀ (startFrame endFrame :
        source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
      (startSelection endSelection :
        source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection carrierFuel),
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        startFrame startSelection →
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          endFrame endSelection →
      ∃ axisStartPoint axisEndPoint startReferencePoint endReferencePoint descriptor,
        source.SemanticAromaticCanonicalSpatialPointAt terminals.left axisStartPoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt terminals.right axisEndPoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt
          startSelection.reference startReferencePoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt
          endSelection.reference endReferencePoint ∧
        RationalAxialSpatialDescriptor axisStartPoint axisEndPoint
          startReferencePoint endReferencePoint descriptor

/-- Every independently ready even-open-cumulene carrier emits at the uniform finite bound. -/
theorem exists_aromaticCanonicalEvenOpenCumuleneAxialAssignment_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals)
    (evidence : source.AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence
      carrierFuel ruleFuel unit terminals) :
    ∃ assignment,
      source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
        carrierFuel ruleFuel unit = some assignment := by
  have terminalsComputed :=
    (source.aromaticCanonicalOpenCumuleneTerminals?_eq_some_iff
      unit terminals).mpr evidence.terminalsDerived
  obtain ⟨startFrame, startFrameComputed⟩ :=
    source.exists_buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame_at_twice
      carrierFuel terminals.left terminals.leftPartner
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel terminals.left)
      evidence.startDependencies
  obtain ⟨endFrame, endFrameComputed⟩ :=
    source.exists_buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame_at_twice
      carrierFuel terminals.right terminals.rightPartner
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel terminals.right)
      evidence.endDependencies
  have startFrameDerived :=
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
      carrierFuel terminals.left terminals.leftPartner
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel terminals.left)
      (2 * (carrierFuel + 1)) startFrame startFrameComputed
  have endFrameDerived :=
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
      carrierFuel terminals.right terminals.rightPartner
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel terminals.right)
      (2 * (carrierFuel + 1)) endFrame endFrameComputed
  obtain ⟨startSelection, startSelectionDerived⟩ :=
    evidence.startSelectable startFrame startFrameDerived
  obtain ⟨endSelection, endSelectionDerived⟩ :=
    evidence.endSelectable endFrame endFrameDerived
  have startSelectionComputed :=
    (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff_declarative
      startFrame startSelection).mpr startSelectionDerived
  have endSelectionComputed :=
    (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff_declarative
      endFrame endSelection).mpr endSelectionDerived
  obtain ⟨axisStartPoint, axisEndPoint, startReferencePoint, endReferencePoint,
      descriptor, axisStartPointDerived, axisEndPointDerived,
      startReferencePointDerived, endReferencePointDerived, descriptorDerived⟩ :=
    evidence.spatiallyNondegenerate startFrame endFrame startSelection endSelection
      startSelectionDerived endSelectionDerived
  have axisStartPointComputed :=
    (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
      terminals.left axisStartPoint).mpr axisStartPointDerived
  have axisEndPointComputed :=
    (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
      terminals.right axisEndPoint).mpr axisEndPointDerived
  have startReferencePointComputed :=
    (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
      startSelection.reference startReferencePoint).mpr startReferencePointDerived
  have endReferencePointComputed :=
    (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
      endSelection.reference endReferencePoint).mpr endReferencePointDerived
  have descriptorComputed :=
    (axialDescriptorOfSpatialReferences?_eq_some_iff
      axisStartPoint axisEndPoint startReferencePoint endReferencePoint descriptor).mpr
        descriptorDerived
  refine ⟨{
      unit
      terminals
      startReference := startSelection.reference
      endReference := endSelection.reference
      descriptor
    }, ?_⟩
  simp [aromaticCanonicalEvenOpenCumuleneAxialAssignment?, terminalsComputed,
    startFrameComputed, endFrameComputed, startSelectionComputed,
    endSelectionComputed, axisStartPointComputed, axisEndPointComputed,
    startReferencePointComputed, endReferencePointComputed, descriptorComputed]

/-- Even-route completeness and correctness hold for the same emitted assignment. -/
theorem exists_aromaticCanonicalEvenOpenCumuleneAxialAssignment_and_judgment_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals)
    (evidence : source.AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence
      carrierFuel ruleFuel unit terminals) :
    ∃ assignment,
      source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
          carrierFuel ruleFuel unit = some assignment ∧
        source.DeclarativeAromaticCanonicalEvenOpenCumuleneAxialAssignment
          carrierFuel ruleFuel assignment := by
  obtain ⟨assignment, computed⟩ :=
    source.exists_aromaticCanonicalEvenOpenCumuleneAxialAssignment_of_dependencies
      carrierFuel ruleFuel unit terminals evidence
  exact ⟨assignment, computed,
    source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_sound
      carrierFuel ruleFuel unit evidence.owner assignment computed⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
