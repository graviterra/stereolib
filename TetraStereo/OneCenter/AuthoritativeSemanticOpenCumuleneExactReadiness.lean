import TetraStereo.OneCenter.AuthoritativeSemanticOpenCumuleneExactOnceCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondExactReadinessCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact canonical readiness for source-canonical open cumulenes

The earlier finite-completeness records are chemically meaningful sufficient conditions.  This
module states the exact independent normal form compiled by the odd and even per-unit analyzers,
proves both converses, and lifts that equivalence to literal whole-family count one.  A canonical
carrier is therefore emitted exactly once iff its own canonical topology, Rules-1a--5 endpoint
frames, selections, coordinates, and final geometry judgment exist; other canonical carriers are
classified by exact refusal rather than hidden behind an all-units-ready premise.
-/

/-! ## Odd open cumulenes -/

/-- Exact implementation-level decomposition of one odd-open-cumulene result. -/
def AromaticCanonicalOddOpenCumuleneSpatialExecutableJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) : Prop :=
  ∃ terminals leftFrame rightFrame leftSelection rightSelection
      leftPoint rightPoint leftReferencePoint rightReferencePoint geometry outcome,
    source.aromaticCanonicalOpenCumuleneTerminals? unit = some terminals ∧
      source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel terminals.left terminals.leftPartner
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel terminals.left)
          (2 * (carrierFuel + 1)) = some leftFrame ∧
      source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel terminals.right terminals.rightPartner
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel terminals.right)
          (2 * (carrierFuel + 1)) = some rightFrame ∧
      source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? leftFrame =
        some leftSelection ∧
      source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? rightFrame =
        some rightSelection ∧
      source.aromaticCanonicalSpatialPointAt? terminals.left = some leftPoint ∧
      source.aromaticCanonicalSpatialPointAt? terminals.right = some rightPoint ∧
      source.aromaticCanonicalSpatialPointAt? leftSelection.reference =
        some leftReferencePoint ∧
      source.aromaticCanonicalSpatialPointAt? rightSelection.reference =
        some rightReferencePoint ∧
      rule3GeometryOfSpatialReferences? leftPoint rightPoint
          leftReferencePoint rightReferencePoint = some geometry ∧
      aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
          leftSelection.enantiomorphic rightSelection.enantiomorphic geometry = some outcome ∧
      ({ unit
         terminals
         leftReference := leftSelection.reference
         rightReference := rightSelection.reference
         geometry
         outcome } : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) = assignment

/-- The odd per-unit executable succeeds exactly when every fallible boundary succeeds. -/
theorem aromaticCanonicalOddOpenCumuleneSpatialAssignment?_eq_some_iff_executable
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) :
    source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
        carrierFuel ruleFuel unit = some assignment ↔
      source.AromaticCanonicalOddOpenCumuleneSpatialExecutableJudgment
        carrierFuel ruleFuel unit assignment := by
  classical
  simp [aromaticCanonicalOddOpenCumuleneSpatialAssignment?,
    AromaticCanonicalOddOpenCumuleneSpatialExecutableJudgment,
    Option.bind_eq_some_iff]

/-- Independent canonical normal form of one odd-open-cumulene result. -/
def AromaticCanonicalOddOpenCumuleneCanonicalSpatialJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) : Prop :=
  ∃ terminals leftFrame rightFrame leftSelection rightSelection
      leftPoint rightPoint leftReferencePoint rightReferencePoint geometry outcome,
    source.DeclarativeAromaticCanonicalOpenCumuleneTerminals unit terminals ∧
      source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5CanonicalFrame
        carrierFuel terminals.left terminals.leftPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel terminals.left)
        (2 * (carrierFuel + 1)) leftFrame ∧
      source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5CanonicalFrame
        carrierFuel terminals.right terminals.rightPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel terminals.right)
        (2 * (carrierFuel + 1)) rightFrame ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        leftFrame leftSelection ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        rightFrame rightSelection ∧
      source.SemanticAromaticCanonicalSpatialPointAt terminals.left leftPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt terminals.right rightPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        leftSelection.reference leftReferencePoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        rightSelection.reference rightReferencePoint ∧
      RationalRule3SpatialGeometry leftPoint rightPoint
        leftReferencePoint rightReferencePoint geometry ∧
      AromaticCanonicalOrdinaryDoubleBondPlanarOutcomeJudgment
        leftSelection.enantiomorphic rightSelection.enantiomorphic geometry outcome ∧
      ({ unit
         terminals
         leftReference := leftSelection.reference
         rightReference := rightSelection.reference
         geometry
         outcome } : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) = assignment

/-- Executable and independent canonical odd judgments are equivalent. -/
theorem aromaticCanonicalOddOpenCumuleneSpatialExecutableJudgment_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) :
    source.AromaticCanonicalOddOpenCumuleneSpatialExecutableJudgment
        carrierFuel ruleFuel unit assignment ↔
      source.AromaticCanonicalOddOpenCumuleneCanonicalSpatialJudgment
        carrierFuel ruleFuel unit assignment := by
  simp only [AromaticCanonicalOddOpenCumuleneSpatialExecutableJudgment,
    AromaticCanonicalOddOpenCumuleneCanonicalSpatialJudgment,
    source.aromaticCanonicalOpenCumuleneTerminals?_eq_some_iff,
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_eq_some_iff_canonical,
    source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff_declarative,
    source.aromaticCanonicalSpatialPointAt?_eq_some_iff,
    rule3GeometryOfSpatialReferences?_eq_some_iff,
    aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?_eq_some_iff]

/-- Necessary-and-sufficient per-unit odd descriptor theorem. -/
theorem aromaticCanonicalOddOpenCumuleneSpatialAssignment?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) :
    source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
        carrierFuel ruleFuel unit = some assignment ↔
      source.AromaticCanonicalOddOpenCumuleneCanonicalSpatialJudgment
        carrierFuel ruleFuel unit assignment :=
  (source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_eq_some_iff_executable
    carrierFuel ruleFuel unit assignment).trans
      (source.aromaticCanonicalOddOpenCumuleneSpatialExecutableJudgment_iff_canonical
        carrierFuel ruleFuel unit assignment)

/-- Minimal exact readiness of a canonical odd carrier. -/
def AromaticCanonicalOddOpenCumuleneCanonicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) : Prop :=
  unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits ∧
    ∃ assignment,
      source.AromaticCanonicalOddOpenCumuleneCanonicalSpatialJudgment
        carrierFuel ruleFuel unit assignment

/-- Odd per-unit option success is exactly the descriptor part of canonical readiness. -/
theorem aromaticCanonicalOddOpenCumuleneSpatialAssignment?_isSome_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
      carrierFuel ruleFuel unit).isSome = true ↔
      ∃ assignment,
        source.AromaticCanonicalOddOpenCumuleneCanonicalSpatialJudgment
          carrierFuel ruleFuel unit assignment := by
  rw [Option.isSome_iff_exists]
  exact exists_congr fun assignment =>
    source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_eq_some_iff_canonical
      carrierFuel ruleFuel unit assignment

/-- Odd per-unit refusal has no hidden operational branch. -/
theorem aromaticCanonicalOddOpenCumuleneSpatialAssignment?_eq_none_iff_not_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) :
    source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
        carrierFuel ruleFuel unit = none ↔
      ¬ ∃ assignment,
        source.AromaticCanonicalOddOpenCumuleneCanonicalSpatialJudgment
          carrierFuel ruleFuel unit assignment := by
  rw [← source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_isSome_iff_canonical]
  cases source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
      carrierFuel ruleFuel unit <;> simp

/-- Literal whole-family count one is equivalent to exact odd canonical readiness. -/
theorem exists_count_analyzeAromaticCanonicalOddOpenCumuleneSpatial_eq_one_iff_canonicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) :
    (∃ assignment,
        assignment.unit = unit ∧
          (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
            carrierFuel ruleFuel).count assignment = 1) ↔
      source.AromaticCanonicalOddOpenCumuleneCanonicalReadiness
        carrierFuel ruleFuel unit := by
  constructor
  · rintro ⟨assignment, unitIdentity, countOne⟩
    have present : assignment ∈
        source.analyzeAromaticCanonicalOddOpenCumuleneSpatial carrierFuel ruleFuel :=
      List.count_pos_iff.mp (by omega)
    obtain ⟨origin, owner, computed⟩ :=
      (source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
        carrierFuel ruleFuel assignment).mp present
    have originIdentity : origin = unit :=
      (source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_unit_eq
        carrierFuel ruleFuel origin assignment computed).symm.trans unitIdentity
    subst origin
    exact ⟨owner, assignment,
      (source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_eq_some_iff_canonical
        carrierFuel ruleFuel unit assignment).mp computed⟩
  · rintro ⟨owner, assignment, canonical⟩
    have computed :=
      (source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_eq_some_iff_canonical
        carrierFuel ruleFuel unit assignment).mpr canonical
    have unitIdentity :=
      source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_unit_eq
        carrierFuel ruleFuel unit assignment computed
    have present : assignment ∈
        source.analyzeAromaticCanonicalOddOpenCumuleneSpatial carrierFuel ruleFuel :=
      (source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
        carrierFuel ruleFuel assignment).mpr ⟨unit, owner, computed⟩
    refine ⟨assignment, unitIdentity, ?_⟩
    rw [(source.analyzeAromaticCanonicalOddOpenCumuleneSpatial_nodup
      carrierFuel ruleFuel).count]
    simp [present]

/-! ## Even open cumulenes -/

/-- Exact implementation-level decomposition of one even-open-cumulene result. -/
def AromaticCanonicalEvenOpenCumuleneAxialExecutableJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) : Prop :=
  ∃ terminals startFrame endFrame startSelection endSelection
      axisStartPoint axisEndPoint startReferencePoint endReferencePoint descriptor,
    source.aromaticCanonicalOpenCumuleneTerminals? unit = some terminals ∧
      source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel terminals.left terminals.leftPartner
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel terminals.left)
          (2 * (carrierFuel + 1)) = some startFrame ∧
      source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel terminals.right terminals.rightPartner
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel terminals.right)
          (2 * (carrierFuel + 1)) = some endFrame ∧
      source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? startFrame =
        some startSelection ∧
      source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? endFrame =
        some endSelection ∧
      source.aromaticCanonicalSpatialPointAt? terminals.left = some axisStartPoint ∧
      source.aromaticCanonicalSpatialPointAt? terminals.right = some axisEndPoint ∧
      source.aromaticCanonicalSpatialPointAt? startSelection.reference =
        some startReferencePoint ∧
      source.aromaticCanonicalSpatialPointAt? endSelection.reference =
        some endReferencePoint ∧
      axialDescriptorOfSpatialReferences? axisStartPoint axisEndPoint
          startReferencePoint endReferencePoint = some descriptor ∧
      ({ unit
         terminals
         startReference := startSelection.reference
         endReference := endSelection.reference
         descriptor } : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) = assignment

/-- The even per-unit executable succeeds exactly when every fallible boundary succeeds. -/
theorem aromaticCanonicalEvenOpenCumuleneAxialAssignment?_eq_some_iff_executable
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) :
    source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
        carrierFuel ruleFuel unit = some assignment ↔
      source.AromaticCanonicalEvenOpenCumuleneAxialExecutableJudgment
        carrierFuel ruleFuel unit assignment := by
  classical
  simp [aromaticCanonicalEvenOpenCumuleneAxialAssignment?,
    AromaticCanonicalEvenOpenCumuleneAxialExecutableJudgment,
    Option.bind_eq_some_iff]

/-- Independent canonical normal form of one even-open-cumulene result. -/
def AromaticCanonicalEvenOpenCumuleneCanonicalAxialJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) : Prop :=
  ∃ terminals startFrame endFrame startSelection endSelection
      axisStartPoint axisEndPoint startReferencePoint endReferencePoint descriptor,
    source.DeclarativeAromaticCanonicalOpenCumuleneTerminals unit terminals ∧
      source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5CanonicalFrame
        carrierFuel terminals.left terminals.leftPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel terminals.left)
        (2 * (carrierFuel + 1)) startFrame ∧
      source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5CanonicalFrame
        carrierFuel terminals.right terminals.rightPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel terminals.right)
        (2 * (carrierFuel + 1)) endFrame ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        startFrame startSelection ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        endFrame endSelection ∧
      source.SemanticAromaticCanonicalSpatialPointAt terminals.left axisStartPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt terminals.right axisEndPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        startSelection.reference startReferencePoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        endSelection.reference endReferencePoint ∧
      RationalAxialSpatialDescriptor axisStartPoint axisEndPoint
        startReferencePoint endReferencePoint descriptor ∧
      ({ unit
         terminals
         startReference := startSelection.reference
         endReference := endSelection.reference
         descriptor } : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) = assignment

/-- Executable and independent canonical even judgments are equivalent. -/
theorem aromaticCanonicalEvenOpenCumuleneAxialExecutableJudgment_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) :
    source.AromaticCanonicalEvenOpenCumuleneAxialExecutableJudgment
        carrierFuel ruleFuel unit assignment ↔
      source.AromaticCanonicalEvenOpenCumuleneCanonicalAxialJudgment
        carrierFuel ruleFuel unit assignment := by
  simp only [AromaticCanonicalEvenOpenCumuleneAxialExecutableJudgment,
    AromaticCanonicalEvenOpenCumuleneCanonicalAxialJudgment,
    source.aromaticCanonicalOpenCumuleneTerminals?_eq_some_iff,
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_eq_some_iff_canonical,
    source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff_declarative,
    source.aromaticCanonicalSpatialPointAt?_eq_some_iff,
    axialDescriptorOfSpatialReferences?_eq_some_iff]

/-- Necessary-and-sufficient per-unit even descriptor theorem. -/
theorem aromaticCanonicalEvenOpenCumuleneAxialAssignment?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) :
    source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
        carrierFuel ruleFuel unit = some assignment ↔
      source.AromaticCanonicalEvenOpenCumuleneCanonicalAxialJudgment
        carrierFuel ruleFuel unit assignment :=
  (source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_eq_some_iff_executable
    carrierFuel ruleFuel unit assignment).trans
      (source.aromaticCanonicalEvenOpenCumuleneAxialExecutableJudgment_iff_canonical
        carrierFuel ruleFuel unit assignment)

/-- Minimal exact readiness of a canonical even carrier. -/
def AromaticCanonicalEvenOpenCumuleneCanonicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) : Prop :=
  unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits ∧
    ∃ assignment,
      source.AromaticCanonicalEvenOpenCumuleneCanonicalAxialJudgment
        carrierFuel ruleFuel unit assignment

/-- Even per-unit option success is exactly the descriptor part of canonical readiness. -/
theorem aromaticCanonicalEvenOpenCumuleneAxialAssignment?_isSome_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
      carrierFuel ruleFuel unit).isSome = true ↔
      ∃ assignment,
        source.AromaticCanonicalEvenOpenCumuleneCanonicalAxialJudgment
          carrierFuel ruleFuel unit assignment := by
  rw [Option.isSome_iff_exists]
  exact exists_congr fun assignment =>
    source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_eq_some_iff_canonical
      carrierFuel ruleFuel unit assignment

/-- Even per-unit refusal has no hidden operational branch. -/
theorem aromaticCanonicalEvenOpenCumuleneAxialAssignment?_eq_none_iff_not_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) :
    source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
        carrierFuel ruleFuel unit = none ↔
      ¬ ∃ assignment,
        source.AromaticCanonicalEvenOpenCumuleneCanonicalAxialJudgment
          carrierFuel ruleFuel unit assignment := by
  rw [← source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_isSome_iff_canonical]
  cases source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
      carrierFuel ruleFuel unit <;> simp

/-- Literal whole-family count one is equivalent to exact even canonical readiness. -/
theorem exists_count_analyzeAromaticCanonicalEvenOpenCumuleneAxial_eq_one_iff_canonicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) :
    (∃ assignment,
        assignment.unit = unit ∧
          (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
            carrierFuel ruleFuel).count assignment = 1) ↔
      source.AromaticCanonicalEvenOpenCumuleneCanonicalReadiness
        carrierFuel ruleFuel unit := by
  constructor
  · rintro ⟨assignment, unitIdentity, countOne⟩
    have present : assignment ∈
        source.analyzeAromaticCanonicalEvenOpenCumuleneAxial carrierFuel ruleFuel :=
      List.count_pos_iff.mp (by omega)
    obtain ⟨origin, owner, computed⟩ :=
      (source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
        carrierFuel ruleFuel assignment).mp present
    have originIdentity : origin = unit :=
      (source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_unit_eq
        carrierFuel ruleFuel origin assignment computed).symm.trans unitIdentity
    subst origin
    exact ⟨owner, assignment,
      (source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_eq_some_iff_canonical
        carrierFuel ruleFuel unit assignment).mp computed⟩
  · rintro ⟨owner, assignment, canonical⟩
    have computed :=
      (source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_eq_some_iff_canonical
        carrierFuel ruleFuel unit assignment).mpr canonical
    have unitIdentity :=
      source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_unit_eq
        carrierFuel ruleFuel unit assignment computed
    have present : assignment ∈
        source.analyzeAromaticCanonicalEvenOpenCumuleneAxial carrierFuel ruleFuel :=
      (source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
        carrierFuel ruleFuel assignment).mpr ⟨unit, owner, computed⟩
    refine ⟨assignment, unitIdentity, ?_⟩
    rw [(source.analyzeAromaticCanonicalEvenOpenCumuleneAxial_nodup
      carrierFuel ruleFuel).count]
    simp [present]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
