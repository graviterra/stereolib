import TetraStereo.OneCenter.IUPACPrimitive35Interpreter
import TetraStereo.OneCenter.CIPObservedPolyhedralCompletePipelineExactness
import TetraStereo.OneCenter.CIPIR9HigherBipyramidalUnifiedCompletePipeline

set_option autoImplicit false

/-!
# Molecular bridge for the primitive P-93/IR-9 provision family

The primitive-35 interpreter proves operation-graph refinement.  This module connects that
operation-level result to the actual certified molecular polyhedral pipeline.  A successful
public assignment is equivalent to the independent IR-9 observation judgment and, in one
certificate, produces the reviewed authority observations for geometry symbols, finite donor
numbering, priming, configuration-index routing, and absolute-configuration routing.

This is deliberately observation-scoped.  It does not claim that every molecule supplies all
source observations required by every prose provision; that remaining perception/source-totality
boundary stays explicit in `Primitive35ProvisionSemanticsComplete`.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93.GeometryIngress

/-- The reviewed authority input is inside the primitive-35 admitted domain, and the certified
molecular analyzer refers to the same checked semantic molecule and materialized parser diagram.
Keeping both premises explicit prevents either an out-of-domain input or an unrelated authority
value from being paired with the normalization result. -/
def Primitive35MolecularSourceBinding
    (source : AuthoritativeChemicalInput) (result : ChemistryNormalizationResult) : Prop :=
  source.StructurallyWellFormed ∧
    result.parsed.AuthoritativeStructureAgreement source

/-- Evidence that one real molecular polyhedral assignment reaches the reviewed primitive-35
authority semantics.  The first field is the complete independent molecular judgment.  The
remaining fields expose, in bulk, the concrete reviewed observations generated from it. -/
structure Primitive35MolecularPolyhedralAuthorityCertificate
    (source : AuthoritativeChemicalInput)
    (result : ChemistryNormalizationResult)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment) : Prop where
  sourceBinding : Primitive35MolecularSourceBinding source result
  independentJudgment :
    PolyhedralObservationAssignmentJudgment result record assignment
  ir9GeometrySymbol :
    ∃ observation : UnaryAuthorityObservation PolyhedralGeometry String,
      observation =
        { input := record.geometry
          output := (BlueBookP93.geometryOfProduction record.geometry).symbol } ∧
      ir9PolyhedralSymbolProduces observation ∧
      ir9PolyhedralSymbolReference.Judges source observation
  p93GeometrySymbol :
    record.geometry ∈ p93CommonPolyhedralGeometries →
      ∃ observation : UnaryAuthorityObservation PolyhedralGeometry String,
        observation =
          { input := record.geometry
            output := (BlueBookP93.geometryOfProduction record.geometry).symbol } ∧
        p93PolyhedralSymbolProduces observation ∧
        p93PolyhedralSymbolReference.Judges source observation
  donorNumbering :
    ∃ observation : PriorityNumberingAuthorityObservation,
      priorityNumberingProduces observation ∧
      priorityNumberingReference.Judges source observation
  donorPriming :
    ∃ observation : PrimingAuthorityObservation,
      primingConventionProduces observation ∧
      primingConventionReference.Judges source observation
  configurationRouting :
    ∃ priorities positions index,
      result.observedPolyhedralPriorityNumbers? record.center record.geometry
          record.ligands record.priming = some priorities ∧
      polyhedralConfigurationIndex? record.geometry priorities positions = some index ∧
      BlueBookP93.GeometryObservation.configurationIndex?
          (BlueBookP93.geometryOfProduction record.geometry)
          (priorities.map BlueBookP93.priorityOfProduction) positions =
        some (index.map (List.map BlueBookP93.priorityOfProduction))
  absoluteRouting :
    ∃ rotation? absolute,
      polyhedralAbsoluteConfiguration? record.geometry rotation? = some absolute ∧
      BlueBookP93.GeometryObservation.absoluteConfiguration?
          (BlueBookP93.geometryOfProduction record.geometry)
          (rotation?.map BlueBookP93.rotationOfProduction) =
        some (absolute.map PolyhedralAbsoluteConfiguration.toIndependent)

/-- One independent molecular judgment generates all currently connected primitive-35
P-93/IR-9 authority observations at once. -/
theorem primitive35MolecularPolyhedralAuthorityCertificate_of_judgment
    (source : AuthoritativeChemicalInput)
    (result : ChemistryNormalizationResult)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (sourceBinding : Primitive35MolecularSourceBinding source result)
    (judged : PolyhedralObservationAssignmentJudgment result record assignment) :
    Primitive35MolecularPolyhedralAuthorityCertificate source result record assignment := by
  have independentJudgment := judged
  rcases judged with
    ⟨priorities, memberships, independentRotation?, rotation?, positions, index, absolute,
      recognitionOK, recognitionValid, priorityEq, validFrame,
      ⟨compareAt, baseNumbers, primeCounts, frameEq, baseEq, baseValid,
        primeEq, primeValid, zipped⟩,
      positionsRecognized, orientationRecognized, rotationEq, guardFalse, indexEq,
      absoluteEq, assignmentEq⟩
  have ir9Reference : ir9PolyhedralSymbolReference.Judges source
      ({ input := record.geometry
         output := (BlueBookP93.geometryOfProduction record.geometry).symbol } :
        UnaryAuthorityObservation PolyhedralGeometry String) := by
    rfl
  have ir9Production : ir9PolyhedralSymbolProduces
      ({ input := record.geometry
         output := (BlueBookP93.geometryOfProduction record.geometry).symbol } :
        UnaryAuthorityObservation PolyhedralGeometry String) :=
    (ir9PolyhedralSymbol_production_eq_reference source _).mpr ir9Reference
  have referenceIndex :=
    polyhedralConfigurationIndex?_conforms_P93_IR9 record.geometry priorities positions
  rw [indexEq] at referenceIndex
  have referenceAbsolute :=
    polyhedralAbsoluteConfiguration?_conforms_P93_IR9 record.geometry rotation?
  rw [absoluteEq] at referenceAbsolute
  refine
    { sourceBinding := sourceBinding
      independentJudgment := independentJudgment
      ir9GeometrySymbol := ⟨_, rfl, ir9Production, ir9Reference⟩
      p93GeometrySymbol := ?_
      donorNumbering := ?_
      donorPriming := ?_
      configurationRouting := ⟨priorities, positions, index, priorityEq, indexEq, ?_⟩
      absoluteRouting := ⟨rotation?, absolute, absoluteEq, ?_⟩ }
  · intro common
    have reference : p93PolyhedralSymbolReference.Judges source
        ({ input := record.geometry
           output := (BlueBookP93.geometryOfProduction record.geometry).symbol } :
          UnaryAuthorityObservation PolyhedralGeometry String) :=
      ⟨common, rfl⟩
    exact ⟨_, rfl,
      (p93PolyhedralSymbol_production_eq_reference source _).mpr reference,
      reference⟩
  · let observation : PriorityNumberingAuthorityObservation :=
      { count := record.ligands.length
        compareAt := compareAt
        numbers := baseNumbers }
    have reference : priorityNumberingReference.Judges source observation := baseValid
    exact ⟨observation,
      (priorityNumbering_production_eq_reference source observation).mpr reference,
      reference⟩
  · let observation : PrimingAuthorityObservation :=
      { donorCount := record.ligands.length
        memberships := effectivePolyhedralPrimingMemberships record.ligands.length memberships
        primeCounts := primeCounts }
    have reference : primingConventionReference.Judges source observation := primeValid
    exact ⟨observation,
      (primingConvention_production_eq_reference source observation).mpr reference,
      reference⟩
  · simpa using referenceIndex.symm
  · simpa using referenceAbsolute.symm

/-- Exact local molecular refinement theorem.  Successful production is equivalent to one
proof-bearing bundle of all currently connected P-93/IR-9 reviewed semantics. -/
theorem primitive35MolecularPolyhedral_pipeline_eq_reference
    (source : AuthoritativeChemicalInput)
    (result : ChemistryNormalizationResult)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (sourceBinding : Primitive35MolecularSourceBinding source result) :
    result.polyhedralGeometryObservationAssignment? record = some assignment ↔
      Primitive35MolecularPolyhedralAuthorityCertificate source result record assignment := by
  constructor
  · intro produced
    apply primitive35MolecularPolyhedralAuthorityCertificate_of_judgment source result record
      assignment sourceBinding
    exact (result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
      record assignment).mp produced
  · intro certificate
    exact (result.polyhedralGeometryObservationAssignment?_eq_some_iff_judgment
      record assignment).mpr certificate.independentJudgment

/-- The local authority certificate also reaches the final certified graph-plus-spatial pipeline.
For a supplied record, same-unit observation agreement is the exact remaining emission condition;
native graph analysis cannot own a polyhedral unit. -/
theorem primitive35MolecularPolyhedral_completePipeline_eq_reference
    (source : AuthoritativeChemicalInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (recordPresent : record ∈ observations.polyhedra)
    (authority : Primitive35MolecularPolyhedralAuthorityCertificate
      source certified.result record assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarHelicalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentAgreement
        certified.result observations.polyhedra assignment := by
  exact polyhedralObservationAssignment_mem_completePipeline_iff_agreement
    certified spatial observations derivedPlanes derivedHelices record assignment
      recordPresent authority.independentJudgment

/-! ## Source-scheduled higher-bipyramidal family -/

/-- The reviewed IR-9 bipyramid family corresponding to a source-scheduled candidate. -/
def primitive35HigherBipyramidalKind :
    HigherBipyramidalSourceCandidate → RedBookIR9.BipyramidKind
  | .pentagonal7 _ => .pentagonal7
  | .hexagonal8 _ => .hexagonal8
  | .heptagonal9 _ => .heptagonal9

/-- Proof-relevant provenance for an IR-9.3.4.10 observation.  It retains the complete
source/coordinate derivation and ties the observation's sense to the absolute orientation stored
in that exact derived record. -/
def Primitive35HigherBipyramidalDerivedCAObservationJudgment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (candidate : HigherBipyramidalSourceCandidate)
    (derived : IndexedPolyhedralGeometryObservation)
    (observation : CAAuthorityObservation) : Prop :=
  HigherBipyramidalDerivedRecordJudgment certified spatial candidate derived ∧
    observation.frame =
      .otherBipyramidSeniorAxialNear (primitive35HigherBipyramidalKind candidate) ∧
    match candidate with
    | .pentagonal7 _ =>
        derived.absoluteOrientation = .pentagonalBipyramidAC
          (BlueBookP93.rotationOfProduction observation.sense)
    | .hexagonal8 _ =>
        derived.absoluteOrientation = .hexagonalBipyramidAC
          (BlueBookP93.rotationOfProduction observation.sense)
    | .heptagonal9 _ =>
        derived.absoluteOrientation = .heptagonalBipyramidAC
          (BlueBookP93.rotationOfProduction observation.sense)

/-- One certificate covers the three graph-scheduled, coordinate-derived higher-bipyramidal
families PBPY-7, HBPY-8, and HBPY-9.  Besides structural/admitted-domain binding inherited from
the molecular certificate, it requires that the exact spatial configuration used by perception
is the authority input's spatial evidence. -/
def Primitive35SourceHigherBipyramidalAuthorityCertificate
    (source : AuthoritativeChemicalInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment) : Prop :=
  source.spatial? = some spatial ∧
    ∃ derived,
      HigherBipyramidalDerivedRecordJudgment certified spatial candidate derived ∧
        Primitive35MolecularPolyhedralAuthorityCertificate
          source certified.result derived assignment

/-- Every independently judged source candidate in any of the three higher-bipyramidal families
generates the same molecular authority bundle. -/
theorem primitive35SourceHigherBipyramidalAuthorityCertificate_of_judgment
    (source : AuthoritativeChemicalInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment)
    (sourceBinding : Primitive35MolecularSourceBinding source certified.result)
    (spatialBinding : source.spatial? = some spatial)
    (judged : HigherBipyramidalSpatialAssignmentJudgment
      certified spatial candidate assignment) :
    Primitive35SourceHigherBipyramidalAuthorityCertificate
      source certified spatial candidate assignment := by
  rcases judged with ⟨derived, sourceDerived, assignmentJudged⟩
  exact ⟨spatialBinding, derived, sourceDerived,
    primitive35MolecularPolyhedralAuthorityCertificate_of_judgment
      source certified.result derived assignment sourceBinding assignmentJudged⟩

/-- A source-scheduled higher-bipyramidal certificate constructs the actual reviewed
IR-9.3.4.10 `A/C` provision observation for its family.  The rotation sense comes from the
coordinate orientation judgment embedded in the derived record, not from a free caller input. -/
theorem primitive35SourceHigherBipyramidal_otherBipyramidalCA_row
    (source : AuthoritativeChemicalInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment)
    (authority : Primitive35SourceHigherBipyramidalAuthorityCertificate
      source certified spatial candidate assignment) :
    ∃ derived observation,
      Primitive35HigherBipyramidalDerivedCAObservationJudgment
        certified spatial candidate derived observation ∧
      caAuthorityProduces
        (fun frame => ∃ kind, frame = RedBookIR9.CAReferenceFrame.otherBipyramidSeniorAxialNear kind)
        observation ∧
      otherBipyramidalCAReference.Judges source observation := by
  rcases authority with ⟨_spatialBinding, derived, derivedJudged, _molecularAuthority⟩
  cases candidate with
  | pentagonal7 center =>
      rcases derivedJudged.2 with
        ⟨frame, partition, priorities, placement, sense, frameEq, perceived, priorityEq,
          placementEq, orientation, derivedEq⟩
      let observation : CAAuthorityObservation :=
        { frame := .otherBipyramidSeniorAxialNear .pentagonal7
          sense := sense
          symbol := BlueBookP93.chiralityOfProduction
            (PolyhedralChiralitySymbol.ofRotation sense) }
      have produced : caAuthorityProduces
          (fun frame => ∃ kind,
            frame = RedBookIR9.CAReferenceFrame.otherBipyramidSeniorAxialNear kind)
          observation := by
        exact ⟨⟨.pentagonal7, rfl⟩, rfl⟩
      have provenance : Primitive35HigherBipyramidalDerivedCAObservationJudgment
          certified spatial (.pentagonal7 center) derived observation := by
        refine ⟨derivedJudged, rfl, ?_⟩
        rw [derivedEq]
        rfl
      exact ⟨derived, observation, provenance, produced,
        (caAuthority_production_eq_reference _ source observation).mp produced⟩

  | hexagonal8 center =>
      rcases derivedJudged.2 with
        ⟨frame, partition, priorities, placement, sense, frameEq, perceived, priorityEq,
          placementEq, orientation, derivedEq⟩
      let observation : CAAuthorityObservation :=
        { frame := .otherBipyramidSeniorAxialNear .hexagonal8
          sense := sense
          symbol := BlueBookP93.chiralityOfProduction
            (PolyhedralChiralitySymbol.ofRotation sense) }
      have produced : caAuthorityProduces
          (fun frame => ∃ kind,
            frame = RedBookIR9.CAReferenceFrame.otherBipyramidSeniorAxialNear kind)
          observation := by
        exact ⟨⟨.hexagonal8, rfl⟩, rfl⟩
      have provenance : Primitive35HigherBipyramidalDerivedCAObservationJudgment
          certified spatial (.hexagonal8 center) derived observation := by
        refine ⟨derivedJudged, rfl, ?_⟩
        rw [derivedEq]
        rfl
      exact ⟨derived, observation, provenance, produced,
        (caAuthority_production_eq_reference _ source observation).mp produced⟩
  | heptagonal9 center =>
      rcases derivedJudged.2 with
        ⟨frame, partition, priorities, placement, sense, frameEq, perceived, priorityEq,
          placementEq, orientation, derivedEq⟩
      let observation : CAAuthorityObservation :=
        { frame := .otherBipyramidSeniorAxialNear .heptagonal9
          sense := sense
          symbol := BlueBookP93.chiralityOfProduction
            (PolyhedralChiralitySymbol.ofRotation sense) }
      have produced : caAuthorityProduces
          (fun frame => ∃ kind,
            frame = RedBookIR9.CAReferenceFrame.otherBipyramidSeniorAxialNear kind)
          observation := by
        exact ⟨⟨.heptagonal9, rfl⟩, rfl⟩
      have provenance : Primitive35HigherBipyramidalDerivedCAObservationJudgment
          certified spatial (.heptagonal9 center) derived observation := by
        refine ⟨derivedJudged, rfl, ?_⟩
        rw [derivedEq]
        rfl
      exact ⟨derived, observation, provenance, produced,
        (caAuthority_production_eq_reference _ source observation).mp produced⟩

/-- The coordinate-derived `A/C` witness is packaged at the dependent compiler-row type used by
the 35-row ledger, rather than only at the underlying operation predicate. -/
theorem primitive35SourceHigherBipyramidal_ir9CAOtherBipyramidal_provision
    (source : AuthoritativeChemicalInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment)
    (authority : Primitive35SourceHigherBipyramidalAuthorityCertificate
      source certified spatial candidate assignment) :
    let row : Primitive35AuthorityRow := .ir9CAOtherBipyramidal
    ∃ derived observation,
      Primitive35HigherBipyramidalDerivedCAObservationJudgment
          certified spatial candidate derived observation ∧
        row.ProductionJudges source observation ∧ row.reference.Judges source observation := by
  rcases primitive35SourceHigherBipyramidal_otherBipyramidalCA_row
      source certified spatial candidate assignment authority with
    ⟨derived, observation, provenance, produced, referenced⟩
  exact ⟨derived, observation, provenance, produced, referenced⟩

/-- Exact source-perception bridge for the three represented higher-bipyramidal families.  The
right side is not a caller-supplied geometry label: it contains the graph schedule, coordinate
perception, molecular CIP ranking, independent IR-9 judgment, and reviewed provision evidence. -/
theorem primitive35SourceHigherBipyramidal_pipeline_eq_reference
    (source : AuthoritativeChemicalInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment)
    (sourceBinding : Primitive35MolecularSourceBinding source certified.result)
    (spatialBinding : source.spatial? = some spatial) :
    HigherBipyramidalSpatialAssignmentJudgment certified spatial candidate assignment ↔
      Primitive35SourceHigherBipyramidalAuthorityCertificate
        source certified spatial candidate assignment := by
  constructor
  · exact primitive35SourceHigherBipyramidalAuthorityCertificate_of_judgment
      source certified spatial candidate assignment sourceBinding spatialBinding
  · rintro ⟨_authoritySpatial, derived, sourceDerived, molecularAuthority⟩
    exact ⟨derived, sourceDerived, molecularAuthority.independentJudgment⟩

/-- The source-scheduled authority certificate reaches the unified final analyzer.  Across all
three geometries, same-unit agreement remains the exact and only final emission condition. -/
theorem primitive35SourceHigherBipyramidal_completePipeline_eq_reference
    (source : AuthoritativeChemicalInput)
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (candidate : HigherBipyramidalSourceCandidate)
    (assignment : StereoAssignment)
    (authority : Primitive35SourceHigherBipyramidalAuthorityCertificate
      source certified spatial candidate assignment) :
    assignment ∈ analyzeCertifiedNormalizedWithSourceHigherBipyramidalSpatialGeometry
        certified spatial observations derivedPlanes derivedHelices ↔
      PolyhedralObservationAssignmentAgreement certified.result
        (observations.withSourceHigherBipyramidalSpatialGeometry
          certified spatial).polyhedra assignment := by
  rcases authority with ⟨_authoritySpatial, derived, sourceDerived, molecularAuthority⟩
  apply higherBipyramidalSpatialAssignment_mem_completePipeline_iff_agreement
    certified spatial observations derivedPlanes derivedHelices candidate assignment
  exact ⟨derived, sourceDerived, molecularAuthority.independentJudgment⟩

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35MolecularPolyhedral_pipeline_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35MolecularPolyhedral_completePipeline_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35SourceHigherBipyramidal_pipeline_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35SourceHigherBipyramidal_completePipeline_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35SourceHigherBipyramidal_otherBipyramidalCA_row
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35SourceHigherBipyramidal_ir9CAOtherBipyramidal_provision
