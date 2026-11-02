import TetraStereo.OneCenter.IUPACNext54ProductionFamilyPartition
import TetraStereo.OneCenter.IUPACGlobalCompilerAssembly
import TetraStereo.OneCenter.IUPACPrimitive35Interpreter
import TetraStereo.OneCenter.GeometryAnnotatedCIPConformance

set_option autoImplicit false

/-!
# Concrete production adapter for the 11 descriptor-bearing residual IR-9 rows

Production below is defined from the executable Red Book operations and independently typed
perception/configuration evidence.  It never calls a reviewed `ProvisionReference.Judges`
relation.  In particular, ligand-priority production retains both finite priority-numbering and
finite priming judgments; the explicit IR-9 priming mathematics is not replaced by an output-only
shortcut.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

namespace Next54DescriptorBearingIR9Row

def reference (row : Next54DescriptorBearingIR9Row) : ProvisionReference :=
  row.toAuthorityRow.reference

def geometryChoiceProduces
    (observation : UnaryAuthorityObservation RedBookIR9.GeometryRecognitionObservation
      (Option RedBookIR9.Geometry)) : Prop :=
  observation.input.recognizedGeometry? = observation.output

def diastereoisomerGeneralProduces
    (observation : RedBookIR9.StereoisomerObservation) : Prop :=
  RedBookIR9.Diastereomeric observation

def priorityToProduction
    (priority : RedBookIR9.PriorityNumber) : PolyhedralPriorityNumber :=
  { number := priority.number, primes := priority.primes }

@[simp] theorem priorityToProduction_toIndependent
    (priority : RedBookIR9.PriorityNumber) :
    BlueBookP93.priorityOfProduction (priorityToProduction priority) = priority := by
  rfl

/-- Production-side implementation of the complete IR-9.3.3 configuration-index router. -/
def productionConfigurationIndex :
    RedBookIR9.ConfigurationIndexInput → List (List RedBookIR9.PriorityNumber)
  | .squarePlanar opposite =>
      [squarePlanarConfigurationIndex (priorityToProduction opposite) |>
        List.map BlueBookP93.priorityOfProduction]
  | .octahedral transToOne transToPlane =>
      [octahedronConfigurationIndex (priorityToProduction transToOne)
        (priorityToProduction transToPlane) |>
          List.map BlueBookP93.priorityOfProduction]
  | .squarePyramid4 opposite =>
      [squarePyramid4ConfigurationIndex (priorityToProduction opposite) |>
        List.map BlueBookP93.priorityOfProduction]
  | .squarePyramid5 apical opposite =>
      [squarePyramidConfigurationIndex (priorityToProduction apical)
        (priorityToProduction opposite) |>
          List.map BlueBookP93.priorityOfProduction]
  | .bipyramidal .trigonal5 first second _perpendicular =>
      [trigonalBipyramidConfigurationIndex (priorityToProduction first)
        (priorityToProduction second) |>
          List.map BlueBookP93.priorityOfProduction]
  | .bipyramidal _kind first second perpendicular =>
      bipyramidalConfigurationIndex (priorityToProduction first)
          (priorityToProduction second) (perpendicular.map priorityToProduction) |>
        List.map (List.map BlueBookP93.priorityOfProduction)
  | .tShape stem =>
      [tShapeConfigurationIndex (priorityToProduction stem) |>
        List.map BlueBookP93.priorityOfProduction]
  | .seeSaw first second =>
      [seeSawConfigurationIndex (priorityToProduction first)
        (priorityToProduction second) |>
          List.map BlueBookP93.priorityOfProduction]
  | .trigonalPrism firstFace secondFace =>
      [trigonalPrismConfigurationIndex (firstFace.map priorityToProduction)
        (secondFace.map priorityToProduction) |>
          List.map BlueBookP93.priorityOfProduction]

theorem productionConfigurationIndex_conforms_IR9
    (input : RedBookIR9.ConfigurationIndexInput) :
    productionConfigurationIndex input = RedBookIR9.configurationIndex input := by
  cases input with
  | squarePlanar opposite =>
      simp [productionConfigurationIndex, RedBookIR9.configurationIndex,
        squarePlanarConfigurationIndex_conforms_IR9, BlueBookP93.squarePlanarIndex]
  | octahedral transToOne transToPlane =>
      simp [productionConfigurationIndex, RedBookIR9.configurationIndex,
        octahedronConfigurationIndex_conforms_P93, BlueBookP93.octahedronIndex]
  | squarePyramid4 opposite =>
      simp [productionConfigurationIndex, RedBookIR9.configurationIndex,
        squarePyramid4ConfigurationIndex_conforms_IR9, BlueBookP93.squarePyramid4Index]
  | squarePyramid5 apical opposite =>
      simp [productionConfigurationIndex, RedBookIR9.configurationIndex,
        squarePyramidConfigurationIndex_conforms_P93, BlueBookP93.squarePyramidIndex]
  | bipyramidal kind first second perpendicular =>
      cases kind <;>
        simp [productionConfigurationIndex, RedBookIR9.configurationIndex,
          trigonalBipyramidConfigurationIndex_conforms_P93,
          bipyramidalConfigurationIndex_conforms_IR9,
          BlueBookP93.trigonalBipyramidIndex, BlueBookP93.bipyramidalIndex,
          List.map_map, Function.comp_def]
  | tShape stem =>
      simp [productionConfigurationIndex, RedBookIR9.configurationIndex,
        tShapeConfigurationIndex_conforms_P93, BlueBookP93.tShapeIndex]
  | seeSaw first second =>
      simp [productionConfigurationIndex, RedBookIR9.configurationIndex,
        seeSawConfigurationIndex_conforms_P93, BlueBookP93.seeSawIndex]
  | trigonalPrism firstFace secondFace =>
      simp [productionConfigurationIndex, RedBookIR9.configurationIndex,
        trigonalPrismConfigurationIndex_conforms_IR9, List.map_map, Function.comp_def]

/-- Production validates finite priority numbering and priming through the executable Boolean
checkers used by molecular polyhedral analysis. -/
def productionFiniteDonorPriorityFrameJudged
    (frame : IR9FiniteDonorPriorityFrame) : Prop :=
  frame.numbering.count = frame.priming.donorCount ∧
    densePolyhedralPriorityNumberingOK? frame.numbering.count
      frame.numbering.compareAt frame.numbering.numbers = true ∧
    familyPolyhedralPrimeCountsOK? frame.priming.donorCount
      frame.priming.memberships frame.priming.primeCounts = true

theorem productionFiniteDonorPriorityFrameJudged_conforms_IR9
    (frame : IR9FiniteDonorPriorityFrame) :
    productionFiniteDonorPriorityFrameJudged frame ↔
      FiniteDonorPriorityFrameJudged frame := by
  simp only [productionFiniteDonorPriorityFrameJudged,
    FiniteDonorPriorityFrameJudged]
  rw [densePolyhedralPriorityNumberingOK?_eq_true_iff_IR9,
    familyPolyhedralPrimeCountsOK?_eq_true_iff_IR9]

def configurationIndexProduces
    (observation : IR9ConfigurationIndexAuthorityObservation) : Prop :=
  productionFiniteDonorPriorityFrameJudged observation.frame ∧
    observation.perception.domain.Nodup ∧
    observation.arrangement ∈ observation.perception.domain ∧
    (∀ arrangement ∈ observation.perception.domain,
      observation.frame.numbering.count =
          (observation.perception.encode arrangement).input.geometry.coordinationNumber ∧
        PositionedConfigurationIndexInputWellFormed observation.frame
          (observation.perception.encode arrangement)) ∧
    productionConfigurationIndex
      (observation.perception.encode observation.arrangement).input = observation.output ∧
    observation.arrangement.mirror ≠ observation.arrangement ∧
    observation.arrangement.mirror ∈ observation.perception.domain ∧
    IndependentMirrorImage observation.arrangement observation.arrangement.mirror ∧
    observation.diastereoisomer ∈ observation.perception.domain ∧
    IndependentDiastereoisomer observation.arrangement observation.diastereoisomer ∧
    productionConfigurationIndex
      (observation.perception.encode observation.diastereoisomer).input ≠ observation.output ∧
    (∀ arrangement ∈ observation.perception.domain,
      arrangement.mirror ∈ observation.perception.domain ∧
        productionConfigurationIndex
          (observation.perception.encode arrangement.mirror).input =
        productionConfigurationIndex (observation.perception.encode arrangement).input) ∧
    ∀ left ∈ observation.perception.domain,
      ∀ right ∈ observation.perception.domain,
        IndependentDiastereoisomer left right →
          productionConfigurationIndex (observation.perception.encode right).input ≠
            productionConfigurationIndex (observation.perception.encode left).input

def absoluteConfigurationGeneralProduces
    (observation : IR9AbsoluteConfigurationGeneralAuthorityObservation) : Prop :=
  match observation with
  | .constitutionBased geometry convention =>
      RedBookIR9.constitutionBasedConvention geometry = convention
  | .geometryBasedSkewLines application handedness convention descriptor =>
      (application = .trisBidentateOctahedral ∨
        application = .cisBisBidentateOctahedral) ∧
        convention = .skewLines ∧
        RedBookIR9.configurationSkewDescriptor handedness = descriptor

def rsTetrahedralProduces
    (observation : UnaryAuthorityObservation RedBookIR9.TetrahedralRSObservation RS) : Prop :=
  observation.input.viewedFromCenterTowardLeastPreferred ∧
    RedBookIR9.tetrahedralRS observation.input = observation.output

def caTrigonalPrismaticProduces
    (observation : UnaryAuthorityObservation RedBookIR9.TrigonalPrismCAObservation
      BlueBookP93.ChiralitySymbol) : Prop :=
  observation.input.preferredFaceHasGreaterHighPriorityCount ∧
    observation.input.viewedFromAbovePreferredFace ∧
    RedBookIR9.trigonalPrismCASymbol observation.input = observation.output

def skewLinesProduces
    (observation : UnaryAuthorityObservation RedBookIR9.HelixHandedness
      RedBookIR9.SkewDescriptor) : Prop :=
  RedBookIR9.configurationSkewDescriptor observation.input = observation.output

def chelateConfigurationProduces
    (expectedApplication : RedBookIR9.ChelateApplication)
    (observation : IR9ChelateConfigurationAuthorityObservation) : Prop :=
  observation.application = expectedApplication ∧
    RedBookIR9.availableChelateRingPairs observation.application =
      some observation.availableRingPairCount ∧
    observation.selectedRingPair < observation.availableRingPairCount ∧
    observation.skewLineRoles = [.betweenDonorAtoms, .betweenDonorAtoms] ∧
    observation.skewLineStatus = .helical observation.handedness ∧
    RedBookIR9.configurationSkewDescriptor observation.handedness = observation.descriptor

def skewLinesChelateConformationsProduces
    (observation : UnaryAuthorityObservation RedBookIR9.HelixHandedness
      (List RedBookIR9.ChelateLineRole × RedBookIR9.SkewDescriptor)) : Prop :=
  (RedBookIR9.chelateConformationLines,
    RedBookIR9.conformationSkewDescriptor observation.input) = observation.output

def ligandPriorityGeneralProduces
    (observation : IR9LigandPriorityGeneralAuthorityObservation) : Prop :=
  productionFiniteDonorPriorityFrameJudged observation.frame ∧
    observation.frame.numbering.count =
      observation.relativeInput.input.geometry.coordinationNumber ∧
    PositionedConfigurationIndexInputWellFormed observation.frame observation.relativeInput ∧
    productionConfigurationIndex observation.relativeInput.input = observation.relativeOutput ∧
    AbsolutePriorityUseJudged observation.frame observation.absoluteUse

/-- The row-indexed production program.  Every branch is an executable Red Book operation or a
proof-relevant validation of the independently typed production input. -/
def ProductionJudges :
    (row : Next54DescriptorBearingIR9Row) → row.reference.Observation → Prop
  | .geometryChoice, observation => geometryChoiceProduces observation
  | .diastereoisomerGeneral, observation => diastereoisomerGeneralProduces observation
  | .configurationIndex, observation => configurationIndexProduces observation
  | .absoluteConfigurationGeneral, observation =>
      absoluteConfigurationGeneralProduces observation
  | .rsTetrahedral, observation => rsTetrahedralProduces observation
  | .caTrigonalPrismatic, observation => caTrigonalPrismaticProduces observation
  | .skewLines, observation => skewLinesProduces observation
  | .skewLinesTrisBidentate, observation =>
      chelateConfigurationProduces .trisBidentateOctahedral observation
  | .skewLinesBisBidentate, observation =>
      chelateConfigurationProduces .cisBisBidentateOctahedral observation
  | .skewLinesChelateConformations, observation =>
      skewLinesChelateConformationsProduces observation
  | .ligandPriorityGeneral, observation => ligandPriorityGeneralProduces observation

/-- One dependent family theorem closes all 11 production/reference relations. -/
theorem production_eq_reference
    (row : Next54DescriptorBearingIR9Row)
    (source : AuthoritativeChemicalInput)
    (observation : row.reference.Observation) :
    row.ProductionJudges observation ↔
      row.reference.Judges source observation := by
  cases row with
  | geometryChoice | diastereoisomerGeneral | absoluteConfigurationGeneral
  | rsTetrahedral | caTrigonalPrismatic | skewLines | skewLinesTrisBidentate
  | skewLinesBisBidentate | skewLinesChelateConformations => rfl
  | configurationIndex =>
      simp only [ProductionJudges, configurationIndexProduces, reference, toAuthorityRow,
        Next54IR9AuthorityRow.reference, ir9ConfigurationIndexReference]
      rw [productionFiniteDonorPriorityFrameJudged_conforms_IR9]
      simp only [productionConfigurationIndex_conforms_IR9]
  | ligandPriorityGeneral =>
      simp only [ProductionJudges, ligandPriorityGeneralProduces, reference, toAuthorityRow,
        Next54IR9AuthorityRow.reference, ir9LigandPriorityGeneralReference]
      rw [productionFiniteDonorPriorityFrameJudged_conforms_IR9,
        productionConfigurationIndex_conforms_IR9]

theorem reference_applicable
    (row : Next54DescriptorBearingIR9Row)
    (source : AuthoritativeChemicalInput) :
    row.reference.Applicable source := by
  cases row <;> trivial

theorem provision_mem_next54DescriptorBearing
    (row : Next54DescriptorBearingIR9Row) :
    row.provision ∈ next54DescriptorBearingProvisions := by
  cases row <;> decide

theorem descriptorAssignmentBearing
    (row : Next54DescriptorBearingIR9Row) :
    DescriptorAssignmentBearing row.provision := by
  apply descriptorBearingOfReviewedMember row.provision
  rw [List.mem_toFinset, descriptorBearingReviewedSemanticsSlice_exact]
  simp [reviewed81DescriptorBearingProvisions,
    row.provision_mem_next54DescriptorBearing]

theorem provision_injective : Function.Injective provision := by
  intro left right equal
  cases left <;> cases right <;> simp_all [provision, toAuthorityRow,
    Next54IR9AuthorityRow.provision]

private theorem productionJudges_congr
    (left right : Next54DescriptorBearingIR9Row)
    (provisionEq : left.provision = right.provision)
    {leftObservation : left.reference.Observation}
    {rightObservation : right.reference.Observation}
    (observationEq : HEq leftObservation rightObservation) :
    left.ProductionJudges leftObservation ↔
      right.ProductionJudges rightObservation := by
  cases left <;> cases right <;>
    simp_all [provision, toAuthorityRow, Next54IR9AuthorityRow.provision,
      ProductionJudges]

end Next54DescriptorBearingIR9Row

namespace Next54IR9AuthorityRow

theorem provision_injective : Function.Injective provision := by
  intro left right equal
  cases left <;> cases right <;> simp_all [provision]

end Next54IR9AuthorityRow

theorem next54IR9ReviewedSemantics_row_exact
    (row : Next54IR9AuthorityRow)
    (member : row.provision ∈ next54IR9ResidualProvisions.toFinset) :
    next54IR9ReviewedSemantics.reviewed.row row.provision member = row.semantics := by
  change (next54IR9AuthorityRowOf row.provision _).semantics = row.semantics
  congr 1
  exact Next54IR9AuthorityRow.provision_injective
    (next54IR9AuthorityRowOf_provision row.provision (by simpa using member))

private theorem next54ReviewedSubbatchOf_ir9_exact
    (row : Next54IR9AuthorityRow)
    (member : row.provision ∈ next54Provisions)
    (ir9Member : row.provision ∈ next54IR9ResidualProvisions) :
    next54ReviewedSubbatchOf row.provision member = .ir9Residual ir9Member := by
  have allNodup := next54ReviewedSubbatchProvisions_nodup
  have priorSeparated := (List.nodup_append.mp allNodup).2.2
  cases partitionEq : next54ReviewedSubbatchOf row.provision member with
  | p91 p91Member =>
      exact False.elim (priorSeparated row.provision (by simp [p91Member]) row.provision
        ir9Member rfl)
  | p92Foundational p92Member =>
      exact False.elim (priorSeparated row.provision (by simp [p92Member]) row.provision
        ir9Member rfl)
  | p92DigraphRule1a p92Member =>
      exact False.elim (priorSeparated row.provision (by simp [p92Member]) row.provision
        ir9Member rfl)
  | p93Residual p93Member =>
      exact False.elim (priorSeparated row.provision (by simp [p93Member]) row.provision
        ir9Member rfl)
  | ir9Residual actualMember =>
      congr

theorem next54ReviewedSemantics_ir9_exact
    (row : Next54IR9AuthorityRow)
    (member : row.provision ∈ next54Provisions.toFinset)
    (ir9Member : row.provision ∈ next54IR9ResidualProvisions.toFinset) :
    next54ReviewedSemantics.reviewed.row row.provision member = row.semantics := by
  change next54ReviewedRow row.provision (by simpa using member) = row.semantics
  unfold next54ReviewedRow
  rw [next54ReviewedSubbatchOf_ir9_exact row (by simpa using member)
    (by simpa using ir9Member)]
  exact next54IR9ReviewedSemantics_row_exact row ir9Member

private theorem descriptorBearingReviewedRow_next54_mem_all
    (row : Next54DescriptorBearingReviewedRow) :
    DescriptorBearingReviewedRow.next54 row ∈ DescriptorBearingReviewedRow.all := by
  simp [DescriptorBearingReviewedRow.all, DescriptorBearingReviewedRow.next54Rows,
    Next54DescriptorBearingReviewedRow.all]

theorem descriptorBearingReviewedSemantics_ir9_exact
    (policies : DescriptorBearingReviewedPolicies)
    (row : Next54DescriptorBearingIR9Row) :
    (descriptorBearingReviewedSemantics policies).reviewed.row row.provision
      (by
        apply descriptorBearingReviewedMember row.provision
        exact row.descriptorAssignmentBearing) =
      row.toAuthorityRow.semantics := by
  let reviewedRow : Next54DescriptorBearingReviewedRow :=
    ⟨row.provision, row.provision_mem_next54DescriptorBearing⟩
  change DescriptorBearingReviewedRow.semantics policies
      (descriptorBearingReviewedRowOf
        (DescriptorBearingReviewedRow.next54 reviewedRow).provision _) =
      row.toAuthorityRow.semantics
  rw [descriptorBearingReviewedRowOf_eq (.next54 reviewedRow)
    (descriptorBearingReviewedRow_next54_mem_all reviewedRow)]
  have next54Member : row.provision ∈ next54Provisions.toFinset := by
    simpa using reviewedRow.member_next54Provisions
  have ir9Member : row.provision ∈ next54IR9ResidualProvisions.toFinset := by
    cases row <;> decide
  have reviewedExact :
      next54ReviewedSemantics.reviewed.row row.provision next54Member =
        row.toAuthorityRow.semantics := by
    simpa only [Next54DescriptorBearingIR9Row.provision] using
      next54ReviewedSemantics_ir9_exact row.toAuthorityRow next54Member ir9Member
  change
    { kind := (next54ReviewedSemantics.reviewed.row row.provision next54Member).kind
      sourceSuppliesRule := true
      reference := (next54ReviewedSemantics.reviewed.row row.provision next54Member).reference } =
      row.toAuthorityRow.semantics
  rw [reviewedExact]
  rfl

theorem globalReviewedSemantics_ir9_exact
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Next54DescriptorBearingIR9Row) :
    global.reviewed.row row.provision = row.toAuthorityRow.semantics := by
  rw [global.descriptorBearing_exact row.descriptorAssignmentBearing]
  exact descriptorBearingReviewedSemantics_ir9_exact policies row

theorem next54IR9GlobalReference_eq
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Next54DescriptorBearingIR9Row) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision = row.reference := by
  change ((globalDescriptorAssignmentProjection global.toFrozenCorpus).reference
    row.provision).toReference = row.reference
  rw [DescriptorAssignmentProjection.descriptorBearing_exact
    (globalDescriptorAssignmentProjection global.toFrozenCorpus)
      row.provision row.descriptorAssignmentBearing]
  change (global.reviewed.row row.provision).reference = row.reference
  rw [globalReviewedSemantics_ir9_exact global row]
  rfl

def next54DescriptorBearingIR9Provisions : List IUPACNormativeProvision :=
  Next54DescriptorBearingIR9Row.all.map Next54DescriptorBearingIR9Row.provision

@[simp] theorem next54DescriptorBearingIR9Provisions_length :
    next54DescriptorBearingIR9Provisions.length = 11 := by
  rfl

theorem next54DescriptorBearingIR9Provisions_nodup :
    next54DescriptorBearingIR9Provisions.Nodup := by
  decide

theorem exists_next54DescriptorBearingIR9Row
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54DescriptorBearingIR9Provisions) :
    ∃ row, row ∈ Next54DescriptorBearingIR9Row.all ∧ row.provision = provision := by
  simpa only [next54DescriptorBearingIR9Provisions, List.mem_map] using member

noncomputable def next54DescriptorBearingIR9RowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54DescriptorBearingIR9Provisions) :
    Next54DescriptorBearingIR9Row :=
  Classical.choose (exists_next54DescriptorBearingIR9Row member)

theorem next54DescriptorBearingIR9RowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54DescriptorBearingIR9Provisions) :
    (next54DescriptorBearingIR9RowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_next54DescriptorBearingIR9Row member)).2

theorem next54IR9GlobalReference_eq_of_member
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54DescriptorBearingIR9Provisions) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference provision =
      (next54DescriptorBearingIR9RowOf provision member).reference := by
  let row := next54DescriptorBearingIR9RowOf provision member
  have rowProvision : row.provision = provision :=
    next54DescriptorBearingIR9RowOf_provision provision member
  calc
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference provision =
        (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
          row.provision := congrArg
            ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference)
            rowProvision.symm
    _ = row.reference := next54IR9GlobalReference_eq global row
    _ = (next54DescriptorBearingIR9RowOf provision member).reference := rfl

noncomputable def Next54DescriptorBearingIR9Row.GlobalProductionJudges
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Next54DescriptorBearingIR9Row)
    (observation : ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision).Observation) : Prop :=
  row.ProductionJudges
    (cast (congrArg ProvisionReference.Observation
      (next54IR9GlobalReference_eq global row)) observation)

/-- Concrete residual IR-9 production.  Outside the exact 11-row scope it produces nothing;
later family joins provide the other named next-54 branches. -/
noncomputable def next54IR9GlobalInterpreter
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative) :
    ProvisionInterpreter
      (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus where
  Produces := fun provision _source observation =>
    if member : provision ∈ next54DescriptorBearingIR9Provisions then
      let row := next54DescriptorBearingIR9RowOf provision member
      let referenceEq := next54IR9GlobalReference_eq_of_member global provision member
      row.ProductionJudges
        (cast (congrArg ProvisionReference.Observation referenceEq) observation)
    else False

@[simp] theorem next54IR9GlobalInterpreter_exact
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Next54DescriptorBearingIR9Row)
    (source : AuthoritativeChemicalInput)
    (observation : ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision).Observation) :
    (next54IR9GlobalInterpreter global).Produces row.provision source observation ↔
      row.GlobalProductionJudges global observation := by
  have member : row.provision ∈ next54DescriptorBearingIR9Provisions := by
    change row.provision ∈
      Next54DescriptorBearingIR9Row.all.map Next54DescriptorBearingIR9Row.provision
    exact List.mem_map.mpr ⟨row, Next54DescriptorBearingIR9Row.mem_all row, rfl⟩
  simp only [next54IR9GlobalInterpreter]
  rw [dif_pos member]
  change (next54DescriptorBearingIR9RowOf row.provision member).ProductionJudges
      (cast (congrArg ProvisionReference.Observation
        (next54IR9GlobalReference_eq_of_member global row.provision member)) observation) ↔
    row.ProductionJudges
      (cast (congrArg ProvisionReference.Observation
        (next54IR9GlobalReference_eq global row)) observation)
  apply Next54DescriptorBearingIR9Row.productionJudges_congr
    (next54DescriptorBearingIR9RowOf row.provision member) row
    (next54DescriptorBearingIR9RowOf_provision row.provision member)
  exact (cast_heq _ observation).trans (cast_heq _ observation).symm

/-- Full bidirectional production/reference correctness for every one of the 11 rows. -/
theorem next54IR9GlobalProduction_correct
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Next54DescriptorBearingIR9Row) :
    ProvisionCorrect (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
      (next54IR9GlobalInterpreter global) row.provision := by
  intro source _admitted observation
  let referenceEq := next54IR9GlobalReference_eq global row
  let rowObservation : row.reference.Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq) observation
  have exactJudgment := row.production_eq_reference source rowObservation
  have applicable := row.reference_applicable source
  have applicableTransport := ProvisionReference.applicable_congr referenceEq source
  have judgmentTransport :=
    ProvisionReference.judges_cast_congr referenceEq source observation
  rw [next54IR9GlobalInterpreter_exact global row source observation]
  change row.ProductionJudges rowObservation ↔
    ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision).Applicable source ∧
      ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
        row.provision).Judges source observation
  constructor
  · intro produced
    exact ⟨applicableTransport.mpr applicable,
      judgmentTransport.mpr (exactJudgment.mp produced)⟩
  · rintro ⟨_applicable, judged⟩
    exact exactJudgment.mpr (judgmentTransport.mp judged)

/-- Public named adapter for the residual IR-9 family.  Its interpreter is fixed above and its
correctness field is the dependent 11-row theorem, not a caller-supplied relation. -/
structure Next54IR9GlobalProductionAdapter
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative) where
  interpreter : ProvisionInterpreter
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
  interpreter_exact : interpreter = next54IR9GlobalInterpreter global
  correct : ∀ row : Next54DescriptorBearingIR9Row,
    ProvisionCorrect (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
      interpreter row.provision

noncomputable def next54IR9GlobalProductionAdapter
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative) :
    Next54IR9GlobalProductionAdapter global where
  interpreter := next54IR9GlobalInterpreter global
  interpreter_exact := rfl
  correct := next54IR9GlobalProduction_correct global

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54DescriptorBearingIR9Row.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54IR9GlobalProduction_correct
