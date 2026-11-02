import TetraStereo.OneCenter.IUPACNormativeManifestCore

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def source : IUPACNormativeProvision → IUPACNormativeSource
  | .p10 _ => .blueBook2013P10
  | .appendix3 _ => .blueBook2013Appendix3
  | .retinoid1981 _ => .retinoidRecommendations1981
  | .carotenoid1974 _ => .carotenoidRules1974
  | .steroid1989 _ => .steroidRecommendations1989
  | .cyclitol1973 _ => .cyclitolRecommendations1973
  | .nucleicAcid1970 _ => .nucleicAcidRecommendations1970
  | .lipid1976 _ => .lipidRecommendations1976
  | .glycolipid1997 _ => .glycolipidRecommendations1997
  | .aminoAcidPeptide1983 _ => .aminoAcidPeptideRecommendations1983
  | .carbohydrate1996Foundation _ => .carbohydrateRecommendations1996
  | .carbohydrate1996NamedParents _ => .carbohydrateRecommendations1996
  | .carbohydrate1996ScopeParent _ => .carbohydrateRecommendations1996
  | .carbohydrate1996Derivatives _ => .carbohydrateRecommendations1996
  | .carbohydrate1996UnsaturatedBranched _ => .carbohydrateRecommendations1996
  | .carbohydrate1996AlditolsAcids _ => .carbohydrateRecommendations1996
  | .carbohydrate1996HeteroSubstitutionAnhydride _ => .carbohydrateRecommendations1996
  | .carbohydrate1996Acetals _ => .carbohydrateRecommendations1996
  | .carbohydrate1996ResiduesIons _ => .carbohydrateRecommendations1996
  | .carbohydrate1996GlycosidesRings _ => .carbohydrateRecommendations1996
  | .carbohydrate1996OligosaccharidesPolysaccharides _ =>
      .carbohydrateRecommendations1996
  | .carbohydrate1996AppendixErrataGlossary _ => .carbohydrateRecommendations1996
  | .carbohydrate1996ImageArtifact _ => .carbohydrateRecommendations1996
  | .drawingOverview | .drawingPlainBonds | .drawingHashesDashesWedges
  | .drawingWavyBonds | .drawingStereobondsBetweenStereocenters
  | .drawingAsterisks | .drawingCIPStereodescriptors | .drawingDiastereoisomerMixtures
  | .drawingTetraFourExplicit01 | .drawingTetraFourExplicit02
  | .drawingTetraFourExplicit03 | .drawingTetraFourExplicit04
  | .drawingTetraFourExplicit05 | .drawingTetraFourExplicit06
  | .drawingTetraFourExplicit07 | .drawingTetraFourExplicit08
  | .drawingTetraFourExplicit09 | .drawingTetraFourExplicit10
  | .drawingTetraFourExplicit11 | .drawingTetraFourExplicit12
  | .drawingTetraFourExplicit13 | .drawingTetraFourExplicit14
  | .drawingTetraFourExplicit15 | .drawingTetraFourExplicit16
  | .drawingTetraFourExplicit17 | .drawingTetraFourExplicit18
  | .drawingTetraFourExplicit19 | .drawingTetraFourExplicit20
  | .drawingTetraThreeExplicit01 | .drawingTetraThreeExplicit02
  | .drawingTetraThreeExplicit03 | .drawingTetraThreeExplicit04
  | .drawingTetraThreeExplicit05 | .drawingTetraThreeExplicit06
  | .drawingTetraThreeExplicit07 | .drawingTetraThreeExplicit08
  | .drawingTetraThreeExplicit09 | .drawingTetraThreeExplicit10
  | .drawingTetraThreeExplicit11 | .drawingTetraThreeExplicit12
  | .drawingRingTwoBonds | .drawingRingFusion | .drawingBridgehead | .drawingSpiroFusion
  | .drawingReentrantTetrahedralCenters | .drawingHigherOrderTetrahedralBonds
  | .drawingEvenConsecutiveDoubleBonds | .drawingHinderedBiaryls
  | .drawingFischerProjections | .drawingHaworthProjections | .drawingMillsDepictions
  | .drawingHDotDashCircle | .drawingLinearGeometry | .drawingAngularGeometry
  | .drawingTShapedGeometry | .drawingTrigonalPlanarGeometry
  | .drawingTrigonalPyramidalGeometry | .drawingSquarePlanarGeometry
  | .drawingSquarePyramidalFourGeometry | .drawingSeeSawGeometry
  | .drawingTrigonalBipyramidalGeometry | .drawingSquarePyramidalFiveGeometry
  | .drawingOctahedralGeometry | .drawingTrigonalPrismaticGeometry
  | .drawingHigherCoordinationGeometry | .drawingPerspectiveRestrictions
  | .drawingPerspectiveInterpretation | .drawingPerspectiveBoldBonds
  | .drawingDoubleBondSubstituentPositioning | .drawingOddConsecutiveDoubleBonds
  | .drawingRingDoubleBonds | .drawingUnspecifiedDoubleBondConfiguration
  | .drawingImplicitDoubleBondSubstituents | .drawingPlanarChirality | .drawingHelicenes
  | .drawingMobiusBands | .drawingMolecularPropellers | .drawingMixtureRepresentationGoals
  | .drawingAsDrawnAbsoluteConfiguration | .drawingMixtureExplanatoryText
  | .drawingRacemicAndKnownProportions | .drawingAvoidRacemateRelativeLabels =>
      .graphicalRepresentation2006
  | .ir9PolyhedralConfiguration | .ir9ConfigurationIntroduction
  | .ir9PolyhedralSymbols | .ir9GeometryChoice | .ir9DiastereoisomerGeneral
  | .ir9ConfigurationIndex | .ir9SquarePlanar | .ir9Octahedral
  | .ir9SquarePyramidal | .ir9Bipyramidal | .ir9TShape | .ir9SeeSaw
  | .ir9AbsoluteConfigurationGeneral | .ir9RSTetrahedral | .ir9RSTrigonalPyramidal
  | .ir9CAPolyhedral | .ir9CATrigonalBipyramidal | .ir9CASquarePyramidal
  | .ir9CASeeSaw | .ir9CAOctahedral | .ir9CATrigonalPrismatic
  | .ir9CAOtherBipyramidal | .ir9SkewLines | .ir9SkewLinesTrisBidentate
  | .ir9SkewLinesBisBidentate | .ir9SkewLinesChelateConformations
  | .ir9LigandPriorityGeneral | .ir9PriorityNumbers | .ir9PrimingConvention =>
      .redBook2005IR9
  | .periodicAtomicNumbers => .periodicTable2022
  | .standardAtomicWeights => .atomicWeights2021
  | .isotopeAtomicMasses => .atomicMasses2020
  | _ => .blueBook2013P9

/-- The manifest slice owned by one frozen normative source. -/
def sourceProvisions : IUPACNormativeSource → List IUPACNormativeProvision
  | .blueBook2013P9 =>
      coreProvisions.filter fun provision => source provision = .blueBook2013P9
  | .blueBook2013P10 =>
      BlueBookP10Audit.Provision.all.map IUPACNormativeProvision.p10
  | .blueBook2013Appendix3 =>
      BlueBookAppendix3Audit.Provision.all.map IUPACNormativeProvision.appendix3
  | .graphicalRepresentation2006 =>
      coreProvisions.filter fun provision => source provision = .graphicalRepresentation2006
  | .redBook2005IR9 =>
      [ .ir9PolyhedralConfiguration
      , .ir9ConfigurationIntroduction
      , .ir9PolyhedralSymbols
      , .ir9GeometryChoice
      , .ir9DiastereoisomerGeneral
      , .ir9ConfigurationIndex
      , .ir9SquarePlanar
      , .ir9Octahedral
      , .ir9SquarePyramidal
      , .ir9Bipyramidal
      , .ir9TShape
      , .ir9SeeSaw
      , .ir9AbsoluteConfigurationGeneral
      , .ir9RSTetrahedral
      , .ir9RSTrigonalPyramidal
      , .ir9CAPolyhedral
      , .ir9CATrigonalBipyramidal
      , .ir9CASquarePyramidal
      , .ir9CASeeSaw
      , .ir9CAOctahedral
      , .ir9CATrigonalPrismatic
      , .ir9CAOtherBipyramidal
      , .ir9SkewLines
      , .ir9SkewLinesTrisBidentate
      , .ir9SkewLinesBisBidentate
      , .ir9SkewLinesChelateConformations
      , .ir9LigandPriorityGeneral
      , .ir9PriorityNumbers
      , .ir9PrimingConvention
      ]
  | .periodicTable2022 => [.periodicAtomicNumbers]
  | .atomicWeights2021 => [.standardAtomicWeights]
  | .atomicMasses2020 => [.isotopeAtomicMasses]
  | .steroidRecommendations1989 =>
      Steroid1989.Provision.all.map IUPACNormativeProvision.steroid1989
  | .carotenoidRules1974 =>
      Carotenoid1974.Provision.all.map IUPACNormativeProvision.carotenoid1974
  | .retinoidRecommendations1981 =>
      Retinoid1981.Provision.all.map IUPACNormativeProvision.retinoid1981
  | .carbohydrateRecommendations1996 =>
      Carbohydrate1996ScopeParent.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996ScopeParent ++
        Carbohydrate1996Foundation.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996Foundation ++
        Carbohydrate1996NamedParents.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996NamedParents ++
        Carbohydrate1996Derivatives.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996Derivatives ++
        Carbohydrate1996UnsaturatedBranched.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched ++
        Carbohydrate1996AlditolsAcids.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996AlditolsAcids ++
        Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride ++
        Carbohydrate1996Acetals.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996Acetals ++
        Carbohydrate1996ResiduesIons.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996ResiduesIons ++
        Carbohydrate1996GlycosidesRings.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996GlycosidesRings ++
        Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides ++
        Carbohydrate1996AppendixErrataGlossary.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary ++
        Carbohydrate1996ImageAudit.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996ImageArtifact
  | .aminoAcidPeptideRecommendations1983 =>
      AminoAcidPeptide1983.Provision.all.map IUPACNormativeProvision.aminoAcidPeptide1983
  | .cyclitolRecommendations1973 =>
      Cyclitol1973.Provision.all.map IUPACNormativeProvision.cyclitol1973
  | .nucleicAcidRecommendations1970 =>
      NucleicAcid1970.Provision.all.map IUPACNormativeProvision.nucleicAcid1970
  | .lipidRecommendations1976 =>
      Lipid1976.Provision.all.map IUPACNormativeProvision.lipid1976
  | .glycolipidRecommendations1997 =>
      Glycolipid1997.Provision.all.map IUPACNormativeProvision.glycolipid1997

/-- Source-wise concatenation in the same order as the exhaustive manifest. -/
private def allByNormativeSource : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013P9 ++
    (sourceProvisions .graphicalRepresentation2006 ++
    (sourceProvisions .redBook2005IR9 ++
    (sourceProvisions .periodicTable2022 ++
    (sourceProvisions .atomicWeights2021 ++
    (sourceProvisions .atomicMasses2020 ++
    (sourceProvisions .blueBook2013P10 ++
    (sourceProvisions .blueBook2013Appendix3 ++
    (sourceProvisions .retinoidRecommendations1981 ++
    (sourceProvisions .carotenoidRules1974 ++
    (sourceProvisions .steroidRecommendations1989 ++
    (sourceProvisions .cyclitolRecommendations1973 ++
    (sourceProvisions .nucleicAcidRecommendations1970 ++
    (sourceProvisions .lipidRecommendations1976 ++
    (sourceProvisions .glycolipidRecommendations1997 ++
    (sourceProvisions .aminoAcidPeptideRecommendations1983 ++
      sourceProvisions .carbohydrateRecommendations1996)))))))))))))))

set_option maxRecDepth 8192 in
private theorem coreProvisions_source_partition :
    coreProvisions =
      sourceProvisions .blueBook2013P9 ++
      sourceProvisions .graphicalRepresentation2006 ++
      sourceProvisions .redBook2005IR9 ++
      sourceProvisions .periodicTable2022 ++
      sourceProvisions .atomicWeights2021 ++
      sourceProvisions .atomicMasses2020 := by
  decide

set_option maxRecDepth 8192 in
private theorem all_eq_allByNormativeSource : all = allByNormativeSource := by
  rw [all_eq_core_append_parameterized, coreProvisions_source_partition]
  simp only [allByNormativeSource, parameterizedProvisions, sourceProvisions,
    List.append_assoc]

private theorem source_eq_of_mem_map
    {α : Type} {rows : List α} {wrap : α → IUPACNormativeProvision}
    {normativeSource : IUPACNormativeSource} {provision : IUPACNormativeProvision}
    (wrapSource : ∀ row, source (wrap row) = normativeSource)
    (member : provision ∈ rows.map wrap) : source provision = normativeSource := by
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
  exact wrapSource row

private theorem forall_source_map
    {α : Type} (rows : List α) (wrap : α → IUPACNormativeProvision)
    (normativeSource : IUPACNormativeSource)
    (wrapSource : ∀ row, source (wrap row) = normativeSource) :
    (rows.map wrap).Forall (fun row => source row = normativeSource) := by
  rw [List.forall_iff_forall_mem]
  intro provision member
  exact source_eq_of_mem_map wrapSource member

set_option maxRecDepth 8192 in
private theorem source_eq_of_mem_sourceProvisions
    {provision : IUPACNormativeProvision} {normativeSource : IUPACNormativeSource}
    (member : provision ∈ sourceProvisions normativeSource) :
    source provision = normativeSource := by
  cases normativeSource with
  | blueBook2013P9 => exact of_decide_eq_true (List.mem_filter.mp member).2
  | blueBook2013P10 => exact source_eq_of_mem_map (fun _ => rfl) member
  | blueBook2013Appendix3 => exact source_eq_of_mem_map (fun _ => rfl) member
  | graphicalRepresentation2006 =>
      exact of_decide_eq_true (List.mem_filter.mp member).2
  | redBook2005IR9 =>
      have everyRowHasSource :
          (sourceProvisions .redBook2005IR9).Forall
            (fun row => source row = .redBook2005IR9) := by decide
      exact (List.forall_iff_forall_mem.mp everyRowHasSource) provision member
  | periodicTable2022 =>
      have equal : provision = .periodicAtomicNumbers := by
        simpa only [sourceProvisions, List.mem_singleton] using member
      subst provision
      rfl
  | atomicWeights2021 =>
      have equal : provision = .standardAtomicWeights := by
        simpa only [sourceProvisions, List.mem_singleton] using member
      subst provision
      rfl
  | atomicMasses2020 =>
      have equal : provision = .isotopeAtomicMasses := by
        simpa only [sourceProvisions, List.mem_singleton] using member
      subst provision
      rfl
  | steroidRecommendations1989 => exact source_eq_of_mem_map (fun _ => rfl) member
  | carotenoidRules1974 => exact source_eq_of_mem_map (fun _ => rfl) member
  | retinoidRecommendations1981 => exact source_eq_of_mem_map (fun _ => rfl) member
  | carbohydrateRecommendations1996 =>
      have everyRowHasSource :
          (sourceProvisions .carbohydrateRecommendations1996).Forall
            (fun row => source row = .carbohydrateRecommendations1996) := by
        simp only [sourceProvisions, List.forall_append]
        repeat' constructor
      exact (List.forall_iff_forall_mem.mp everyRowHasSource) provision member
  | aminoAcidPeptideRecommendations1983 =>
      exact source_eq_of_mem_map (fun _ => rfl) member
  | cyclitolRecommendations1973 => exact source_eq_of_mem_map (fun _ => rfl) member
  | nucleicAcidRecommendations1970 => exact source_eq_of_mem_map (fun _ => rfl) member
  | lipidRecommendations1976 => exact source_eq_of_mem_map (fun _ => rfl) member
  | glycolipidRecommendations1997 => exact source_eq_of_mem_map (fun _ => rfl) member

private theorem mem_sourceProvisions_source (provision : IUPACNormativeProvision) :
    provision ∈ sourceProvisions (source provision) := by
  have member : provision ∈ allByNormativeSource := by
    rw [← all_eq_allByNormativeSource]
    exact provision.mem_all
  simp only [allByNormativeSource, List.mem_append] at member
  rcases member with member | member | member | member | member | member | member | member |
      member | member | member | member | member | member | member | member | member <;>
    have sourceEqual := source_eq_of_mem_sourceProvisions member <;>
    rw [sourceEqual] <;>
    exact member

@[simp] theorem mem_sourceProvisions_iff
    (provision : IUPACNormativeProvision) (normativeSource : IUPACNormativeSource) :
    provision ∈ sourceProvisions normativeSource ↔ source provision = normativeSource := by
  constructor
  · exact source_eq_of_mem_sourceProvisions
  · intro sourceEqual
    rw [← sourceEqual]
    exact mem_sourceProvisions_source provision

/-- Standard weights and individual nuclide masses remain distinct normative obligations owned by
their respective frozen authorities. -/
theorem rule2_mass_source_partition :
    sourceProvisions .atomicWeights2021 = [.standardAtomicWeights] ∧
      sourceProvisions .atomicMasses2020 = [.isotopeAtomicMasses] := by
  exact ⟨rfl, rfl⟩





@[simp] theorem delegated_specialist_source_provision_count
    (document : P10DelegatedAuthorityCorpus.Document) :
    (sourceProvisions (IUPACNormativeSource.ofDelegatedDocument document)).length =
      if document = .retinoid1981 then 13
      else if document = .carotenoid1974 then 10
      else if document = .steroid1989 then 62
      else if document = .cyclitol1973 then 37
      else if document = .nucleicAcid1970 then 21
      else if document = .lipid1976 then 31
      else if document = .glycolipid1997 then 43
      else if document = .aminoAcidPeptide1983 then 45
      else if document = .carbohydrate1996 then 1704 else 0 := by
  cases document <;>
    simp [IUPACNormativeSource.ofDelegatedDocument, sourceProvisions]

set_option maxRecDepth 4096 in
@[simp] theorem graphicalProvisionCount :
    (sourceProvisions .graphicalRepresentation2006).length = 82 := by
  rfl

set_option maxRecDepth 8192 in


@[simp] theorem p10ProvisionCountDuringAudit :
    (sourceProvisions .blueBook2013P10).length = 71 := by
  simp [sourceProvisions]

/-- Appendix 3 now has one explicit obligation for each of 164 retained parent structures and each
of the seven reusable carotene end-group diagrams. -/
@[simp] theorem appendix3ProvisionCountDuringAudit :
    (sourceProvisions .blueBook2013Appendix3).length = 171 := by
  simp [sourceProvisions]

@[simp] theorem retinoid1981ProvisionCount :
    (sourceProvisions .retinoidRecommendations1981).length = 13 := by
  simp [sourceProvisions]

@[simp] theorem carotenoid1974ProvisionCount :
    (sourceProvisions .carotenoidRules1974).length = 10 := by
  simp [sourceProvisions]

@[simp] theorem steroid1989ProvisionCount :
    (sourceProvisions .steroidRecommendations1989).length = 62 := by
  simp [sourceProvisions]

@[simp] theorem cyclitol1973ProvisionCount :
    (sourceProvisions .cyclitolRecommendations1973).length = 37 := by
  simp [sourceProvisions]

@[simp] theorem nucleicAcid1970ProvisionCount :
    (sourceProvisions .nucleicAcidRecommendations1970).length = 21 := by
  simp [sourceProvisions]

@[simp] theorem lipid1976ProvisionCount :
    (sourceProvisions .lipidRecommendations1976).length = 31 := by
  simp [sourceProvisions]

@[simp] theorem glycolipid1997ProvisionCount :
    (sourceProvisions .glycolipidRecommendations1997).length = 43 := by
  simp [sourceProvisions]

@[simp] theorem aminoAcidPeptide1983ProvisionCount :
    (sourceProvisions .aminoAcidPeptideRecommendations1983).length = 45 := by
  simp [sourceProvisions]

@[simp] theorem carbohydrate1996ProvisionCountDuringAudit :
    (sourceProvisions .carbohydrateRecommendations1996).length = 1704 := by
  simp [sourceProvisions]


def ofIR9Provision : RedBookIR9.Provision → IUPACNormativeProvision
  | .polyhedralConfiguration => .ir9PolyhedralConfiguration
  | .configurationIntroduction => .ir9ConfigurationIntroduction
  | .polyhedralSymbols => .ir9PolyhedralSymbols
  | .geometryChoice => .ir9GeometryChoice
  | .diastereoisomerGeneral => .ir9DiastereoisomerGeneral
  | .configurationIndex => .ir9ConfigurationIndex
  | .squarePlanar => .ir9SquarePlanar
  | .octahedral => .ir9Octahedral
  | .squarePyramidal => .ir9SquarePyramidal
  | .bipyramidal => .ir9Bipyramidal
  | .tShape => .ir9TShape
  | .seeSaw => .ir9SeeSaw
  | .absoluteConfigurationGeneral => .ir9AbsoluteConfigurationGeneral
  | .rsTetrahedral => .ir9RSTetrahedral
  | .rsTrigonalPyramidal => .ir9RSTrigonalPyramidal
  | .caPolyhedral => .ir9CAPolyhedral
  | .caTrigonalBipyramidal => .ir9CATrigonalBipyramidal
  | .caSquarePyramidal => .ir9CASquarePyramidal
  | .caSeeSaw => .ir9CASeeSaw
  | .caOctahedral => .ir9CAOctahedral
  | .caTrigonalPrismatic => .ir9CATrigonalPrismatic
  | .caOtherBipyramidal => .ir9CAOtherBipyramidal
  | .skewLines => .ir9SkewLines
  | .skewLinesTrisBidentate => .ir9SkewLinesTrisBidentate
  | .skewLinesBisBidentate => .ir9SkewLinesBisBidentate
  | .skewLinesChelateConformations => .ir9SkewLinesChelateConformations
  | .ligandPriorityGeneral => .ir9LigandPriorityGeneral
  | .priorityNumbers => .ir9PriorityNumbers
  | .primingConvention => .ir9PrimingConvention

def ir9SemanticsSlice : List IUPACNormativeProvision :=
  RedBookIR9.Provision.all.map ofIR9Provision

@[simp] theorem ir9SemanticsSlice_exact :
    ir9SemanticsSlice = sourceProvisions .redBook2005IR9 := by
  rfl

@[simp] theorem ir9ProvisionCount :
    (sourceProvisions .redBook2005IR9).length = 29 := by
  rfl

/-- The first independently transcribed P-10 semantic slice. -/
def p101SemanticsSlice : List IUPACNormativeProvision :=
  BlueBookP101.p101Provisions.map IUPACNormativeProvision.p10

@[simp] theorem p101SemanticsSlice_length : p101SemanticsSlice.length = 19 := by
  simp [p101SemanticsSlice]

def p102SemanticsSlice : List IUPACNormativeProvision :=
  BlueBookP102.p102Provisions.map IUPACNormativeProvision.p10

@[simp] theorem p102SemanticsSlice_length : p102SemanticsSlice.length = 28 := by
  simp [p102SemanticsSlice]

def p103to107SemanticsSlice : List IUPACNormativeProvision :=
  BlueBookP103to107.p103to107Provisions.map IUPACNormativeProvision.p10

@[simp] theorem p103to107SemanticsSlice_length : p103to107SemanticsSlice.length = 24 := by
  simp [p103to107SemanticsSlice]

def p10SemanticsSlice : List IUPACNormativeProvision :=
  p101SemanticsSlice ++ p102SemanticsSlice ++ p103to107SemanticsSlice

@[simp] theorem p10SemanticsSlice_exact :
    p10SemanticsSlice = sourceProvisions .blueBook2013P10 := by
  rfl

def retinoid1981SemanticsSlice : List IUPACNormativeProvision :=
  Retinoid1981.Provision.all.map IUPACNormativeProvision.retinoid1981

@[simp] theorem retinoid1981SemanticsSlice_exact :
    retinoid1981SemanticsSlice = sourceProvisions .retinoidRecommendations1981 := by
  rfl

def carotenoid1974SemanticsSlice : List IUPACNormativeProvision :=
  Carotenoid1974.Provision.all.map IUPACNormativeProvision.carotenoid1974

@[simp] theorem carotenoid1974SemanticsSlice_exact :
    carotenoid1974SemanticsSlice = sourceProvisions .carotenoidRules1974 := by
  rfl

def steroid1989SemanticsSlice : List IUPACNormativeProvision :=
  Steroid1989.Provision.all.map IUPACNormativeProvision.steroid1989

@[simp] theorem steroid1989SemanticsSlice_exact :
    steroid1989SemanticsSlice = sourceProvisions .steroidRecommendations1989 := by
  rfl

def cyclitol1973SemanticsSlice : List IUPACNormativeProvision :=
  Cyclitol1973.Provision.all.map IUPACNormativeProvision.cyclitol1973

@[simp] theorem cyclitol1973SemanticsSlice_exact :
    cyclitol1973SemanticsSlice = sourceProvisions .cyclitolRecommendations1973 := by
  rfl

def nucleicAcid1970SemanticsSlice : List IUPACNormativeProvision :=
  NucleicAcid1970.Provision.all.map IUPACNormativeProvision.nucleicAcid1970

@[simp] theorem nucleicAcid1970SemanticsSlice_exact :
    nucleicAcid1970SemanticsSlice = sourceProvisions .nucleicAcidRecommendations1970 := by
  rfl

def lipid1976SemanticsSlice : List IUPACNormativeProvision :=
  Lipid1976.Provision.all.map IUPACNormativeProvision.lipid1976

@[simp] theorem lipid1976SemanticsSlice_exact :
    lipid1976SemanticsSlice = sourceProvisions .lipidRecommendations1976 := by
  rfl

def glycolipid1997SemanticsSlice : List IUPACNormativeProvision :=
  Glycolipid1997.Provision.all.map IUPACNormativeProvision.glycolipid1997

@[simp] theorem glycolipid1997SemanticsSlice_exact :
    glycolipid1997SemanticsSlice = sourceProvisions .glycolipidRecommendations1997 := by
  rfl

def aminoAcidPeptide1983SemanticsSlice : List IUPACNormativeProvision :=
  AminoAcidPeptide1983.Provision.all.map IUPACNormativeProvision.aminoAcidPeptide1983

@[simp] theorem aminoAcidPeptide1983SemanticsSlice_exact :
    aminoAcidPeptide1983SemanticsSlice =
      sourceProvisions .aminoAcidPeptideRecommendations1983 := by
  rfl

def carbohydrate1996FoundationSemanticsSlice : List IUPACNormativeProvision :=
  Carbohydrate1996Foundation.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996Foundation

@[simp] theorem carbohydrate1996FoundationSemanticsSlice_length :
    carbohydrate1996FoundationSemanticsSlice.length = 71 := by
  simp [carbohydrate1996FoundationSemanticsSlice]

def carbohydrate1996ScopeParentSemanticsSlice : List IUPACNormativeProvision :=
  Carbohydrate1996ScopeParent.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996ScopeParent

@[simp] theorem carbohydrate1996ScopeParentSemanticsSlice_length :
    carbohydrate1996ScopeParentSemanticsSlice.length = 95 := by
  simp [carbohydrate1996ScopeParentSemanticsSlice]

def carbohydrate1996NamedParentsSemanticsSlice : List IUPACNormativeProvision :=
  Carbohydrate1996NamedParents.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996NamedParents

@[simp] theorem carbohydrate1996NamedParentsSemanticsSlice_length :
    carbohydrate1996NamedParentsSemanticsSlice.length = 112 := by
  simp [carbohydrate1996NamedParentsSemanticsSlice]

def carbohydrate1996DerivativesSemanticsSlice : List IUPACNormativeProvision :=
  Carbohydrate1996Derivatives.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996Derivatives

@[simp] theorem carbohydrate1996DerivativesSemanticsSlice_length :
    carbohydrate1996DerivativesSemanticsSlice.length = 122 := by
  simp [carbohydrate1996DerivativesSemanticsSlice]

def carbohydrate1996UnsaturatedBranchedSemanticsSlice : List IUPACNormativeProvision :=
  Carbohydrate1996UnsaturatedBranched.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched

@[simp] theorem carbohydrate1996UnsaturatedBranchedSemanticsSlice_length :
    carbohydrate1996UnsaturatedBranchedSemanticsSlice.length = 85 := by
  simp [carbohydrate1996UnsaturatedBranchedSemanticsSlice]

def carbohydrate1996AlditolsAcidsSemanticsSlice : List IUPACNormativeProvision :=
  Carbohydrate1996AlditolsAcids.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996AlditolsAcids

@[simp] theorem carbohydrate1996AlditolsAcidsSemanticsSlice_length :
    carbohydrate1996AlditolsAcidsSemanticsSlice.length = 114 := by
  simp [carbohydrate1996AlditolsAcidsSemanticsSlice]

def carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice :
    List IUPACNormativeProvision :=
  Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride

@[simp] theorem carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice_length :
    carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice.length = 69 := by
  simp [carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice]

def carbohydrate1996AcetalsSemanticsSlice : List IUPACNormativeProvision :=
  Carbohydrate1996Acetals.Provision.all.map IUPACNormativeProvision.carbohydrate1996Acetals

@[simp] theorem carbohydrate1996AcetalsSemanticsSlice_length :
    carbohydrate1996AcetalsSemanticsSlice.length = 38 := by
  simp [carbohydrate1996AcetalsSemanticsSlice]

def carbohydrate1996ResiduesIonsSemanticsSlice : List IUPACNormativeProvision :=
  Carbohydrate1996ResiduesIons.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996ResiduesIons

@[simp] theorem carbohydrate1996ResiduesIonsSemanticsSlice_length :
    carbohydrate1996ResiduesIonsSemanticsSlice.length = 60 := by
  simp [carbohydrate1996ResiduesIonsSemanticsSlice]

def carbohydrate1996GlycosidesRingsSemanticsSlice : List IUPACNormativeProvision :=
  Carbohydrate1996GlycosidesRings.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996GlycosidesRings

@[simp] theorem carbohydrate1996GlycosidesRingsSemanticsSlice_length :
    carbohydrate1996GlycosidesRingsSemanticsSlice.length = 113 := by
  simp [carbohydrate1996GlycosidesRingsSemanticsSlice]

def carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice :
    List IUPACNormativeProvision :=
  Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides

@[simp] theorem carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice_length :
    carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice.length = 220 := by
  simp [carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice]

def carbohydrate1996AppendixErrataGlossarySemanticsSlice : List IUPACNormativeProvision :=
  Carbohydrate1996AppendixErrataGlossary.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary

@[simp] theorem carbohydrate1996AppendixErrataGlossarySemanticsSlice_length :
    carbohydrate1996AppendixErrataGlossarySemanticsSlice.length = 175 := by
  simp [carbohydrate1996AppendixErrataGlossarySemanticsSlice]

/-- Frozen image artifacts are source obligations, not independent molecular-graph semantics. -/
def carbohydrate1996ImageArtifactSourceSlice : List IUPACNormativeProvision :=
  Carbohydrate1996ImageAudit.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem carbohydrate1996ImageArtifactSourceSlice_length :
    carbohydrate1996ImageArtifactSourceSlice.length = 430 := by
  simp [carbohydrate1996ImageArtifactSourceSlice]

def carbohydrate1996TranscribedImageSemanticsSlice : List IUPACNormativeProvision :=
  Carbohydrate1996ImageAudit.Provision.transcribed.map
    IUPACNormativeProvision.carbohydrate1996ImageArtifact

def carbohydrate1996UntranscribedImageSourceSlice : List IUPACNormativeProvision :=
  Carbohydrate1996ImageAudit.Provision.notTranscribed.map
    IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem carbohydrate1996ImageGraphProgressCounts :
    carbohydrate1996TranscribedImageSemanticsSlice.length = 6 ∧
      carbohydrate1996UntranscribedImageSourceSlice.length = 424 := by
  simp [carbohydrate1996TranscribedImageSemanticsSlice,
    carbohydrate1996UntranscribedImageSourceSlice]

def carbohydrate1996SemanticsSlice : List IUPACNormativeProvision :=
  carbohydrate1996ScopeParentSemanticsSlice ++ carbohydrate1996FoundationSemanticsSlice ++
    carbohydrate1996NamedParentsSemanticsSlice ++ carbohydrate1996DerivativesSemanticsSlice ++
    carbohydrate1996UnsaturatedBranchedSemanticsSlice ++
    carbohydrate1996AlditolsAcidsSemanticsSlice ++
    carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice ++
    carbohydrate1996AcetalsSemanticsSlice ++ carbohydrate1996ResiduesIonsSemanticsSlice ++
    carbohydrate1996GlycosidesRingsSemanticsSlice ++
    carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice ++
    carbohydrate1996AppendixErrataGlossarySemanticsSlice

@[simp] theorem carbohydrate1996SourcePartition_exact :
    carbohydrate1996SemanticsSlice ++ carbohydrate1996ImageArtifactSourceSlice =
      sourceProvisions .carbohydrateRecommendations1996 := by
  simp [carbohydrate1996SemanticsSlice, carbohydrate1996ImageArtifactSourceSlice,
    carbohydrate1996ScopeParentSemanticsSlice,
    carbohydrate1996FoundationSemanticsSlice,
    carbohydrate1996NamedParentsSemanticsSlice,
    carbohydrate1996DerivativesSemanticsSlice,
    carbohydrate1996UnsaturatedBranchedSemanticsSlice,
    carbohydrate1996AlditolsAcidsSemanticsSlice,
    carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice,
    carbohydrate1996AcetalsSemanticsSlice,
    carbohydrate1996ResiduesIonsSemanticsSlice,
    carbohydrate1996GlycosidesRingsSemanticsSlice,
    carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice,
    carbohydrate1996AppendixErrataGlossarySemanticsSlice,
    sourceProvisions, List.append_assoc]

def sourceSection : IUPACNormativeProvision → String
  | .p10 provision => provision.sourceSection
  | .appendix3 provision => provision.sourceKey
  | .retinoid1981 provision => provision.sourceKey
  | .carotenoid1974 provision => provision.sourceKey
  | .steroid1989 provision => provision.sourceKey
  | .cyclitol1973 provision => provision.sourceKey
  | .nucleicAcid1970 provision => provision.sourceKey
  | .lipid1976 provision => provision.sourceKey
  | .glycolipid1997 provision => provision.sourceKey
  | .aminoAcidPeptide1983 provision => provision.sourceKey
  | .carbohydrate1996Foundation provision => provision.sourceKey
  | .carbohydrate1996NamedParents provision => provision.sourceKey
  | .carbohydrate1996ScopeParent provision => provision.sourceKey
  | .carbohydrate1996Derivatives provision => provision.sourceKey
  | .carbohydrate1996UnsaturatedBranched provision => provision.sourceKey
  | .carbohydrate1996AlditolsAcids provision => provision.sourceKey
  | .carbohydrate1996HeteroSubstitutionAnhydride provision => provision.sourceKey
  | .carbohydrate1996Acetals provision => provision.sourceKey
  | .carbohydrate1996ResiduesIons provision => provision.sourceKey
  | .carbohydrate1996GlycosidesRings provision => provision.sourceKey
  | .carbohydrate1996OligosaccharidesPolysaccharides provision => provision.sourceKey
  | .carbohydrate1996AppendixErrataGlossary provision => provision.sourceKey
  | .carbohydrate1996ImageArtifact provision => provision.sourceKey
  | .p90ScopeAndTerminology => "P-90"
  | .p91ConfigurationDepiction => "P-91.1"
  | .p91DescriptorVocabulary => "P-91.2.1"
  | .p91OtherAcceptableDescriptors => "P-91.2.1.2"
  | .p91SubstitutiveNomenclatureDescriptors => "P-91.2.1.2.1"
  | .p91NaturalProductDescriptors => "P-91.2.1.2.2"
  | .p91DescriptorOmission => "P-91.2.2"
  | .p91NamingOfStereoisomers => "P-91.3"
  | .p92StereogenicUnits => "P-92.1.1"
  | .p92ChiralityDefinition => "P-92.1.1/chirality"
  | .p92ChiralityCenterDefinition => "P-92.1.1(a)"
  | .p92ChiralityAxisDefinition => "P-92.1.1(b)"
  | .p92ChiralityPlaneDefinition => "P-92.1.1(c)"
  | .p92PseudoasymmetricUnitDefinition => "P-92.1.1(d)"
  | .p92CisTransDoubleBondUnitDefinition => "P-92.1.1(e)"
  | .p92EnantiomorphicDoubleBondUnitDefinition => "P-92.1.1(f)"
  | .p92BondingNumberScope => "P-92.1.2"
  | .p92ChiralityRuleGeneral => "P-92.1.2.1"
  | .p92CenterChiralityRule => "P-92.1.2.1.1"
  | .p92AxisChiralityRule => "P-92.1.2.1.2"
  | .p92PlaneChiralityRule => "P-92.1.2.1.3"
  | .p92HelicityRule => "P-92.1.2.2"
  | .p92HelicityAxis => "P-92.1.2.2.1"
  | .p92HelicityPlane => "P-92.1.2.2.2"
  | .p92RSMPDescriptorCorrespondence => "P-92.1.2.2.3"
  | .p92SequenceRulePropertyClasses => "P-92.1.3"
  | .p92SequenceRuleReflectionBehavior => "P-92.1.3"
  | .p92LigandDentateKinds => "P-92.1.3"
  | .p92SequenceRuleHierarchy => "P-92.1.3"
  | .p92AcyclicDigraph => "P-92.1.4.1"
  | .p92MultipleBondDigraph => "P-92.1.4.2"
  | .p92CyclicDigraph => "P-92.1.4.3"
  | .p92MancudeDigraph => "P-92.1.4.4"
  | .p92SphereExploration => "P-92.1.5"
  | .p92RuleExhaustivity => "P-92.1.6"
  | .p92Rule1aAtomicNumber => "P-92.2.1"
  | .p92Rule1aMultipleBondDuplicates => "P-92.2.1.2"
  | .p92Rule1aMancude => "P-92.2.1.4"
  | .p92Rule1aSaturatedCompounds => "P-92.2.1.1"
  | .p92Rule1aDoubleTripleBonds => "P-92.2.1.2"
  | .p92Rule1aSaturatedRings => "P-92.2.1.3"
  | .p92Rule1bDuplicateProximity => "P-92.2.2"
  | .p92Rule2IsotopeMass => "P-92.3"
  | .p92Rule3Geometry => "P-92.4"
  | .p92Rule3SeqCisTrans => "P-92.4.1"
  | .p92Rule3Priority => "P-92.4.2"
  | .p92Rule4aUnitKind => "P-92.5.1"
  | .p92Rule4bLikeUnlike => "P-92.5.2"
  | .p92Rule4bPairingMethodology => "P-92.5.2.1"
  | .p92Rule4cPseudoasymmetry => "P-92.5.3"
  | .p92Rule5Enantiomorph => "P-92.6"
  | .p93OtherElementTetrahedra => "P-93.2"
  | .p93AbsoluteConfiguration => "P-93.1.1"
  | .p93RelativeConfiguration => "P-93.1.2.1"
  | .p93MixedAbsoluteRelativeConfiguration => "P-93.1.2.2"
  | .p93Racemates => "P-93.1.3"
  | .p93Ambo => "P-93.1.4"
  | .p93OtherElementGeneralMethodology => "P-93.2.1"
  | .p93AzaniumPhosphanium => "P-93.2.2"
  | .p93AminePhosphaneOxides => "P-93.2.3"
  | .p93PhosphatesPhosphonates => "P-93.2.4"
  | .p93SulfatesSulfonates => "P-93.2.5"
  | .p93Group14Noncarbon => "P-93.2.6"
  | .p93NontetrahedralGeneralMethodology => "P-93.3.1"
  | .p93PolyhedralSymbols => "P-93.3.2/Table 9.1"
  | .p93PolyhedralGeometryRecognition => "P-93.3.1--P-93.3.2"
  | .p93PolyhedralPriorityNumbering => "P-93.3.3.1"
  | .p93TrigonalPyramid => "P-93.3.3.2"
  | .p93TShape => "P-93.3.3.3"
  | .p93SeeSaw => "P-93.3.3.4"
  | .p93TrigonalBipyramid => "P-93.3.3.5"
  | .p93SquarePyramid => "P-93.3.3.6"
  | .p93Octahedron => "P-93.3.3.7"
  | .p93PolyhedralChirality => "P-93.3.4"
  | .p93AcyclicCenters => "P-93.4.1"
  | .p93SingleAcyclicCenter => "P-93.4.1.1"
  | .p93MultipleDescriptorsOneCenter => "P-93.4.1.2"
  | .p93PrefixComponentCenters => "P-93.4.1.3"
  | .p93OrdinaryDoubleBonds => "P-93.4.2.1"
  | .p93DoubleBondEZCisTrans => "P-93.4.2.1.1"
  | .p93MultipleDoubleBonds => "P-93.4.2.1.2"
  | .p93HeteroatomDoubleBonds => "P-93.4.2.1.3"
  | .p93EvenCumulenes => "P-93.4.2.2"
  | .p93OddCumulenes => "P-93.4.2.3"
  | .p93MultipleAcyclicStereogenicUnits => "P-93.4.2.4"
  | .p93CyclicConfigurations => "P-93.5"
  | .p93MonocyclicAbsoluteCenters => "P-93.5.1.1.1"
  | .p93MonocyclicAchiralCenters => "P-93.5.1.1.2"
  | .p93MonocyclicCisTrans => "P-93.5.1.2"
  | .p93MonocyclicRCT => "P-93.5.1.3"
  | .p93UnsaturatedMonocycles => "P-93.5.1.4"
  | .p93CyclicDoubleBonds => "P-93.5.1.4.1"
  | .p93ExocyclicDoubleBondEZ => "P-93.5.1.4.2.1"
  | .p93ExocyclicDoubleBondOther => "P-93.5.1.4.2.2"
  | .p93VonBaeyerCIPCenters => "P-93.5.2.1"
  | .p93VonBaeyerEndoExoSynAnti => "P-93.5.2.2.1"
  | .p93VonBaeyerCisTrans => "P-93.5.2.2.2"
  | .p93VonBaeyerDoubleBonds => "P-93.5.2.3"
  | .p93SpiroXabcd => "P-93.5.3.1"
  | .p93SpiroXabab => "P-93.5.3.2"
  | .p93SpiroDoubleBonds => "P-93.5.3.3"
  | .p93SpiroNontetrahedralCenters => "P-93.5.3.4"
  | .p93SpiroAxialChirality => "P-93.5.3.5"
  | .p93FusedBridgedCIP => "P-93.5.4.1"
  | .p93CisoidTransoid => "P-93.5.4.2"
  | .p93CyclophanePlanes => "P-93.5.5.1"
  | .p93CyclophaneCenters => "P-93.5.5.2"
  | .p93CyclophaneDoubleBonds => "P-93.5.5.3"
  | .p93FullereneGeneralMethodology => "P-93.5.6.1"
  | .p93FullereneInherentParentChirality => "P-93.5.6.2"
  | .p93FullereneInherentSubstitutionChirality => "P-93.5.6.3"
  | .p93FullereneNoninherentSubstitutionChirality => "P-93.5.6.4"
  | .p93FullereneChiralSubstituents => "P-93.5.6.5"
  | .p93FullereneSuperimposedStereogenicElements => "P-93.5.6.6"
  | .p93RingAssemblyAxes => "P-93.5.7.1"
  | .p93RingAssemblyCenters => "P-93.5.7.2"
  | .p93RingAssemblyDoubleBonds => "P-93.5.7.3"
  | .p93CoupledRingChainConfigurations => "P-93.6"
  | .p94ConformationDefinition => "P-94.1"
  | .p94TorsionAngle => "P-94.2.1"
  | .p94TorsionLonePairs => "P-94.2.2"
  | .p94EclipsedStaggeredGauche => "P-94.3.1.1"
  | .p94TrigonalConformations => "P-94.3.1.2"
  | .p94SCisSTrans => "P-94.3.1.3"
  | .p94Envelope => "P-94.3.2.1"
  | .p94ChairBoatTwist => "P-94.3.2.2"
  | .p94HalfChair => "P-94.3.2.3"
  | .p94Crown => "P-94.3.2.4"
  | .p94Tub => "P-94.3.2.5"
  | .p94InOut => "P-94.3.2.6"
  | .drawingOverview => "ST-0.1"
  | .drawingPlainBonds => "ST-0.2"
  | .drawingHashesDashesWedges => "ST-0.3"
  | .drawingWavyBonds => "ST-0.4"
  | .drawingStereobondsBetweenStereocenters => "ST-0.5"
  | .drawingAsterisks => "ST-0.6"
  | .drawingCIPStereodescriptors => "ST-0.7"
  | .drawingDiastereoisomerMixtures => "ST-0.8"
  | .drawingTetraFourExplicit01 => "ST-1.1.1"
  | .drawingTetraFourExplicit02 => "ST-1.1.2"
  | .drawingTetraFourExplicit03 => "ST-1.1.3"
  | .drawingTetraFourExplicit04 => "ST-1.1.4"
  | .drawingTetraFourExplicit05 => "ST-1.1.5"
  | .drawingTetraFourExplicit06 => "ST-1.1.6"
  | .drawingTetraFourExplicit07 => "ST-1.1.7"
  | .drawingTetraFourExplicit08 => "ST-1.1.8"
  | .drawingTetraFourExplicit09 => "ST-1.1.9"
  | .drawingTetraFourExplicit10 => "ST-1.1.10"
  | .drawingTetraFourExplicit11 => "ST-1.1.11"
  | .drawingTetraFourExplicit12 => "ST-1.1.12"
  | .drawingTetraFourExplicit13 => "ST-1.1.13"
  | .drawingTetraFourExplicit14 => "ST-1.1.14"
  | .drawingTetraFourExplicit15 => "ST-1.1.15"
  | .drawingTetraFourExplicit16 => "ST-1.1.16"
  | .drawingTetraFourExplicit17 => "ST-1.1.17"
  | .drawingTetraFourExplicit18 => "ST-1.1.18"
  | .drawingTetraFourExplicit19 => "ST-1.1.19"
  | .drawingTetraFourExplicit20 => "ST-1.1.20"
  | .drawingTetraThreeExplicit01 => "ST-1.2.1"
  | .drawingTetraThreeExplicit02 => "ST-1.2.2"
  | .drawingTetraThreeExplicit03 => "ST-1.2.3"
  | .drawingTetraThreeExplicit04 => "ST-1.2.4"
  | .drawingTetraThreeExplicit05 => "ST-1.2.5"
  | .drawingTetraThreeExplicit06 => "ST-1.2.6"
  | .drawingTetraThreeExplicit07 => "ST-1.2.7"
  | .drawingTetraThreeExplicit08 => "ST-1.2.8"
  | .drawingTetraThreeExplicit09 => "ST-1.2.9"
  | .drawingTetraThreeExplicit10 => "ST-1.2.10"
  | .drawingTetraThreeExplicit11 => "ST-1.2.11"
  | .drawingTetraThreeExplicit12 => "ST-1.2.12"
  | .drawingRingTwoBonds => "ST-1.3.1"
  | .drawingRingFusion => "ST-1.3.2"
  | .drawingBridgehead => "ST-1.3.3"
  | .drawingSpiroFusion => "ST-1.3.4"
  | .drawingReentrantTetrahedralCenters => "ST-1.4"
  | .drawingHigherOrderTetrahedralBonds => "ST-1.5"
  | .drawingEvenConsecutiveDoubleBonds => "ST-1.6"
  | .drawingHinderedBiaryls => "ST-1.7"
  | .drawingFischerProjections => "ST-1.8"
  | .drawingHaworthProjections => "ST-1.9"
  | .drawingMillsDepictions => "ST-1.10"
  | .drawingHDotDashCircle => "ST-1.11"
  | .drawingLinearGeometry => "ST-2.1"
  | .drawingAngularGeometry => "ST-2.2"
  | .drawingTShapedGeometry => "ST-2.3"
  | .drawingTrigonalPlanarGeometry => "ST-2.4"
  | .drawingTrigonalPyramidalGeometry => "ST-2.5"
  | .drawingSquarePlanarGeometry => "ST-2.6"
  | .drawingSquarePyramidalFourGeometry => "ST-2.7"
  | .drawingSeeSawGeometry => "ST-2.8"
  | .drawingTrigonalBipyramidalGeometry => "ST-2.9"
  | .drawingSquarePyramidalFiveGeometry => "ST-2.10"
  | .drawingOctahedralGeometry => "ST-2.11"
  | .drawingTrigonalPrismaticGeometry => "ST-2.12"
  | .drawingHigherCoordinationGeometry => "ST-2.13"
  | .drawingPerspectiveRestrictions => "ST-3.1"
  | .drawingPerspectiveInterpretation => "ST-3.2"
  | .drawingPerspectiveBoldBonds => "ST-3.3"
  | .drawingDoubleBondSubstituentPositioning => "ST-4.1"
  | .drawingOddConsecutiveDoubleBonds => "ST-4.2"
  | .drawingRingDoubleBonds => "ST-4.3"
  | .drawingUnspecifiedDoubleBondConfiguration => "ST-4.4"
  | .drawingImplicitDoubleBondSubstituents => "ST-4.5"
  | .drawingPlanarChirality => "ST-5.1"
  | .drawingHelicenes => "ST-5.2"
  | .drawingMobiusBands => "ST-5.3"
  | .drawingMolecularPropellers => "ST-5.4"
  | .drawingMixtureRepresentationGoals => "ST-6.1"
  | .drawingAsDrawnAbsoluteConfiguration => "ST-6.2"
  | .drawingMixtureExplanatoryText => "ST-6.3"
  | .drawingRacemicAndKnownProportions => "ST-6.4"
  | .drawingAvoidRacemateRelativeLabels => "ST-6.5"
  | .ir9PolyhedralConfiguration => "IR-9.3"
  | .ir9ConfigurationIntroduction => "IR-9.3.1"
  | .ir9PolyhedralSymbols => "IR-9.3.2.1/Tables IR-9.2--IR-9.3"
  | .ir9GeometryChoice => "IR-9.3.2.2"
  | .ir9DiastereoisomerGeneral => "IR-9.3.3.1"
  | .ir9ConfigurationIndex => "IR-9.3.3.2"
  | .ir9SquarePlanar => "IR-9.3.3.3"
  | .ir9Octahedral => "IR-9.3.3.4"
  | .ir9SquarePyramidal => "IR-9.3.3.5"
  | .ir9Bipyramidal => "IR-9.3.3.6"
  | .ir9TShape => "IR-9.3.3.7"
  | .ir9SeeSaw => "IR-9.3.3.8"
  | .ir9AbsoluteConfigurationGeneral => "IR-9.3.4.1"
  | .ir9RSTetrahedral => "IR-9.3.4.2"
  | .ir9RSTrigonalPyramidal => "IR-9.3.4.3"
  | .ir9CAPolyhedral => "IR-9.3.4.4"
  | .ir9CATrigonalBipyramidal => "IR-9.3.4.5"
  | .ir9CASquarePyramidal => "IR-9.3.4.6"
  | .ir9CASeeSaw => "IR-9.3.4.7"
  | .ir9CAOctahedral => "IR-9.3.4.8"
  | .ir9CATrigonalPrismatic => "IR-9.3.4.9"
  | .ir9CAOtherBipyramidal => "IR-9.3.4.10"
  | .ir9SkewLines => "IR-9.3.4.11"
  | .ir9SkewLinesTrisBidentate => "IR-9.3.4.12"
  | .ir9SkewLinesBisBidentate => "IR-9.3.4.13"
  | .ir9SkewLinesChelateConformations => "IR-9.3.4.14"
  | .ir9LigandPriorityGeneral => "IR-9.3.5.1"
  | .ir9PriorityNumbers => "IR-9.3.5.2"
  | .ir9PrimingConvention => "IR-9.3.5.3"
  | .periodicAtomicNumbers => "Periodic table"
  | .standardAtomicWeights => "Standard atomic weights"
  | .isotopeAtomicMasses => "AME-2020 nuclide atomic-mass records"

@[simp] theorem sourceSection_ofIR9Provision (provision : RedBookIR9.Provision) :
    sourceSection (ofIR9Provision provision) = provision.sourceSection := by
  cases provision <;> rfl

/-- No two drawing obligations in the manifest silently share the same subsection/table-row key. -/
theorem graphicalSourceSections_nodup :
    ((sourceProvisions .graphicalRepresentation2006).map sourceSection).Nodup := by
  set_option maxRecDepth 4096 in
    decide

/-- Coarse implementation maturity.  `primitiveProved` is deliberately below end-to-end: it says
that a local comparison or conversion is checked, not that every applicable molecular occurrence
reaches it. -/
inductive CoverageMaturity where
  | absent
  | partiallyCovered
  | primitiveProved
  | endToEndProved
  deriving DecidableEq, Repr

/-- Provisions whose complete production path is proved equal to the independent semantics on
every admitted applicable input.  This inventory is intentionally empty today.  A future entry
must also carry proof in `ProvisionTerminalLedger`; the list alone is not a completion certificate. -/
def endToEndProvedProvisions : List IUPACNormativeProvision := []

/-- Stable 35-row source/program inventory used by the primitive compiler.  Unlike the coverage
status below, this list does not change when its rows are promoted. -/
def primitive35Provisions : List IUPACNormativeProvision :=
  [ .p92Rule1aAtomicNumber
  , .p92Rule1bDuplicateProximity
  , .p92Rule2IsotopeMass
  , .p92Rule3Geometry
  , .p92Rule3SeqCisTrans
  , .p92Rule3Priority
  , .p92Rule4aUnitKind
  , .p92Rule4bLikeUnlike
  , .p92Rule4bPairingMethodology
  , .p92Rule4cPseudoasymmetry
  , .p92Rule5Enantiomorph
  , .p93PolyhedralSymbols
  , .p93PolyhedralPriorityNumbering
  , .p93TShape
  , .p93SeeSaw
  , .p93TrigonalBipyramid
  , .p93SquarePyramid
  , .p93Octahedron
  , .p93PolyhedralChirality
  , .ir9PolyhedralSymbols
  , .ir9SquarePlanar
  , .ir9Octahedral
  , .ir9SquarePyramidal
  , .ir9Bipyramidal
  , .ir9TShape
  , .ir9SeeSaw
  , .ir9RSTrigonalPyramidal
  , .ir9CAPolyhedral
  , .ir9CATrigonalBipyramidal
  , .ir9CASquarePyramidal
  , .ir9CASeeSaw
  , .ir9CAOctahedral
  , .ir9CAOtherBipyramidal
  , .ir9PriorityNumbers
  , .ir9PrimingConvention
  ]

@[simp] theorem primitive35ProvisionCount : primitive35Provisions.length = 35 := by
  rfl

/-- Current project-management status.  This alias records that all 35 stable primitive rows are
presently at `primitiveProved`; the production architecture does not depend on this status name. -/
def primitiveProvedProvisions : List IUPACNormativeProvision :=
  primitive35Provisions

/-- Provisions for which production has some relevant implementation, but no complete local or
end-to-end theorem.  Every provision in neither list is honestly classified as absent. -/
def partiallyCoveredProvisions : List IUPACNormativeProvision :=
  [ .p91ConfigurationDepiction
  , .p91DescriptorVocabulary
  , .p92StereogenicUnits
  , .p92CenterChiralityRule
  , .p92AxisChiralityRule
  , .p92PlaneChiralityRule
  , .p92HelicityRule
  , .p92HelicityAxis
  , .p92HelicityPlane
  , .p92AcyclicDigraph
  , .p92MultipleBondDigraph
  , .p92CyclicDigraph
  , .p92MancudeDigraph
  , .p92SphereExploration
  , .p92RuleExhaustivity
  , .p92Rule1aMultipleBondDuplicates
  , .p92Rule1aMancude
  , .p92Rule1aSaturatedCompounds
  , .p92Rule1aDoubleTripleBonds
  , .p92Rule1aSaturatedRings
  , .p93OtherElementTetrahedra
  , .p93OtherElementGeneralMethodology
  , .p93AzaniumPhosphanium
  , .p93AminePhosphaneOxides
  , .p93PhosphatesPhosphonates
  , .p93SulfatesSulfonates
  , .p93Group14Noncarbon
  , .p93NontetrahedralGeneralMethodology
  , .p93AcyclicCenters
  , .p93SingleAcyclicCenter
  , .p93OrdinaryDoubleBonds
  , .p93DoubleBondEZCisTrans
  , .p93EvenCumulenes
  , .p93OddCumulenes
  , .p93CyclicConfigurations
  , .p93MonocyclicAbsoluteCenters
  , .p93MonocyclicAchiralCenters
  , .p93MonocyclicCisTrans
  , .p93SpiroXabcd
  , .p93SpiroXabab
  , .p93SpiroAxialChirality
  , .p93FusedBridgedCIP
  , .p93CyclophanePlanes
  , .p93RingAssemblyAxes
  , .p93RingAssemblyCenters
  , .p93RingAssemblyDoubleBonds
  , .p93CoupledRingChainConfigurations
  , .p93TrigonalPyramid
  , .ir9ConfigurationIntroduction
  , .ir9DiastereoisomerGeneral
  , .ir9ConfigurationIndex
  , .ir9AbsoluteConfigurationGeneral
  , .ir9RSTetrahedral
  , .ir9LigandPriorityGeneral
  , .drawingPlainBonds
  , .drawingHashesDashesWedges
  , .drawingWavyBonds
  , .drawingCIPStereodescriptors
  , .drawingEvenConsecutiveDoubleBonds
  , .drawingHinderedBiaryls
  , .drawingDoubleBondSubstituentPositioning
  , .drawingOddConsecutiveDoubleBonds
  , .drawingUnspecifiedDoubleBondConfiguration
  , .drawingPlanarChirality
  , .drawingHelicenes
  , .drawingAsDrawnAbsoluteConfiguration
  , .periodicAtomicNumbers
  , .standardAtomicWeights
  , .isotopeAtomicMasses
  ]



def currentMaturity (provision : IUPACNormativeProvision) : CoverageMaturity :=
  if provision ∈ endToEndProvedProvisions then .endToEndProved
  else if provision ∈ primitiveProvedProvisions then .primitiveProved
  else if provision ∈ partiallyCoveredProvisions then .partiallyCovered
  else .absent








inductive SemanticsMaturity where
  | absent
  | partiallyFormalized
  | provisionComplete
  deriving DecidableEq, Repr

/-- Primitive-implementation rows whose independent reference semantics have been separately
audited.  This is intentionally an explicit semantics-side inventory rather than an alias for
`primitiveProvedProvisions`: promoting implementation maturity must not silently manufacture its
own normative target. -/
def independentPrimitiveSemanticsProvisions : List IUPACNormativeProvision :=
  [ .p92Rule1aAtomicNumber
  , .p92Rule1bDuplicateProximity
  , .p92Rule2IsotopeMass
  , .p92Rule3Geometry
  , .p92Rule3SeqCisTrans
  , .p92Rule3Priority
  , .p92Rule4aUnitKind
  , .p92Rule4bLikeUnlike
  , .p92Rule4bPairingMethodology
  , .p92Rule4cPseudoasymmetry
  , .p92Rule5Enantiomorph
  , .p93PolyhedralSymbols
  , .p93PolyhedralPriorityNumbering
  , .p93TShape
  , .p93SeeSaw
  , .p93TrigonalBipyramid
  , .p93SquarePyramid
  , .p93Octahedron
  , .p93PolyhedralChirality
  , .ir9PolyhedralSymbols
  , .ir9SquarePlanar
  , .ir9Octahedral
  , .ir9SquarePyramidal
  , .ir9Bipyramidal
  , .ir9TShape
  , .ir9SeeSaw
  , .ir9RSTrigonalPyramidal
  , .ir9CAPolyhedral
  , .ir9CATrigonalBipyramidal
  , .ir9CASquarePyramidal
  , .ir9CASeeSaw
  , .ir9CAOctahedral
  , .ir9CAOtherBipyramidal
  , .ir9PriorityNumbers
  , .ir9PrimingConvention
  ]

/-- The implementation and semantics inventories are checked against one another rather than
coupled by definition.  A future implementation promotion therefore creates a proof obligation
until an independently audited target is added on the semantics side. -/
theorem primitiveProved_mem_independentPrimitiveSemantics :
    ∀ provision ∈ primitiveProvedProvisions,
      provision ∈ independentPrimitiveSemanticsProvisions := by
  decide

/-- Provisions with a genuinely independent formal target, but not yet every applicability,
perception, naming, and exception clause needed to close the whole source provision. -/
def directPartiallyFormalizedSemanticsProvisions : List IUPACNormativeProvision :=
  [ .periodicAtomicNumbers
  , .standardAtomicWeights
  , .isotopeAtomicMasses
  , .p90ScopeAndTerminology
  , .p91ConfigurationDepiction
  , .p91DescriptorVocabulary
  , .p91OtherAcceptableDescriptors
  , .p91SubstitutiveNomenclatureDescriptors
  , .p91NaturalProductDescriptors
  , .p91DescriptorOmission
  , .p91NamingOfStereoisomers
  , .p92StereogenicUnits
  , .p92ChiralityDefinition
  , .p92ChiralityCenterDefinition
  , .p92ChiralityAxisDefinition
  , .p92ChiralityPlaneDefinition
  , .p92PseudoasymmetricUnitDefinition
  , .p92CisTransDoubleBondUnitDefinition
  , .p92EnantiomorphicDoubleBondUnitDefinition
  , .p92BondingNumberScope
  , .p92ChiralityRuleGeneral
  , .p92CenterChiralityRule
  , .p92AxisChiralityRule
  , .p92PlaneChiralityRule
  , .p92HelicityRule
  , .p92HelicityAxis
  , .p92HelicityPlane
  , .p92RSMPDescriptorCorrespondence
  , .p92SequenceRulePropertyClasses
  , .p92SequenceRuleReflectionBehavior
  , .p92LigandDentateKinds
  , .p92SequenceRuleHierarchy
  , .p92AcyclicDigraph
  , .p92MultipleBondDigraph
  , .p92CyclicDigraph
  , .p92MancudeDigraph
  , .p92SphereExploration
  , .p92RuleExhaustivity
  , .p92Rule1aMultipleBondDuplicates
  , .p92Rule1aMancude
  , .p92Rule1aSaturatedCompounds
  , .p92Rule1aDoubleTripleBonds
  , .p92Rule1aSaturatedRings
  , .p93AbsoluteConfiguration
  , .p93RelativeConfiguration
  , .p93MixedAbsoluteRelativeConfiguration
  , .p93Racemates
  , .p93Ambo
  , .p93OtherElementTetrahedra
  , .p93OtherElementGeneralMethodology
  , .p93AzaniumPhosphanium
  , .p93AminePhosphaneOxides
  , .p93PhosphatesPhosphonates
  , .p93SulfatesSulfonates
  , .p93Group14Noncarbon
  , .p93NontetrahedralGeneralMethodology
  , .p93PolyhedralGeometryRecognition
  , .p93TrigonalPyramid
  , .p93AcyclicCenters
  , .p93SingleAcyclicCenter
  , .p93MultipleDescriptorsOneCenter
  , .p93PrefixComponentCenters
  , .p93OrdinaryDoubleBonds
  , .p93DoubleBondEZCisTrans
  , .p93MultipleDoubleBonds
  , .p93HeteroatomDoubleBonds
  , .p93EvenCumulenes
  , .p93OddCumulenes
  , .p93MultipleAcyclicStereogenicUnits
  , .p93CyclicConfigurations
  , .p93MonocyclicAbsoluteCenters
  , .p93MonocyclicAchiralCenters
  , .p93MonocyclicCisTrans
  , .p93MonocyclicRCT
  , .p93UnsaturatedMonocycles
  , .p93CyclicDoubleBonds
  , .p93ExocyclicDoubleBondEZ
  , .p93ExocyclicDoubleBondOther
  , .p93VonBaeyerCIPCenters
  , .p93VonBaeyerEndoExoSynAnti
  , .p93VonBaeyerCisTrans
  , .p93VonBaeyerDoubleBonds
  , .p93SpiroXabcd
  , .p93SpiroXabab
  , .p93SpiroDoubleBonds
  , .p93SpiroNontetrahedralCenters
  , .p93SpiroAxialChirality
  , .p93FusedBridgedCIP
  , .p93CisoidTransoid
  , .p93CyclophanePlanes
  , .p93CyclophaneCenters
  , .p93CyclophaneDoubleBonds
  , .p93FullereneGeneralMethodology
  , .p93FullereneInherentParentChirality
  , .p93FullereneInherentSubstitutionChirality
  , .p93FullereneNoninherentSubstitutionChirality
  , .p93FullereneChiralSubstituents
  , .p93FullereneSuperimposedStereogenicElements
  , .p93RingAssemblyAxes
  , .p93RingAssemblyCenters
  , .p93RingAssemblyDoubleBonds
  , .p93CoupledRingChainConfigurations
  , .drawingOverview
  , .drawingPlainBonds
  , .drawingHashesDashesWedges
  , .drawingWavyBonds
  , .drawingStereobondsBetweenStereocenters
  , .drawingAsterisks
  , .drawingCIPStereodescriptors
  , .drawingDiastereoisomerMixtures
  , .drawingTetraFourExplicit01
  , .drawingTetraFourExplicit02
  , .drawingTetraFourExplicit03
  , .drawingTetraFourExplicit04
  , .drawingTetraFourExplicit05
  , .drawingTetraFourExplicit06
  , .drawingTetraFourExplicit07
  , .drawingTetraFourExplicit08
  , .drawingTetraFourExplicit09
  , .drawingTetraFourExplicit10
  , .drawingTetraFourExplicit11
  , .drawingTetraFourExplicit12
  , .drawingTetraFourExplicit13
  , .drawingTetraFourExplicit14
  , .drawingTetraFourExplicit15
  , .drawingTetraFourExplicit16
  , .drawingTetraFourExplicit17
  , .drawingTetraFourExplicit18
  , .drawingTetraFourExplicit19
  , .drawingTetraFourExplicit20
  , .drawingTetraThreeExplicit01
  , .drawingTetraThreeExplicit02
  , .drawingTetraThreeExplicit03
  , .drawingTetraThreeExplicit04
  , .drawingTetraThreeExplicit05
  , .drawingTetraThreeExplicit06
  , .drawingTetraThreeExplicit07
  , .drawingTetraThreeExplicit08
  , .drawingTetraThreeExplicit09
  , .drawingTetraThreeExplicit10
  , .drawingTetraThreeExplicit11
  , .drawingTetraThreeExplicit12
  , .drawingRingTwoBonds
  , .drawingRingFusion
  , .drawingBridgehead
  , .drawingSpiroFusion
  , .drawingReentrantTetrahedralCenters
  , .drawingHigherOrderTetrahedralBonds
  , .drawingEvenConsecutiveDoubleBonds
  , .drawingHinderedBiaryls
  , .drawingFischerProjections
  , .drawingHaworthProjections
  , .drawingMillsDepictions
  , .drawingHDotDashCircle
  , .drawingLinearGeometry
  , .drawingAngularGeometry
  , .drawingTShapedGeometry
  , .drawingTrigonalPlanarGeometry
  , .drawingTrigonalPyramidalGeometry
  , .drawingSquarePlanarGeometry
  , .drawingSquarePyramidalFourGeometry
  , .drawingSeeSawGeometry
  , .drawingTrigonalBipyramidalGeometry
  , .drawingSquarePyramidalFiveGeometry
  , .drawingOctahedralGeometry
  , .drawingTrigonalPrismaticGeometry
  , .drawingHigherCoordinationGeometry
  , .drawingPerspectiveRestrictions
  , .drawingPerspectiveInterpretation
  , .drawingPerspectiveBoldBonds
  , .drawingDoubleBondSubstituentPositioning
  , .drawingOddConsecutiveDoubleBonds
  , .drawingRingDoubleBonds
  , .drawingUnspecifiedDoubleBondConfiguration
  , .drawingImplicitDoubleBondSubstituents
  , .drawingPlanarChirality
  , .drawingHelicenes
  , .drawingMobiusBands
  , .drawingMolecularPropellers
  , .drawingMixtureRepresentationGoals
  , .drawingAsDrawnAbsoluteConfiguration
  , .drawingMixtureExplanatoryText
  , .drawingRacemicAndKnownProportions
  , .drawingAvoidRacemateRelativeLabels
  , .p94ConformationDefinition
  , .p94TorsionAngle
  , .p94TorsionLonePairs
  , .p94EclipsedStaggeredGauche
  , .p94TrigonalConformations
  , .p94SCisSTrans
  , .p94Envelope
  , .p94ChairBoatTwist
  , .p94HalfChair
  , .p94Crown
  , .p94Tub
  , .p94InOut
  ]

/-- Complete current partial-semantics inventory, factored into independently checkable source
chunks so coverage proofs do not normalize the whole delegated corpus. -/
def partiallyFormalizedSemanticsProvisions : List IUPACNormativeProvision :=
  independentPrimitiveSemanticsProvisions ++ (directPartiallyFormalizedSemanticsProvisions ++
    (ir9SemanticsSlice ++ (p10SemanticsSlice ++ (retinoid1981SemanticsSlice ++
    (carotenoid1974SemanticsSlice ++ (steroid1989SemanticsSlice ++
    (cyclitol1973SemanticsSlice ++ (nucleicAcid1970SemanticsSlice ++
    (lipid1976SemanticsSlice ++ (glycolipid1997SemanticsSlice ++
    (aminoAcidPeptide1983SemanticsSlice ++ (carbohydrate1996SemanticsSlice ++
    carbohydrate1996TranscribedImageSemanticsSlice))))))))))))

/-- The partial-semantics prefix before the six explicitly transcribed carbohydrate images. -/
private def nonImagePartiallyFormalizedSemanticsProvisions : List IUPACNormativeProvision :=
  independentPrimitiveSemanticsProvisions ++ (directPartiallyFormalizedSemanticsProvisions ++
    (ir9SemanticsSlice ++ (p10SemanticsSlice ++ (retinoid1981SemanticsSlice ++
    (carotenoid1974SemanticsSlice ++ (steroid1989SemanticsSlice ++
    (cyclitol1973SemanticsSlice ++ (nucleicAcid1970SemanticsSlice ++
    (lipid1976SemanticsSlice ++ (glycolipid1997SemanticsSlice ++
    (aminoAcidPeptide1983SemanticsSlice ++ carbohydrate1996SemanticsSlice)))))))))))

private theorem partiallyFormalizedSemanticsProvisions_eq_nonImage_append_transcribed :
    partiallyFormalizedSemanticsProvisions =
      nonImagePartiallyFormalizedSemanticsProvisions ++
        carbohydrate1996TranscribedImageSemanticsSlice := by
  simp [partiallyFormalizedSemanticsProvisions,
    nonImagePartiallyFormalizedSemanticsProvisions, List.append_assoc]

private def isCarbohydrateImageArtifactProvision : IUPACNormativeProvision → Bool
  | .carbohydrate1996ImageArtifact _ => true
  | _ => false

private theorem forall_nonImage_map
    {α : Type} (rows : List α) (wrap : α → IUPACNormativeProvision)
    (wrapNotImage : ∀ row, isCarbohydrateImageArtifactProvision (wrap row) = false) :
    (rows.map wrap).Forall
      (fun row => isCarbohydrateImageArtifactProvision row = false) := by
  rw [List.forall_iff_forall_mem]
  intro provision member
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
  exact wrapNotImage row

set_option maxRecDepth 8192 in
private theorem carbohydrate1996SemanticsSlice_has_no_image_artifacts :
    carbohydrate1996SemanticsSlice.Forall
      (fun row => isCarbohydrateImageArtifactProvision row = false) := by
  simp only [carbohydrate1996SemanticsSlice, List.forall_append]
  repeat' constructor

private theorem nonImagePartiallyFormalizedSemanticsProvisions_has_no_image_artifacts
    (provision : IUPACNormativeProvision)
    (member : provision ∈ nonImagePartiallyFormalizedSemanticsProvisions) :
    isCarbohydrateImageArtifactProvision provision = false := by
  simp only [nonImagePartiallyFormalizedSemanticsProvisions, List.mem_append] at member
  rcases member with member | member | member | member | member | member | member | member |
      member | member | member | member | member
  · have noImages : ∀ row ∈ independentPrimitiveSemanticsProvisions,
        isCarbohydrateImageArtifactProvision row = false := by decide
    exact noImages provision member
  · have noImages : ∀ row ∈ directPartiallyFormalizedSemanticsProvisions,
        isCarbohydrateImageArtifactProvision row = false := by
      set_option maxRecDepth 4096 in
        decide
    exact noImages provision member
  · have noImages : ∀ row ∈ ir9SemanticsSlice,
        isCarbohydrateImageArtifactProvision row = false := by decide
    exact noImages provision member
  · have noImages : ∀ row ∈ p10SemanticsSlice,
        isCarbohydrateImageArtifactProvision row = false := by decide
    exact noImages provision member
  · have noImages : ∀ row ∈ retinoid1981SemanticsSlice,
        isCarbohydrateImageArtifactProvision row = false := by decide
    exact noImages provision member
  · have noImages : ∀ row ∈ carotenoid1974SemanticsSlice,
        isCarbohydrateImageArtifactProvision row = false := by decide
    exact noImages provision member
  · have noImages : ∀ row ∈ steroid1989SemanticsSlice,
        isCarbohydrateImageArtifactProvision row = false := by decide
    exact noImages provision member
  · have noImages : ∀ row ∈ cyclitol1973SemanticsSlice,
        isCarbohydrateImageArtifactProvision row = false := by decide
    exact noImages provision member
  · have noImages : ∀ row ∈ nucleicAcid1970SemanticsSlice,
        isCarbohydrateImageArtifactProvision row = false := by decide
    exact noImages provision member
  · have noImages : ∀ row ∈ lipid1976SemanticsSlice,
        isCarbohydrateImageArtifactProvision row = false := by decide
    exact noImages provision member
  · have noImages : ∀ row ∈ glycolipid1997SemanticsSlice,
        isCarbohydrateImageArtifactProvision row = false := by decide
    exact noImages provision member
  · have noImages : ∀ row ∈ aminoAcidPeptide1983SemanticsSlice,
        isCarbohydrateImageArtifactProvision row = false := by decide
    exact noImages provision member
  · exact (List.forall_iff_forall_mem.mp
      carbohydrate1996SemanticsSlice_has_no_image_artifacts) provision member

/-- Empty until a provision's prose, tables, figures, applicability boundary, and result relation
have all been transcribed and independently reviewed. -/
def provisionCompleteSemanticsProvisions : List IUPACNormativeProvision := []

def currentSemanticsMaturity (provision : IUPACNormativeProvision) : SemanticsMaturity :=
  if provision ∈ provisionCompleteSemanticsProvisions then .provisionComplete
  else if provision ∈ partiallyFormalizedSemanticsProvisions then .partiallyFormalized
  else .absent

/-- Membership in the audited partial-semantics inventory is sufficient for, and remains strictly
below, provision-complete maturity.  Keeping this lemma separate prevents downstream coverage
proofs from normalizing the entire 2,452-row manifest. -/
theorem currentSemanticsMaturity_eq_partiallyFormalized_of_mem
    {provision : IUPACNormativeProvision}
    (member : provision ∈ partiallyFormalizedSemanticsProvisions) :
    currentSemanticsMaturity provision = .partiallyFormalized := by
  simp [currentSemanticsMaturity, provisionCompleteSemanticsProvisions, member]

theorem currentSemanticsMaturity_eq_absent_of_not_mem
    {provision : IUPACNormativeProvision}
    (notMember : provision ∉ partiallyFormalizedSemanticsProvisions) :
    currentSemanticsMaturity provision = .absent := by
  simp [currentSemanticsMaturity, provisionCompleteSemanticsProvisions, notMember]

/-- The two direct kernel-backed inventories form the prefix of the partial-semantics inventory. -/
theorem mem_partiallyFormalizedSemanticsProvisions_of_mem_primitive_or_direct
    {provision : IUPACNormativeProvision}
    (member : provision ∈ primitiveProvedProvisions ∨
      provision ∈ directPartiallyFormalizedSemanticsProvisions) :
    provision ∈ partiallyFormalizedSemanticsProvisions := by
  rcases member with member | member
  · exact List.mem_append_left _
      (primitiveProved_mem_independentPrimitiveSemantics provision member)
  · exact List.mem_append_right _ (List.mem_append_left _ member)

theorem currentSemanticsMaturity_eq_partiallyFormalized_of_mem_direct
    {provision : IUPACNormativeProvision}
    (member : provision ∈ directPartiallyFormalizedSemanticsProvisions) :
    currentSemanticsMaturity provision = .partiallyFormalized :=
  currentSemanticsMaturity_eq_partiallyFormalized_of_mem
    (mem_partiallyFormalizedSemanticsProvisions_of_mem_primitive_or_direct (Or.inr member))

/-- The authority-data target is independently formalized only in part; this maturity tag does
not certify whole-provision source adoption or implementation completion. -/
theorem periodicAtomicNumbers_semantics_partiallyFormalized :
    currentSemanticsMaturity .periodicAtomicNumbers = .partiallyFormalized :=
  currentSemanticsMaturity_eq_partiallyFormalized_of_mem_direct (by decide)

theorem standardAtomicWeights_semantics_partiallyFormalized :
    currentSemanticsMaturity .standardAtomicWeights = .partiallyFormalized :=
  currentSemanticsMaturity_eq_partiallyFormalized_of_mem_direct (by decide)

theorem isotopeAtomicMasses_semantics_partiallyFormalized :
    currentSemanticsMaturity .isotopeAtomicMasses = .partiallyFormalized :=
  currentSemanticsMaturity_eq_partiallyFormalized_of_mem_direct (by decide)

def p91SemanticsSlice : List IUPACNormativeProvision :=
  [ .p91ConfigurationDepiction
  , .p91DescriptorVocabulary
  , .p91OtherAcceptableDescriptors
  , .p91SubstitutiveNomenclatureDescriptors
  , .p91NaturalProductDescriptors
  , .p91DescriptorOmission
  , .p91NamingOfStereoisomers
  ]

def p90SemanticsSlice : List IUPACNormativeProvision :=
  [ .p90ScopeAndTerminology ]

def p92FoundationalSemanticsSlice : List IUPACNormativeProvision :=
  [ .p92StereogenicUnits
  , .p92ChiralityDefinition
  , .p92ChiralityCenterDefinition
  , .p92ChiralityAxisDefinition
  , .p92ChiralityPlaneDefinition
  , .p92PseudoasymmetricUnitDefinition
  , .p92CisTransDoubleBondUnitDefinition
  , .p92EnantiomorphicDoubleBondUnitDefinition
  , .p92BondingNumberScope
  , .p92ChiralityRuleGeneral
  , .p92CenterChiralityRule
  , .p92AxisChiralityRule
  , .p92PlaneChiralityRule
  , .p92HelicityRule
  , .p92HelicityAxis
  , .p92HelicityPlane
  , .p92RSMPDescriptorCorrespondence
  , .p92SequenceRulePropertyClasses
  , .p92SequenceRuleReflectionBehavior
  , .p92LigandDentateKinds
  , .p92SequenceRuleHierarchy
  ]

def p92DigraphAndRule1aSemanticsSlice : List IUPACNormativeProvision :=
  [ .p92AcyclicDigraph
  , .p92MultipleBondDigraph
  , .p92CyclicDigraph
  , .p92MancudeDigraph
  , .p92SphereExploration
  , .p92RuleExhaustivity
  , .p92Rule1aMultipleBondDuplicates
  , .p92Rule1aMancude
  , .p92Rule1aSaturatedCompounds
  , .p92Rule1aDoubleTripleBonds
  , .p92Rule1aSaturatedRings
  ]

/-- Remaining whole-rule P-92 provisions, separated from the foundational and digraph slices. -/
def p92RuleSemanticsSlice : List IUPACNormativeProvision :=
  [ .p92Rule1aAtomicNumber
  , .p92Rule1bDuplicateProximity
  , .p92Rule2IsotopeMass
  , .p92Rule3Geometry
  , .p92Rule3SeqCisTrans
  , .p92Rule3Priority
  , .p92Rule4aUnitKind
  , .p92Rule4bLikeUnlike
  , .p92Rule4bPairingMethodology
  , .p92Rule4cPseudoasymmetry
  , .p92Rule5Enantiomorph
  ]

def p92SourceProvisions : List IUPACNormativeProvision :=
  p92FoundationalSemanticsSlice ++ p92DigraphAndRule1aSemanticsSlice ++
    p92RuleSemanticsSlice

@[simp] theorem p92SourceProvisionCount : p92SourceProvisions.length = 43 := by
  rfl

set_option maxRecDepth 16384 in
theorem every_p92_provision_has_partial_independent_semantics :
    ∀ provision ∈ p92SourceProvisions,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  apply mem_partiallyFormalizedSemanticsProvisions_of_mem_primitive_or_direct
  rw [p92SourceProvisions] at member
  simp only [List.mem_append] at member
  rcases member with (member | member) | member
  · right
    have included : p92FoundationalSemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member
  · right
    have included : p92DigraphAndRule1aSemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member
  · left
    have included : p92RuleSemanticsSlice.Sublist primitiveProvedProvisions := by decide
    exact included.subset member

def p93GeneralSemanticsSlice : List IUPACNormativeProvision :=
  [ .p93AbsoluteConfiguration
  , .p93RelativeConfiguration
  , .p93MixedAbsoluteRelativeConfiguration
  , .p93Racemates
  , .p93Ambo
  ]

def p93NoncarbonTetrahedraSemanticsSlice : List IUPACNormativeProvision :=
  [ .p93OtherElementTetrahedra
  , .p93OtherElementGeneralMethodology
  , .p93AzaniumPhosphanium
  , .p93AminePhosphaneOxides
  , .p93PhosphatesPhosphonates
  , .p93SulfatesSulfonates
  , .p93Group14Noncarbon
  ]

def p93PolyhedralSemanticsSlice : List IUPACNormativeProvision :=
  [ .p93NontetrahedralGeneralMethodology
  , .p93PolyhedralSymbols
  , .p93PolyhedralGeometryRecognition
  , .p93PolyhedralPriorityNumbering
  , .p93TrigonalPyramid
  , .p93TShape
  , .p93SeeSaw
  , .p93TrigonalBipyramid
  , .p93SquarePyramid
  , .p93Octahedron
  , .p93PolyhedralChirality
  ]

def p93AcyclicSemanticsSlice : List IUPACNormativeProvision :=
  [ .p93AcyclicCenters
  , .p93SingleAcyclicCenter
  , .p93MultipleDescriptorsOneCenter
  , .p93PrefixComponentCenters
  , .p93OrdinaryDoubleBonds
  , .p93DoubleBondEZCisTrans
  , .p93MultipleDoubleBonds
  , .p93HeteroatomDoubleBonds
  , .p93EvenCumulenes
  , .p93OddCumulenes
  , .p93MultipleAcyclicStereogenicUnits
  ]

def p93CyclicSemanticsSlice : List IUPACNormativeProvision :=
  [ .p93CyclicConfigurations
  , .p93MonocyclicAbsoluteCenters
  , .p93MonocyclicAchiralCenters
  , .p93MonocyclicCisTrans
  , .p93MonocyclicRCT
  , .p93UnsaturatedMonocycles
  , .p93CyclicDoubleBonds
  , .p93ExocyclicDoubleBondEZ
  , .p93ExocyclicDoubleBondOther
  , .p93VonBaeyerCIPCenters
  , .p93VonBaeyerEndoExoSynAnti
  , .p93VonBaeyerCisTrans
  , .p93VonBaeyerDoubleBonds
  , .p93SpiroXabcd
  , .p93SpiroXabab
  , .p93SpiroDoubleBonds
  , .p93SpiroNontetrahedralCenters
  , .p93SpiroAxialChirality
  , .p93FusedBridgedCIP
  , .p93CisoidTransoid
  , .p93CyclophanePlanes
  , .p93CyclophaneCenters
  , .p93CyclophaneDoubleBonds
  , .p93FullereneGeneralMethodology
  , .p93FullereneInherentParentChirality
  , .p93FullereneInherentSubstitutionChirality
  , .p93FullereneNoninherentSubstitutionChirality
  , .p93FullereneChiralSubstituents
  , .p93FullereneSuperimposedStereogenicElements
  , .p93RingAssemblyAxes
  , .p93RingAssemblyCenters
  , .p93RingAssemblyDoubleBonds
  , .p93CoupledRingChainConfigurations
  ]

/-- All manifest provisions whose stable source key lies in P-93. -/
def p93SourceProvisions : List IUPACNormativeProvision :=
  p93GeneralSemanticsSlice ++ p93NoncarbonTetrahedraSemanticsSlice ++
    p93PolyhedralSemanticsSlice ++ p93AcyclicSemanticsSlice ++ p93CyclicSemanticsSlice

@[simp] theorem p93SourceProvisionCount : p93SourceProvisions.length = 67 := by
  rfl

set_option maxRecDepth 16384 in
theorem every_p93_provision_has_partial_independent_semantics :
    ∀ provision ∈ p93SourceProvisions,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  apply mem_partiallyFormalizedSemanticsProvisions_of_mem_primitive_or_direct
  rw [p93SourceProvisions] at member
  simp only [List.mem_append] at member
  rcases member with (((member | member) | member) | member) | member
  · right
    have included : p93GeneralSemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member
  · right
    have included : p93NoncarbonTetrahedraSemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member
  · have included : ∀ row ∈ p93PolyhedralSemanticsSlice,
        row ∈ primitiveProvedProvisions ∨
          row ∈ directPartiallyFormalizedSemanticsProvisions := by decide
    exact included provision member
  · right
    have included : p93AcyclicSemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member
  · right
    have included : p93CyclicSemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member

def drawingST0SemanticsSlice : List IUPACNormativeProvision :=
  [ .drawingOverview
  , .drawingPlainBonds
  , .drawingHashesDashesWedges
  , .drawingWavyBonds
  , .drawingStereobondsBetweenStereocenters
  , .drawingAsterisks
  , .drawingCIPStereodescriptors
  , .drawingDiastereoisomerMixtures
  ]

def drawingST1TetrahedralTableSemanticsSlice : List IUPACNormativeProvision :=
  [ .drawingTetraFourExplicit01
  , .drawingTetraFourExplicit02
  , .drawingTetraFourExplicit03
  , .drawingTetraFourExplicit04
  , .drawingTetraFourExplicit05
  , .drawingTetraFourExplicit06
  , .drawingTetraFourExplicit07
  , .drawingTetraFourExplicit08
  , .drawingTetraFourExplicit09
  , .drawingTetraFourExplicit10
  , .drawingTetraFourExplicit11
  , .drawingTetraFourExplicit12
  , .drawingTetraFourExplicit13
  , .drawingTetraFourExplicit14
  , .drawingTetraFourExplicit15
  , .drawingTetraFourExplicit16
  , .drawingTetraFourExplicit17
  , .drawingTetraFourExplicit18
  , .drawingTetraFourExplicit19
  , .drawingTetraFourExplicit20
  , .drawingTetraThreeExplicit01
  , .drawingTetraThreeExplicit02
  , .drawingTetraThreeExplicit03
  , .drawingTetraThreeExplicit04
  , .drawingTetraThreeExplicit05
  , .drawingTetraThreeExplicit06
  , .drawingTetraThreeExplicit07
  , .drawingTetraThreeExplicit08
  , .drawingTetraThreeExplicit09
  , .drawingTetraThreeExplicit10
  , .drawingTetraThreeExplicit11
  , .drawingTetraThreeExplicit12
  ]

def drawingST1SpecialSemanticsSlice : List IUPACNormativeProvision :=
  [ .drawingRingTwoBonds
  , .drawingRingFusion
  , .drawingBridgehead
  , .drawingSpiroFusion
  , .drawingReentrantTetrahedralCenters
  , .drawingHigherOrderTetrahedralBonds
  , .drawingEvenConsecutiveDoubleBonds
  , .drawingHinderedBiaryls
  , .drawingFischerProjections
  , .drawingHaworthProjections
  , .drawingMillsDepictions
  , .drawingHDotDashCircle
  ]

def drawingST2SemanticsSlice : List IUPACNormativeProvision :=
  [ .drawingLinearGeometry
  , .drawingAngularGeometry
  , .drawingTShapedGeometry
  , .drawingTrigonalPlanarGeometry
  , .drawingTrigonalPyramidalGeometry
  , .drawingSquarePlanarGeometry
  , .drawingSquarePyramidalFourGeometry
  , .drawingSeeSawGeometry
  , .drawingTrigonalBipyramidalGeometry
  , .drawingSquarePyramidalFiveGeometry
  , .drawingOctahedralGeometry
  , .drawingTrigonalPrismaticGeometry
  , .drawingHigherCoordinationGeometry
  ]

def drawingST3to6SemanticsSlice : List IUPACNormativeProvision :=
  [ .drawingPerspectiveRestrictions
  , .drawingPerspectiveInterpretation
  , .drawingPerspectiveBoldBonds
  , .drawingDoubleBondSubstituentPositioning
  , .drawingOddConsecutiveDoubleBonds
  , .drawingRingDoubleBonds
  , .drawingUnspecifiedDoubleBondConfiguration
  , .drawingImplicitDoubleBondSubstituents
  , .drawingPlanarChirality
  , .drawingHelicenes
  , .drawingMobiusBands
  , .drawingMolecularPropellers
  , .drawingMixtureRepresentationGoals
  , .drawingAsDrawnAbsoluteConfiguration
  , .drawingMixtureExplanatoryText
  , .drawingRacemicAndKnownProportions
  , .drawingAvoidRacemateRelativeLabels
  ]

def allDrawingSemanticsSlices : List IUPACNormativeProvision :=
  drawingST0SemanticsSlice ++
  drawingST1TetrahedralTableSemanticsSlice ++
  drawingST1SpecialSemanticsSlice ++
  drawingST2SemanticsSlice ++
  drawingST3to6SemanticsSlice

set_option maxRecDepth 4096 in
@[simp] theorem allDrawingSemanticsSlices_exact :
    allDrawingSemanticsSlices = sourceProvisions .graphicalRepresentation2006 := by
  rfl

def p94SemanticsSlice : List IUPACNormativeProvision :=
  [ .p94ConformationDefinition
  , .p94TorsionAngle
  , .p94TorsionLonePairs
  , .p94EclipsedStaggeredGauche
  , .p94TrigonalConformations
  , .p94SCisSTrans
  , .p94Envelope
  , .p94ChairBoatTwist
  , .p94HalfChair
  , .p94Crown
  , .p94Tub
  , .p94InOut
  ]

@[simp] theorem blueBookP9ProvisionCount :
    (sourceProvisions .blueBook2013P9).length = 130 := by
  rfl

set_option maxRecDepth 16384 in
/-- Every currently enumerated P-90--P-94 source key has a non-vacuous independent target.  This
does not promote any provision to complete: applicability, figures, exceptions, recognition, and
production refinement remain tracked by the stronger maturity state. -/
theorem every_blueBookP9_provision_has_partial_independent_semantics :
    ∀ provision ∈ sourceProvisions .blueBook2013P9,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  apply mem_partiallyFormalizedSemanticsProvisions_of_mem_primitive_or_direct
  have included : ∀ row ∈ sourceProvisions .blueBook2013P9,
      row ∈ primitiveProvedProvisions ∨
        row ∈ directPartiallyFormalizedSemanticsProvisions := by decide
  exact included provision member

/-- Every enumerated Red Book IR-9.3 clause now has an independent semantic target.  This remains
`partiallyFormalized`: coordinate thresholds, all figure cases, production perception, and the
remaining geometry-specific descriptor constructors are not yet refinement-proved. -/
theorem every_ir9_provision_has_partial_independent_semantics :
    ∀ provision ∈ sourceProvisions .redBook2005IR9,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  rw [← ir9SemanticsSlice_exact] at member
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, member, or_true, true_or]

/-- All 19 P-101 stereochemical provisions now have independent retained-parent semantics.  The
Table 10.1/Appendix 3 inventory and production naming refinement remain open, so this is partial. -/
theorem every_p101_provision_has_partial_independent_semantics :
    ∀ provision ∈ p101SemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  have p10Member : provision ∈ p10SemanticsSlice :=
    List.mem_append_left _ (List.mem_append_left _ member)
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, p10Member, or_true, true_or]

theorem every_p102_provision_has_partial_independent_semantics :
    ∀ provision ∈ p102SemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  have p10Member : provision ∈ p10SemanticsSlice :=
    List.mem_append_left _ (List.mem_append_right _ member)
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, p10Member, or_true, true_or]

theorem every_p103to107_provision_has_partial_independent_semantics :
    ∀ provision ∈ p103to107SemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  have p10Member : provision ∈ p10SemanticsSlice :=
    List.mem_append_right _ member
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, p10Member, or_true, true_or]




theorem every_p10_provision_has_partial_independent_semantics :
    ∀ provision ∈ sourceProvisions .blueBook2013P10,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  rw [← p10SemanticsSlice_exact] at member
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, member, or_true, true_or]




theorem every_retinoid1981_provision_has_partial_independent_semantics :
    ∀ provision ∈ sourceProvisions .retinoidRecommendations1981,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  rw [← retinoid1981SemanticsSlice_exact] at member
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, member, or_true, true_or]



theorem every_carotenoid1974_provision_has_partial_independent_semantics :
    ∀ provision ∈ sourceProvisions .carotenoidRules1974,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  rw [← carotenoid1974SemanticsSlice_exact] at member
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, member, or_true, true_or]

/-- All 62 configuration-bearing obligations found across the 1989 steroid rules, corrected
tables, and 1992 locant addendum have independent targets.  Full retained-structure transcription
and production refinement remain open. -/
theorem every_steroid1989_provision_has_partial_independent_semantics :
    ∀ provision ∈ sourceProvisions .steroidRecommendations1989,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  rw [← steroid1989SemanticsSlice_exact] at member
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, member, or_true, true_or]




theorem every_cyclitol1973_provision_has_partial_independent_semantics :
    ∀ provision ∈ sourceProvisions .cyclitolRecommendations1973,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  rw [← cyclitol1973SemanticsSlice_exact] at member
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, member, or_true, true_or]

/-- All 21 constitution/configuration defaults imported from the corrected 1970 nucleic-acid
symbol recommendation have independent targets.  Retained structure diagrams and production
symbol-to-molecule refinement remain open. -/
theorem every_nucleicAcid1970_provision_has_partial_independent_semantics :
    ∀ provision ∈ sourceProvisions .nucleicAcidRecommendations1970,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  rw [← nucleicAcid1970SemanticsSlice_exact] at member
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, member, or_true, true_or]




theorem every_lipid1976_provision_has_partial_independent_semantics :
    ∀ provision ∈ sourceProvisions .lipidRecommendations1976,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  rw [← lipid1976SemanticsSlice_exact] at member
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, member, or_true, true_or]

/-- All 43 configuration-bearing glycolipid obligations—including every Table-2 root row and
every Table-3 Svennerholm row—have independent source-level targets.  Structure-code parsing,
carbohydrate graph refinement, and production refinement remain open. -/
theorem every_glycolipid1997_provision_has_partial_independent_semantics :
    ∀ provision ∈ sourceProvisions .glycolipidRecommendations1997,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  rw [← glycolipid1997SemanticsSlice_exact] at member
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, member, or_true, true_or]

/-- All 45 audited configuration-bearing amino-acid and peptide obligations have independent
targets.  Corrected figure transcription, the full retained-name inventory, and production
name/symbol refinement remain open. -/
theorem every_aminoAcidPeptide1983_provision_has_partial_independent_semantics :
    ∀ provision ∈ sourceProvisions .aminoAcidPeptideRecommendations1983,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  rw [← aminoAcidPeptide1983SemanticsSlice_exact] at member
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, member, or_true, true_or]

/-- All 1274 textual/table obligations from the preamble, 2-Carb-1 through 2-Carb-39, appendix,
errata, and terminology glossary—including the
complete parent-choice hierarchy, all twelve conformation rows, both complete named-parent
charts, all 27 worked examples in 2-Carb-8--12, the deoxy/amino retained-name inventories, and
all 50 printed examples in 2-Carb-13--16, every unsaturation rule/example, and all six Chart-V
branch-parent rows, plus the alditol/sugar-acid symmetry and tartaric R/S rules—have independent
source-level targets.  O/N-substitution, anomeric-anhydride ring preference, and every new
acetal/hemiacetal-center R/S rule are also included, together with the complete residue/radical/
ion suffix routing and the special free-valence meaning of alpha/beta.  The remaining carbohydrate
sections cover glycosides, ring-atom replacement, fused rings, spiro R/S, disaccharides,
oligosaccharides, all 45 residue-symbol rows, and polysaccharides.  All 122 retained-name rows,
all 22 published corrections, and all 25 glossary cells are included.  Six exceptional chemical
images now also have well-formed graph templates.  The remaining structure diagrams,
external-reference closure, and production refinement remain open. -/
theorem every_carbohydrate1996_textual_provision_has_partial_independent_semantics :
    ∀ provision ∈ carbohydrate1996SemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, member, or_true, true_or]

/-- The five generic glossary structures and corrected lysine--GlcNAc linkage have reviewed,
well-formed symbolic graph templates and therefore enter only partial semantic maturity. -/
theorem every_transcribed_carbohydrate1996_image_is_partially_formalized :
    ∀ provision ∈ carbohydrate1996TranscribedImageSemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized := by
  intro provision member
  apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem
  simp only [partiallyFormalizedSemanticsProvisions, List.mem_append, member, or_true]

/-- Of the remaining 424 image artifacts, 419 chemical drawings still require reviewed molecular
graphs and five are audited nonchemical glyphs. -/
theorem every_untranscribed_carbohydrate1996_image_is_source_only :
    ∀ provision ∈ carbohydrate1996UntranscribedImageSourceSlice,
      currentSemanticsMaturity provision = .absent := by
  intro provision member
  obtain ⟨imageProvision, imageNotTranscribed, rfl⟩ := List.mem_map.mp member
  apply currentSemanticsMaturity_eq_absent_of_not_mem
  intro partiallyFormalized
  rw [partiallyFormalizedSemanticsProvisions_eq_nonImage_append_transcribed] at partiallyFormalized
  rcases List.mem_append.mp partiallyFormalized with nonImage | transcribed
  · have notImage :=
      nonImagePartiallyFormalizedSemanticsProvisions_has_no_image_artifacts _ nonImage
    simp [isCarbohydrateImageArtifactProvision] at notImage
  · obtain ⟨transcribedProvision, imageTranscribed, equal⟩ := List.mem_map.mp transcribed
    cases equal
    have transcribedFlag := (List.mem_filter.mp imageTranscribed).2
    have notTranscribedFlag := (List.mem_filter.mp imageNotTranscribed).2
    simp [transcribedFlag] at notTranscribedFlag

/-- The stronger atom-level source-to-chemistry gate is currently false.  Symbolic topology and
external identity fixtures do not inhabit the reviewed atom-level catalog. -/
theorem carbohydrate1996_atom_level_image_coverage_is_incomplete :
    ¬Carbohydrate1996ImageTranscription.ExactArtifactCoverage
      Carbohydrate1996ImageTranscription.currentAtomLevelTranscriptions :=
  Carbohydrate1996ImageTranscription.current_atom_level_image_coverage_is_incomplete

@[simp] theorem semanticsSliceCounts :
    p90SemanticsSlice.length = 1 ∧
    p91SemanticsSlice.length = 7 ∧
    p92FoundationalSemanticsSlice.length = 21 ∧
    p92DigraphAndRule1aSemanticsSlice.length = 11 ∧
    p93GeneralSemanticsSlice.length = 5 ∧
    p93NoncarbonTetrahedraSemanticsSlice.length = 7 ∧
    p93PolyhedralSemanticsSlice.length = 11 ∧
    p93AcyclicSemanticsSlice.length = 11 ∧
    p93CyclicSemanticsSlice.length = 33 ∧
    drawingST0SemanticsSlice.length = 8 ∧
    drawingST1TetrahedralTableSemanticsSlice.length = 32 ∧
    drawingST1SpecialSemanticsSlice.length = 12 ∧
    drawingST2SemanticsSlice.length = 13 ∧
    drawingST3to6SemanticsSlice.length = 17 ∧
    p94SemanticsSlice.length = 12 := by
  simp [p90SemanticsSlice, p91SemanticsSlice, p92FoundationalSemanticsSlice,
    p92DigraphAndRule1aSemanticsSlice, p93GeneralSemanticsSlice,
    p93NoncarbonTetrahedraSemanticsSlice, p93PolyhedralSemanticsSlice,
    p93AcyclicSemanticsSlice, p93CyclicSemanticsSlice, drawingST0SemanticsSlice,
    drawingST1TetrahedralTableSemanticsSlice, drawingST1SpecialSemanticsSlice,
    drawingST2SemanticsSlice, drawingST3to6SemanticsSlice, p94SemanticsSlice]

set_option maxRecDepth 16384 in
theorem current_semantics_slices_are_honestly_partial :
    (∀ provision ∈ p90SemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ p91SemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ p92FoundationalSemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ p92DigraphAndRule1aSemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ p93GeneralSemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ p93NoncarbonTetrahedraSemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ p93PolyhedralSemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ p93AcyclicSemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ p93CyclicSemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ drawingST0SemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ drawingST1TetrahedralTableSemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ drawingST1SpecialSemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ drawingST2SemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ drawingST3to6SemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) ∧
    (∀ provision ∈ p94SemanticsSlice,
      currentSemanticsMaturity provision = .partiallyFormalized) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro provision member
    apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem_direct
    have included : p90SemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member
  · intro provision member
    apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem_direct
    have included : p91SemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member
  · intro provision member
    apply every_p92_provision_has_partial_independent_semantics provision
    simp only [p92SourceProvisions, List.mem_append, member, true_or]
  · intro provision member
    apply every_p92_provision_has_partial_independent_semantics provision
    simp only [p92SourceProvisions, List.mem_append, member, or_true, true_or]
  · intro provision member
    apply every_p93_provision_has_partial_independent_semantics provision
    simp only [p93SourceProvisions, List.mem_append, member, true_or]
  · intro provision member
    apply every_p93_provision_has_partial_independent_semantics provision
    simp only [p93SourceProvisions, List.mem_append, member, or_true, true_or]
  · intro provision member
    apply every_p93_provision_has_partial_independent_semantics provision
    simp only [p93SourceProvisions, List.mem_append, member, or_true, true_or]
  · intro provision member
    apply every_p93_provision_has_partial_independent_semantics provision
    simp only [p93SourceProvisions, List.mem_append, member, or_true, true_or]
  · intro provision member
    apply every_p93_provision_has_partial_independent_semantics provision
    simp only [p93SourceProvisions, List.mem_append, member, or_true]
  · intro provision member
    apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem_direct
    have included : drawingST0SemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member
  · intro provision member
    apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem_direct
    have included : drawingST1TetrahedralTableSemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member
  · intro provision member
    apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem_direct
    have included : drawingST1SpecialSemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member
  · intro provision member
    apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem_direct
    have included : drawingST2SemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member
  · intro provision member
    apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem_direct
    have included : drawingST3to6SemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member
  · intro provision member
    apply currentSemanticsMaturity_eq_partiallyFormalized_of_mem_direct
    have included : p94SemanticsSlice.Sublist
        directPartiallyFormalizedSemanticsProvisions := by decide
    exact included.subset member

def CurrentManifestSemanticsComplete : Prop :=
  ∀ provision, currentSemanticsMaturity provision = .provisionComplete

theorem current_manifest_semantics_not_complete : ¬CurrentManifestSemanticsComplete := by
  intro complete
  have := complete IUPACNormativeProvision.p93RelativeConfiguration
  have member :
      IUPACNormativeProvision.p93RelativeConfiguration ∈
        partiallyFormalizedSemanticsProvisions := by
    apply mem_partiallyFormalizedSemanticsProvisions_of_mem_primitive_or_direct
    right
    set_option maxRecDepth 4096 in
      decide
  simp [currentSemanticsMaturity, provisionCompleteSemanticsProvisions, member] at this

/-- The eight P-92 sequence-rule slots as whole normative provisions. -/
def sequenceRuleProvisions : List IUPACNormativeProvision :=
  [ .p92Rule1aAtomicNumber
  , .p92Rule1bDuplicateProximity
  , .p92Rule2IsotopeMass
  , .p92Rule3Geometry
  , .p92Rule4aUnitKind
  , .p92Rule4bLikeUnlike
  , .p92Rule4cPseudoasymmetry
  , .p92Rule5Enantiomorph
  ]

def ofOfficialSequenceRule : OfficialCIPSequenceRule → IUPACNormativeProvision
  | .rule1aAtomicNumber => .p92Rule1aAtomicNumber
  | .rule1bDuplicateNodeProximity => .p92Rule1bDuplicateProximity
  | .rule2AtomicMass => .p92Rule2IsotopeMass
  | .rule3DoubleBondGeometry => .p92Rule3Geometry
  | .rule4aStereogenicUnitKind => .p92Rule4aUnitKind
  | .rule4bLikeUnlikeDescriptorPairs => .p92Rule4bLikeUnlike
  | .rule4cPseudoasymmetricDescriptor => .p92Rule4cPseudoasymmetry
  | .rule5EnantiomorphicDescriptor => .p92Rule5Enantiomorph

@[simp] theorem official_sequence_rule_manifest_exact :
    OfficialCIPSequenceRule.all.map ofOfficialSequenceRule = sequenceRuleProvisions :=
  rfl

/-- Final coverage gate.  It is intentionally false today and becomes useful proof data only when
paired with the future theorem-bearing completion certificate. -/
def CurrentManifestEndToEndComplete : Prop :=
  ∀ provision, currentMaturity provision = .endToEndProved

theorem current_manifest_not_end_to_end_complete : ¬CurrentManifestEndToEndComplete := by
  intro complete
  have := complete IUPACNormativeProvision.p93Octahedron
  have member : IUPACNormativeProvision.p93Octahedron ∈ primitiveProvedProvisions := by
    simp [primitiveProvedProvisions, primitive35Provisions]
  simp [currentMaturity, endToEndProvedProvisions, member] at this

/-- Kernel evidence behind every provision currently marked `primitiveProved`.  The manifest's
maturity tags remain a roadmap, while these two records contain the actual local theorems. -/
structure CurrentPrimitiveCoverageCertificate : Prop where
  p92 : AuthoritativePrimitiveP92Conformance
  p93Polyhedral : PrimitiveP93PolyhedralConformance

theorem currentPrimitiveCoverage : CurrentPrimitiveCoverageCertificate where
  p92 := authoritativePrimitiveRules_conform_blueBookP92
  p93Polyhedral := primitiveP93Polyhedral_conforms

end IUPACNormativeProvision

end TetraStereo.OneCenter
