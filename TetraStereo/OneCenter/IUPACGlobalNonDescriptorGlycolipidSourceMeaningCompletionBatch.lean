import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataCore
import TetraStereo.KernelOnly

set_option autoImplicit false


















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorGlycolipidSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive DelegatedAuthority where
  | carbohydrateRecommendations1996
  deriving DecidableEq, Repr

inductive CeramideNamingForm where
  | explicitMonosaccharideName
  deriving DecidableEq, Repr

inductive BranchOrderRule where
  | highestAcceptingLocantFirst
  deriving DecidableEq, Repr

def monosaccharides : List Glycolipid1997.Monosaccharide :=
  [ .glucose, .galactose, .mannose, .xylose, .glucosamine, .galactosamine
  , .neuraminicAcid, .fucose, .rhamnose, .myoInositol ]

def defaultSeriesInventory :
    List (Glycolipid1997.Monosaccharide × Glycolipid1997.DLSeries) :=
  monosaccharides.map fun sugar => (sugar, Glycolipid1997.defaultSeries sugar)

def invariantAnomericInventory : List (Glycolipid1997.Monosaccharide × Nat) :=
  monosaccharides.map fun sugar => (sugar, Glycolipid1997.invariantAnomericCarbon sugar)

def citationInventory : List Glycolipid1997.GlycosidicCitation :=
  [ Glycolipid1997.shortCitation .glucose .beta 4
  , Glycolipid1997.shortCitation .neuraminicAcid .alpha 3 ]

def rootInventory :
    List (Glycolipid1997.RootGlycan × String × String) :=
  Glycolipid1997.RootGlycan.all.map fun root => (root, root.structureCode, root.symbol)

def svennerholmInventory :
    List (Glycolipid1997.SvennerholmEntry × String × String) :=
  Glycolipid1997.SvennerholmEntry.all.map fun entry =>
    (entry, entry.structureCode, entry.abbreviation)

/-- Typed payloads preserve concrete source-model values for all forty-three provisions. -/
inductive SourceAssertion where
  | supersedesLipid1976GlycolipidSection (superseded replacement : String)
  | monosaccharideSemanticsDelegatedToCarbohydrateRules (authority : DelegatedAuthority)
  | dlSymbolsGenerallyOmitted
      (printed : Option Glycolipid1997.DLSeries)
      (defaults : List (Glycolipid1997.Monosaccharide × Glycolipid1997.DLSeries))
  | defaultDExceptFucoseAndRhamnose
      (defaults : List (Glycolipid1997.Monosaccharide × Glycolipid1997.DLSeries))
  | inositolSymbolUsesOneDNumbering
      (sugar : Glycolipid1997.Monosaccharide) (series : Glycolipid1997.DLSeries)
  | linkagePositionsAndAnomersRequired (citations : List Glycolipid1997.GlycosidicCitation)
  | shortFormOmitsOnlyInvariantAnomericLocant
      (citations : List Glycolipid1997.GlycosidicCitation)
  | invariantAnomericLocants (inventory : List (Glycolipid1997.Monosaccharide × Nat))
  | ringSizeAndConformationRequireFirmEvidence
      (evidence : Glycolipid1997.RingEvidence) (mayCite : Bool)
  | glycerolAlwaysUsesSn (usesSn : Bool)
  | glycoglycerolipidExampleConfiguration
      (reference : Glycolipid1997.GlycoglycerolipidReference)
  | gpiCombinesPhospholipidAndGlycanRules
      (reference : Glycolipid1997.GPIReference) (core : List Glycolipid1997.GPICoreStep)
  | gpiCoreConfiguration (core : List Glycolipid1997.GPICoreStep)
  | gpiInositolGenerallyDMyo (reference : Glycolipid1997.GPIReference)
  | carbohydrateAttachesToSphingoidO1 (attachmentAtom : Nat)
  | sphinganineConfiguration (configuration : Glycolipid1997.SphingoidConfiguration)
  | unsaturatedSphingoidLocantsAndGeometryRequired
      (configuration : Glycolipid1997.SphingoidConfiguration)
      (geometryDescriptors : List Glycolipid1997.EZ)
  | sphingFourEnineConfiguration (configuration : Glycolipid1997.SphingoidConfiguration)
  | phytosphingosineConfiguration (configuration : Glycolipid1997.SphingoidConfiguration)
  | explicitMonoglycosylceramidePreferred (form : CeramideNamingForm)
  | lactosylceramideConfiguration (structureCode : String)
  | rootStructure (root : Glycolipid1997.RootGlycan) (structureCode symbol : String)
  | additionalResidueAnomerRequired (anomers : List Glycolipid1997.Anomer)
  | branchOrderHighestAcceptingLocantFirst (rule : BranchOrderRule)
  | correctedBranchFigureAlignment
      (erratum : Glycolipid1997.IncorporatedErratum) (changesStructureReading : Bool)
  | svennerholmStructure
      (entry : Glycolipid1997.SvennerholmEntry) (structureCode abbreviation : String)
  deriving DecidableEq, Repr

def sourceAssertion : Glycolipid1997.Provision → SourceAssertion
  | .supersedesLipid1976GlycolipidSection =>
      .supersedesLipid1976GlycolipidSection "Lipid-1976/Lip-3" "Glycolipid-1997"
  | .monosaccharideSemanticsDelegatedToCarbohydrateRules =>
      .monosaccharideSemanticsDelegatedToCarbohydrateRules .carbohydrateRecommendations1996
  | .dlSymbolsGenerallyOmitted =>
      .dlSymbolsGenerallyOmitted (Glycolipid1997.printedSeries none) defaultSeriesInventory
  | .defaultDExceptFucoseAndRhamnose =>
      .defaultDExceptFucoseAndRhamnose defaultSeriesInventory
  | .inositolSymbolUsesOneDNumbering =>
      .inositolSymbolUsesOneDNumbering .myoInositol
        (Glycolipid1997.defaultSeries .myoInositol)
  | .linkagePositionsAndAnomersRequired =>
      .linkagePositionsAndAnomersRequired citationInventory
  | .shortFormOmitsOnlyInvariantAnomericLocant =>
      .shortFormOmitsOnlyInvariantAnomericLocant citationInventory
  | .invariantAnomericLocants => .invariantAnomericLocants invariantAnomericInventory
  | .ringSizeAndConformationRequireFirmEvidence =>
      let evidence : Glycolipid1997.RingEvidence := ⟨true, false⟩
      .ringSizeAndConformationRequireFirmEvidence evidence
        (Glycolipid1997.mayCiteRingSizeAndConformation evidence)
  | .glycerolAlwaysUsesSn => .glycerolAlwaysUsesSn true
  | .glycoglycerolipidExampleConfiguration =>
      .glycoglycerolipidExampleConfiguration Glycolipid1997.sourceGlycoglycerolipidExample
  | .gpiCombinesPhospholipidAndGlycanRules =>
      .gpiCombinesPhospholipidAndGlycanRules
        Glycolipid1997.generalGPIReference Glycolipid1997.gpiCore
  | .gpiCoreConfiguration => .gpiCoreConfiguration Glycolipid1997.gpiCore
  | .gpiInositolGenerallyDMyo =>
      .gpiInositolGenerallyDMyo Glycolipid1997.generalGPIReference
  | .carbohydrateAttachesToSphingoidO1 =>
      .carbohydrateAttachesToSphingoidO1 Glycolipid1997.carbohydrateAttachmentAtomOnSphingoid
  | .sphinganineConfiguration => .sphinganineConfiguration Glycolipid1997.sphinganine
  | .unsaturatedSphingoidLocantsAndGeometryRequired =>
      .unsaturatedSphingoidLocantsAndGeometryRequired Glycolipid1997.sphingFourEnine [.E, .Z]
  | .sphingFourEnineConfiguration =>
      .sphingFourEnineConfiguration Glycolipid1997.sphingFourEnine
  | .phytosphingosineConfiguration =>
      .phytosphingosineConfiguration Glycolipid1997.phytosphingosine
  | .explicitMonoglycosylceramidePreferred =>
      .explicitMonoglycosylceramidePreferred .explicitMonosaccharideName
  | .lactosylceramideConfiguration =>
      .lactosylceramideConfiguration "Galβ4GlcCer"
  | .rootStructure root => .rootStructure root root.structureCode root.symbol
  | .additionalResidueAnomerRequired => .additionalResidueAnomerRequired [.alpha, .beta]
  | .branchOrderHighestAcceptingLocantFirst =>
      .branchOrderHighestAcceptingLocantFirst .highestAcceptingLocantFirst
  | .correctedBranchFigureAlignment =>
      .correctedBranchFigureAlignment .gl65BranchAlignment
        Glycolipid1997.IncorporatedErratum.gl65BranchAlignment.changesStructureReading
  | .svennerholmStructure entry =>
      .svennerholmStructure entry entry.structureCode entry.abbreviation

def SourceAssertion.provision : SourceAssertion → Glycolipid1997.Provision
  | .supersedesLipid1976GlycolipidSection _ _ => .supersedesLipid1976GlycolipidSection
  | .monosaccharideSemanticsDelegatedToCarbohydrateRules _ =>
      .monosaccharideSemanticsDelegatedToCarbohydrateRules
  | .dlSymbolsGenerallyOmitted _ _ => .dlSymbolsGenerallyOmitted
  | .defaultDExceptFucoseAndRhamnose _ => .defaultDExceptFucoseAndRhamnose
  | .inositolSymbolUsesOneDNumbering _ _ => .inositolSymbolUsesOneDNumbering
  | .linkagePositionsAndAnomersRequired _ => .linkagePositionsAndAnomersRequired
  | .shortFormOmitsOnlyInvariantAnomericLocant _ => .shortFormOmitsOnlyInvariantAnomericLocant
  | .invariantAnomericLocants _ => .invariantAnomericLocants
  | .ringSizeAndConformationRequireFirmEvidence _ _ => .ringSizeAndConformationRequireFirmEvidence
  | .glycerolAlwaysUsesSn _ => .glycerolAlwaysUsesSn
  | .glycoglycerolipidExampleConfiguration _ => .glycoglycerolipidExampleConfiguration
  | .gpiCombinesPhospholipidAndGlycanRules _ _ => .gpiCombinesPhospholipidAndGlycanRules
  | .gpiCoreConfiguration _ => .gpiCoreConfiguration
  | .gpiInositolGenerallyDMyo _ => .gpiInositolGenerallyDMyo
  | .carbohydrateAttachesToSphingoidO1 _ => .carbohydrateAttachesToSphingoidO1
  | .sphinganineConfiguration _ => .sphinganineConfiguration
  | .unsaturatedSphingoidLocantsAndGeometryRequired _ _ =>
      .unsaturatedSphingoidLocantsAndGeometryRequired
  | .sphingFourEnineConfiguration _ => .sphingFourEnineConfiguration
  | .phytosphingosineConfiguration _ => .phytosphingosineConfiguration
  | .explicitMonoglycosylceramidePreferred _ => .explicitMonoglycosylceramidePreferred
  | .lactosylceramideConfiguration _ => .lactosylceramideConfiguration
  | .rootStructure root _ _ => .rootStructure root
  | .additionalResidueAnomerRequired _ => .additionalResidueAnomerRequired
  | .branchOrderHighestAcceptingLocantFirst _ => .branchOrderHighestAcceptingLocantFirst
  | .correctedBranchFigureAlignment _ _ => .correctedBranchFigureAlignment
  | .svennerholmStructure entry _ _ => .svennerholmStructure entry

@[simp] theorem sourceAssertion_provision_exact (row : Glycolipid1997.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

def sourceVariantDefects : Glycolipid1997.Provision →
    List Glycolipid1997.UnlistedWebTranscriptionDefect
  | .svennerholmStructure .GQ1b => Glycolipid1997.UnlistedWebTranscriptionDefect.all
  | _ => []

structure SourceMeaning where
  sourceSection : String
  sourceKey : String
  semanticDomain : Glycolipid1997.SemanticDomain
  incorporatedErrata : List Glycolipid1997.IncorporatedErratum
  unlistedWebTranscriptionDefects : List Glycolipid1997.UnlistedWebTranscriptionDefect
  assertion : SourceAssertion
  deriving DecidableEq, Repr

def sourceMeaning (row : Glycolipid1997.Provision) : SourceMeaning :=
  ⟨row.sourceSection, row.sourceKey, Glycolipid1997.provisionSemanticDomain row,
    Glycolipid1997.IncorporatedErratum.all, sourceVariantDefects row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_section_exact (row : Glycolipid1997.Provision) :
    (sourceMeaning row).sourceSection = row.sourceSection := by
  rfl

@[simp] theorem sourceMeaning_key_exact (row : Glycolipid1997.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by
  rfl

@[simp] theorem sourceMeaning_domain_exact (row : Glycolipid1997.Provision) :
    (sourceMeaning row).semanticDomain = Glycolipid1997.provisionSemanticDomain row := by
  rfl

@[simp] theorem sourceMeaning_errata_exact (row : Glycolipid1997.Provision) :
    (sourceMeaning row).incorporatedErrata = Glycolipid1997.IncorporatedErratum.all := by
  rfl

@[simp] theorem sourceMeaning_source_variant_defects_exact (row : Glycolipid1997.Provision) :
    (sourceMeaning row).unlistedWebTranscriptionDefects = sourceVariantDefects row := by
  rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List Glycolipid1997.Provision :=
  Glycolipid1997.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.glycolipid1997

def completionRows : List Glycolipid1997.Provision :=
  Glycolipid1997.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.glycolipid1997

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows IUPACNormativeProvision.glycolipid1997 sourceMeaning
    (by intro _row; rfl)

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = sourceProvisions .glycolipidRecommendations1997 := by
  exact glycolipid1997SemanticsSlice_exact

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 43 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 24 := by
  simp [completionProvisions, completionRows, Glycolipid1997.Provision.base]

@[simp] theorem completion_entry_count : completionBatch.entries.length = 24 := by
  rw [completionBatch.entries_length, completion_provision_count]

private theorem completion_rows_then_indexed_exact :
    completionRows ++ GlobalNonDescriptorIndexedSourceData.glycolipidRows = fullFamilyRows := by
  simp [completionRows, fullFamilyRows, GlobalNonDescriptorIndexedSourceData.glycolipidRows,
    Glycolipid1997.Provision.all, List.append_assoc]

theorem completion_then_indexed_exact_source_order :
    completionProvisions ++ GlobalNonDescriptorIndexedSourceData.glycolipidProvisions =
      sourceProvisions .glycolipidRecommendations1997 := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions, GlobalNonDescriptorIndexedSourceData.glycolipidProvisions,
    fullFamilyProvisions, ← List.map_append]
  rw [completion_rows_then_indexed_exact]

theorem materialized_order_perm_source :
    (GlobalNonDescriptorIndexedSourceData.glycolipidProvisions ++ completionProvisions).Perm
      (sourceProvisions .glycolipidRecommendations1997) := by
  calc
    (GlobalNonDescriptorIndexedSourceData.glycolipidProvisions ++ completionProvisions).Perm
        (completionProvisions ++ GlobalNonDescriptorIndexedSourceData.glycolipidProvisions) :=
      List.perm_append_comm
    _ = sourceProvisions .glycolipidRecommendations1997 :=
      completion_then_indexed_exact_source_order

theorem completion_disjoint_indexed :
    completionProvisions.Disjoint GlobalNonDescriptorIndexedSourceData.glycolipidProvisions := by
  rw [List.disjoint_left]
  intro provision completionMember indexedMember
  rw [completionProvisions, completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  simp only [GlobalNonDescriptorIndexedSourceData.glycolipidProvisions,
    GlobalNonDescriptorIndexedSourceData.glycolipidRows, List.mem_map, List.mem_append] at indexedMember
  rcases indexedMember with ⟨indexedRow, indexedRowMember, indexedExact⟩
  injection indexedExact with rowExact
  subst indexedRow
  rcases indexedRowMember with ⟨root, _rootMember, rootExact⟩ | ⟨entry, _entryMember, entryExact⟩
  · subst row
    simp [Glycolipid1997.Provision.base] at rowMember
  · subst row
    simp [Glycolipid1997.Provision.base] at rowMember

theorem completion_provisions_nodup : completionProvisions.Nodup := by
  exact (by decide : Glycolipid1997.Provision.base.Nodup).map
    (by intro left right equal; cases equal; rfl)

@[simp] theorem completion_entry_provisions_exact :
    completionBatch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      completionProvisions :=
  completionBatch.provisions_exact

theorem every_completion_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ completionBatch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

theorem source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .glycolipidRecommendations1997 := by
  exact IUPACNormativeSource.provisionAuditIncomplete_of_figure_review_open _ rfl

end GlobalNonDescriptorGlycolipidSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorGlycolipidSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorGlycolipidSourceMeaning.completion_then_indexed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorGlycolipidSourceMeaning.materialized_order_perm_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorGlycolipidSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorGlycolipidSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorGlycolipidSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorGlycolipidSourceMeaning.source_audit_still_open
