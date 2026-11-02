import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataCore
import TetraStereo.KernelOnly

set_option autoImplicit false










namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarotenoidSourceMeaning

open GlobalNonDescriptorIndexedSourceData

def sampleAbsoluteConfiguration : List Carotenoid1974.LocatedRS :=
  [⟨"3", .R⟩]

def orderedCarotenoidName : List Carotenoid1974.NameComponent :=
  Carotenoid1974.componentOrder sampleAbsoluteConfiguration ["9"] "beta-carotene"

def cyclicNumberingAssignments :
    List (Carotenoid1974.CyclicProjection × Carotenoid1974.MethylPosition × Nat) :=
  [ (.formulaA, .below, Carotenoid1974.cyclicMethylLocant .formulaA .below)
  , (.formulaA, .above, Carotenoid1974.cyclicMethylLocant .formulaA .above)
  , (.formulaB1, .below, Carotenoid1974.cyclicMethylLocant .formulaB1 .below)
  , (.formulaB1, .above, Carotenoid1974.cyclicMethylLocant .formulaB1 .above)
  , (.formulaB2, .below, Carotenoid1974.cyclicMethylLocant .formulaB2 .below)
  , (.formulaB2, .above, Carotenoid1974.cyclicMethylLocant .formulaB2 .above) ]

def acyclicNumberingAssignments : List (Carotenoid1974.AcyclicMethylRelation × Nat) :=
  [ (.transToMainChain, Carotenoid1974.acyclicMethylLocant .transToMainChain)
  , (.cisToMainChain, Carotenoid1974.acyclicMethylLocant .cisToMainChain) ]

/-- Typed payloads preserve the actual semantic values used by each Rule-12 row. -/
inductive SourceAssertion where
  | chiralCentersUseRS (descriptors : List Carotenoid1974.RS)
  | rsLocantsPrecedeCarotenoidName (components : List Carotenoid1974.NameComponent)
  | knownAlleneConfigurationUsesAbsoluteDescriptor
      (known unknown : Option Carotenoid1974.RS)
  | caroteneStemDefaultsToAllTrans
      (scope : Carotenoid1974.CaroteneDoubleBondScope)
      (geometry : Carotenoid1974.Geometry)
  | cisCitationsFollowAbsoluteConfiguration (components : List Carotenoid1974.NameComponent)
  | trisubstitutedCisUsesMainChainSubstituents
      (reading : Carotenoid1974.TrisubstitutedReading)
      (cisTrans : Carotenoid1974.Geometry) (ez : Carotenoid1974.EZ)
  | neoPrefixDoesNotAssertKnownGeometry
      (designation : Carotenoid1974.NeoDesignation)
      (assertedGeometry : Option Carotenoid1974.Geometry)
  | ezAllowedWhenCisTransAmbiguous
      (reading : Carotenoid1974.TrisubstitutedReading)
      (cisTrans : Carotenoid1974.Geometry) (ez : Carotenoid1974.EZ)
  | cyclicEndGroupGemDimethylNumbering
      (assignments :
        List (Carotenoid1974.CyclicProjection × Carotenoid1974.MethylPosition × Nat))
  | acyclicEndGroupGemDimethylNumbering
      (assignments : List (Carotenoid1974.AcyclicMethylRelation × Nat))
  deriving DecidableEq, Repr

def sourceAssertion : Carotenoid1974.Provision → SourceAssertion
  | .chiralCentersUseRS => .chiralCentersUseRS [.R, .S]
  | .rsLocantsPrecedeCarotenoidName =>
      .rsLocantsPrecedeCarotenoidName orderedCarotenoidName
  | .knownAlleneConfigurationUsesAbsoluteDescriptor =>
      .knownAlleneConfigurationUsesAbsoluteDescriptor
        (Carotenoid1974.knownAbsoluteDescriptor true .R)
        (Carotenoid1974.knownAbsoluteDescriptor false .R)
  | .caroteneStemDefaultsToAllTrans =>
      .caroteneStemDefaultsToAllTrans .allDoubleBonds .trans
  | .cisCitationsFollowAbsoluteConfiguration =>
      .cisCitationsFollowAbsoluteConfiguration orderedCarotenoidName
  | .trisubstitutedCisUsesMainChainSubstituents =>
      .trisubstitutedCisUsesMainChainSubstituents
        Carotenoid1974.carotenoidAmbiguityWitness
        Carotenoid1974.carotenoidAmbiguityWitness.cisTrans
        Carotenoid1974.carotenoidAmbiguityWitness.ez
  | .neoPrefixDoesNotAssertKnownGeometry =>
      let designation : Carotenoid1974.NeoDesignation := ⟨"neo"⟩
      .neoPrefixDoesNotAssertKnownGeometry designation designation.assertedGeometry
  | .ezAllowedWhenCisTransAmbiguous =>
      .ezAllowedWhenCisTransAmbiguous
        Carotenoid1974.carotenoidAmbiguityWitness
        Carotenoid1974.carotenoidAmbiguityWitness.cisTrans
        Carotenoid1974.carotenoidAmbiguityWitness.ez
  | .cyclicEndGroupGemDimethylNumbering =>
      .cyclicEndGroupGemDimethylNumbering cyclicNumberingAssignments
  | .acyclicEndGroupGemDimethylNumbering =>
      .acyclicEndGroupGemDimethylNumbering acyclicNumberingAssignments

structure SourceMeaning where
  sourceSection : String
  sourceKey : String
  semanticDomain : Carotenoid1974.SemanticDomain
  assertion : SourceAssertion
  deriving DecidableEq, Repr

/-- Total source-family compiler for the exact ten-row Carotenoid 1974 slice. -/
def sourceMeaning (row : Carotenoid1974.Provision) : SourceMeaning :=
  ⟨row.sourceSection, row.sourceKey, Carotenoid1974.provisionSemanticDomain row,
    sourceAssertion row⟩

@[simp] theorem sourceMeaning_section_exact (row : Carotenoid1974.Provision) :
    (sourceMeaning row).sourceSection = row.sourceSection := by
  rfl

@[simp] theorem sourceMeaning_key_exact (row : Carotenoid1974.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by
  rfl

@[simp] theorem sourceMeaning_domain_exact (row : Carotenoid1974.Provision) :
    (sourceMeaning row).semanticDomain = Carotenoid1974.provisionSemanticDomain row := by
  rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  cases left <;> cases right <;> simp [sourceMeaning, sourceAssertion] at equal ⊢

def rows : List Carotenoid1974.Provision :=
  Carotenoid1974.Provision.all

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carotenoid1974

def batch : GlobalNonDescriptorSourceMeaningBatch provisions :=
  totalMeaningBatch rows IUPACNormativeProvision.carotenoid1974 sourceMeaning
    (by intro _row; rfl)

@[simp] theorem provisions_exact :
    provisions = sourceProvisions .carotenoidRules1974 := by
  exact carotenoid1974SemanticsSlice_exact

@[simp] theorem provision_count : provisions.length = 10 := by
  simp [provisions, rows]

@[simp] theorem entry_count : batch.entries.length = 10 := by
  rw [batch.entries_length, provision_count]

theorem provisions_nodup : provisions.Nodup := by
  exact Carotenoid1974.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

@[simp] theorem entry_provisions_exact :
    batch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision = provisions :=
  batch.provisions_exact

theorem every_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ batch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment


theorem source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .carotenoidRules1974 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    Carotenoid1974.currentSourceReviewProvisionEnumerationConfirmed,
    Carotenoid1974.currentSourceReviewProseTableCoverageConfirmed,
    Carotenoid1974.currentSourceReviewFigureGraphTranscriptionsReviewed]

end GlobalNonDescriptorCarotenoidSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarotenoidSourceMeaning.provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarotenoidSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarotenoidSourceMeaning.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarotenoidSourceMeaning.every_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarotenoidSourceMeaning.source_audit_still_open
