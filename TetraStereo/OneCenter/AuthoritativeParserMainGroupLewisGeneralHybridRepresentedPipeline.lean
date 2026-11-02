import TetraStereo.OneCenter.AuthoritativeParserMainGroupLewisGeneralHybridEvidence
import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralHybridRepresentedPipeline

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace RawMolecule

open AuthoritativeChemicalInput

/-!
# Parser annotations through the complete represented stereochemical pipeline

This module composes the raw-indexed, independently validated electronic-state sidecar with the
inventory-aware five-family source analyzer.  Parser validation therefore guards the same public
result containing tetrahedral, ordinary-double-bond, odd/even open-cumulene, and fully cyclic P-31
outcomes rather than ending at a family-local helper.
-/

/-- Complete represented analysis after exact parser-index and generalized-Lewis validation. -/
noncomputable def analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes :=
  source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
    (molecule.parserAtomElectronicStateRecords source converted annotations)
    ready.2 carrierFuel ruleFuel

/-- Total parser entry point for the represented five-family result. -/
noncomputable def analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel ruleFuel : Nat) :
    Option (List source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes) := by
  classical
  exact if ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations then
    some (molecule.analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
      source converted annotations ready carrierFuel ruleFuel)
  else none

/-- Parser-level failure is exactly the already-expanded invalid-index/source/duplicate/ledger/
unresolved-endpoint refusal, now at the complete represented output boundary. -/
@[simp] theorem analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_eq_none_iff_refusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel ruleFuel : Nat) :
    molecule.analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
        source converted annotations carrierFuel ruleFuel = none ↔
      molecule.ParserMainGroupLewisGeneralHybridCertificationRefusal
        source converted annotations := by
  classical
  rw [← molecule.not_parserMainGroupLewisGeneralHybridCertificationReady_iff_refusal
    source converted annotations]
  simp [analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?]

/-- Exact successful result for any parser-readiness witness. -/
theorem analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_eq_some_of_ready
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat) :
    molecule.analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
        source converted annotations carrierFuel ruleFuel =
      some
        (molecule.analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
          source converted annotations ready carrierFuel ruleFuel) := by
  classical
  simp [analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?, ready]

/-- Every parser-produced represented result has the independent complete-rule/geometry judgment
associated with its family. -/
theorem analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_member_sound
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes)
    (present : result ∈
      molecule.analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
        source converted annotations ready carrierFuel ruleFuel) :
    source.DeclarativeAromaticCanonicalHybridElectronicInventoryRepresentedMember
      (molecule.parserAtomElectronicStateRecords source converted annotations)
      ready.2 carrierFuel ruleFuel result := by
  exact source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_member_sound
    (molecule.parserAtomElectronicStateRecords source converted annotations)
    ready.2 carrierFuel ruleFuel result present

/-- The parser-produced complete represented list is duplicate-free. -/
theorem analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_nodup
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat) :
    (molecule.analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
      source converted annotations ready carrierFuel ruleFuel).Nodup := by
  exact source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_nodup
    (molecule.parserAtomElectronicStateRecords source converted annotations)
    ready.2 carrierFuel ruleFuel

/-- Every successful total parser analysis returns a duplicate-free result. -/
theorem analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_some_nodup
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel ruleFuel : Nat)
    (results : List source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes)
    (computed : molecule.analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
      source converted annotations carrierFuel ruleFuel = some results) : results.Nodup := by
  classical
  unfold analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence? at computed
  split at computed
  next ready =>
    simp only [Option.some.injEq] at computed
    subst results
    exact molecule.analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_nodup
      source converted annotations ready carrierFuel ruleFuel
  next notReady => contradiction

/-- Parser-level readiness for the exact-once complete represented theorem.  The first field
validates transport and electronic evidence; the second gives the independent family readiness
obligations for the resulting semantic records. -/
structure ParserMainGroupLewisGeneralHybridRepresentedPipelineReadyAtBound
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel : Nat) : Prop where
  parserElectronic : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
    source converted annotations
  represented : source.AromaticCanonicalHybridElectronicInventoryRepresentedPipelineReadyAtBound
    (molecule.parserAtomElectronicStateRecords source converted annotations) carrierFuel

/-- At the uniform finite bound, the total parser entry point returns the exact five-family list,
and the existing complete-result structure proves emitted correctness, global `Nodup`, and literal
count one for every ready physical unit. -/
theorem analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence_complete_at_bound
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel : Nat)
    (ready : molecule.ParserMainGroupLewisGeneralHybridRepresentedPipelineReadyAtBound
      source converted annotations carrierFuel) :
    ∃ results,
      molecule.analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
          source converted annotations carrierFuel (2 * (carrierFuel + 1)) = some results ∧
        results =
          source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
            (molecule.parserAtomElectronicStateRecords source converted annotations)
            ready.represented.electronic carrierFuel (2 * (carrierFuel + 1)) ∧
        source.AromaticCanonicalHybridElectronicInventoryRepresentedPipelineCompleteAtBound
          (molecule.parserAtomElectronicStateRecords source converted annotations)
          carrierFuel ready.represented := by
  let results :=
    source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
      (molecule.parserAtomElectronicStateRecords source converted annotations)
      ready.represented.electronic carrierFuel (2 * (carrierFuel + 1))
  refine ⟨results, ?_, rfl,
    source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventory_complete_at_bound
      (molecule.parserAtomElectronicStateRecords source converted annotations)
      carrierFuel ready.represented⟩
  simpa [results] using
    molecule.analyzeRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_eq_some_of_ready
      source converted annotations ready.parserElectronic carrierFuel (2 * (carrierFuel + 1))

end RawMolecule
end TetraStereo.OneCenter
