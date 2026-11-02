import TetraStereo.OneCenter.AuthoritativeParserMainGroupLewisGeneralHybridRichRepresentedPipeline
import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralHybridRichCanonicalCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace RawMolecule

open AuthoritativeChemicalInput

/-!
# Parser-level unconditional rich canonical completeness

The raw parser boundary needs only its exact generalized-Lewis certification.  Once that succeeds,
the resulting rich five-family list inherits the source theorem which classifies every candidate by
canonical readiness; no global assumption that all connectivity candidates are stereogenic is
required.
-/

/-- Exact canonical-completeness package carried by a particular successful total parser result. -/
def ParserMainGroupLewisGeneralHybridRichCanonicalCompleteResult
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel ruleFuel : Nat)
    (results : List source.AromaticCanonicalHybridRichRepresentedResult) : Prop :=
  ∃ ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations,
    results =
        molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
          source converted annotations ready carrierFuel ruleFuel ∧
      source.AromaticCanonicalHybridRichRepresentedCanonicalCompleteness
        (molecule.parserAtomElectronicStateRecords source converted annotations)
        ready.2 carrierFuel ruleFuel

/-- Every electronically certified parser result has unconditional per-candidate canonical
completeness in the rich five-family source analyzer. -/
theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_canonical_complete
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalHybridRichRepresentedCanonicalCompleteness
      (molecule.parserAtomElectronicStateRecords source converted annotations)
      ready.2 carrierFuel ruleFuel := by
  exact source.analyzeAromaticCanonicalHybridRichRepresented_canonical_complete
    (molecule.parserAtomElectronicStateRecords source converted annotations)
    ready.2 carrierFuel ruleFuel

/-- Exact normal form for success of the total parser entry point. -/
theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_eq_some_iff_canonicalCompleteResult
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel ruleFuel : Nat)
    (results : List source.AromaticCanonicalHybridRichRepresentedResult) :
    molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
        source converted annotations carrierFuel ruleFuel = some results ↔
      molecule.ParserMainGroupLewisGeneralHybridRichCanonicalCompleteResult
        source converted annotations carrierFuel ruleFuel results := by
  classical
  constructor
  · intro computed
    unfold analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
      at computed
    split at computed
    next ready =>
      simp only [Option.some.injEq] at computed
      refine ⟨ready, computed.symm, ?_⟩
      exact
        molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_canonical_complete
          source converted annotations ready carrierFuel ruleFuel
    next notReady => contradiction
  · rintro ⟨ready, resultIdentity, _complete⟩
    rw [resultIdentity]
    exact
      molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_eq_some_of_ready
        source converted annotations ready carrierFuel ruleFuel

/-- Any successful total parser call returns an exact canonical-complete result. -/
theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_some_canonical_complete
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel ruleFuel : Nat)
    (results : List source.AromaticCanonicalHybridRichRepresentedResult)
    (computed :
      molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
        source converted annotations carrierFuel ruleFuel = some results) :
    molecule.ParserMainGroupLewisGeneralHybridRichCanonicalCompleteResult
      source converted annotations carrierFuel ruleFuel results :=
  (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_eq_some_iff_canonicalCompleteResult
    source converted annotations carrierFuel ruleFuel results).mp computed

/-- The total parser endpoint is exhaustive: it returns a canonically complete rich result or the
already proved explicit electronic-certification refusal. -/
theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence_canonicalComplete_or_refusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel ruleFuel : Nat) :
    (∃ results,
        molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
            source converted annotations carrierFuel ruleFuel = some results ∧
          molecule.ParserMainGroupLewisGeneralHybridRichCanonicalCompleteResult
            source converted annotations carrierFuel ruleFuel results) ∨
      molecule.ParserMainGroupLewisGeneralHybridCertificationRefusal
        source converted annotations := by
  classical
  by_cases ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations
  · left
    let results :=
      molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
        source converted annotations ready carrierFuel ruleFuel
    have computed :
        molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
            source converted annotations carrierFuel ruleFuel = some results := by
      exact
        molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_eq_some_of_ready
          source converted annotations ready carrierFuel ruleFuel
    exact ⟨results, computed,
      (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_eq_some_iff_canonicalCompleteResult
        source converted annotations carrierFuel ruleFuel results).mp computed⟩
  · right
    exact
      (molecule.not_parserMainGroupLewisGeneralHybridCertificationReady_iff_refusal
        source converted annotations).mp ready

end RawMolecule
end TetraStereo.OneCenter
