import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6RSPseudoConservativeExtension
import TetraStereo.OneCenter.AuthoritativeParserMainGroupLewisGeneralHybridRepresentedPipeline
import TetraStereo.OneCenter.AuthoritativeParserMainGroupLewisGeneralHybridRichRepresentedPipeline

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Reuse of the established chemical readiness contract by the rich represented pipeline

The `R/S/r/s` endpoint is now proved to have exactly the same success domain as the older
case-erasing `R/S` endpoint.  Consequently neither the source five-family pipeline nor its parser
front end needs a new case-specific readiness premise.
-/

/-- The established concrete chemical-readiness package already proves full case-preserving
tetrahedral readiness. -/
theorem aromaticCanonicalConcreteRule3Through6RSPseudoReady_of_chemicallyReadyAtBound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalConcreteRule3Through6ChemicallyReadyAtBound
      carrierFuel center) :
    source.AromaticCanonicalConcreteRule3Through6RSPseudoReady
      carrierFuel (2 * (carrierFuel + 1)) center := by
  exact
    source.aromaticCanonicalScheduledRule3Through6RSPseudoReady_of_chemicallyReadyAtBound
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel (2 * (carrierFuel + 1))) center ready

/-- Upgrade the previous five-family readiness record without adding any premise. -/
def AromaticCanonicalHybridElectronicInventoryRepresentedPipelineReadyAtBound.toRich
    (source : AuthoritativeChemicalInput)
    {supplied : List source.AromaticCanonicalAtomElectronicStateRecord}
    {carrierFuel : Nat}
    (ready : source.AromaticCanonicalHybridElectronicInventoryRepresentedPipelineReadyAtBound
      supplied carrierFuel) :
    source.AromaticCanonicalHybridRichRepresentedPipelineReadyAtBound
      supplied carrierFuel where
  electronic := ready.electronic
  tetrahedral := fun center =>
    source.aromaticCanonicalConcreteRule3Through6RSPseudoReady_of_chemicallyReadyAtBound
      carrierFuel center (ready.tetrahedral center)
  ordinaryDoubleBond := ready.ordinaryDoubleBond
  oddOpenCumulene := ready.oddOpenCumulene
  evenOpenCumulene := ready.evenOpenCumulene

/-- The rich five-family exact-once theorem follows from the original chemically stated
readiness record, so retaining descriptor case has no downstream completeness cost. -/
theorem analyzeAromaticCanonicalHybridRichRepresented_complete_at_bound_of_legacyReady
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel : Nat)
    (ready : source.AromaticCanonicalHybridElectronicInventoryRepresentedPipelineReadyAtBound
      supplied carrierFuel) :
    source.AromaticCanonicalHybridRichRepresentedPipelineCompleteAtBound
      supplied carrierFuel ready.toRich :=
  source.analyzeAromaticCanonicalHybridRichRepresented_complete_at_bound
    supplied carrierFuel ready.toRich

end AuthoritativeChemicalInput

namespace RawMolecule

open AuthoritativeChemicalInput

/-- Upgrade the previous parser-level readiness record without adding any parser, electronic,
or stereochemical premise. -/
def ParserMainGroupLewisGeneralHybridRepresentedPipelineReadyAtBound.toRich
    (molecule : RawMolecule)
    {source : AuthoritativeChemicalInput}
    {converted : molecule.toSemanticMolecule? = some source.molecule}
    {annotations : List ParserAtomElectronicStateAnnotation}
    {carrierFuel : Nat}
    (ready : molecule.ParserMainGroupLewisGeneralHybridRepresentedPipelineReadyAtBound
      source converted annotations carrierFuel) :
    molecule.ParserMainGroupLewisGeneralHybridRichRepresentedPipelineReadyAtBound
      source converted annotations carrierFuel where
  parserElectronic := ready.parserElectronic
  represented := ready.represented.toRich

/-- Parser-to-rich exact-once completeness under exactly the previously established parser and
chemical readiness contract. -/
theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence_complete_at_bound_of_legacyReady
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel : Nat)
    (ready : molecule.ParserMainGroupLewisGeneralHybridRepresentedPipelineReadyAtBound
      source converted annotations carrierFuel) :
    ∃ results,
      molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
          source converted annotations carrierFuel (2 * (carrierFuel + 1)) = some results ∧
        results =
          source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            (molecule.parserAtomElectronicStateRecords source converted annotations)
            ready.toRich.represented.electronic carrierFuel (2 * (carrierFuel + 1)) ∧
        source.AromaticCanonicalHybridRichRepresentedPipelineCompleteAtBound
          (molecule.parserAtomElectronicStateRecords source converted annotations)
          carrierFuel ready.toRich.represented :=
  molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence_complete_at_bound
    source converted annotations carrierFuel ready.toRich

end RawMolecule
end TetraStereo.OneCenter
