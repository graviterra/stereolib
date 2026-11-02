import TetraStereo.OneCenter.IUPACP92ParserRepresentationBridge
import TetraStereo.OneCenter.IUPACP92ExactDigraphProductionRefinement
import TetraStereo.OneCenter.IUPACP92Rule1aProductionRefinement
import TetraStereo.OneCenter.IUPACP92ScheduleAndScalarProductionRefinement
import TetraStereo.OneCenter.IUPACP92SaturatedRingProductionRefinement
import TetraStereo.OneCenter.IUPACP92MancudeProductionRefinement
import TetraStereo.OneCenter.IUPACP92SemanticGraphProductionCore
import TetraStereo.OneCenter.SemanticLocalizedMancudeFiniteRealization

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# One dependent production-soundness theorem for the 11-row P-92 family

This module replaces eleven disconnected projection claims with one typed production relation.
Each constructor records an actual production observation and its concrete build/admission
premises.  One dependent case split proves that every such observation is independently
applicable, judged, and admitted for the same authoritative input.

The former saturated-ring transport constructor was removed because it embedded the reviewed
judgment as production evidence.  The replacement below uses the independent source-semantic
atom-cycle/node-path/closing-duplicate enumerator; reverse realization and `ProvisionCorrect` are
proved downstream in `IUPACP92FamilyProductionCompleteness`.  This module proves soundness and
domain closure only.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open DeclarativeCIP
open RawMolecule

/-- Fixed source-semantic observation for one real parent and its complete multiple-bond duplicate
fiber.  The node list is computed by the finite-range scan, not supplied by a caller. -/
def p92SemanticRule1aMultipleBondDuplicatesObservation
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount)
    (parent : (p92SemanticExactDigraphObservation source center ligand).graph.Node)
    (parentAtom duplicatedAtom : Fin source.molecule.atomCount) :
    P92Rule1aMultipleBondDuplicatesAuthorityObservation where
  expansion := p92SemanticExactDigraphObservation source center ligand
  parentNode := parent
  parentAtom := parentAtom
  duplicatedAtom := duplicatedAtom
  duplicateNodes := p92SemanticMultipleBondDuplicateNodes
    (p92SemanticOfficialSourceTree source center ligand) parent duplicatedAtom

/-- Fixed source-semantic observation for both ends of one double or triple bond. -/
def p92SemanticRule1aDoubleTripleBondsObservation
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount)
    (leftNode rightNode : (p92SemanticExactDigraphObservation source center ligand).graph.Node)
    (leftAtom rightAtom : Fin source.molecule.atomCount) :
    P92Rule1aDoubleTripleBondsAuthorityObservation where
  expansion := p92SemanticExactDigraphObservation source center ligand
  leftNode := leftNode
  rightNode := rightNode
  leftAtom := leftAtom
  rightAtom := rightAtom
  duplicatesAtLeft := p92SemanticMultipleBondDuplicateNodes
    (p92SemanticOfficialSourceTree source center ligand) leftNode rightAtom
  duplicatesAtRight := p92SemanticMultipleBondDuplicateNodes
    (p92SemanticOfficialSourceTree source center ligand) rightNode leftAtom

/-- One certified member emitted by the exhaustive source-semantic saturated-ring enumerator. -/
def p92SemanticRule1aSaturatedRingsObservation
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount)
    (ringAtoms : List (Fin source.molecule.atomCount))
    (realization :
      List (p92SemanticExactDigraphObservation source center ligand).graph.Node ×
        (p92SemanticExactDigraphObservation source center ligand).graph.Node) :
    P92Rule1aSaturatedRingsAuthorityObservation :=
  p92Rule1aSaturatedRingsObservationOfGraph source.molecule.atomCount
    (p92CanonicalLocalizedMoleculeGraph source center ligand) center ligand
    (p92SemanticExactDigraphObservation source center ligand).graph
    ringAtoms realization.1 realization.2

/-- Heterogeneous production witnesses for exactly the 11 P-92 digraph/Rule-1a authority rows. -/
inductive Next54P92ProductionWitness :
    (row : Next54P92DigraphRule1aAuthorityRow) →
      (source : AuthoritativeChemicalInput) → row.reference.Observation → Prop where
  | acyclicDigraph
      (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
      (center ligand : Fin molecule.atomCount) (key : RawMolecule.CanonicalBranchKey)
      (certificate : RawMolecule.P92ParserRepresentationCertificate source molecule)
      (built : branchCanonicalKey? molecule center ligand = some key)
      (complete : key.complete = true)
      (rootBond : (molecule.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
      (hasNoRingDuplicate : P92GraphHasNoRingDuplicate (key.toDeclarativeDigraph molecule)) :
      Next54P92ProductionWitness .acyclicDigraph source
        (p92ProductionExactDigraphObservation molecule center ligand key)
  | multipleBondDigraph
      (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
      (center ligand : Fin molecule.atomCount) (key : RawMolecule.CanonicalBranchKey)
      (certificate : RawMolecule.P92ParserRepresentationCertificate source molecule)
      (built : branchCanonicalKey? molecule center ligand = some key)
      (complete : key.complete = true)
      (rootBond : (molecule.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
      (hasMultipleBondDuplicate :
        P92GraphHasMultipleBondDuplicate (key.toDeclarativeDigraph molecule)) :
      Next54P92ProductionWitness .multipleBondDigraph source
        (p92ProductionExactDigraphObservation molecule center ligand key)
  | cyclicDigraph
      (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
      (center ligand : Fin molecule.atomCount) (key : RawMolecule.CanonicalBranchKey)
      (certificate : RawMolecule.P92ParserRepresentationCertificate source molecule)
      (built : branchCanonicalKey? molecule center ligand = some key)
      (complete : key.complete = true)
      (rootBond : (molecule.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
      (hasRingDuplicate : P92GraphHasRingDuplicate (key.toDeclarativeDigraph molecule)) :
      Next54P92ProductionWitness .cyclicDigraph source
        (p92ProductionExactDigraphObservation molecule center ligand key)
  | semanticAcyclicDigraph
      (source : AuthoritativeChemicalInput)
      (center ligand : Fin source.molecule.atomCount)
      (represented : P92CanonicalConstitutionRepresents source center ligand
        (p92CanonicalLocalizedMoleculeGraph source center ligand))
      (rootBond : (p92CanonicalLocalizedMoleculeGraph source center ligand).Adj center ligand)
      (hasNoRingDuplicate :
        (p92SemanticExactDigraphObservation source center ligand).HasNoRingDuplicate) :
      Next54P92ProductionWitness .acyclicDigraph source
        (p92SemanticExactDigraphObservation source center ligand)
  | semanticMultipleBondDigraph
      (source : AuthoritativeChemicalInput)
      (center ligand : Fin source.molecule.atomCount)
      (represented : P92CanonicalConstitutionRepresents source center ligand
        (p92CanonicalLocalizedMoleculeGraph source center ligand))
      (rootBond : (p92CanonicalLocalizedMoleculeGraph source center ligand).Adj center ligand)
      (hasMultipleBondDuplicate :
        (p92SemanticExactDigraphObservation source center ligand).HasMultipleBondDuplicate) :
      Next54P92ProductionWitness .multipleBondDigraph source
        (p92SemanticExactDigraphObservation source center ligand)
  | semanticCyclicDigraph
      (source : AuthoritativeChemicalInput)
      (center ligand : Fin source.molecule.atomCount)
      (represented : P92CanonicalConstitutionRepresents source center ligand
        (p92CanonicalLocalizedMoleculeGraph source center ligand))
      (rootBond : (p92CanonicalLocalizedMoleculeGraph source center ligand).Adj center ligand)
      (hasRingDuplicate :
        (p92SemanticExactDigraphObservation source center ligand).HasRingDuplicate) :
      Next54P92ProductionWitness .cyclicDigraph source
        (p92SemanticExactDigraphObservation source center ligand)
  | mancudeDigraph
      (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
      (certificate : RawMolecule.P92ParserRepresentationCertificate source molecule)
      (attached duplicated : Fin molecule.atomCount)
      (localized : molecule.toMoleculeGraph.LocalizedMancudeEdge attached duplicated)
      (represented : P92MancudeAttachmentRepresented molecule.toMoleculeGraph attached)
      (label : RawMolecule.CIPAtomicLabel)
      (produced : molecule.mancudeRule1aLabel? attached.val duplicated.val = some label) :
      Next54P92ProductionWitness .mancudeDigraph source
        (p92ProductionMancudeDigraphObservation molecule attached label)
  | semanticMancudeDigraphExactAverage
      (source : AuthoritativeChemicalInput)
      (attached : Fin source.molecule.atomCount)
      (represents : P92ClassicalConstitutionRepresents source
        source.molecule.toLocalizedMoleculeGraph)
      (represented : P92MancudeAttachmentRepresented
        source.molecule.toLocalizedMoleculeGraph attached) :
      Next54P92ProductionWitness .mancudeDigraph source
        { atomCount := source.molecule.atomCount
          molecule := source.molecule.toLocalizedMoleculeGraph
          attached := attached
          representedAtomicNumber := source.molecule.semanticExactMancudeAverage attached }
  | sphereExploration
      (source : AuthoritativeChemicalInput)
      (comparison : P92LigandComparisonAuthorityContext)
      (positions : List (List Nat)) (comparisonAt : List Nat → Ordering)
      (ready : comparison.Ready source)
      (ordered : positions.Pairwise HierarchyAddressBefore)
      (outside : ∀ position, position ∉ positions → comparisonAt position = Ordering.eq) :
      Next54P92ProductionWitness .sphereExploration source
        (p92ProductionSphereExplorationObservation comparison positions comparisonAt)
  | ruleExhaustivity
      (source : AuthoritativeChemicalInput)
      (comparison : P92LigandComparisonAuthorityContext)
      (ready : comparison.Ready source) (outcomeAt : SequenceRule → Ordering) :
      Next54P92ProductionWitness .ruleExhaustivity source
        (p92ProductionRuleExhaustivityObservation comparison outcomeAt)
  | rule1aMultipleBondDuplicates
      (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
      (center ligand : Fin molecule.atomCount) (key : RawMolecule.CanonicalBranchKey)
      (certificate : RawMolecule.P92ParserRepresentationCertificate source molecule)
      (built : branchCanonicalKey? molecule center ligand = some key)
      (complete : key.complete = true)
      (rootBond : (molecule.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
      (parentNode : (key.toDeclarativeDigraph molecule).Node)
      (parentAtom duplicatedAtom : Fin molecule.atomCount)
      (parentLabel : (key.toDeclarativeDigraph molecule).label parentNode =
        ⟨some parentAtom, NodeProvenance.realAtom⟩)
      (multipleBond : 1 < (molecule.canonicalHierarchyMoleculeGraph center ligand).bond
        parentAtom duplicatedAtom) :
      Next54P92ProductionWitness .rule1aMultipleBondDuplicates source
        (p92ProductionRule1aMultipleBondDuplicatesObservation molecule center ligand key
          parentNode parentAtom duplicatedAtom)
  | semanticRule1aMultipleBondDuplicates
      (source : AuthoritativeChemicalInput)
      (center ligand : Fin source.molecule.atomCount)
      (represented : P92CanonicalConstitutionRepresents source center ligand
        (p92CanonicalLocalizedMoleculeGraph source center ligand))
      (rootBond : (p92CanonicalLocalizedMoleculeGraph source center ligand).Adj center ligand)
      (parent : (p92SemanticExactDigraphObservation source center ligand).graph.Node)
      (parentAtom duplicatedAtom : Fin source.molecule.atomCount)
      (parentLabel : (p92SemanticExactDigraphObservation source center ligand).graph.label parent =
        ⟨some parentAtom, NodeProvenance.realAtom⟩)
      (multipleBond : 1 < (p92CanonicalLocalizedMoleculeGraph source center ligand).bond
        parentAtom duplicatedAtom) :
      Next54P92ProductionWitness .rule1aMultipleBondDuplicates source
        (p92SemanticRule1aMultipleBondDuplicatesObservation source center ligand parent
          parentAtom duplicatedAtom)
  | rule1aMancude
      (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
      (certificate : RawMolecule.P92ParserRepresentationCertificate source molecule)
      (leftAttached leftDuplicated rightAttached rightDuplicated : Fin molecule.atomCount)
      (leftLocalized :
        molecule.toMoleculeGraph.LocalizedMancudeEdge leftAttached leftDuplicated)
      (rightLocalized :
        molecule.toMoleculeGraph.LocalizedMancudeEdge rightAttached rightDuplicated)
      (leftRepresented :
        P92MancudeAttachmentRepresented molecule.toMoleculeGraph leftAttached)
      (rightRepresented :
        P92MancudeAttachmentRepresented molecule.toMoleculeGraph rightAttached)
      (leftLabel rightLabel : RawMolecule.CIPAtomicLabel)
      (leftProduced :
        molecule.mancudeRule1aLabel? leftAttached.val leftDuplicated.val = some leftLabel)
      (rightProduced :
        molecule.mancudeRule1aLabel? rightAttached.val rightDuplicated.val = some rightLabel) :
      Next54P92ProductionWitness .rule1aMancude source
        (p92ProductionRule1aMancudeObservation molecule leftAttached rightAttached
          leftLabel rightLabel)
  | semanticRule1aMancudeExactComparison
      (source : AuthoritativeChemicalInput)
      (leftAttached rightAttached : Fin source.molecule.atomCount)
      (represents : P92ClassicalConstitutionRepresents source
        source.molecule.toLocalizedMoleculeGraph)
      (leftRepresented : P92MancudeAttachmentRepresented
        source.molecule.toLocalizedMoleculeGraph leftAttached)
      (rightRepresented : P92MancudeAttachmentRepresented
        source.molecule.toLocalizedMoleculeGraph rightAttached) :
      Next54P92ProductionWitness .rule1aMancude source
        { atomCount := source.molecule.atomCount
          molecule := source.molecule.toLocalizedMoleculeGraph
          leftAttached := leftAttached
          rightAttached := rightAttached
          outcome := @compare ℚ Rat.linearOrder.toOrd
            (source.molecule.semanticExactMancudeAverage leftAttached).value
            (source.molecule.semanticExactMancudeAverage rightAttached).value }
  | rule1aSaturatedCompounds
      (source : AuthoritativeChemicalInput) (atomCount : Nat)
      (molecule : MoleculeGraph (Fin atomCount))
      (represents : P92ClassicalConstitutionRepresents source molecule)
      (left right : Fin atomCount)
      (leftSaturated : P92AtomSaturated molecule left)
      (rightSaturated : P92AtomSaturated molecule right) :
      Next54P92ProductionWitness .rule1aSaturatedCompounds source
        (p92ProductionRule1aSaturatedCompoundsObservation atomCount molecule left right)
  | rule1aDoubleTripleBonds
      (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
      (center ligand : Fin molecule.atomCount) (key : RawMolecule.CanonicalBranchKey)
      (certificate : RawMolecule.P92ParserRepresentationCertificate source molecule)
      (built : branchCanonicalKey? molecule center ligand = some key)
      (complete : key.complete = true)
      (rootBond : (molecule.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
      (leftNode rightNode : (key.toDeclarativeDigraph molecule).Node)
      (leftAtom rightAtom : Fin molecule.atomCount)
      (leftLabel : (key.toDeclarativeDigraph molecule).label leftNode =
        ⟨some leftAtom, NodeProvenance.realAtom⟩)
      (rightLabel : (key.toDeclarativeDigraph molecule).label rightNode =
        ⟨some rightAtom, NodeProvenance.realAtom⟩)
      (bondOrder :
        (molecule.canonicalHierarchyMoleculeGraph center ligand).bond leftAtom rightAtom = 2 ∨
          (molecule.canonicalHierarchyMoleculeGraph center ligand).bond leftAtom rightAtom = 3) :
      Next54P92ProductionWitness .rule1aDoubleTripleBonds source
        (p92ProductionRule1aDoubleTripleBondsObservation molecule center ligand key
          leftNode rightNode leftAtom rightAtom)
  | semanticRule1aDoubleTripleBonds
      (source : AuthoritativeChemicalInput)
      (center ligand : Fin source.molecule.atomCount)
      (represented : P92CanonicalConstitutionRepresents source center ligand
        (p92CanonicalLocalizedMoleculeGraph source center ligand))
      (rootBond : (p92CanonicalLocalizedMoleculeGraph source center ligand).Adj center ligand)
      (leftNode rightNode :
        (p92SemanticExactDigraphObservation source center ligand).graph.Node)
      (leftAtom rightAtom : Fin source.molecule.atomCount)
      (leftLabel : (p92SemanticExactDigraphObservation source center ligand).graph.label leftNode =
        ⟨some leftAtom, NodeProvenance.realAtom⟩)
      (rightLabel : (p92SemanticExactDigraphObservation source center ligand).graph.label rightNode =
        ⟨some rightAtom, NodeProvenance.realAtom⟩)
      (bondOrder :
        (p92CanonicalLocalizedMoleculeGraph source center ligand).bond leftAtom rightAtom = 2 ∨
          (p92CanonicalLocalizedMoleculeGraph source center ligand).bond leftAtom rightAtom = 3) :
      Next54P92ProductionWitness .rule1aDoubleTripleBonds source
        (p92SemanticRule1aDoubleTripleBondsObservation source center ligand leftNode rightNode
          leftAtom rightAtom)
  | semanticRule1aSaturatedRings
      (source : AuthoritativeChemicalInput)
      (center ligand : Fin source.molecule.atomCount)
      (represented : P92CanonicalConstitutionRepresents source center ligand
        (p92CanonicalLocalizedMoleculeGraph source center ligand))
      (rootBond : (p92CanonicalLocalizedMoleculeGraph source center ligand).Adj center ligand)
      (ringAtoms : List (Fin source.molecule.atomCount))
      (realization :
        List (p92SemanticExactDigraphObservation source center ligand).graph.Node ×
          (p92SemanticExactDigraphObservation source center ligand).graph.Node)
      (atomsEmitted : ringAtoms ∈ p92CandidateRingAtomLists source.molecule.atomCount)
      (realizationEmitted : realization ∈
        p92SemanticSaturatedRingRealizations source center ligand ringAtoms)
      (saturated : P92IsSaturatedRing
        (p92CanonicalLocalizedMoleculeGraph source center ligand) ringAtoms) :
      Next54P92ProductionWitness .rule1aSaturatedRings source
        (p92SemanticRule1aSaturatedRingsObservation source center ligand ringAtoms realization)

namespace Next54P92ProductionWitness

/-- The eleven production projections recombined into one semantic-family soundness theorem. -/
theorem judged
    {row : Next54P92DigraphRule1aAuthorityRow}
    {source : AuthoritativeChemicalInput}
    {observation : row.reference.Observation}
    (produced : Next54P92ProductionWitness row source observation) :
    row.reference.Judges source observation := by
  cases produced with
  | acyclicDigraph source molecule center ligand key certificate built complete
      rootBond hasNoRingDuplicate =>
      exact p92ProductionAcyclicDigraph_judged source molecule center ligand key
        (certificate.representsCanonicalHierarchy center ligand)
        certificate.wellFormed certificate.bondRecordsUnique built complete rootBond
          hasNoRingDuplicate
  | multipleBondDigraph source molecule center ligand key certificate built complete
      rootBond hasMultipleBondDuplicate =>
      exact p92ProductionMultipleBondDigraph_judged source molecule center ligand key
        (certificate.representsCanonicalHierarchy center ligand)
        certificate.wellFormed certificate.bondRecordsUnique built complete rootBond
          hasMultipleBondDuplicate
  | cyclicDigraph source molecule center ligand key certificate built complete
      rootBond hasRingDuplicate =>
      exact p92ProductionCyclicDigraph_judged source molecule center ligand key
        (certificate.representsCanonicalHierarchy center ligand)
        certificate.wellFormed certificate.bondRecordsUnique built complete rootBond
          hasRingDuplicate
  | semanticAcyclicDigraph source center ligand represented rootBond
      hasNoRingDuplicate =>
      exact ⟨p92SemanticExactDigraphObservation_represents source center ligand
          represented,
        p92SemanticExactDigraphObservation_faithful source center ligand rootBond,
        hasNoRingDuplicate⟩
  | semanticMultipleBondDigraph source center ligand represented rootBond
      hasMultipleBondDuplicate =>
      exact ⟨p92SemanticExactDigraphObservation_represents source center ligand
          represented,
        p92SemanticExactDigraphObservation_faithful source center ligand rootBond,
        hasMultipleBondDuplicate⟩
  | semanticCyclicDigraph source center ligand represented rootBond
      hasRingDuplicate =>
      exact ⟨p92SemanticExactDigraphObservation_represents source center ligand
          represented,
        p92SemanticExactDigraphObservation_faithful source center ligand rootBond,
        hasRingDuplicate⟩
  | mancudeDigraph source molecule certificate attached duplicated localized represented label
      production =>
      exact p92ProductionMancudeDigraph_judged source molecule certificate.wellFormed
        certificate.bondRecordsUnique certificate.representsToMoleculeGraph attached duplicated
          localized represented label production
  | semanticMancudeDigraphExactAverage source attached represents represented =>
      exact ⟨represents, represented,
        congrArg ExactAtomicNumber.value
          (source.molecule.semanticExactMancudeAverage_eq_independent attached)⟩
  | sphereExploration source comparison positions comparisonAt ready ordered outside =>
      exact p92ProductionSphereExploration_judged source comparison positions comparisonAt
        ready ordered outside
  | ruleExhaustivity source comparison ready outcomeAt =>
      exact p92ProductionRuleExhaustivity_judged source comparison ready outcomeAt
  | rule1aMultipleBondDuplicates source molecule center ligand key certificate built
      complete rootBond parentNode parentAtom duplicatedAtom parentLabel multipleBond =>
      exact p92ProductionRule1aMultipleBondDuplicates_judged source molecule center ligand key
        (certificate.representsCanonicalHierarchy center ligand)
        certificate.wellFormed certificate.bondRecordsUnique built complete rootBond parentNode
          parentAtom duplicatedAtom parentLabel multipleBond
  | semanticRule1aMultipleBondDuplicates source center ligand represented rootBond parent
      parentAtom duplicatedAtom parentLabel multipleBond =>
      have faithful :=
        p92SemanticExactDigraphObservation_faithful source center ligand rootBond
      exact ⟨represented, faithful,
        P92ExactDigraphAuthorityObservation.generatedSemanticMultipleBondDuplicateChildrenExact
          source center ligand faithful parent parentAtom duplicatedAtom parentLabel multipleBond⟩
  | rule1aMancude source molecule certificate leftAttached leftDuplicated rightAttached
      rightDuplicated leftLocalized rightLocalized leftRepresented rightRepresented leftLabel
      rightLabel leftProduced rightProduced =>
      exact p92ProductionRule1aMancude_judged source molecule certificate.wellFormed
        certificate.bondRecordsUnique certificate.representsToMoleculeGraph leftAttached
          leftDuplicated rightAttached rightDuplicated leftLocalized rightLocalized leftRepresented
            rightRepresented leftLabel rightLabel leftProduced rightProduced
  | semanticRule1aMancudeExactComparison source leftAttached rightAttached represents
      leftRepresented rightRepresented =>
      refine ⟨represents, leftRepresented, rightRepresented, ?_⟩
      unfold ExactAtomicNumber.Outcome
      rw [← source.molecule.semanticExactMancudeAverage_eq_independent leftAttached,
        ← source.molecule.semanticExactMancudeAverage_eq_independent rightAttached]
  | rule1aSaturatedCompounds source atomCount molecule represents left right leftSaturated
      rightSaturated =>
      exact p92ProductionRule1aSaturatedCompounds_judged source atomCount
        molecule left right represents leftSaturated rightSaturated
  | rule1aDoubleTripleBonds source molecule center ligand key certificate built complete
      rootBond leftNode rightNode leftAtom rightAtom leftLabel rightLabel bondOrder =>
      exact p92ProductionRule1aDoubleTripleBonds_judged source molecule center ligand key
        (certificate.representsCanonicalHierarchy center ligand)
        certificate.wellFormed certificate.bondRecordsUnique built complete rootBond leftNode
          rightNode leftAtom rightAtom leftLabel rightLabel bondOrder
  | semanticRule1aDoubleTripleBonds source center ligand represented rootBond leftNode rightNode
      leftAtom rightAtom leftLabel rightLabel bondOrder =>
      have faithful :=
        p92SemanticExactDigraphObservation_faithful source center ligand rootBond
      have leftMultiple :
          1 < (p92CanonicalLocalizedMoleculeGraph source center ligand).bond leftAtom rightAtom := by
        rcases bondOrder with bondOrder | bondOrder
        · rw [bondOrder]
          decide
        · rw [bondOrder]
          decide
      have rightMultiple :
          1 < (p92CanonicalLocalizedMoleculeGraph source center ligand).bond rightAtom leftAtom := by
        rw [← (p92CanonicalLocalizedMoleculeGraph source center ligand).bond_symm leftAtom rightAtom]
        exact leftMultiple
      exact ⟨represented, faithful, bondOrder,
        P92ExactDigraphAuthorityObservation.generatedSemanticMultipleBondDuplicateChildrenExact
          source center ligand faithful leftNode leftAtom rightAtom leftLabel leftMultiple,
        P92ExactDigraphAuthorityObservation.generatedSemanticMultipleBondDuplicateChildrenExact
          source center ligand faithful rightNode rightAtom leftAtom rightLabel rightMultiple⟩
  | semanticRule1aSaturatedRings source center ligand represented rootBond ringAtoms realization
      _atomsEmitted realizationEmitted saturated =>
      have faithful :=
        p92SemanticExactDigraphObservation_faithful source center ligand rootBond
      rcases (mem_p92SemanticSaturatedRingRealizations_iff source center ligand ringAtoms
        realization.1 realization.2).mp realizationEmitted with
        ⟨realNodes, path, closure⟩
      exact ⟨represented, faithful, saturated, realNodes, path, closure⟩

/-- Every concrete family production result is applicable and independently judged. -/
theorem applicable_and_judged
    {row : Next54P92DigraphRule1aAuthorityRow}
    {source : AuthoritativeChemicalInput}
    {observation : row.reference.Observation}
    (produced : Next54P92ProductionWitness row source observation) :
    row.reference.Applicable source ∧ row.reference.Judges source observation := by
  have judged := produced.judged
  exact ⟨row.applicable_of_judged source observation judged, judged⟩

/-- Production closure for all 11 rows follows from the same family theorem. -/
theorem observationAdmitted
    {row : Next54P92DigraphRule1aAuthorityRow}
    {source : AuthoritativeChemicalInput}
    {observation : row.reference.Observation}
    (produced : Next54P92ProductionWitness row source observation) :
    row.observationAdmitted source observation :=
  row.observationAdmitted_of_judged source observation produced.judged

end Next54P92ProductionWitness

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92ProductionWitness.judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92ProductionWitness.applicable_and_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92ProductionWitness.observationAdmitted
