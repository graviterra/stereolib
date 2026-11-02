import TetraStereo.OneCenter.IUPACP92FamilyProductionSoundness
import TetraStereo.OneCenter.IUPACP92ObservationEquivalence

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Reverse realization for the P-92 production family

This module proves genuine reverse realization for the three P-92 rows whose reviewed judgment
already determines the production observation uniquely: sphere exploration, exhaustive rule
ordering, and saturated-compound Rule 1a.  The two mancude rows are now likewise complete through
the exact finite maximum-matching average on the represented molecular graph; this removes the
old parser, Kekule-form, and 14-edge implementation boundary.  The six graph-backed rows retain
one explicit hierarchy-production boundary and are saturated by graph isomorphism and
duplicate-list permutation.  No production relation is defined as the reviewed reference.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open DeclarativeCIP

/-- Every independently judged sphere schedule is literally the result of the production scan. -/
theorem p92SphereExploration_reverse_realization
    (source : AuthoritativeChemicalInput)
    (observation : P92SphereExplorationAuthorityObservation)
    (judged : p92SphereExplorationReference.Judges source observation) :
    Next54P92ProductionWitness .sphereExploration source observation := by
  rcases observation with ⟨comparison, positions, comparisonAt, outcome⟩
  rcases judged with ⟨ready, ordered, outside, firstDifference⟩
  dsimp at ready ordered outside firstDifference ⊢
  have outcomeExact :
      firstStrictOnHierarchySchedule positions comparisonAt = outcome :=
    (firstDifference_iff_firstStrictOnHierarchySchedule comparisonAt positions
      ordered outside outcome).mp firstDifference
  subst outcome
  exact .sphereExploration source comparison positions comparisonAt ready ordered outside

/-- The first strict sequence rule is unique because rule ranks are injective. -/
theorem p92RuleExhaustivity_reverse_realization
    (source : AuthoritativeChemicalInput)
    (observation : P92RuleExhaustivityAuthorityObservation)
    (judged : p92RuleExhaustivityReference.Judges source observation) :
    Next54P92ProductionWitness .ruleExhaustivity source observation := by
  rcases observation with ⟨comparison, outcomeAt, firstDecisive?, outcome⟩
  rcases judged with ⟨ready, judged⟩
  dsimp at ready judged ⊢
  cases firstDecisive? with
  | none =>
      rcases judged with ⟨outcomeExact, allTie⟩
      have outcomeExact' : outcome = Ordering.eq := by
        simpa using outcomeExact
      have allTie' : ∀ rule, outcomeAt rule = Ordering.eq := by
        intro rule
        simpa using allTie rule
      rw [outcomeExact']
      have selectedNone : firstStrictSequenceRule? outcomeAt = none := by
        simp [firstStrictSequenceRule?, allTie']
      simpa [p92ProductionRuleExhaustivityObservation, selectedNone] using
        (Next54P92ProductionWitness.ruleExhaustivity source comparison ready outcomeAt)
  | some rule =>
      rcases judged with ⟨outcomeStrict, ruleOutcome, earlierTie⟩
      have ruleOutcome' : outcomeAt rule = outcome := by
        simpa using ruleOutcome
      have ruleStrict : P92OrderingStrict (outcomeAt rule) := by
        rw [ruleOutcome']
        exact outcomeStrict
      have ruleNeTie : outcomeAt rule ≠ Ordering.eq := by
        exact p92OrderingStrict_ne_eq ruleStrict
      have notAllTie : ¬ ∀ candidate, outcomeAt candidate = Ordering.eq := by
        intro allTie
        exact ruleNeTie (allTie rule)
      have selectedRule : firstStrictSequenceRule? outcomeAt = some rule :=
        firstStrictSequenceRule_eq_some_of_spec outcomeAt rule ruleStrict earlierTie
      rw [← ruleOutcome']
      simpa [p92ProductionRuleExhaustivityObservation, selectedRule] using
        (Next54P92ProductionWitness.ruleExhaustivity source comparison ready outcomeAt)

/-- Exact atomic-number comparison realizes every judged saturated-compound observation. -/
theorem p92Rule1aSaturatedCompounds_reverse_realization
    (source : AuthoritativeChemicalInput)
    (observation : P92Rule1aSaturatedCompoundsAuthorityObservation)
    (judged : p92Rule1aSaturatedCompoundsReference.Judges source observation) :
    Next54P92ProductionWitness .rule1aSaturatedCompounds source observation := by
  rcases observation with ⟨atomCount, molecule, left, right, outcome⟩
  rcases judged with ⟨represents, leftSaturated, rightSaturated, outcomeExact⟩
  unfold ExactAtomicNumber.Outcome at outcomeExact
  have outcomeExact' :
      @compare ℚ Rat.linearOrder.toOrd
        (ExactAtomicNumber.ofNat (molecule.atomZ left)).value
        (ExactAtomicNumber.ofNat (molecule.atomZ right)).value = outcome := by
    simpa using outcomeExact
  rw [← outcomeExact']
  exact .rule1aSaturatedCompounds source atomCount molecule represents left right
    leftSaturated rightSaturated

/-! ## Observationally saturated production -/

/-- The two rows produced by one authoritative mancude execution. -/
inductive Next54P92MancudeAuthorityRow where
  | mancudeDigraph
  | rule1aMancude
  deriving DecidableEq, Repr

namespace Next54P92MancudeAuthorityRow

def authorityRow : Next54P92MancudeAuthorityRow → Next54P92DigraphRule1aAuthorityRow
  | .mancudeDigraph => .mancudeDigraph
  | .rule1aMancude => .rule1aMancude

end Next54P92MancudeAuthorityRow

/-- Production for a reviewed observation means that the fixed implementation produced a
canonical observation carrying the same chemical content.  This is strictly stronger than
judgment truth and strictly weaker than syntactic record equality. -/
def Next54P92Produces
    (row : Next54P92DigraphRule1aAuthorityRow)
  (source : AuthoritativeChemicalInput)
  (observation : row.reference.Observation) : Prop :=
  ∃ produced : row.reference.Observation,
    Next54P92ProductionWitness row source produced ∧
      Next54P92ObservationEquivalent row produced observation

namespace Next54P92Produces

theorem of_witness
    {row : Next54P92DigraphRule1aAuthorityRow}
    {source : AuthoritativeChemicalInput}
    {observation : row.reference.Observation}
    (produced : Next54P92ProductionWitness row source observation) :
    Next54P92Produces row source observation :=
  ⟨observation, produced, Next54P92ObservationEquivalent.refl row observation⟩

theorem judged
    {row : Next54P92DigraphRule1aAuthorityRow}
    {source : AuthoritativeChemicalInput}
    {observation : row.reference.Observation}
    (produced : Next54P92Produces row source observation) :
    row.reference.Judges source observation := by
  rcases produced with ⟨canonical, canonicalProduced, equivalent⟩
  exact (equivalent.judges_iff source).mp canonicalProduced.judged

theorem applicable_and_judged
    {row : Next54P92DigraphRule1aAuthorityRow}
    {source : AuthoritativeChemicalInput}
    {observation : row.reference.Observation}
    (produced : Next54P92Produces row source observation) :
    row.reference.Applicable source ∧ row.reference.Judges source observation := by
  have judged := produced.judged
  exact ⟨row.applicable_of_judged source observation judged, judged⟩

end Next54P92Produces

/-! ## Assumption-free exact-digraph family -/

/-- Every independently judged acyclic exact digraph is realized by the fixed source-only
semantic hierarchy.  Faithful-expansion uniqueness supplies the representation isomorphism; no
reviewed hierarchy is copied into production. -/
theorem p92AcyclicDigraph_reverse_realization
    (source : AuthoritativeChemicalInput)
    (observation : P92ExactDigraphAuthorityObservation)
    (judged : p92AcyclicDigraphReference.Judges source observation) :
    Next54P92Produces .acyclicDigraph source observation := by
  rcases observation with ⟨atomCount, molecule, externalParent, ligand, graph⟩
  rcases judged with ⟨represented, referenceFaithful, referenceHasNoRingDuplicate⟩
  change P92CanonicalConstitutionRepresents source externalParent ligand molecule at represented
  change RootedDigraph.FaithfulExactExpansion molecule externalParent ligand
    graph.toRootedDigraph at referenceFaithful
  change P92GraphHasNoRingDuplicate graph.toRootedDigraph at referenceHasNoRingDuplicate
  have atomCountExact := represented.atomCount_exact
  subst atomCount
  have moleculeExact :=
    p92CanonicalConstitutionRepresents_eq_canonicalLocalizedMoleculeGraph
      source externalParent ligand molecule represented
  subst molecule
  let production := p92SemanticExactDigraphObservation source externalParent ligand
  have rootBond :
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand).Adj
        externalParent ligand :=
    referenceFaithful.2.1
  have productionFaithful : production.Faithful :=
    p92SemanticExactDigraphObservation_faithful source externalParent ligand rootBond
  rcases RootedDigraph.faithfulExactExpansion_unique_up_to_iso
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand)
      externalParent ligand production.graph.toRootedDigraph graph.toRootedDigraph
      productionFaithful referenceFaithful with ⟨iso⟩
  have productionHasNoRingDuplicate : production.HasNoRingDuplicate :=
    (p92GraphHasNoRingDuplicate_iff_of_iso iso).mpr referenceHasNoRingDuplicate
  refine ⟨production, ?_, ?_⟩
  · exact .semanticAcyclicDigraph source externalParent ligand represented rootBond
      productionHasNoRingDuplicate
  · exact .ofIso source.molecule.atomCount
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand)
      externalParent ligand production.graph graph iso

/-- Every independently judged multiple-bond exact digraph is realized by the same fixed
source-only hierarchy, with the duplicate predicate transported across faithful uniqueness. -/
theorem p92MultipleBondDigraph_reverse_realization
    (source : AuthoritativeChemicalInput)
    (observation : P92ExactDigraphAuthorityObservation)
    (judged : p92MultipleBondDigraphReference.Judges source observation) :
    Next54P92Produces .multipleBondDigraph source observation := by
  rcases observation with ⟨atomCount, molecule, externalParent, ligand, graph⟩
  rcases judged with ⟨represented, referenceFaithful, referenceHasMultipleBondDuplicate⟩
  change P92CanonicalConstitutionRepresents source externalParent ligand molecule at represented
  change RootedDigraph.FaithfulExactExpansion molecule externalParent ligand
    graph.toRootedDigraph at referenceFaithful
  change P92GraphHasMultipleBondDuplicate graph.toRootedDigraph at referenceHasMultipleBondDuplicate
  have atomCountExact := represented.atomCount_exact
  subst atomCount
  have moleculeExact :=
    p92CanonicalConstitutionRepresents_eq_canonicalLocalizedMoleculeGraph
      source externalParent ligand molecule represented
  subst molecule
  let production := p92SemanticExactDigraphObservation source externalParent ligand
  have rootBond :
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand).Adj
        externalParent ligand :=
    referenceFaithful.2.1
  have productionFaithful : production.Faithful :=
    p92SemanticExactDigraphObservation_faithful source externalParent ligand rootBond
  rcases RootedDigraph.faithfulExactExpansion_unique_up_to_iso
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand)
      externalParent ligand production.graph.toRootedDigraph graph.toRootedDigraph
      productionFaithful referenceFaithful with ⟨iso⟩
  have productionHasMultipleBondDuplicate : production.HasMultipleBondDuplicate :=
    (p92GraphHasMultipleBondDuplicate_iff_of_iso iso).mpr
      referenceHasMultipleBondDuplicate
  refine ⟨production, ?_, ?_⟩
  · exact .semanticMultipleBondDigraph source externalParent ligand represented rootBond
      productionHasMultipleBondDuplicate
  · exact .ofIso source.molecule.atomCount
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand)
      externalParent ligand production.graph graph iso

/-- Every independently judged cyclic exact digraph is realized by the same fixed source-only
hierarchy, with the ring-duplicate predicate transported across faithful uniqueness. -/
theorem p92CyclicDigraph_reverse_realization
    (source : AuthoritativeChemicalInput)
    (observation : P92ExactDigraphAuthorityObservation)
    (judged : p92CyclicDigraphReference.Judges source observation) :
    Next54P92Produces .cyclicDigraph source observation := by
  rcases observation with ⟨atomCount, molecule, externalParent, ligand, graph⟩
  rcases judged with ⟨represented, referenceFaithful, referenceHasRingDuplicate⟩
  change P92CanonicalConstitutionRepresents source externalParent ligand molecule at represented
  change RootedDigraph.FaithfulExactExpansion molecule externalParent ligand
    graph.toRootedDigraph at referenceFaithful
  change P92GraphHasRingDuplicate graph.toRootedDigraph at referenceHasRingDuplicate
  have atomCountExact := represented.atomCount_exact
  subst atomCount
  have moleculeExact :=
    p92CanonicalConstitutionRepresents_eq_canonicalLocalizedMoleculeGraph
      source externalParent ligand molecule represented
  subst molecule
  let production := p92SemanticExactDigraphObservation source externalParent ligand
  have rootBond :
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand).Adj
        externalParent ligand :=
    referenceFaithful.2.1
  have productionFaithful : production.Faithful :=
    p92SemanticExactDigraphObservation_faithful source externalParent ligand rootBond
  rcases RootedDigraph.faithfulExactExpansion_unique_up_to_iso
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand)
      externalParent ligand production.graph.toRootedDigraph graph.toRootedDigraph
      productionFaithful referenceFaithful with ⟨iso⟩
  have productionHasRingDuplicate : production.HasRingDuplicate :=
    (p92GraphHasRingDuplicate_iff_of_iso iso).mpr referenceHasRingDuplicate
  refine ⟨production, ?_, ?_⟩
  · exact .semanticCyclicDigraph source externalParent ligand represented rootBond
      productionHasRingDuplicate
  · exact .ofIso source.molecule.atomCount
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand)
      externalParent ligand production.graph graph iso

/-- The executable finite duplicate-fiber scan realizes every independently judged single-parent
Rule-1a duplicate observation, up to the canonical faithful-expansion node permutation. -/
theorem p92Rule1aMultipleBondDuplicates_reverse_realization
    (source : AuthoritativeChemicalInput)
    (observation : P92Rule1aMultipleBondDuplicatesAuthorityObservation)
    (judged : p92Rule1aMultipleBondDuplicatesReference.Judges source observation) :
    Next54P92Produces .rule1aMultipleBondDuplicates source observation := by
  rcases observation with
    ⟨⟨atomCount, molecule, externalParent, ligand, graph⟩,
      referenceParent, parentAtom, duplicatedAtom, referenceNodes⟩
  rcases judged with ⟨represented, referenceFaithful, referenceExact⟩
  change P92CanonicalConstitutionRepresents source externalParent ligand molecule at represented
  change RootedDigraph.FaithfulExactExpansion molecule externalParent ligand
    graph.toRootedDigraph at referenceFaithful
  change P92MultipleBondDuplicateChildrenExact
    (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand graph)
    referenceParent parentAtom duplicatedAtom referenceNodes at referenceExact
  have atomCountExact := represented.atomCount_exact
  subst atomCount
  have moleculeExact :=
    p92CanonicalConstitutionRepresents_eq_canonicalLocalizedMoleculeGraph
      source externalParent ligand molecule represented
  subst molecule
  let production := p92SemanticExactDigraphObservation source externalParent ligand
  have rootBond :
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand).Adj
        externalParent ligand :=
    referenceFaithful.2.1
  have productionFaithful : production.Faithful :=
    p92SemanticExactDigraphObservation_faithful source externalParent ligand rootBond
  rcases RootedDigraph.faithfulExactExpansion_unique_up_to_iso
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand)
      externalParent ligand production.graph.toRootedDigraph graph.toRootedDigraph
      productionFaithful referenceFaithful with ⟨iso⟩
  let productionParent := iso.toEquiv.symm referenceParent
  have parentEq : iso.toEquiv productionParent = referenceParent := by
    simp [productionParent]
  have productionParentLabel : production.graph.label productionParent =
      ⟨some parentAtom, NodeProvenance.realAtom⟩ := by
    exact (iso.map_label productionParent).trans (by simpa [parentEq] using referenceExact.1)
  have multipleBond : 1 < production.molecule.bond parentAtom duplicatedAtom :=
    referenceExact.2.1
  let productionNodes := p92SemanticMultipleBondDuplicateNodes
    (p92SemanticOfficialSourceTree source externalParent ligand) productionParent duplicatedAtom
  have productionExact : P92MultipleBondDuplicateChildrenExact production productionParent
      parentAtom duplicatedAtom productionNodes :=
    P92ExactDigraphAuthorityObservation.generatedSemanticMultipleBondDuplicateChildrenExact
      source externalParent ligand productionFaithful productionParent parentAtom duplicatedAtom
        productionParentLabel multipleBond
  have nodesPerm : (productionNodes.map iso.toEquiv).Perm referenceNodes :=
    Next54P92ObservationEquivalent.P92MultipleBondDuplicateChildrenExact.map_perm_of_iso
      source.molecule.atomCount
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand) externalParent ligand
      production.graph graph iso productionParent referenceParent parentEq parentAtom duplicatedAtom
      productionNodes referenceNodes productionExact referenceExact
  refine ⟨p92SemanticRule1aMultipleBondDuplicatesObservation source externalParent ligand
      productionParent parentAtom duplicatedAtom, ?_, ?_⟩
  · exact .semanticRule1aMultipleBondDuplicates source externalParent ligand represented rootBond
      productionParent parentAtom duplicatedAtom productionParentLabel multipleBond
  · exact .ofIsoPerm source.molecule.atomCount
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand) externalParent ligand
      production.graph graph iso productionParent referenceParent parentEq parentAtom duplicatedAtom
      productionNodes referenceNodes nodesPerm

/-- The same executable duplicate-fiber scan realizes both endpoint lists of every independently
judged double/triple-bond replacement observation. -/
theorem p92Rule1aDoubleTripleBonds_reverse_realization
    (source : AuthoritativeChemicalInput)
    (observation : P92Rule1aDoubleTripleBondsAuthorityObservation)
    (judged : p92Rule1aDoubleTripleBondsReference.Judges source observation) :
    Next54P92Produces .rule1aDoubleTripleBonds source observation := by
  rcases observation with
    ⟨⟨atomCount, molecule, externalParent, ligand, graph⟩,
      referenceLeft, referenceRight, leftAtom, rightAtom,
      referenceLeftNodes, referenceRightNodes⟩
  rcases judged with
    ⟨represented, referenceFaithful, bondOrder, referenceLeftExact, referenceRightExact⟩
  change P92CanonicalConstitutionRepresents source externalParent ligand molecule at represented
  change RootedDigraph.FaithfulExactExpansion molecule externalParent ligand
    graph.toRootedDigraph at referenceFaithful
  change P92MultipleBondDuplicateChildrenExact
    (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand graph)
    referenceLeft leftAtom rightAtom referenceLeftNodes at referenceLeftExact
  change P92MultipleBondDuplicateChildrenExact
    (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand graph)
    referenceRight rightAtom leftAtom referenceRightNodes at referenceRightExact
  have atomCountExact := represented.atomCount_exact
  subst atomCount
  have moleculeExact :=
    p92CanonicalConstitutionRepresents_eq_canonicalLocalizedMoleculeGraph
      source externalParent ligand molecule represented
  subst molecule
  let production := p92SemanticExactDigraphObservation source externalParent ligand
  have rootBond :
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand).Adj
        externalParent ligand :=
    referenceFaithful.2.1
  have productionFaithful : production.Faithful :=
    p92SemanticExactDigraphObservation_faithful source externalParent ligand rootBond
  rcases RootedDigraph.faithfulExactExpansion_unique_up_to_iso
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand)
      externalParent ligand production.graph.toRootedDigraph graph.toRootedDigraph
      productionFaithful referenceFaithful with ⟨iso⟩
  let productionLeft := iso.toEquiv.symm referenceLeft
  let productionRight := iso.toEquiv.symm referenceRight
  have leftEq : iso.toEquiv productionLeft = referenceLeft := by simp [productionLeft]
  have rightEq : iso.toEquiv productionRight = referenceRight := by simp [productionRight]
  have productionLeftLabel : production.graph.label productionLeft =
      ⟨some leftAtom, NodeProvenance.realAtom⟩ := by
    exact (iso.map_label productionLeft).trans (by simpa [leftEq] using referenceLeftExact.1)
  have productionRightLabel : production.graph.label productionRight =
      ⟨some rightAtom, NodeProvenance.realAtom⟩ := by
    exact (iso.map_label productionRight).trans (by simpa [rightEq] using referenceRightExact.1)
  let productionLeftNodes := p92SemanticMultipleBondDuplicateNodes
    (p92SemanticOfficialSourceTree source externalParent ligand) productionLeft rightAtom
  let productionRightNodes := p92SemanticMultipleBondDuplicateNodes
    (p92SemanticOfficialSourceTree source externalParent ligand) productionRight leftAtom
  have productionLeftExact : P92MultipleBondDuplicateChildrenExact production productionLeft
      leftAtom rightAtom productionLeftNodes :=
    P92ExactDigraphAuthorityObservation.generatedSemanticMultipleBondDuplicateChildrenExact
      source externalParent ligand productionFaithful productionLeft leftAtom rightAtom
        productionLeftLabel referenceLeftExact.2.1
  have productionRightExact : P92MultipleBondDuplicateChildrenExact production productionRight
      rightAtom leftAtom productionRightNodes :=
    P92ExactDigraphAuthorityObservation.generatedSemanticMultipleBondDuplicateChildrenExact
      source externalParent ligand productionFaithful productionRight rightAtom leftAtom
        productionRightLabel referenceRightExact.2.1
  have leftNodesPerm : (productionLeftNodes.map iso.toEquiv).Perm referenceLeftNodes :=
    Next54P92ObservationEquivalent.P92MultipleBondDuplicateChildrenExact.map_perm_of_iso
      source.molecule.atomCount
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand) externalParent ligand
      production.graph graph iso productionLeft referenceLeft leftEq leftAtom rightAtom
      productionLeftNodes referenceLeftNodes productionLeftExact referenceLeftExact
  have rightNodesPerm : (productionRightNodes.map iso.toEquiv).Perm referenceRightNodes :=
    Next54P92ObservationEquivalent.P92MultipleBondDuplicateChildrenExact.map_perm_of_iso
      source.molecule.atomCount
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand) externalParent ligand
      production.graph graph iso productionRight referenceRight rightEq rightAtom leftAtom
      productionRightNodes referenceRightNodes productionRightExact referenceRightExact
  refine ⟨p92SemanticRule1aDoubleTripleBondsObservation source externalParent ligand
      productionLeft productionRight leftAtom rightAtom, ?_, ?_⟩
  · exact .semanticRule1aDoubleTripleBonds source externalParent ligand represented rootBond
      productionLeft productionRight leftAtom rightAtom productionLeftLabel productionRightLabel
        bondOrder
  · exact .ofIsoPerm source.molecule.atomCount
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand) externalParent ligand
      production.graph graph iso productionLeft productionRight referenceLeft referenceRight
      leftEq rightEq leftAtom rightAtom productionLeftNodes referenceLeftNodes
      productionRightNodes referenceRightNodes leftNodesPerm rightNodesPerm

/-! ## Assumption-free exact mancude family -/

/-- Both reviewed mancude rows are realized by the same exact finite maximum-matching analyzer.
The analyzer operates on the represented constitutional graph itself and therefore has no parser
format, selected Kekule form, or component-size premise. -/
theorem p92MancudeFamily_reverse_realization
    (family : Next54P92MancudeAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : family.authorityRow.reference.Observation)
    (judged : family.authorityRow.reference.Judges source observation) :
    Next54P92Produces family.authorityRow source observation := by
  cases family with
  | mancudeDigraph =>
      rcases observation with ⟨atomCount, molecule, attached, representedAtomicNumber⟩
      rcases judged with ⟨represents, represented, valueExact⟩
      change P92ClassicalConstitutionRepresents source molecule at represents
      have atomCountExact := represents.atomCount_exact
      subst atomCount
      have moleculeExact :=
        p92ClassicalConstitutionRepresents_eq_localizedMoleculeGraph source molecule represents
      subst molecule
      have semanticValueExact :
          (source.molecule.semanticExactMancudeAverage attached).value =
            representedAtomicNumber.value :=
        (congrArg ExactAtomicNumber.value
          (source.molecule.semanticExactMancudeAverage_eq_independent attached)).trans
            valueExact.symm
      refine ⟨
        { atomCount := source.molecule.atomCount
          molecule := source.molecule.toLocalizedMoleculeGraph
          attached := attached
          representedAtomicNumber := source.molecule.semanticExactMancudeAverage attached },
        .semanticMancudeDigraphExactAverage source attached represents represented,
        ?_⟩
      exact .ofValueEq source.molecule.atomCount source.molecule.toLocalizedMoleculeGraph attached
        (source.molecule.semanticExactMancudeAverage attached) representedAtomicNumber
          semanticValueExact
  | rule1aMancude =>
      rcases observation with ⟨atomCount, molecule, leftAttached, rightAttached, outcome⟩
      rcases judged with ⟨represents, leftRepresented, rightRepresented, outcomeExact⟩
      change P92ClassicalConstitutionRepresents source molecule at represents
      have atomCountExact := represents.atomCount_exact
      subst atomCount
      have moleculeExact :=
        p92ClassicalConstitutionRepresents_eq_localizedMoleculeGraph source molecule represents
      subst molecule
      unfold ExactAtomicNumber.Outcome at outcomeExact
      have semanticOutcomeExact :
          @compare ℚ Rat.linearOrder.toOrd
            (source.molecule.semanticExactMancudeAverage leftAttached).value
            (source.molecule.semanticExactMancudeAverage rightAttached).value = outcome := by
        rw [source.molecule.semanticExactMancudeAverage_eq_independent leftAttached,
          source.molecule.semanticExactMancudeAverage_eq_independent rightAttached]
        exact outcomeExact
      rw [← semanticOutcomeExact]
      exact Next54P92Produces.of_witness
        (.semanticRule1aMancudeExactComparison source
          leftAttached rightAttached represents leftRepresented rightRepresented)

/-- Every independently judged saturated-ring path is an emitted member of the exhaustive
source-only atom-cycle/node-path/closing-duplicate program.  The reviewed path is used only to
prove completeness of that finite enumeration. -/
theorem p92Rule1aSaturatedRings_reverse_realization
    (source : AuthoritativeChemicalInput)
    (observation : P92Rule1aSaturatedRingsAuthorityObservation)
    (judged : p92Rule1aSaturatedRingsReference.Judges source observation) :
    Next54P92Produces .rule1aSaturatedRings source observation := by
  rcases observation with
    ⟨⟨atomCount, molecule, externalParent, ligand, graph⟩,
      ringAtoms, referenceNodes, referenceClosing⟩
  rcases judged with
    ⟨represented, referenceFaithful, saturated, referenceRealNodes, referencePath,
      referenceClosure⟩
  change P92CanonicalConstitutionRepresents source externalParent ligand molecule at represented
  change RootedDigraph.FaithfulExactExpansion molecule externalParent ligand
    graph.toRootedDigraph at referenceFaithful
  have atomCountExact := represented.atomCount_exact
  subst atomCount
  have moleculeExact :=
    p92CanonicalConstitutionRepresents_eq_canonicalLocalizedMoleculeGraph
      source externalParent ligand molecule represented
  subst molecule
  let production := p92SemanticExactDigraphObservation source externalParent ligand
  have rootBond :
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand).Adj
        externalParent ligand :=
    referenceFaithful.2.1
  have productionFaithful : production.Faithful :=
    p92SemanticExactDigraphObservation_faithful source externalParent ligand rootBond
  rcases RootedDigraph.faithfulExactExpansion_unique_up_to_iso
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand)
      externalParent ligand production.graph.toRootedDigraph graph.toRootedDigraph
      productionFaithful referenceFaithful with ⟨iso⟩
  let productionNodes := referenceNodes.map iso.toEquiv.symm
  let productionClosing := iso.toEquiv.symm referenceClosing
  have productionRealNodes : P92RealNodesRepresentAtoms production ringAtoms productionNodes :=
    p92RealNodesRepresentAtoms_map_equivSymm source.molecule.atomCount
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand) externalParent ligand
      production.graph graph iso ringAtoms referenceNodes referenceRealNodes
  have productionPath : P92DigraphNodePath production.graph.toRootedDigraph productionNodes :=
    p92DigraphNodePath_map_equivSymm iso referenceNodes referencePath
  have productionClosure : P92SelectedRingClosureWitness
      (p92Rule1aSaturatedRingsObservationOfGraph source.molecule.atomCount
        (p92CanonicalLocalizedMoleculeGraph source externalParent ligand) externalParent ligand
        production.graph ringAtoms productionNodes productionClosing) :=
    p92SelectedRingClosureWitness_transport source.molecule.atomCount
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand) externalParent ligand
      production.graph graph iso ringAtoms referenceNodes referenceClosing referenceClosure
  have atomsEmitted : ringAtoms ∈ p92CandidateRingAtomLists source.molecule.atomCount :=
    mem_p92CandidateRingAtomLists_of_nodup ringAtoms saturated.2.1
  have realizationEmitted : (productionNodes, productionClosing) ∈
      p92SemanticSaturatedRingRealizations source externalParent ligand ringAtoms :=
    (mem_p92SemanticSaturatedRingRealizations_iff source externalParent ligand ringAtoms
      productionNodes productionClosing).mpr
        ⟨productionRealNodes, productionPath, productionClosure⟩
  have ringNodesEq : productionNodes.map iso.toEquiv = referenceNodes := by
    have mapRoundtrip : ∀ nodes : List graph.Node,
        (nodes.map iso.toEquiv.symm).map iso.toEquiv = nodes := by
      intro nodes
      induction nodes with
      | nil => rfl
      | cons node nodes inductionHypothesis =>
          simp only [List.map_cons]
          rw [iso.toEquiv.apply_symm_apply, inductionHypothesis]
    exact mapRoundtrip referenceNodes
  have closingEq : iso.toEquiv productionClosing = referenceClosing := by
    exact iso.toEquiv.apply_symm_apply referenceClosing
  refine ⟨p92SemanticRule1aSaturatedRingsObservation source externalParent ligand ringAtoms
      (productionNodes, productionClosing), ?_, ?_⟩
  · exact .semanticRule1aSaturatedRings source externalParent ligand represented rootBond
      ringAtoms (productionNodes, productionClosing) atomsEmitted realizationEmitted saturated
  · exact .ofIso source.molecule.atomCount
      (p92CanonicalLocalizedMoleculeGraph source externalParent ligand) externalParent ligand
      production.graph graph iso ringAtoms productionNodes referenceNodes ringNodesEq
      productionClosing referenceClosing closingEq

/-- One unconditional dependent reverse-realization theorem for all eleven P-92 rows. -/
theorem next54P92_reverse_realization
    (row : Next54P92DigraphRule1aAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : row.reference.Observation)
    (judged : row.reference.Judges source observation) :
    Next54P92Produces row source observation := by
  cases row with
  | acyclicDigraph => exact p92AcyclicDigraph_reverse_realization source observation judged
  | multipleBondDigraph =>
      exact p92MultipleBondDigraph_reverse_realization source observation judged
  | cyclicDigraph => exact p92CyclicDigraph_reverse_realization source observation judged
  | mancudeDigraph =>
      exact p92MancudeFamily_reverse_realization .mancudeDigraph source observation judged
  | sphereExploration =>
      exact Next54P92Produces.of_witness
        (p92SphereExploration_reverse_realization source observation judged)
  | ruleExhaustivity =>
      exact Next54P92Produces.of_witness
        (p92RuleExhaustivity_reverse_realization source observation judged)
  | rule1aMultipleBondDuplicates =>
      exact p92Rule1aMultipleBondDuplicates_reverse_realization source observation judged
  | rule1aMancude =>
      exact p92MancudeFamily_reverse_realization .rule1aMancude source observation judged
  | rule1aSaturatedCompounds =>
      exact Next54P92Produces.of_witness
        (p92Rule1aSaturatedCompounds_reverse_realization source observation judged)
  | rule1aDoubleTripleBonds =>
      exact p92Rule1aDoubleTripleBonds_reverse_realization source observation judged
  | rule1aSaturatedRings =>
      exact p92Rule1aSaturatedRings_reverse_realization source observation judged

/-- Full P-92 family correctness is assumption-free: the fixed production relation equals the
independent reference for every one of the eleven rows. -/
theorem next54P92_production_iff_reference
    (row : Next54P92DigraphRule1aAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : row.reference.Observation) :
    Next54P92Produces row source observation ↔
      row.reference.Applicable source ∧ row.reference.Judges source observation := by
  constructor
  · exact Next54P92Produces.applicable_and_judged
  · intro expected
    exact next54P92_reverse_realization row source observation expected.2

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92SphereExploration_reverse_realization
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92RuleExhaustivity_reverse_realization
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92Rule1aSaturatedCompounds_reverse_realization
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92Produces.judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92Produces.applicable_and_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92MancudeFamily_reverse_realization
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92Rule1aSaturatedRings_reverse_realization
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P92_reverse_realization
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P92_production_iff_reference
