import TetraStereo.OneCenter.IUPACP92FamilyProductionSoundness

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Assumption-free nonvacuity for the P-92 digraph and Rule-1a family

The witnesses in this module are small, explicit constitutions.  They enter through the same
parser-to-semantic representation certificate as ordinary production inputs and are judged by
the dependent eleven-row production soundness theorem.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open DeclarativeCIP

namespace Next54P92DigraphRule1aNonvacuity

private def carbon : AtomSpec := AtomSpec.aliphatic Element.C

private def periodicCarbon : PeriodicElement :=
  { atomicNumber := 6, positive := by decide, atMost118 := by decide }

private def singleBondRaw : RawMolecule where
  atoms := [carbon, carbon, carbon]
  bonds :=
    [{ source := 0, target := 1, kind := .single },
     { source := 0, target := 2, kind := .single }]

private theorem singleBondRaw_embeds : singleBondRaw.toSemanticMolecule?.isSome = true := by
  decide

private def singleBondSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [{ element := periodicCarbon }, { element := periodicCarbon },
         { element := periodicCarbon }]
      interactions :=
        [{ participants := [0, 1], kind := .covalent 1 },
         { participants := [0, 2], kind := .covalent 1 }] }

private def singleBondCertificate :
    RawMolecule.P92ParserRepresentationCertificate singleBondSource singleBondRaw where
  embedded := by rfl
  wellFormed := by
    intro bond member
    simp [singleBondRaw] at member
    rcases member with rfl | rfl <;>
      simp [RawMolecule.BondEndpointsOK, RawMolecule.atomCount, singleBondRaw]
  bondRecordsUnique := by
    simp [RawMolecule.BondRecordsUnique, RawBond.edgeKey, singleBondRaw]
  rule2MassesKnown :=
    (RawMolecule.rule2MassesKnown?_eq_true_iff singleBondRaw).mp (by decide)
  classicalCovalent := by
    constructor
    · intro atom member
      simp [singleBondRaw, carbon] at member
      rcases member with rfl | rfl | rfl
      all_goals rfl
    · intro bond member
      simp [singleBondRaw] at member
      rcases member with rfl | rfl
      all_goals trivial

private theorem singleBondSource_wellFormed : singleBondSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff singleBondSource).mp
    (by decide)

private def singleCenter : Fin singleBondSource.molecule.atomCount := ⟨0, by decide⟩
private def singleLigand : Fin singleBondSource.molecule.atomCount := ⟨1, by decide⟩
private def singleSecondLigand : Fin singleBondSource.molecule.atomCount := ⟨2, by decide⟩

private theorem singleBondCanonicalRepresents :
    P92CanonicalConstitutionRepresents singleBondSource singleCenter singleLigand
      (p92CanonicalLocalizedMoleculeGraph singleBondSource singleCenter singleLigand) := by
  apply p92CanonicalConstitutionRepresents_canonicalLocalizedMoleculeGraph singleBondSource
    singleBondRaw.toMoleculeGraph
  exact singleBondCertificate.representsToMoleculeGraph

private theorem singleBondRootBond :
    (p92CanonicalLocalizedMoleculeGraph singleBondSource singleCenter singleLigand).Adj
      singleCenter singleLigand := by
  decide

private theorem singleBondHasNoRingDuplicate :
    (p92SemanticExactDigraphObservation singleBondSource singleCenter singleLigand).HasNoRingDuplicate := by
  classical
  intro node distance
  have faithful := p92SemanticExactDigraphObservation_faithful singleBondSource
    singleCenter singleLigand singleBondRootBond
  let graph :=
    (p92SemanticExactDigraphObservation singleBondSource singleCenter singleLigand).graph.toRootedDigraph
  have rootLabel := faithful.1.1.1
  obtain ⟨_addressing, multiplicities⟩ := faithful.1.2
  have noRootChild : ∀ child, ¬graph.child graph.root child := by
    intro child edge
    obtain ⟨atom, atomLabel⟩ := faithful.2.2.1 graph.root child edge
    have positive : 0 < RootedDigraph.ChildAtomCount graph graph.root atom := by
      letI : Fintype graph.Node := graph.nodeFintype
      unfold RootedDigraph.ChildAtomCount RootedDigraph.ChildCountWhere
      exact Nat.card_pos_iff.mpr ⟨⟨child, edge, atomLabel⟩, inferInstance⟩
    have counts := multiplicities graph.root singleLigand
      (by simpa [graph] using congrArg NodeLabel.atom? rootLabel)
      (by
        rw [congrArg NodeLabel.provenance rootLabel]
        trivial) atom
    fin_cases atom
    · have suppressed : RootedDigraph.SuppressedParentAtom graph singleCenter singleCenter graph.root :=
        Or.inl ⟨rfl, rfl⟩
      change 0 < RootedDigraph.ChildAtomCount graph graph.root singleCenter at positive
      have total : RootedDigraph.ChildAtomCount graph graph.root singleCenter =
          (p92CanonicalLocalizedMoleculeGraph singleBondSource singleCenter singleLigand).bond
              singleLigand singleCenter -
            (if RootedDigraph.SuppressedParentAtom graph singleCenter singleCenter graph.root
              then 1 else 0) := by
        simpa [graph, p92SemanticExactDigraphObservation] using counts.1
      have rootOrder :
          (p92CanonicalLocalizedMoleculeGraph singleBondSource singleCenter singleLigand).bond
            singleLigand singleCenter = 1 := by decide
      rw [total, rootOrder, if_pos suppressed] at positive
      omega
    · change 0 < RootedDigraph.ChildAtomCount graph graph.root singleLigand at positive
      have total : RootedDigraph.ChildAtomCount graph graph.root singleLigand =
          (p92CanonicalLocalizedMoleculeGraph singleBondSource singleCenter singleLigand).bond
              singleLigand singleLigand -
            (if RootedDigraph.SuppressedParentAtom graph singleCenter singleLigand graph.root
              then 1 else 0) := by
        simpa [graph, p92SemanticExactDigraphObservation] using counts.1
      rw [total,
        (p92CanonicalLocalizedMoleculeGraph singleBondSource singleCenter singleLigand).bond_self]
        at positive
      omega
    · change 0 < RootedDigraph.ChildAtomCount graph graph.root singleSecondLigand at positive
      have total : RootedDigraph.ChildAtomCount graph graph.root singleSecondLigand =
          (p92CanonicalLocalizedMoleculeGraph singleBondSource singleCenter singleLigand).bond
              singleLigand singleSecondLigand -
            (if RootedDigraph.SuppressedParentAtom graph singleCenter singleSecondLigand graph.root
              then 1 else 0) := by
        simpa [graph, p92SemanticExactDigraphObservation] using counts.1
      have noBond :
          (p92CanonicalLocalizedMoleculeGraph singleBondSource singleCenter singleLigand).bond
            singleLigand singleSecondLigand = 0 := by decide
      rw [total, noBond] at positive
      omega
  have nodeEqRoot : node = graph.root := by
    have reachable : Relation.ReflTransGen graph.child graph.root node := graph.reachable node
    induction reachable with
    | refl => rfl
    | tail path edge inductionHypothesis =>
        subst_vars
        exact (noRootChild _ edge).elim
  change (graph.label node).provenance ≠ NodeProvenance.ringDuplicate distance
  rw [nodeEqRoot, rootLabel]
  simp

private def singleBondAcyclicWitness :
    Next54P92ProductionWitness .acyclicDigraph singleBondSource
      (p92SemanticExactDigraphObservation singleBondSource singleCenter singleLigand) :=
  .semanticAcyclicDigraph singleBondSource singleCenter singleLigand
    singleBondCanonicalRepresents singleBondRootBond singleBondHasNoRingDuplicate

private theorem singleBondSecondRootBond :
    (p92CanonicalLocalizedMoleculeGraph singleBondSource singleCenter singleSecondLigand).Adj
      singleCenter singleSecondLigand := by
  decide

private def singleBondComparison : P92LigandComparisonAuthorityContext where
  left := p92SemanticExactDigraphObservation singleBondSource singleCenter singleLigand
  right := p92SemanticExactDigraphObservation singleBondSource singleCenter singleSecondLigand

private theorem singleBondComparison_ready : singleBondComparison.Ready singleBondSource := by
  refine ⟨⟨singleBondCanonicalRepresents, ?_⟩, by decide, by decide, ?_, ?_⟩
  · apply p92CanonicalConstitutionRepresents_canonicalLocalizedMoleculeGraph singleBondSource
      singleBondRaw.toMoleculeGraph
    exact singleBondCertificate.representsToMoleculeGraph
  · exact p92SemanticExactDigraphObservation_faithful singleBondSource singleCenter singleLigand
      singleBondRootBond
  · exact p92SemanticExactDigraphObservation_faithful singleBondSource singleCenter
      singleSecondLigand singleBondSecondRootBond

private def sphereWitness :
    Next54P92ProductionWitness .sphereExploration singleBondSource
      (p92ProductionSphereExplorationObservation singleBondComparison [] (fun _ => .eq)) :=
  .sphereExploration singleBondSource singleBondComparison [] (fun _ => .eq)
    singleBondComparison_ready (by simp) (by simp)

private def exhaustivityWitness :
    Next54P92ProductionWitness .ruleExhaustivity singleBondSource
      (p92ProductionRuleExhaustivityObservation singleBondComparison (fun _ => .eq)) :=
  .ruleExhaustivity singleBondSource singleBondComparison singleBondComparison_ready
    (fun _ => .eq)

private theorem singleCenter_saturated :
    P92AtomSaturated singleBondRaw.toMoleculeGraph singleCenter := by
  intro other
  fin_cases other <;> decide

private theorem singleLigand_saturated :
    P92AtomSaturated singleBondRaw.toMoleculeGraph singleLigand := by
  intro other
  fin_cases other <;> decide

private def saturatedCompoundsWitness :
    Next54P92ProductionWitness .rule1aSaturatedCompounds singleBondSource
      (p92ProductionRule1aSaturatedCompoundsObservation 3 singleBondRaw.toMoleculeGraph
        singleCenter singleLigand) :=
  .rule1aSaturatedCompounds singleBondSource 3 singleBondRaw.toMoleculeGraph
    singleBondCertificate.representsToMoleculeGraph singleCenter singleLigand
      singleCenter_saturated singleLigand_saturated

theorem acyclicDigraph_reference_nonvacuous :
    ∃ source, ∃ observation :
        Next54P92DigraphRule1aAuthorityRow.acyclicDigraph.reference.Observation,
      source.StructurallyWellFormed ∧
        Next54P92DigraphRule1aAuthorityRow.acyclicDigraph.reference.Applicable source ∧
        Next54P92DigraphRule1aAuthorityRow.acyclicDigraph.reference.Judges source observation := by
  exact ⟨singleBondSource, _, singleBondSource_wellFormed,
    singleBondAcyclicWitness.applicable_and_judged⟩

theorem sphereExploration_reference_nonvacuous :
    ∃ source, ∃ observation :
        Next54P92DigraphRule1aAuthorityRow.sphereExploration.reference.Observation,
      source.StructurallyWellFormed ∧
        Next54P92DigraphRule1aAuthorityRow.sphereExploration.reference.Applicable source ∧
        Next54P92DigraphRule1aAuthorityRow.sphereExploration.reference.Judges source observation := by
  exact ⟨singleBondSource, _, singleBondSource_wellFormed,
    sphereWitness.applicable_and_judged⟩

theorem ruleExhaustivity_reference_nonvacuous :
    ∃ source, ∃ observation :
        Next54P92DigraphRule1aAuthorityRow.ruleExhaustivity.reference.Observation,
      source.StructurallyWellFormed ∧
        Next54P92DigraphRule1aAuthorityRow.ruleExhaustivity.reference.Applicable source ∧
        Next54P92DigraphRule1aAuthorityRow.ruleExhaustivity.reference.Judges source observation := by
  exact ⟨singleBondSource, _, singleBondSource_wellFormed,
    exhaustivityWitness.applicable_and_judged⟩

theorem saturatedCompounds_reference_nonvacuous :
    ∃ source, ∃ observation :
        Next54P92DigraphRule1aAuthorityRow.rule1aSaturatedCompounds.reference.Observation,
      source.StructurallyWellFormed ∧
        Next54P92DigraphRule1aAuthorityRow.rule1aSaturatedCompounds.reference.Applicable source ∧
        Next54P92DigraphRule1aAuthorityRow.rule1aSaturatedCompounds.reference.Judges source observation := by
  exact ⟨singleBondSource, _, singleBondSource_wellFormed,
    saturatedCompoundsWitness.applicable_and_judged⟩

/-- Uniform family-level nonvacuity statement. -/
def ReferenceNonvacuous (row : Next54P92DigraphRule1aAuthorityRow) : Prop :=
  ∃ source, ∃ observation : row.reference.Observation,
    source.StructurallyWellFormed ∧ row.reference.Applicable source ∧
      row.reference.Judges source observation

/-- A fresh molecular neighbor of the ligand is represented by a concrete real child of the
root in every faithful expansion. -/
private theorem exists_real_child_at_root
    {atomCount : Nat} (molecule : MoleculeGraph (Fin atomCount))
    (externalParent ligand target : Fin atomCount) (graph : RootedDigraph (Fin atomCount))
    (faithful : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand graph)
    (adjacent : molecule.Adj ligand target) (target_ne_external : target ≠ externalParent) :
    ∃ child, graph.child graph.root child ∧
      graph.label child = ⟨some target, NodeProvenance.realAtom⟩ := by
  classical
  have rootLabel := faithful.1.1.1
  obtain ⟨addressing, multiplicities⟩ := faithful.1.2
  have notBranch :
      ¬RootedDigraph.BranchAncestorAtom graph externalParent target graph.root := by
    simp [RootedDigraph.BranchAncestorAtom, target_ne_external,
      addressing.not_ancestorAtom_root target]
  have counts := multiplicities graph.root ligand
    (by simpa using congrArg NodeLabel.atom? rootLabel)
    (by rw [congrArg NodeLabel.provenance rootLabel]; trivial) target
  have countEq : RootedDigraph.ChildAtomProvenanceCount graph graph.root target
      RootedDigraph.ProvenanceRealAtom = 1 := by
    simpa [adjacent, notBranch] using counts.2.2.2
  have positive : 0 < RootedDigraph.ChildAtomProvenanceCount graph graph.root target
      RootedDigraph.ProvenanceRealAtom := by omega
  letI : Fintype graph.Node := graph.nodeFintype
  unfold RootedDigraph.ChildAtomProvenanceCount RootedDigraph.ChildCountWhere at positive
  obtain ⟨witness⟩ := Nat.card_pos_iff.mp positive
  rcases witness with ⟨child, edge, atomLabel, provenance⟩
  cases labelEq : graph.label child with
  | mk atom? actualProvenance =>
      cases atom? with
      | none => simp [labelEq] at atomLabel
      | some atom =>
          rw [labelEq] at atomLabel
          have atomEq : atom = target := Option.some.inj atomLabel
          subst atom
          cases actualProvenance with
          | realAtom => exact ⟨child, edge, labelEq⟩
          | multipleBondDuplicate distance =>
              simp [labelEq, RootedDigraph.ProvenanceRealAtom] at provenance
          | ringDuplicate distance =>
              simp [labelEq, RootedDigraph.ProvenanceRealAtom] at provenance
          | phantom => simp [labelEq, RootedDigraph.ProvenanceRealAtom] at provenance
          | lonePair => simp [labelEq, RootedDigraph.ProvenanceRealAtom] at provenance
          | auxiliary => simp [labelEq, RootedDigraph.ProvenanceRealAtom] at provenance

private theorem exists_real_child
    {atomCount : Nat} (molecule : MoleculeGraph (Fin atomCount))
    (externalParent ligand parentAtom target : Fin atomCount)
    (graph : RootedDigraph (Fin atomCount))
    (faithful : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand graph)
    (parent : graph.Node)
    (parentLabel : graph.label parent = ⟨some parentAtom, NodeProvenance.realAtom⟩)
    (adjacent : molecule.Adj parentAtom target)
    (notBranch : ¬RootedDigraph.BranchAncestorAtom graph externalParent target parent) :
    ∃ child, graph.child parent child ∧
      graph.label child = ⟨some target, NodeProvenance.realAtom⟩ := by
  classical
  obtain ⟨_addressing, multiplicities⟩ := faithful.1.2
  have counts := multiplicities parent parentAtom
    (by simpa using congrArg NodeLabel.atom? parentLabel)
    (by rw [congrArg NodeLabel.provenance parentLabel]; trivial) target
  have countEq : RootedDigraph.ChildAtomProvenanceCount graph parent target
      RootedDigraph.ProvenanceRealAtom = 1 := by
    simpa [adjacent, notBranch] using counts.2.2.2
  have positive : 0 < RootedDigraph.ChildAtomProvenanceCount graph parent target
      RootedDigraph.ProvenanceRealAtom := by omega
  letI : Fintype graph.Node := graph.nodeFintype
  unfold RootedDigraph.ChildAtomProvenanceCount RootedDigraph.ChildCountWhere at positive
  obtain ⟨witness⟩ := Nat.card_pos_iff.mp positive
  rcases witness with ⟨child, edge, atomLabel, provenance⟩
  cases labelEq : graph.label child with
  | mk atom? actualProvenance =>
      cases atom? with
      | none => simp [labelEq] at atomLabel
      | some atom =>
          rw [labelEq] at atomLabel
          have atomEq : atom = target := Option.some.inj atomLabel
          subst atom
          cases actualProvenance with
          | realAtom => exact ⟨child, edge, labelEq⟩
          | multipleBondDuplicate distance =>
              simp [labelEq, RootedDigraph.ProvenanceRealAtom] at provenance
          | ringDuplicate distance =>
              simp [labelEq, RootedDigraph.ProvenanceRealAtom] at provenance
          | phantom => simp [labelEq, RootedDigraph.ProvenanceRealAtom] at provenance
          | lonePair => simp [labelEq, RootedDigraph.ProvenanceRealAtom] at provenance
          | auxiliary => simp [labelEq, RootedDigraph.ProvenanceRealAtom] at provenance

private theorem not_ancestor_atom_at_single_child_of_root
    {Atom : Type} (graph : RootedDigraph Atom) (addressing : graph.Addressing)
    (node : graph.Node) (edge : graph.child graph.root node)
    (rootAtom target : Atom)
    (rootLabel : (graph.label graph.root).atom? = some rootAtom)
    (different : target ≠ rootAtom) :
    ¬RootedDigraph.AncestorAtom graph node target := by
  rintro ⟨ancestor, path, ancestorLabel⟩
  obtain ⟨lastParent, prefixPath, lastEdge⟩ := Relation.TransGen.tail'_iff.mp path
  have lastParentEq : lastParent = graph.root := addressing.parent_unique lastEdge edge
  subst lastParent
  cases prefixPath with
  | refl =>
      have same : target = rootAtom := Option.some.inj (ancestorLabel.symm.trans rootLabel)
      exact different same
  | tail earlierPath prefixEdge =>
      exact addressing.not_child_root _ prefixEdge

/-- A bonded ancestor which is not the suppressed immediate-parent occurrence produces one
concrete ring-duplicate child. -/
private theorem exists_ring_duplicate_child
    {atomCount : Nat} (molecule : MoleculeGraph (Fin atomCount))
    (externalParent ligand parentAtom target : Fin atomCount)
    (graph : RootedDigraph (Fin atomCount))
    (faithful : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand graph)
    (parent : graph.Node)
    (parentLabel : graph.label parent = ⟨some parentAtom, NodeProvenance.realAtom⟩)
    (adjacent : molecule.Adj parentAtom target)
    (ancestor : RootedDigraph.BranchAncestorAtom graph externalParent target parent)
    (notSuppressed :
      ¬RootedDigraph.SuppressedParentAtom graph externalParent target parent) :
    ∃ child distance, graph.child parent child ∧
      graph.label child = ⟨some target, NodeProvenance.ringDuplicate distance⟩ := by
  classical
  obtain ⟨_addressing, multiplicities⟩ := faithful.1.2
  have counts := multiplicities parent parentAtom
    (by simpa using congrArg NodeLabel.atom? parentLabel)
    (by rw [congrArg NodeLabel.provenance parentLabel]; trivial) target
  have countEq : RootedDigraph.ChildAtomProvenanceCount graph parent target
      RootedDigraph.ProvenanceRingDuplicate = 1 := by
    simpa [adjacent, ancestor, notSuppressed] using counts.2.2.1
  have positive : 0 < RootedDigraph.ChildAtomProvenanceCount graph parent target
      RootedDigraph.ProvenanceRingDuplicate := by omega
  letI : Fintype graph.Node := graph.nodeFintype
  unfold RootedDigraph.ChildAtomProvenanceCount RootedDigraph.ChildCountWhere at positive
  obtain ⟨witness⟩ := Nat.card_pos_iff.mp positive
  rcases witness with ⟨child, edge, atomLabel, provenance⟩
  cases labelEq : graph.label child with
  | mk atom? actualProvenance =>
      cases atom? with
      | none => simp [labelEq] at atomLabel
      | some atom =>
          rw [labelEq] at atomLabel
          have atomEq : atom = target := Option.some.inj atomLabel
          subst atom
          cases actualProvenance with
          | ringDuplicate distance => exact ⟨child, distance, edge, labelEq⟩
          | realAtom => simp [labelEq, RootedDigraph.ProvenanceRingDuplicate] at provenance
          | multipleBondDuplicate distance =>
              simp [labelEq, RootedDigraph.ProvenanceRingDuplicate] at provenance
          | phantom => simp [labelEq, RootedDigraph.ProvenanceRingDuplicate] at provenance
          | lonePair => simp [labelEq, RootedDigraph.ProvenanceRingDuplicate] at provenance
          | auxiliary => simp [labelEq, RootedDigraph.ProvenanceRingDuplicate] at provenance

/-! ## Multiple-bond seed and its two bulk consequences -/

private def doubleBondRaw : RawMolecule where
  atoms := [carbon, carbon]
  bonds := [{ source := 0, target := 1, kind := .double }]

private def doubleBondSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [{ element := periodicCarbon }, { element := periodicCarbon }]
      interactions := [{ participants := [0, 1], kind := .covalent 2 }] }

private def doubleBondCertificate :
    RawMolecule.P92ParserRepresentationCertificate doubleBondSource doubleBondRaw where
  embedded := by rfl
  wellFormed := by
    intro bond member
    simp [doubleBondRaw] at member
    subst bond
    simp [RawMolecule.BondEndpointsOK, RawMolecule.atomCount, doubleBondRaw]
  bondRecordsUnique := by simp [RawMolecule.BondRecordsUnique, doubleBondRaw]
  rule2MassesKnown :=
    (RawMolecule.rule2MassesKnown?_eq_true_iff doubleBondRaw).mp (by decide)
  classicalCovalent := by
    constructor
    · intro atom member
      simp [doubleBondRaw, carbon] at member
      rcases member with rfl | rfl ; rfl
    · intro bond member
      simp [doubleBondRaw] at member
      subst bond
      trivial

private theorem doubleBondSource_wellFormed : doubleBondSource.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff doubleBondSource).mp
    (by decide)

private def doubleCenter : Fin doubleBondSource.molecule.atomCount := ⟨0, by decide⟩
private def doubleLigand : Fin doubleBondSource.molecule.atomCount := ⟨1, by decide⟩

private theorem doubleBondCanonicalRepresents :
    P92CanonicalConstitutionRepresents doubleBondSource doubleCenter doubleLigand
      (p92CanonicalLocalizedMoleculeGraph doubleBondSource doubleCenter doubleLigand) := by
  apply p92CanonicalConstitutionRepresents_canonicalLocalizedMoleculeGraph doubleBondSource
    doubleBondRaw.toMoleculeGraph
  exact doubleBondCertificate.representsToMoleculeGraph

private theorem doubleBondRootBond :
    (p92CanonicalLocalizedMoleculeGraph doubleBondSource doubleCenter doubleLigand).Adj
      doubleCenter doubleLigand := by
  decide

private theorem doubleBondHasMultipleBondDuplicate :
    (p92SemanticExactDigraphObservation doubleBondSource doubleCenter doubleLigand).HasMultipleBondDuplicate := by
  classical
  let observation := p92SemanticExactDigraphObservation doubleBondSource doubleCenter doubleLigand
  let graph := observation.graph.toRootedDigraph
  have faithful := p92SemanticExactDigraphObservation_faithful doubleBondSource
    doubleCenter doubleLigand doubleBondRootBond
  have rootLabel := faithful.1.1.1
  obtain ⟨_addressing, multiplicities⟩ := faithful.1.2
  have counts := multiplicities graph.root doubleLigand
    (by simpa [graph, observation] using congrArg NodeLabel.atom? rootLabel)
    (by rw [congrArg NodeLabel.provenance rootLabel]; trivial) doubleCenter
  have countEq : RootedDigraph.ChildAtomProvenanceCount graph graph.root doubleCenter
      RootedDigraph.ProvenanceMultipleBondDuplicate = 1 := by
    have order : observation.molecule.bond doubleLigand doubleCenter = 2 := by decide
    simpa [order] using counts.2.1
  have positive : 0 < RootedDigraph.ChildAtomProvenanceCount graph graph.root doubleCenter
      RootedDigraph.ProvenanceMultipleBondDuplicate := by omega
  letI : Fintype graph.Node := graph.nodeFintype
  unfold RootedDigraph.ChildAtomProvenanceCount RootedDigraph.ChildCountWhere at positive
  obtain ⟨witness⟩ := Nat.card_pos_iff.mp positive
  rcases witness with ⟨node, _edge, _atomLabel, provenance⟩
  cases provenanceEq : (graph.label node).provenance with
  | realAtom => simp [RootedDigraph.ProvenanceMultipleBondDuplicate, provenanceEq] at provenance
  | ringDuplicate distance =>
      simp [RootedDigraph.ProvenanceMultipleBondDuplicate, provenanceEq] at provenance
  | multipleBondDuplicate distance =>
      exact ⟨node, distance, by simpa [graph, observation] using provenanceEq⟩
  | phantom => simp [RootedDigraph.ProvenanceMultipleBondDuplicate, provenanceEq] at provenance
  | lonePair => simp [RootedDigraph.ProvenanceMultipleBondDuplicate, provenanceEq] at provenance
  | auxiliary => simp [RootedDigraph.ProvenanceMultipleBondDuplicate, provenanceEq] at provenance

private def doubleBondDigraphWitness :
    Next54P92ProductionWitness .multipleBondDigraph doubleBondSource
      (p92SemanticExactDigraphObservation doubleBondSource doubleCenter doubleLigand) :=
  .semanticMultipleBondDigraph doubleBondSource doubleCenter doubleLigand
    doubleBondCanonicalRepresents doubleBondRootBond doubleBondHasMultipleBondDuplicate

private theorem doubleRootLabel :
    (p92SemanticExactDigraphObservation doubleBondSource doubleCenter doubleLigand).graph.label
        (p92SemanticExactDigraphObservation doubleBondSource doubleCenter doubleLigand).graph.root =
      ⟨some doubleLigand, NodeProvenance.realAtom⟩ := by
  have faithful := p92SemanticExactDigraphObservation_faithful doubleBondSource
    doubleCenter doubleLigand doubleBondRootBond
  exact faithful.1.1.1

private theorem doubleOrderAtRoot :
    1 < (p92CanonicalLocalizedMoleculeGraph doubleBondSource doubleCenter doubleLigand).bond
      doubleLigand doubleCenter := by decide

private def multipleBondDuplicatesWitness :
    Next54P92ProductionWitness .rule1aMultipleBondDuplicates doubleBondSource
      (p92SemanticRule1aMultipleBondDuplicatesObservation doubleBondSource doubleCenter
        doubleLigand
        (p92SemanticExactDigraphObservation doubleBondSource doubleCenter doubleLigand).graph.root
        doubleLigand doubleCenter) :=
  .semanticRule1aMultipleBondDuplicates doubleBondSource doubleCenter doubleLigand
    doubleBondCanonicalRepresents doubleBondRootBond _ doubleLigand doubleCenter
      doubleRootLabel doubleOrderAtRoot

theorem multipleBondDigraph_reference_nonvacuous :
    ReferenceNonvacuous .multipleBondDigraph := by
  exact ⟨doubleBondSource, _, doubleBondSource_wellFormed,
    doubleBondDigraphWitness.applicable_and_judged⟩

theorem multipleBondDuplicates_reference_nonvacuous :
    ReferenceNonvacuous .rule1aMultipleBondDuplicates := by
  exact ⟨doubleBondSource, _, doubleBondSource_wellFormed,
    multipleBondDuplicatesWitness.applicable_and_judged⟩

/-! ## A root with a forward double bond -/

private def forwardDoubleRaw : RawMolecule where
  atoms := [carbon, carbon, carbon]
  bonds :=
    [{ source := 0, target := 1, kind := .single },
     { source := 1, target := 2, kind := .double }]

private def forwardDoubleSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [{ element := periodicCarbon }, { element := periodicCarbon },
          { element := periodicCarbon }]
      interactions :=
        [{ participants := [0, 1], kind := .covalent 1 },
         { participants := [1, 2], kind := .covalent 2 }] }

private def forwardDoubleCertificate :
    RawMolecule.P92ParserRepresentationCertificate forwardDoubleSource forwardDoubleRaw where
  embedded := by rfl
  wellFormed := by
    intro bond member
    simp [forwardDoubleRaw] at member
    rcases member with rfl | rfl <;>
      simp [RawMolecule.BondEndpointsOK, RawMolecule.atomCount, forwardDoubleRaw]
  bondRecordsUnique := by
    simp [RawMolecule.BondRecordsUnique, forwardDoubleRaw, RawBond.edgeKey]
  rule2MassesKnown :=
    (RawMolecule.rule2MassesKnown?_eq_true_iff forwardDoubleRaw).mp (by decide)
  classicalCovalent := by
    constructor
    · intro atom member
      simp [forwardDoubleRaw, carbon] at member
      rcases member with rfl | rfl | rfl ; rfl
    · intro bond member
      simp [forwardDoubleRaw] at member
      rcases member with rfl | rfl <;> trivial

private theorem forwardDoubleSource_wellFormed : forwardDoubleSource.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff forwardDoubleSource).mp
    (by decide)

private def forwardCenter : Fin forwardDoubleSource.molecule.atomCount := ⟨0, by decide⟩
private def forwardLigand : Fin forwardDoubleSource.molecule.atomCount := ⟨1, by decide⟩
private def forwardAtom : Fin forwardDoubleSource.molecule.atomCount := ⟨2, by decide⟩

private theorem forwardCanonicalRepresents :
    P92CanonicalConstitutionRepresents forwardDoubleSource forwardCenter forwardLigand
      (p92CanonicalLocalizedMoleculeGraph forwardDoubleSource forwardCenter forwardLigand) := by
  apply p92CanonicalConstitutionRepresents_canonicalLocalizedMoleculeGraph forwardDoubleSource
    forwardDoubleRaw.toMoleculeGraph
  exact forwardDoubleCertificate.representsToMoleculeGraph

private theorem forwardRootBond :
    (p92CanonicalLocalizedMoleculeGraph forwardDoubleSource forwardCenter forwardLigand).Adj
      forwardCenter forwardLigand := by decide

private theorem forwardBond :
    (p92CanonicalLocalizedMoleculeGraph forwardDoubleSource forwardCenter forwardLigand).Adj
      forwardLigand forwardAtom := by decide

private theorem forwardAtom_ne_center : forwardAtom ≠ forwardCenter := by decide

private theorem exists_forwardRealChild :
    ∃ child,
      (p92SemanticExactDigraphObservation forwardDoubleSource forwardCenter forwardLigand).graph.child
        (p92SemanticExactDigraphObservation forwardDoubleSource forwardCenter forwardLigand).graph.root
        child ∧
      (p92SemanticExactDigraphObservation forwardDoubleSource forwardCenter forwardLigand).graph.label
        child = ⟨some forwardAtom, NodeProvenance.realAtom⟩ := by
  let observation := p92SemanticExactDigraphObservation forwardDoubleSource forwardCenter forwardLigand
  have faithful := p92SemanticExactDigraphObservation_faithful forwardDoubleSource
    forwardCenter forwardLigand forwardRootBond
  simpa [observation] using exists_real_child_at_root observation.molecule forwardCenter
    forwardLigand forwardAtom observation.graph.toRootedDigraph faithful forwardBond
      forwardAtom_ne_center

private noncomputable def forwardRealChild :
    (p92SemanticExactDigraphObservation forwardDoubleSource forwardCenter forwardLigand).graph.Node :=
  Classical.choose exists_forwardRealChild

private theorem forwardRealChild_label :
    (p92SemanticExactDigraphObservation forwardDoubleSource forwardCenter forwardLigand).graph.label
        forwardRealChild = ⟨some forwardAtom, NodeProvenance.realAtom⟩ :=
  (Classical.choose_spec exists_forwardRealChild).2

private theorem forwardRootLabel :
    (p92SemanticExactDigraphObservation forwardDoubleSource forwardCenter forwardLigand).graph.label
        (p92SemanticExactDigraphObservation forwardDoubleSource forwardCenter forwardLigand).graph.root =
      ⟨some forwardLigand, NodeProvenance.realAtom⟩ :=
  (p92SemanticExactDigraphObservation_faithful forwardDoubleSource forwardCenter forwardLigand
    forwardRootBond).1.1.1

private theorem forwardBondOrder :
    (p92CanonicalLocalizedMoleculeGraph forwardDoubleSource forwardCenter forwardLigand).bond
        forwardLigand forwardAtom = 2 := by decide

private def doubleTripleBondsWitness :
    Next54P92ProductionWitness .rule1aDoubleTripleBonds forwardDoubleSource
      (p92SemanticRule1aDoubleTripleBondsObservation forwardDoubleSource forwardCenter
        forwardLigand
        (p92SemanticExactDigraphObservation forwardDoubleSource forwardCenter forwardLigand).graph.root
        forwardRealChild forwardLigand forwardAtom) :=
  .semanticRule1aDoubleTripleBonds forwardDoubleSource forwardCenter forwardLigand
    forwardCanonicalRepresents forwardRootBond _ _ forwardLigand forwardAtom
      forwardRootLabel forwardRealChild_label (Or.inl forwardBondOrder)

theorem doubleTripleBonds_reference_nonvacuous :
    ReferenceNonvacuous .rule1aDoubleTripleBonds := by
  exact ⟨forwardDoubleSource, _, forwardDoubleSource_wellFormed,
    doubleTripleBondsWitness.applicable_and_judged⟩

/-! ## Three-membered cycle seed -/

private def triangleRaw : RawMolecule where
  atoms := [carbon, carbon, carbon]
  bonds :=
    [{ source := 0, target := 1, kind := .single },
     { source := 1, target := 2, kind := .single },
     { source := 2, target := 0, kind := .single }]

private def triangleSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [{ element := periodicCarbon }, { element := periodicCarbon },
          { element := periodicCarbon }]
      interactions :=
        [{ participants := [0, 1], kind := .covalent 1 },
         { participants := [1, 2], kind := .covalent 1 },
         { participants := [2, 0], kind := .covalent 1 }] }

private def triangleCertificate :
    RawMolecule.P92ParserRepresentationCertificate triangleSource triangleRaw where
  embedded := by rfl
  wellFormed := by
    intro bond member
    simp [triangleRaw] at member
    rcases member with rfl | rfl | rfl <;>
      simp [RawMolecule.BondEndpointsOK, RawMolecule.atomCount, triangleRaw]
  bondRecordsUnique := by
    simp [RawMolecule.BondRecordsUnique, triangleRaw, RawBond.edgeKey]
  rule2MassesKnown :=
    (RawMolecule.rule2MassesKnown?_eq_true_iff triangleRaw).mp (by decide)
  classicalCovalent := by
    constructor
    · intro atom member
      simp [triangleRaw, carbon] at member
      rcases member with rfl | rfl | rfl ; rfl
    · intro bond member
      simp [triangleRaw] at member
      rcases member with rfl | rfl | rfl <;> trivial

private theorem triangleSource_wellFormed : triangleSource.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff triangleSource).mp
    (by decide)

private def triangleCenter : Fin triangleSource.molecule.atomCount := ⟨0, by decide⟩
private def triangleLigand : Fin triangleSource.molecule.atomCount := ⟨1, by decide⟩
private def triangleNext : Fin triangleSource.molecule.atomCount := ⟨2, by decide⟩

private theorem triangleCanonicalRepresents :
    P92CanonicalConstitutionRepresents triangleSource triangleCenter triangleLigand
      (p92CanonicalLocalizedMoleculeGraph triangleSource triangleCenter triangleLigand) := by
  apply p92CanonicalConstitutionRepresents_canonicalLocalizedMoleculeGraph triangleSource
    triangleRaw.toMoleculeGraph
  exact triangleCertificate.representsToMoleculeGraph

private theorem triangleRootBond :
    (p92CanonicalLocalizedMoleculeGraph triangleSource triangleCenter triangleLigand).Adj
      triangleCenter triangleLigand := by decide

private theorem triangleForwardBond :
    (p92CanonicalLocalizedMoleculeGraph triangleSource triangleCenter triangleLigand).Adj
      triangleLigand triangleNext := by decide

private theorem triangleClosingBond :
    (p92CanonicalLocalizedMoleculeGraph triangleSource triangleCenter triangleLigand).Adj
      triangleNext triangleCenter := by decide

private theorem triangleNext_ne_center : triangleNext ≠ triangleCenter := by decide

private theorem triangle_hasRingDuplicate :
    (p92SemanticExactDigraphObservation triangleSource triangleCenter triangleLigand).HasRingDuplicate := by
  classical
  let observation := p92SemanticExactDigraphObservation triangleSource triangleCenter triangleLigand
  let graph := observation.graph.toRootedDigraph
  have faithful := p92SemanticExactDigraphObservation_faithful triangleSource
    triangleCenter triangleLigand triangleRootBond
  obtain ⟨addressing, _multiplicities⟩ := faithful.1.2
  obtain ⟨nextNode, nextEdge, nextLabel⟩ := exists_real_child_at_root
    observation.molecule triangleCenter triangleLigand triangleNext graph faithful
      triangleForwardBond triangleNext_ne_center
  have nextNeRoot : nextNode ≠ graph.root := by
    intro same
    subst nextNode
    exact addressing.not_child_root graph.root nextEdge
  have notParentCenter :
      ¬RootedDigraph.ParentAtom graph nextNode triangleCenter := by
    rintro ⟨parent, parentEdge, parentAtom⟩
    have parentEq : parent = graph.root := addressing.parent_unique parentEdge nextEdge
    subst parent
    have rootLabel := faithful.1.1.1
    have atomConflict : triangleLigand = triangleCenter := by
      apply Option.some.inj
      exact (congrArg NodeLabel.atom? rootLabel).symm.trans parentAtom
    exact (by decide : triangleLigand ≠ triangleCenter) atomConflict
  have notSuppressed :
      ¬RootedDigraph.SuppressedParentAtom graph triangleCenter triangleCenter nextNode := by
    simp [RootedDigraph.SuppressedParentAtom, nextNeRoot, notParentCenter]
  obtain ⟨duplicate, distance, _edge, duplicateLabel⟩ :=
    exists_ring_duplicate_child observation.molecule triangleCenter triangleLigand triangleNext
      triangleCenter graph faithful nextNode nextLabel triangleClosingBond (Or.inl rfl)
        notSuppressed
  exact ⟨duplicate, distance, by
    have provenance := congrArg NodeLabel.provenance duplicateLabel
    simpa [graph, observation] using provenance⟩

private def cyclicDigraphWitness :
    Next54P92ProductionWitness .cyclicDigraph triangleSource
      (p92SemanticExactDigraphObservation triangleSource triangleCenter triangleLigand) :=
  .semanticCyclicDigraph triangleSource triangleCenter triangleLigand
    triangleCanonicalRepresents triangleRootBond triangle_hasRingDuplicate

theorem cyclicDigraph_reference_nonvacuous : ReferenceNonvacuous .cyclicDigraph := by
  exact ⟨triangleSource, _, triangleSource_wellFormed,
    cyclicDigraphWitness.applicable_and_judged⟩

/-! ## Source-attached saturated ring seed -/

private def attachedTriangleRaw : RawMolecule where
  atoms := [carbon, carbon, carbon, carbon]
  bonds :=
    [{ source := 0, target := 1, kind := .single },
     { source := 1, target := 2, kind := .single },
     { source := 2, target := 3, kind := .single },
     { source := 3, target := 1, kind := .single }]

private def attachedTriangleSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 4 { element := periodicCarbon }
      interactions :=
        [{ participants := [0, 1], kind := .covalent 1 },
         { participants := [1, 2], kind := .covalent 1 },
         { participants := [2, 3], kind := .covalent 1 },
         { participants := [3, 1], kind := .covalent 1 }] }

private def attachedTriangleCertificate :
    RawMolecule.P92ParserRepresentationCertificate attachedTriangleSource attachedTriangleRaw where
  embedded := by rfl
  wellFormed := by
    intro bond member
    simp [attachedTriangleRaw] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [RawMolecule.BondEndpointsOK, RawMolecule.atomCount, attachedTriangleRaw]
  bondRecordsUnique := by
    simp [RawMolecule.BondRecordsUnique, attachedTriangleRaw, RawBond.edgeKey]
  rule2MassesKnown :=
    (RawMolecule.rule2MassesKnown?_eq_true_iff attachedTriangleRaw).mp (by decide)
  classicalCovalent := by
    constructor
    · intro atom member
      simp [attachedTriangleRaw, carbon] at member
      rcases member with rfl | rfl | rfl | rfl ; rfl
    · intro bond member
      simp [attachedTriangleRaw] at member
      rcases member with rfl | rfl | rfl | rfl <;> trivial

private theorem attachedTriangleSource_wellFormed :
    attachedTriangleSource.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff attachedTriangleSource).mp
    (by decide)

private def attachedCenter : Fin attachedTriangleSource.molecule.atomCount := ⟨0, by decide⟩
private def ringFirst : Fin attachedTriangleSource.molecule.atomCount := ⟨1, by decide⟩
private def ringSecond : Fin attachedTriangleSource.molecule.atomCount := ⟨2, by decide⟩
private def ringThird : Fin attachedTriangleSource.molecule.atomCount := ⟨3, by decide⟩

private theorem attachedTriangleCanonicalRepresents :
    P92CanonicalConstitutionRepresents attachedTriangleSource attachedCenter ringFirst
      (p92CanonicalLocalizedMoleculeGraph attachedTriangleSource attachedCenter ringFirst) := by
  apply p92CanonicalConstitutionRepresents_canonicalLocalizedMoleculeGraph attachedTriangleSource
    attachedTriangleRaw.toMoleculeGraph
  exact attachedTriangleCertificate.representsToMoleculeGraph

private theorem attachedRootBond :
    (p92CanonicalLocalizedMoleculeGraph attachedTriangleSource attachedCenter ringFirst).Adj
      attachedCenter ringFirst := by decide

private theorem ringFirstSecondBond :
    (p92CanonicalLocalizedMoleculeGraph attachedTriangleSource attachedCenter ringFirst).Adj
      ringFirst ringSecond := by decide

private theorem ringSecondThirdBond :
    (p92CanonicalLocalizedMoleculeGraph attachedTriangleSource attachedCenter ringFirst).Adj
      ringSecond ringThird := by decide

private theorem ringThirdFirstBond :
    (p92CanonicalLocalizedMoleculeGraph attachedTriangleSource attachedCenter ringFirst).Adj
      ringThird ringFirst := by decide

private theorem exists_ringSecondNode :
    ∃ node,
      (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst).graph.child
        (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst).graph.root
        node ∧
      (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst).graph.label
        node = ⟨some ringSecond, NodeProvenance.realAtom⟩ := by
  let observation := p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst
  have faithful := p92SemanticExactDigraphObservation_faithful attachedTriangleSource
    attachedCenter ringFirst attachedRootBond
  simpa [observation] using exists_real_child_at_root observation.molecule attachedCenter ringFirst
    ringSecond observation.graph.toRootedDigraph faithful ringFirstSecondBond (by decide)

private noncomputable def ringSecondNode := Classical.choose exists_ringSecondNode
private def ringSecondNode_edge := (Classical.choose_spec exists_ringSecondNode).1
private def ringSecondNode_label := (Classical.choose_spec exists_ringSecondNode).2

private theorem exists_ringThirdNode :
    ∃ node,
      (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst).graph.child
        ringSecondNode node ∧
      (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst).graph.label
        node = ⟨some ringThird, NodeProvenance.realAtom⟩ := by
  let observation := p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst
  let graph := observation.graph.toRootedDigraph
  have faithful := p92SemanticExactDigraphObservation_faithful attachedTriangleSource
    attachedCenter ringFirst attachedRootBond
  obtain ⟨addressing, _multiplicities⟩ := faithful.1.2
  have noAncestor : ¬RootedDigraph.AncestorAtom graph ringSecondNode ringThird :=
    not_ancestor_atom_at_single_child_of_root graph addressing ringSecondNode
      ringSecondNode_edge ringFirst ringThird
      (by simpa [graph, observation] using congrArg NodeLabel.atom? faithful.1.1.1) (by decide)
  have notBranch :
      ¬RootedDigraph.BranchAncestorAtom graph attachedCenter ringThird ringSecondNode := by
    simp [RootedDigraph.BranchAncestorAtom, noAncestor]
    decide
  simpa [graph, observation] using exists_real_child observation.molecule attachedCenter ringFirst
    ringSecond ringThird graph faithful ringSecondNode ringSecondNode_label ringSecondThirdBond
      notBranch

private noncomputable def ringThirdNode := Classical.choose exists_ringThirdNode
private def ringThirdNode_edge := (Classical.choose_spec exists_ringThirdNode).1
private def ringThirdNode_label := (Classical.choose_spec exists_ringThirdNode).2

private theorem exists_ringClosingDuplicate :
    ∃ node distance,
      (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst).graph.child
        ringThirdNode node ∧
      (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst).graph.label
        node = ⟨some ringFirst, NodeProvenance.ringDuplicate distance⟩ := by
  let observation := p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst
  let graph := observation.graph.toRootedDigraph
  have faithful := p92SemanticExactDigraphObservation_faithful attachedTriangleSource
    attachedCenter ringFirst attachedRootBond
  obtain ⟨addressing, _multiplicities⟩ := faithful.1.2
  have thirdNeRoot : ringThirdNode ≠ graph.root := by
    intro same
    exact addressing.not_child_root ringSecondNode (same ▸ ringThirdNode_edge)
  have notParentFirst : ¬RootedDigraph.ParentAtom graph ringThirdNode ringFirst := by
    rintro ⟨parent, parentEdge, parentLabel⟩
    have parentEq : parent = ringSecondNode :=
      addressing.parent_unique parentEdge ringThirdNode_edge
    subst parent
    have conflict : ringSecond = ringFirst := by
      apply Option.some.inj
      exact (congrArg NodeLabel.atom? ringSecondNode_label).symm.trans parentLabel
    exact (by decide : ringSecond ≠ ringFirst) conflict
  have notSuppressed :
      ¬RootedDigraph.SuppressedParentAtom graph attachedCenter ringFirst ringThirdNode := by
    simp [RootedDigraph.SuppressedParentAtom, thirdNeRoot, notParentFirst]
  have ancestor : RootedDigraph.BranchAncestorAtom graph attachedCenter ringFirst ringThirdNode := by
    right
    refine ⟨graph.root, ?_, ?_⟩
    · exact Relation.TransGen.tail (Relation.TransGen.single ringSecondNode_edge)
        ringThirdNode_edge
    · simpa [graph, observation] using congrArg NodeLabel.atom? faithful.1.1.1
  simpa [graph, observation] using exists_ring_duplicate_child observation.molecule attachedCenter
    ringFirst ringThird ringFirst graph faithful ringThirdNode ringThirdNode_label
      ringThirdFirstBond ancestor notSuppressed

private noncomputable def ringClosingDuplicate := Classical.choose exists_ringClosingDuplicate
private noncomputable def ringClosingDistance :=
  Classical.choose (Classical.choose_spec exists_ringClosingDuplicate)
private def ringClosingDuplicate_edge :=
  (Classical.choose_spec (Classical.choose_spec exists_ringClosingDuplicate)).1
private def ringClosingDuplicate_label :=
  (Classical.choose_spec (Classical.choose_spec exists_ringClosingDuplicate)).2

private def attachedRingAtoms : List (Fin attachedTriangleSource.molecule.atomCount) :=
  [ringFirst, ringSecond, ringThird]

private noncomputable def attachedRingNodes : List
    (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst).graph.Node :=
  [(p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst).graph.root,
    ringSecondNode, ringThirdNode]

private theorem attachedRing_consecutive_iff (left right) :
    P92ConsecutiveInCycle attachedRingAtoms left right ↔
      (left = ringFirst ∧ right = ringSecond) ∨
      (left = ringSecond ∧ right = ringThird) ∨
      (left = ringThird ∧ right = ringFirst) := by
  constructor
  · rintro (⟨before, after, decomposition⟩ | closing)
    · cases before with
      | nil =>
          simp [attachedRingAtoms] at decomposition
          exact Or.inl ⟨decomposition.1.symm, decomposition.2.1.symm⟩
      | cons first rest =>
          cases rest with
          | nil =>
              simp [attachedRingAtoms] at decomposition
              exact Or.inr (Or.inl ⟨decomposition.2.1.symm, decomposition.2.2.1.symm⟩)
          | cons second tail =>
              have lengthEq := congrArg List.length decomposition
              simp [attachedRingAtoms] at lengthEq
              omega
    · have exactClosing : left = ringThird ∧ right = ringFirst := by
        have raw : ringThird = left ∧ ringFirst = right := by
          simpa [attachedRingAtoms] using closing
        exact ⟨raw.1.symm, raw.2.symm⟩
      exact Or.inr (Or.inr exactClosing)
  · rintro (aligned | aligned | aligned)
    · rcases aligned with ⟨rfl, rfl⟩
      exact Or.inl ⟨[], [ringThird], rfl⟩
    · rcases aligned with ⟨rfl, rfl⟩
      exact Or.inl ⟨[ringFirst], [], rfl⟩
    · rcases aligned with ⟨rfl, rfl⟩
      exact Or.inr (by simp [attachedRingAtoms])

private theorem attachedRing_saturated :
    P92IsSaturatedRing
      (p92CanonicalLocalizedMoleculeGraph attachedTriangleSource attachedCenter ringFirst)
      attachedRingAtoms := by
  refine ⟨by simp [attachedRingAtoms], by decide, ?_⟩
  intro left right consecutive
  rcases (attachedRing_consecutive_iff left right).mp consecutive with
    aligned | aligned | aligned
  · rcases aligned with ⟨rfl, rfl⟩
    decide
  · rcases aligned with ⟨rfl, rfl⟩
    decide
  · rcases aligned with ⟨rfl, rfl⟩
    decide

private theorem attachedRingNodes_represent :
    P92RealNodesRepresentAtoms
      (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst)
      attachedRingAtoms attachedRingNodes := by
  apply List.Forall₂.cons
  · exact (p92SemanticExactDigraphObservation_faithful attachedTriangleSource attachedCenter
      ringFirst attachedRootBond).1.1.1
  apply List.Forall₂.cons
  · exact ringSecondNode_label
  apply List.Forall₂.cons
  · exact ringThirdNode_label
  exact List.Forall₂.nil

private theorem attachedRingNodes_path :
    P92DigraphNodePath
      (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter
        ringFirst).graph.toRootedDigraph attachedRingNodes := by
  exact ⟨ringSecondNode_edge, ringThirdNode_edge, trivial⟩

private theorem ringClosingDistance_eq_rootDepth :
    ringClosingDistance =
      (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter
        ringFirst).graph.depth
          (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter
            ringFirst).graph.root + 1 := by
  let observation := p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst
  let graph := observation.graph.toRootedDigraph
  have faithful := p92SemanticExactDigraphObservation_faithful attachedTriangleSource
    attachedCenter ringFirst attachedRootBond
  have legal := faithful.ringDuplicate_distance_at observation.molecule attachedCenter ringFirst
    graph ringThirdNode ringClosingDuplicate ringClosingDuplicate_edge ringFirst
      ringClosingDistance ringClosingDuplicate_label
  rcases legal with external | ⟨ancestor, ancestorPath, ancestorLabel, distanceEq⟩
  · exact ((by decide : ringFirst ≠ attachedCenter) external.1).elim
  · have rootPath : Relation.TransGen graph.child graph.root ringThirdNode :=
      Relation.TransGen.tail (Relation.TransGen.single ringSecondNode_edge) ringThirdNode_edge
    have rootAtom : (graph.label graph.root).atom? = some ringFirst := by
      simpa [graph, observation] using congrArg NodeLabel.atom? faithful.1.1.1
    have depthEq : graph.depth graph.root = graph.depth ancestor :=
      faithful.ancestorAtomAtDepth_unique observation.molecule attachedCenter ringFirst graph
        ringThirdNode ringFirst (graph.depth graph.root) (graph.depth ancestor)
        ⟨graph.root, rootPath, rootAtom, rfl⟩
        ⟨ancestor, ancestorPath, ancestorLabel, rfl⟩
    calc
      ringClosingDistance = graph.depth ancestor + 1 := distanceEq
      _ = graph.depth graph.root + 1 := congrArg (fun depth => depth + 1) depthEq.symm
      _ = observation.graph.depth observation.graph.root + 1 := rfl

private theorem attachedRingClosure :
    P92SelectedRingClosureWitness
      (p92Rule1aSaturatedRingsObservationOfGraph attachedTriangleSource.molecule.atomCount
        (p92CanonicalLocalizedMoleculeGraph attachedTriangleSource attachedCenter ringFirst)
        attachedCenter ringFirst
        (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst).graph
        attachedRingAtoms attachedRingNodes ringClosingDuplicate) := by
  refine ⟨ringFirst,
    (p92SemanticExactDigraphObservation attachedTriangleSource attachedCenter ringFirst).graph.root,
    ringThirdNode, ringClosingDistance, ?_, ?_, ?_, ringClosingDuplicate_edge,
    ringClosingDuplicate_label, ringClosingDistance_eq_rootDepth⟩
  · rfl
  · rfl
  · rfl

private theorem attachedRingRealization_emitted :
    (attachedRingNodes, ringClosingDuplicate) ∈
      p92SemanticSaturatedRingRealizations attachedTriangleSource attachedCenter ringFirst
        attachedRingAtoms := by
  exact (mem_p92SemanticSaturatedRingRealizations_iff attachedTriangleSource attachedCenter
    ringFirst attachedRingAtoms attachedRingNodes ringClosingDuplicate).2
      ⟨attachedRingNodes_represent, attachedRingNodes_path, attachedRingClosure⟩

private theorem attachedRingAtoms_emitted :
    attachedRingAtoms ∈ p92CandidateRingAtomLists attachedTriangleSource.molecule.atomCount :=
  mem_p92CandidateRingAtomLists_of_nodup attachedRingAtoms (by decide)

private noncomputable def saturatedRingsWitness :
    Next54P92ProductionWitness .rule1aSaturatedRings attachedTriangleSource
      (p92SemanticRule1aSaturatedRingsObservation attachedTriangleSource attachedCenter ringFirst
        attachedRingAtoms (attachedRingNodes, ringClosingDuplicate)) :=
  .semanticRule1aSaturatedRings attachedTriangleSource attachedCenter ringFirst
    attachedTriangleCanonicalRepresents attachedRootBond attachedRingAtoms
      (attachedRingNodes, ringClosingDuplicate) attachedRingAtoms_emitted
        attachedRingRealization_emitted attachedRing_saturated

theorem saturatedRings_reference_nonvacuous : ReferenceNonvacuous .rule1aSaturatedRings := by
  exact ⟨attachedTriangleSource, _, attachedTriangleSource_wellFormed,
    saturatedRingsWitness.applicable_and_judged⟩

/-! ## Alternating four-cycle mancude seed -/

private def evenMancudeRaw : RawMolecule where
  atoms := [carbon, carbon, carbon, carbon]
  bonds :=
    [{ source := 0, target := 1, kind := .double },
     { source := 1, target := 2, kind := .single },
     { source := 2, target := 3, kind := .double },
     { source := 3, target := 0, kind := .single }]

private def evenMancudeSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 4 { element := periodicCarbon }
      interactions :=
        [{ participants := [0, 1], kind := .covalent 2 },
         { participants := [1, 2], kind := .covalent 1 },
         { participants := [2, 3], kind := .covalent 2 },
         { participants := [3, 0], kind := .covalent 1 }] }

private def evenMancudeCertificate :
    RawMolecule.P92ParserRepresentationCertificate evenMancudeSource evenMancudeRaw where
  embedded := by rfl
  wellFormed := by
    intro bond member
    simp [evenMancudeRaw] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [RawMolecule.BondEndpointsOK, RawMolecule.atomCount, evenMancudeRaw]
  bondRecordsUnique := by
    simp [RawMolecule.BondRecordsUnique, evenMancudeRaw, RawBond.edgeKey]
  rule2MassesKnown :=
    (RawMolecule.rule2MassesKnown?_eq_true_iff evenMancudeRaw).mp (by decide)
  classicalCovalent := by
    constructor
    · intro atom member
      simp [evenMancudeRaw, carbon] at member
      rcases member with rfl | rfl | rfl | rfl ; rfl
    · intro bond member
      simp [evenMancudeRaw] at member
      rcases member with rfl | rfl | rfl | rfl <;> trivial

private theorem evenMancudeSource_wellFormed : evenMancudeSource.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff evenMancudeSource).mp
    (by decide)

private def mancudeZero : Fin evenMancudeSource.molecule.atomCount := ⟨0, by decide⟩
private def mancudeOne : Fin evenMancudeSource.molecule.atomCount := ⟨1, by decide⟩
private def mancudeTwo : Fin evenMancudeSource.molecule.atomCount := ⟨2, by decide⟩
private def mancudeThree : Fin evenMancudeSource.molecule.atomCount := ⟨3, by decide⟩

private def evenPerfectMatching :
    Fin evenMancudeSource.molecule.atomCount →
      Option (Fin evenMancudeSource.molecule.atomCount) := fun atom =>
  if atom = mancudeZero then some mancudeOne
  else if atom = mancudeOne then some mancudeZero
  else if atom = mancudeTwo then some mancudeThree
  else some mancudeTwo

private theorem evenPerfectMatching_isMatching :
    evenMancudeSource.molecule.toLocalizedMoleculeGraph.IsMancudeMatching
      mancudeZero evenPerfectMatching := by
  exact (evenMancudeSource.molecule.semanticMancudeMatching?_eq_true_iff
    mancudeZero evenPerfectMatching).mp (by decide)

private theorem evenPerfectMatching_saturation :
    MoleculeGraph.mancudeSaturation evenPerfectMatching = 4 := by
  decide

private theorem mancudeSaturation_le_four
    (matching : Fin evenMancudeSource.molecule.atomCount →
      Option (Fin evenMancudeSource.molecule.atomCount)) :
    MoleculeGraph.mancudeSaturation matching ≤ 4 := by
  unfold MoleculeGraph.mancudeSaturation
  calc
    ((Finset.univ : Finset (Fin evenMancudeSource.molecule.atomCount)).filter
        fun atom => (matching atom).isSome).card ≤
        (Finset.univ : Finset (Fin evenMancudeSource.molecule.atomCount)).card :=
      Finset.card_filter_le _ _
    _ = 4 := by decide

private theorem evenPerfectMatching_isMaximum :
    evenMancudeSource.molecule.toLocalizedMoleculeGraph.IsMaximumMancudeMatching
      mancudeZero evenPerfectMatching := by
  refine ⟨evenPerfectMatching_isMatching, ?_⟩
  intro other _otherMatching
  rw [evenPerfectMatching_saturation]
  exact mancudeSaturation_le_four other

private theorem evenPerfectMatching_independentMaximum :
    evenPerfectMatching ∈
      evenMancudeSource.molecule.toLocalizedMoleculeGraph.maximumMancudeMatchings
        mancudeZero := by
  classical
  simp only [MoleculeGraph.maximumMancudeMatchings, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact evenPerfectMatching_isMaximum

private theorem evenPerfectMatching_isMatching_at_two :
    evenMancudeSource.molecule.toLocalizedMoleculeGraph.IsMancudeMatching
      mancudeTwo evenPerfectMatching := by
  exact (evenMancudeSource.molecule.semanticMancudeMatching?_eq_true_iff
    mancudeTwo evenPerfectMatching).mp (by decide)

private theorem evenPerfectMatching_isMaximum_at_two :
    evenMancudeSource.molecule.toLocalizedMoleculeGraph.IsMaximumMancudeMatching
      mancudeTwo evenPerfectMatching := by
  refine ⟨evenPerfectMatching_isMatching_at_two, ?_⟩
  intro other _otherMatching
  rw [evenPerfectMatching_saturation]
  exact mancudeSaturation_le_four other

private theorem evenPerfectMatching_independentMaximum_at_two :
    evenPerfectMatching ∈
      evenMancudeSource.molecule.toLocalizedMoleculeGraph.maximumMancudeMatchings
        mancudeTwo := by
  classical
  simp only [MoleculeGraph.maximumMancudeMatchings, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact evenPerfectMatching_isMaximum_at_two

private theorem evenMancudeZeroOne_localized :
    evenMancudeSource.molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge
      mancudeZero mancudeOne := by
  exact (evenMancudeSource.molecule.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff
    mancudeZero mancudeOne).mp (by decide)

private theorem evenMancudeTwoThree_localized :
    evenMancudeSource.molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge
      mancudeTwo mancudeThree := by
  exact (evenMancudeSource.molecule.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff
    mancudeTwo mancudeThree).mp (by decide)

private theorem evenMancudeZero_represented :
    P92MancudeAttachmentRepresented
      evenMancudeSource.molecule.toLocalizedMoleculeGraph mancudeZero := by
  refine ⟨mancudeOne, evenPerfectMatching, by decide, ?_,
    evenPerfectMatching_independentMaximum, ?_⟩
  · exact Relation.ReflTransGen.single evenMancudeZeroOne_localized
  · simp [evenPerfectMatching]

private theorem evenMancudeTwo_represented :
    P92MancudeAttachmentRepresented
      evenMancudeSource.molecule.toLocalizedMoleculeGraph mancudeTwo := by
  refine ⟨mancudeThree, evenPerfectMatching, by decide, ?_,
    evenPerfectMatching_independentMaximum_at_two, ?_⟩
  · exact Relation.ReflTransGen.single evenMancudeTwoThree_localized
  · simp [evenPerfectMatching, mancudeTwo, mancudeZero, mancudeOne]

private theorem evenMancudeRepresents :
    P92ClassicalConstitutionRepresents evenMancudeSource
      evenMancudeSource.molecule.toLocalizedMoleculeGraph := by
  apply RawMolecule.p92ClassicalConstitutionRepresents_transportGraph
    evenMancudeCertificate.representsToMoleculeGraph
  · intro atom
    fin_cases atom <;> rfl
  · intro atom
    fin_cases atom <;> rfl
  · intro atom
    fin_cases atom <;> rfl
  · intro first second
    fin_cases first <;> fin_cases second <;> decide

private noncomputable def mancudeDigraphWitness :
    Next54P92ProductionWitness .mancudeDigraph evenMancudeSource
      { atomCount := evenMancudeSource.molecule.atomCount
        molecule := evenMancudeSource.molecule.toLocalizedMoleculeGraph
        attached := mancudeZero
        representedAtomicNumber :=
          evenMancudeSource.molecule.semanticExactMancudeAverage mancudeZero } :=
  .semanticMancudeDigraphExactAverage evenMancudeSource mancudeZero
    evenMancudeRepresents evenMancudeZero_represented

private noncomputable def rule1aMancudeWitness :
    Next54P92ProductionWitness .rule1aMancude evenMancudeSource
      { atomCount := evenMancudeSource.molecule.atomCount
        molecule := evenMancudeSource.molecule.toLocalizedMoleculeGraph
        leftAttached := mancudeZero
        rightAttached := mancudeTwo
        outcome := @compare ℚ Rat.linearOrder.toOrd
          (evenMancudeSource.molecule.semanticExactMancudeAverage mancudeZero).value
          (evenMancudeSource.molecule.semanticExactMancudeAverage mancudeTwo).value } :=
  .semanticRule1aMancudeExactComparison evenMancudeSource mancudeZero mancudeTwo
    evenMancudeRepresents evenMancudeZero_represented evenMancudeTwo_represented

theorem mancudeDigraph_reference_nonvacuous : ReferenceNonvacuous .mancudeDigraph := by
  exact ⟨evenMancudeSource, _, evenMancudeSource_wellFormed,
    mancudeDigraphWitness.applicable_and_judged⟩

theorem mancudeRule1a_reference_nonvacuous : ReferenceNonvacuous .rule1aMancude := by
  exact ⟨evenMancudeSource, _, evenMancudeSource_wellFormed,
    rule1aMancudeWitness.applicable_and_judged⟩

end Next54P92DigraphRule1aNonvacuity

namespace Next54P92DigraphRule1aAuthorityRow

/-- Every P-92 digraph/Rule-1a authority row has a structurally well-formed, source-anchored
production witness judged by its independent complete reference. -/
theorem reference_nonvacuous (row : Next54P92DigraphRule1aAuthorityRow) :
    ∃ input, ∃ observation : row.reference.Observation,
      input.StructurallyWellFormed ∧ row.reference.Applicable input ∧
        row.reference.Judges input observation := by
  cases row with
  | acyclicDigraph =>
      exact Next54P92DigraphRule1aNonvacuity.acyclicDigraph_reference_nonvacuous
  | multipleBondDigraph =>
      exact Next54P92DigraphRule1aNonvacuity.multipleBondDigraph_reference_nonvacuous
  | cyclicDigraph =>
      exact Next54P92DigraphRule1aNonvacuity.cyclicDigraph_reference_nonvacuous
  | mancudeDigraph =>
      exact Next54P92DigraphRule1aNonvacuity.mancudeDigraph_reference_nonvacuous
  | sphereExploration =>
      exact Next54P92DigraphRule1aNonvacuity.sphereExploration_reference_nonvacuous
  | ruleExhaustivity =>
      exact Next54P92DigraphRule1aNonvacuity.ruleExhaustivity_reference_nonvacuous
  | rule1aMultipleBondDuplicates =>
      exact Next54P92DigraphRule1aNonvacuity.multipleBondDuplicates_reference_nonvacuous
  | rule1aMancude =>
      exact Next54P92DigraphRule1aNonvacuity.mancudeRule1a_reference_nonvacuous
  | rule1aSaturatedCompounds =>
      exact Next54P92DigraphRule1aNonvacuity.saturatedCompounds_reference_nonvacuous
  | rule1aDoubleTripleBonds =>
      exact Next54P92DigraphRule1aNonvacuity.doubleTripleBonds_reference_nonvacuous
  | rule1aSaturatedRings =>
      exact Next54P92DigraphRule1aNonvacuity.saturatedRings_reference_nonvacuous

end Next54P92DigraphRule1aAuthorityRow

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92DigraphRule1aAuthorityRow.reference_nonvacuous
