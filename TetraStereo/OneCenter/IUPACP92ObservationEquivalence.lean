import TetraStereo.OneCenter.IUPACP92SaturatedRingProductionRefinement

set_option autoImplicit false

/-!
# Observational equivalence for the P-92 digraph and Rule-1a family

Exact rooted digraphs may be reindexed, duplicate-node enumerations may be permuted, and exact
rational labels may be written by different numerator/denominator pairs.  These relations record
those semantic identifications without quotienting the independent reviewed observations.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open DeclarativeCIP

noncomputable section

inductive P92ExactDigraphObservationEquivalent :
    P92ExactDigraphAuthorityObservation → P92ExactDigraphAuthorityObservation → Prop where
  | ofIso
      (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
      (externalParent ligand : Fin atomCount)
      (leftGraph rightGraph : P92FiniteRootedDigraph (Fin atomCount))
      (iso : RootedDigraph.Iso leftGraph.toRootedDigraph rightGraph.toRootedDigraph) :
      P92ExactDigraphObservationEquivalent
        (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand leftGraph)
        (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand rightGraph)

inductive P92MancudeDigraphObservationEquivalent :
    P92MancudeDigraphAuthorityObservation →
      P92MancudeDigraphAuthorityObservation → Prop where
  | ofValueEq
      (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
      (attached : Fin atomCount) (leftValue rightValue : ExactAtomicNumber)
      (value_eq : leftValue.value = rightValue.value) :
      P92MancudeDigraphObservationEquivalent
        ⟨atomCount, molecule, attached, leftValue⟩
        ⟨atomCount, molecule, attached, rightValue⟩

inductive P92Rule1aMultipleBondDuplicatesObservationEquivalent :
    P92Rule1aMultipleBondDuplicatesAuthorityObservation →
      P92Rule1aMultipleBondDuplicatesAuthorityObservation → Prop where
  | ofIsoPerm
      (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
      (externalParent ligand : Fin atomCount)
      (leftGraph rightGraph : P92FiniteRootedDigraph (Fin atomCount))
      (iso : RootedDigraph.Iso leftGraph.toRootedDigraph rightGraph.toRootedDigraph)
      (leftParent : leftGraph.Node) (rightParent : rightGraph.Node)
      (parent_eq : iso.toEquiv leftParent = rightParent)
      (parentAtom duplicatedAtom : Fin atomCount)
      (leftNodes : List leftGraph.Node) (rightNodes : List rightGraph.Node)
      (nodes_perm : (leftNodes.map iso.toEquiv).Perm rightNodes) :
      P92Rule1aMultipleBondDuplicatesObservationEquivalent
        ⟨p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand leftGraph,
          leftParent, parentAtom, duplicatedAtom, leftNodes⟩
        ⟨p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand rightGraph,
          rightParent, parentAtom, duplicatedAtom, rightNodes⟩

inductive P92Rule1aDoubleTripleBondsObservationEquivalent :
    P92Rule1aDoubleTripleBondsAuthorityObservation →
      P92Rule1aDoubleTripleBondsAuthorityObservation → Prop where
  | ofIsoPerm
      (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
      (externalParent ligand : Fin atomCount)
      (leftGraph rightGraph : P92FiniteRootedDigraph (Fin atomCount))
      (iso : RootedDigraph.Iso leftGraph.toRootedDigraph rightGraph.toRootedDigraph)
      (leftLeftNode leftRightNode : leftGraph.Node)
      (rightLeftNode rightRightNode : rightGraph.Node)
      (leftNode_eq : iso.toEquiv leftLeftNode = rightLeftNode)
      (rightNode_eq : iso.toEquiv leftRightNode = rightRightNode)
      (leftAtom rightAtom : Fin atomCount)
      (leftDuplicatesAtLeft : List leftGraph.Node)
      (rightDuplicatesAtLeft : List rightGraph.Node)
      (leftDuplicatesAtRight : List leftGraph.Node)
      (rightDuplicatesAtRight : List rightGraph.Node)
      (duplicatesAtLeft_perm :
        (leftDuplicatesAtLeft.map iso.toEquiv).Perm rightDuplicatesAtLeft)
      (duplicatesAtRight_perm :
        (leftDuplicatesAtRight.map iso.toEquiv).Perm rightDuplicatesAtRight) :
      P92Rule1aDoubleTripleBondsObservationEquivalent
        ⟨p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand leftGraph,
          leftLeftNode, leftRightNode, leftAtom, rightAtom,
          leftDuplicatesAtLeft, leftDuplicatesAtRight⟩
        ⟨p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand rightGraph,
          rightLeftNode, rightRightNode, leftAtom, rightAtom,
          rightDuplicatesAtLeft, rightDuplicatesAtRight⟩

inductive P92Rule1aSaturatedRingsObservationEquivalent :
    P92Rule1aSaturatedRingsAuthorityObservation →
      P92Rule1aSaturatedRingsAuthorityObservation → Prop where
  | ofIso
      (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
      (externalParent ligand : Fin atomCount)
      (leftGraph rightGraph : P92FiniteRootedDigraph (Fin atomCount))
      (iso : RootedDigraph.Iso leftGraph.toRootedDigraph rightGraph.toRootedDigraph)
      (ringAtoms : List (Fin atomCount))
      (leftRingNodes : List leftGraph.Node) (rightRingNodes : List rightGraph.Node)
      (ringNodes_eq : leftRingNodes.map iso.toEquiv = rightRingNodes)
      (leftClosing : leftGraph.Node) (rightClosing : rightGraph.Node)
      (closing_eq : iso.toEquiv leftClosing = rightClosing) :
      P92Rule1aSaturatedRingsObservationEquivalent
        (p92Rule1aSaturatedRingsObservationOfGraph atomCount molecule externalParent ligand
          leftGraph ringAtoms leftRingNodes leftClosing)
        (p92Rule1aSaturatedRingsObservationOfGraph atomCount molecule externalParent ligand
          rightGraph ringAtoms rightRingNodes rightClosing)

def Next54P92ObservationEquivalent
    (row : Next54P92DigraphRule1aAuthorityRow) :
    row.reference.Observation → row.reference.Observation → Prop :=
  match row with
  | .acyclicDigraph | .multipleBondDigraph | .cyclicDigraph =>
      P92ExactDigraphObservationEquivalent
  | .mancudeDigraph => P92MancudeDigraphObservationEquivalent
  | .sphereExploration | .ruleExhaustivity => Eq
  | .rule1aMultipleBondDuplicates =>
      P92Rule1aMultipleBondDuplicatesObservationEquivalent
  | .rule1aMancude | .rule1aSaturatedCompounds => Eq
  | .rule1aDoubleTripleBonds => P92Rule1aDoubleTripleBondsObservationEquivalent
  | .rule1aSaturatedRings => P92Rule1aSaturatedRingsObservationEquivalent

noncomputable def p92ExactDigraphObservationCanonicalize :
    P92ExactDigraphAuthorityObservation → P92ExactDigraphAuthorityObservation
  | ⟨atomCount, molecule, externalParent, ligand, graph⟩ =>
      p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand
        (P92FiniteRootedDigraph.ofRootedDigraph graph.toRootedDigraph)

noncomputable def p92Rule1aMultipleBondDuplicatesObservationCanonicalize :
    P92Rule1aMultipleBondDuplicatesAuthorityObservation →
      P92Rule1aMultipleBondDuplicatesAuthorityObservation
  | ⟨⟨atomCount, molecule, externalParent, ligand, graph⟩,
      parent, parentAtom, duplicatedAtom, nodes⟩ =>
      let encoded := P92FiniteRootedDigraph.ofRootedDigraph graph.toRootedDigraph
      let encodingIso := P92FiniteRootedDigraph.ofRootedDigraphIso graph.toRootedDigraph
      ⟨p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand encoded,
        encodingIso.toEquiv parent, parentAtom, duplicatedAtom,
        nodes.map encodingIso.toEquiv⟩

noncomputable def p92Rule1aDoubleTripleBondsObservationCanonicalize :
    P92Rule1aDoubleTripleBondsAuthorityObservation →
      P92Rule1aDoubleTripleBondsAuthorityObservation
  | ⟨⟨atomCount, molecule, externalParent, ligand, graph⟩,
      leftNode, rightNode, leftAtom, rightAtom, duplicatesAtLeft, duplicatesAtRight⟩ =>
      let encoded := P92FiniteRootedDigraph.ofRootedDigraph graph.toRootedDigraph
      let encodingIso := P92FiniteRootedDigraph.ofRootedDigraphIso graph.toRootedDigraph
      ⟨p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand encoded,
        encodingIso.toEquiv leftNode, encodingIso.toEquiv rightNode, leftAtom, rightAtom,
        duplicatesAtLeft.map encodingIso.toEquiv,
        duplicatesAtRight.map encodingIso.toEquiv⟩

noncomputable def p92Rule1aSaturatedRingsObservationCanonicalize :
    P92Rule1aSaturatedRingsAuthorityObservation →
      P92Rule1aSaturatedRingsAuthorityObservation
  | ⟨⟨atomCount, molecule, externalParent, ligand, graph⟩,
      ringAtoms, ringNodes, closing⟩ =>
      let encoded := P92FiniteRootedDigraph.ofRootedDigraph graph.toRootedDigraph
      let encodingIso := P92FiniteRootedDigraph.ofRootedDigraphIso graph.toRootedDigraph
      p92Rule1aSaturatedRingsObservationOfGraph atomCount molecule externalParent ligand encoded
        ringAtoms (ringNodes.map encodingIso.toEquiv) (encodingIso.toEquiv closing)

/-- Fixed representative selection for every P-92 family observation.  Graph-backed observations
are reindexed onto their canonical finite-node encoding; all other observations are unchanged. -/
noncomputable def Next54P92ObservationCanonicalize
    (row : Next54P92DigraphRule1aAuthorityRow) :
    row.reference.Observation → row.reference.Observation :=
  match row with
  | .acyclicDigraph | .multipleBondDigraph | .cyclicDigraph =>
      p92ExactDigraphObservationCanonicalize
  | .rule1aMultipleBondDuplicates =>
      p92Rule1aMultipleBondDuplicatesObservationCanonicalize
  | .rule1aDoubleTripleBonds => p92Rule1aDoubleTripleBondsObservationCanonicalize
  | .rule1aSaturatedRings => p92Rule1aSaturatedRingsObservationCanonicalize
  | .mancudeDigraph | .sphereExploration | .ruleExhaustivity | .rule1aMancude |
      .rule1aSaturatedCompounds => fun observation => observation

namespace Next54P92ObservationEquivalent

private theorem map_equivRefl {alpha : Type} (values : List alpha) :
    List.map (⇑(Equiv.refl alpha)) values = values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons]
      exact congrArg (List.cons head) inductionHypothesis

private theorem map_equiv_symm_roundtrip {alpha beta : Type} (equiv : alpha ≃ beta)
    (values : List alpha) :
    (values.map equiv).map equiv.symm = values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons]
      rw [equiv.symm_apply_apply]
      exact congrArg (List.cons head) inductionHypothesis

theorem refl (row : Next54P92DigraphRule1aAuthorityRow)
    (observation : row.reference.Observation) :
    Next54P92ObservationEquivalent row observation observation := by
  cases row with
  | acyclicDigraph | multipleBondDigraph | cyclicDigraph =>
      rcases observation with ⟨atomCount, molecule, externalParent, ligand, graph⟩
      exact .ofIso atomCount molecule externalParent ligand graph graph (.refl _)
  | mancudeDigraph =>
      rcases observation with ⟨atomCount, molecule, attached, value⟩
      exact .ofValueEq atomCount molecule attached value value rfl
  | sphereExploration | ruleExhaustivity | rule1aMancude | rule1aSaturatedCompounds => rfl
  | rule1aMultipleBondDuplicates =>
      rcases observation with ⟨⟨atomCount, molecule, externalParent, ligand, graph⟩,
        parent, parentAtom, duplicatedAtom, nodes⟩
      exact .ofIsoPerm atomCount molecule externalParent ligand graph graph (.refl _)
        parent parent rfl parentAtom duplicatedAtom nodes nodes (by
          have hEquiv : (RootedDigraph.Iso.refl graph.toRootedDigraph).toEquiv =
              Equiv.refl graph.Node := rfl
          rw [hEquiv]
          exact (congrArg (fun values => values.Perm nodes)
            (map_equivRefl nodes)).mpr (.refl _))
  | rule1aDoubleTripleBonds =>
      rcases observation with ⟨⟨atomCount, molecule, externalParent, ligand, graph⟩,
        leftNode, rightNode, leftAtom, rightAtom, duplicatesAtLeft, duplicatesAtRight⟩
      exact .ofIsoPerm atomCount molecule externalParent ligand graph graph (.refl _)
        leftNode rightNode leftNode rightNode rfl rfl leftAtom rightAtom
        duplicatesAtLeft duplicatesAtLeft duplicatesAtRight duplicatesAtRight (by
          have hEquiv : (RootedDigraph.Iso.refl graph.toRootedDigraph).toEquiv =
              Equiv.refl graph.Node := rfl
          rw [hEquiv]
          exact (congrArg (fun values => values.Perm duplicatesAtLeft)
            (map_equivRefl duplicatesAtLeft)).mpr (.refl _)) (by
          have hEquiv : (RootedDigraph.Iso.refl graph.toRootedDigraph).toEquiv =
              Equiv.refl graph.Node := rfl
          rw [hEquiv]
          exact (congrArg (fun values => values.Perm duplicatesAtRight)
            (map_equivRefl duplicatesAtRight)).mpr (.refl _))
  | rule1aSaturatedRings =>
      rcases observation with ⟨⟨atomCount, molecule, externalParent, ligand, graph⟩,
        ringAtoms, ringNodes, closing⟩
      exact .ofIso atomCount molecule externalParent ligand graph graph (.refl _)
        ringAtoms ringNodes ringNodes (by
          have hEquiv : (RootedDigraph.Iso.refl graph.toRootedDigraph).toEquiv =
              Equiv.refl graph.Node := rfl
          rw [hEquiv]
          exact map_equivRefl ringNodes) closing closing rfl

/-- Canonical finite-node re-encoding preserves the complete structural observation semantics. -/
theorem canonicalize (row : Next54P92DigraphRule1aAuthorityRow)
    (observation : row.reference.Observation) :
    Next54P92ObservationEquivalent row
      (Next54P92ObservationCanonicalize row observation) observation := by
  cases row with
  | acyclicDigraph | multipleBondDigraph | cyclicDigraph =>
      rcases observation with ⟨atomCount, molecule, externalParent, ligand, graph⟩
      let encoded := P92FiniteRootedDigraph.ofRootedDigraph graph.toRootedDigraph
      let encodingIso := P92FiniteRootedDigraph.ofRootedDigraphIso graph.toRootedDigraph
      exact .ofIso atomCount molecule externalParent ligand encoded graph encodingIso.symm
  | mancudeDigraph | sphereExploration | ruleExhaustivity | rule1aMancude |
      rule1aSaturatedCompounds =>
      exact refl _ observation
  | rule1aMultipleBondDuplicates =>
      rcases observation with ⟨⟨atomCount, molecule, externalParent, ligand, graph⟩,
        parent, parentAtom, duplicatedAtom, nodes⟩
      let encoded := P92FiniteRootedDigraph.ofRootedDigraph graph.toRootedDigraph
      let encodingIso := P92FiniteRootedDigraph.ofRootedDigraphIso graph.toRootedDigraph
      exact .ofIsoPerm atomCount molecule externalParent ligand encoded graph encodingIso.symm
        (encodingIso.toEquiv parent) parent (by
          change encodingIso.toEquiv.symm (encodingIso.toEquiv parent) = parent
          exact encodingIso.toEquiv.symm_apply_apply parent)
        parentAtom duplicatedAtom (nodes.map encodingIso.toEquiv) nodes (by
          have inverse_eq : encodingIso.symm.toEquiv = encodingIso.toEquiv.symm := rfl
          rw [inverse_eq, map_equiv_symm_roundtrip])
  | rule1aDoubleTripleBonds =>
      rcases observation with ⟨⟨atomCount, molecule, externalParent, ligand, graph⟩,
        leftNode, rightNode, leftAtom, rightAtom, duplicatesAtLeft, duplicatesAtRight⟩
      let encoded := P92FiniteRootedDigraph.ofRootedDigraph graph.toRootedDigraph
      let encodingIso := P92FiniteRootedDigraph.ofRootedDigraphIso graph.toRootedDigraph
      exact .ofIsoPerm atomCount molecule externalParent ligand encoded graph encodingIso.symm
        (encodingIso.toEquiv leftNode) (encodingIso.toEquiv rightNode) leftNode rightNode (by
          change encodingIso.toEquiv.symm (encodingIso.toEquiv leftNode) = leftNode
          exact encodingIso.toEquiv.symm_apply_apply leftNode) (by
          change encodingIso.toEquiv.symm (encodingIso.toEquiv rightNode) = rightNode
          exact encodingIso.toEquiv.symm_apply_apply rightNode)
        leftAtom rightAtom (duplicatesAtLeft.map encodingIso.toEquiv) duplicatesAtLeft
        (duplicatesAtRight.map encodingIso.toEquiv) duplicatesAtRight (by
          have inverse_eq : encodingIso.symm.toEquiv = encodingIso.toEquiv.symm := rfl
          rw [inverse_eq, map_equiv_symm_roundtrip]) (by
          have inverse_eq : encodingIso.symm.toEquiv = encodingIso.toEquiv.symm := rfl
          rw [inverse_eq, map_equiv_symm_roundtrip])
  | rule1aSaturatedRings =>
      rcases observation with ⟨⟨atomCount, molecule, externalParent, ligand, graph⟩,
        ringAtoms, ringNodes, closing⟩
      let encoded := P92FiniteRootedDigraph.ofRootedDigraph graph.toRootedDigraph
      let encodingIso := P92FiniteRootedDigraph.ofRootedDigraphIso graph.toRootedDigraph
      exact .ofIso atomCount molecule externalParent ligand encoded graph encodingIso.symm
        ringAtoms (ringNodes.map encodingIso.toEquiv) ringNodes
          (map_equiv_symm_roundtrip encodingIso.toEquiv ringNodes)
        (encodingIso.toEquiv closing) closing (by
          change encodingIso.toEquiv.symm (encodingIso.toEquiv closing) = closing
          exact encodingIso.toEquiv.symm_apply_apply closing)

private theorem exactDigraph_acyclic_judges_iff
    {left right : P92ExactDigraphAuthorityObservation}
    (equivalent : P92ExactDigraphObservationEquivalent left right)
    (source : AuthoritativeChemicalInput) :
    p92AcyclicDigraphReference.Judges source left ↔
      p92AcyclicDigraphReference.Judges source right := by
  cases equivalent with
  | ofIso atomCount molecule externalParent ligand leftGraph rightGraph iso =>
      exact and_congr_right fun _ => and_congr
        (RootedDigraph.faithfulExactExpansion_iso_iff molecule externalParent ligand iso)
        (p92GraphHasNoRingDuplicate_iff_of_iso iso)

private theorem exactDigraph_multipleBond_judges_iff
    {left right : P92ExactDigraphAuthorityObservation}
    (equivalent : P92ExactDigraphObservationEquivalent left right)
    (source : AuthoritativeChemicalInput) :
    p92MultipleBondDigraphReference.Judges source left ↔
      p92MultipleBondDigraphReference.Judges source right := by
  cases equivalent with
  | ofIso atomCount molecule externalParent ligand leftGraph rightGraph iso =>
      exact and_congr_right fun _ => and_congr
        (RootedDigraph.faithfulExactExpansion_iso_iff molecule externalParent ligand iso)
        (p92GraphHasMultipleBondDuplicate_iff_of_iso iso)

private theorem exactDigraph_cyclic_judges_iff
    {left right : P92ExactDigraphAuthorityObservation}
    (equivalent : P92ExactDigraphObservationEquivalent left right)
    (source : AuthoritativeChemicalInput) :
    p92CyclicDigraphReference.Judges source left ↔
      p92CyclicDigraphReference.Judges source right := by
  cases equivalent with
  | ofIso atomCount molecule externalParent ligand leftGraph rightGraph iso =>
      exact and_congr_right fun _ => and_congr
        (RootedDigraph.faithfulExactExpansion_iso_iff molecule externalParent ligand iso)
        (p92GraphHasRingDuplicate_iff_of_iso iso)

private theorem mancudeDigraph_judges_iff
    {left right : P92MancudeDigraphAuthorityObservation}
    (equivalent : P92MancudeDigraphObservationEquivalent left right)
    (source : AuthoritativeChemicalInput) :
    p92MancudeDigraphReference.Judges source left ↔
      p92MancudeDigraphReference.Judges source right := by
  cases equivalent with
  | ofValueEq atomCount molecule attached leftValue rightValue value_eq =>
      constructor
      · rintro ⟨represents, represented, exact⟩
        exact ⟨represents, represented, value_eq.symm.trans exact⟩
      · rintro ⟨represents, represented, exact⟩
        exact ⟨represents, represented, value_eq.trans exact⟩

private theorem multipleBondDuplicateChild_iff_of_iso
    (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
    (externalParent ligand : Fin atomCount)
    (leftGraph rightGraph : P92FiniteRootedDigraph (Fin atomCount))
    (iso : RootedDigraph.Iso leftGraph.toRootedDigraph rightGraph.toRootedDigraph)
    (leftParent : leftGraph.Node) (rightParent : rightGraph.Node)
    (parent_eq : iso.toEquiv leftParent = rightParent)
    (atom : Fin atomCount) (node : leftGraph.Node) :
    P92MultipleBondDuplicateChild
        (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand leftGraph)
        leftParent atom node ↔
      P92MultipleBondDuplicateChild
        (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand rightGraph)
        rightParent atom (iso.toEquiv node) := by
  constructor
  · rintro ⟨child, distance, label, distance_eq⟩
    refine ⟨?_, distance, ?_, ?_⟩
    · simpa [parent_eq] using (iso.map_child leftParent node).mp child
    · exact (iso.map_label node).symm.trans label
    · calc
        distance = leftGraph.depth leftParent + 1 := distance_eq
        _ = rightGraph.depth (iso.toEquiv leftParent) + 1 :=
          congrArg (fun depth => depth + 1) (iso.map_depth leftParent)
        _ = rightGraph.depth rightParent + 1 := by rw [parent_eq]
  · rintro ⟨child, distance, label, distance_eq⟩
    refine ⟨?_, distance, ?_, ?_⟩
    · exact (iso.map_child leftParent node).mpr (by simpa [parent_eq] using child)
    · exact (iso.map_label node).trans label
    · calc
        distance = rightGraph.depth rightParent + 1 := distance_eq
        _ = rightGraph.depth (iso.toEquiv leftParent) + 1 := by rw [parent_eq]
        _ = leftGraph.depth leftParent + 1 :=
          congrArg (fun depth => depth + 1) (iso.map_depth leftParent).symm

private theorem multipleBondDuplicateChildrenExact_of_iso_perm
    (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
    (externalParent ligand : Fin atomCount)
    (leftGraph rightGraph : P92FiniteRootedDigraph (Fin atomCount))
    (iso : RootedDigraph.Iso leftGraph.toRootedDigraph rightGraph.toRootedDigraph)
    (leftParent : leftGraph.Node) (rightParent : rightGraph.Node)
    (parent_eq : iso.toEquiv leftParent = rightParent)
    (parentAtom duplicatedAtom : Fin atomCount)
    (leftNodes : List leftGraph.Node) (rightNodes : List rightGraph.Node)
    (nodes_perm : (leftNodes.map iso.toEquiv).Perm rightNodes)
    (leftExact : P92MultipleBondDuplicateChildrenExact
      (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand leftGraph)
      leftParent parentAtom duplicatedAtom leftNodes) :
    P92MultipleBondDuplicateChildrenExact
      (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand rightGraph)
      rightParent parentAtom duplicatedAtom rightNodes := by
  rcases leftExact with ⟨parentLabel, multipleBond, nodesNodup, length_eq, mem_iff⟩
  refine ⟨?_, multipleBond, ?_, ?_, ?_⟩
  · rw [← parent_eq]
    exact (iso.map_label leftParent).symm.trans parentLabel
  · exact nodes_perm.nodup_iff.mp (nodesNodup.map iso.toEquiv.injective)
  · exact nodes_perm.length_eq.symm.trans (by simpa using length_eq)
  · intro rightNode
    rw [← nodes_perm.mem_iff]
    constructor
    · intro mappedMember
      rcases List.mem_map.mp mappedMember with ⟨leftNode, leftMember, node_eq⟩
      subst rightNode
      exact (multipleBondDuplicateChild_iff_of_iso atomCount molecule externalParent ligand
        leftGraph rightGraph iso leftParent rightParent parent_eq duplicatedAtom leftNode).mp
          ((mem_iff leftNode).mp leftMember)
    · intro rightChild
      let leftNode := iso.toEquiv.symm rightNode
      have leftChild : P92MultipleBondDuplicateChild
          (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand leftGraph)
          leftParent duplicatedAtom leftNode :=
        (multipleBondDuplicateChild_iff_of_iso atomCount molecule externalParent ligand
          leftGraph rightGraph iso leftParent rightParent parent_eq duplicatedAtom leftNode).mpr
            (by simpa [leftNode] using rightChild)
      exact List.mem_map.mpr
        ⟨leftNode, (mem_iff leftNode).mpr leftChild, by simp [leftNode]⟩

/-- Two exact duplicate-child enumerations on isomorphic faithful graph presentations agree up to
the induced node permutation.  This is the reusable completeness direction for both Rule-1a
multiple-bond rows. -/
theorem P92MultipleBondDuplicateChildrenExact.map_perm_of_iso
    (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
    (externalParent ligand : Fin atomCount)
    (leftGraph rightGraph : P92FiniteRootedDigraph (Fin atomCount))
    (iso : RootedDigraph.Iso leftGraph.toRootedDigraph rightGraph.toRootedDigraph)
    (leftParent : leftGraph.Node) (rightParent : rightGraph.Node)
    (parent_eq : iso.toEquiv leftParent = rightParent)
    (parentAtom duplicatedAtom : Fin atomCount)
    (leftNodes : List leftGraph.Node) (rightNodes : List rightGraph.Node)
    (leftExact : P92MultipleBondDuplicateChildrenExact
      (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand leftGraph)
      leftParent parentAtom duplicatedAtom leftNodes)
    (rightExact : P92MultipleBondDuplicateChildrenExact
      (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand rightGraph)
      rightParent parentAtom duplicatedAtom rightNodes) :
    (leftNodes.map iso.toEquiv).Perm rightNodes := by
  rcases leftExact with ⟨_leftLabel, _leftMultiple, leftNodup, _leftLength, leftMember⟩
  rcases rightExact with ⟨_rightLabel, _rightMultiple, rightNodup, _rightLength, rightMember⟩
  apply (List.perm_ext_iff_of_nodup (leftNodup.map iso.toEquiv.injective) rightNodup).mpr
  intro rightNode
  constructor
  · intro mappedMember
    rcases List.mem_map.mp mappedMember with ⟨leftNode, leftNodeMember, mapped⟩
    subst rightNode
    apply (rightMember (iso.toEquiv leftNode)).mpr
    exact (multipleBondDuplicateChild_iff_of_iso atomCount molecule externalParent ligand
      leftGraph rightGraph iso leftParent rightParent parent_eq duplicatedAtom leftNode).mp
        ((leftMember leftNode).mp leftNodeMember)
  · intro rightNodeMember
    let leftNode := iso.toEquiv.symm rightNode
    have leftChild : P92MultipleBondDuplicateChild
        (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand leftGraph)
        leftParent duplicatedAtom leftNode :=
      (multipleBondDuplicateChild_iff_of_iso atomCount molecule externalParent ligand
        leftGraph rightGraph iso leftParent rightParent parent_eq duplicatedAtom leftNode).mpr
          (by simpa [leftNode] using (rightMember rightNode).mp rightNodeMember)
    exact List.mem_map.mpr
      ⟨leftNode, (leftMember leftNode).mpr leftChild, by simp [leftNode]⟩

private theorem multipleBondDuplicates_judges_iff
    {left right : P92Rule1aMultipleBondDuplicatesAuthorityObservation}
    (equivalent : P92Rule1aMultipleBondDuplicatesObservationEquivalent left right)
    (source : AuthoritativeChemicalInput) :
    p92Rule1aMultipleBondDuplicatesReference.Judges source left ↔
      p92Rule1aMultipleBondDuplicatesReference.Judges source right := by
  cases equivalent with
  | ofIsoPerm atomCount molecule externalParent ligand leftGraph rightGraph iso leftParent
      rightParent parent_eq parentAtom duplicatedAtom leftNodes rightNodes nodes_perm =>
      constructor
      · rintro ⟨represents, faithful, exact⟩
        exact ⟨represents,
          (RootedDigraph.faithfulExactExpansion_iso_iff molecule externalParent ligand iso).mp
            faithful,
          multipleBondDuplicateChildrenExact_of_iso_perm atomCount molecule externalParent ligand
            leftGraph rightGraph iso leftParent rightParent parent_eq parentAtom duplicatedAtom
              leftNodes rightNodes nodes_perm exact⟩
      · rintro ⟨represents, faithful, exact⟩
        let inversePerm : (rightNodes.map iso.toEquiv.symm).Perm leftNodes := by
          have mapped := nodes_perm.map iso.toEquiv.symm
          simpa using mapped.symm
        exact ⟨represents,
          (RootedDigraph.faithfulExactExpansion_iso_iff molecule externalParent ligand iso).mpr
            faithful,
          multipleBondDuplicateChildrenExact_of_iso_perm atomCount molecule externalParent ligand
            rightGraph leftGraph iso.symm rightParent leftParent (by
              change iso.toEquiv.symm rightParent = leftParent
              rw [← parent_eq]
              exact iso.toEquiv.symm_apply_apply leftParent)
              parentAtom duplicatedAtom rightNodes leftNodes inversePerm exact⟩

private theorem doubleTripleBonds_judges_iff
    {left right : P92Rule1aDoubleTripleBondsAuthorityObservation}
    (equivalent : P92Rule1aDoubleTripleBondsObservationEquivalent left right)
    (source : AuthoritativeChemicalInput) :
    p92Rule1aDoubleTripleBondsReference.Judges source left ↔
      p92Rule1aDoubleTripleBondsReference.Judges source right := by
  cases equivalent with
  | ofIsoPerm atomCount molecule externalParent ligand leftGraph rightGraph iso
      leftLeftNode leftRightNode rightLeftNode rightRightNode leftNode_eq rightNode_eq
      leftAtom rightAtom leftDuplicatesAtLeft rightDuplicatesAtLeft leftDuplicatesAtRight
      rightDuplicatesAtRight duplicatesAtLeft_perm duplicatesAtRight_perm =>
      constructor
      · rintro ⟨represents, faithful, bondOrder, leftExact, rightExact⟩
        exact ⟨represents,
          (RootedDigraph.faithfulExactExpansion_iso_iff molecule externalParent ligand iso).mp
            faithful,
          bondOrder,
          multipleBondDuplicateChildrenExact_of_iso_perm atomCount molecule externalParent ligand
            leftGraph rightGraph iso leftLeftNode rightLeftNode leftNode_eq leftAtom rightAtom
              leftDuplicatesAtLeft rightDuplicatesAtLeft duplicatesAtLeft_perm leftExact,
          multipleBondDuplicateChildrenExact_of_iso_perm atomCount molecule externalParent ligand
            leftGraph rightGraph iso leftRightNode rightRightNode rightNode_eq rightAtom leftAtom
              leftDuplicatesAtRight rightDuplicatesAtRight duplicatesAtRight_perm rightExact⟩
      · rintro ⟨represents, faithful, bondOrder, leftExact, rightExact⟩
        let inverseLeftPerm :
            (rightDuplicatesAtLeft.map iso.toEquiv.symm).Perm leftDuplicatesAtLeft := by
          have mapped := duplicatesAtLeft_perm.map iso.toEquiv.symm
          simpa using mapped.symm
        let inverseRightPerm :
            (rightDuplicatesAtRight.map iso.toEquiv.symm).Perm leftDuplicatesAtRight := by
          have mapped := duplicatesAtRight_perm.map iso.toEquiv.symm
          simpa using mapped.symm
        have inverseLeftNode : iso.symm.toEquiv rightLeftNode = leftLeftNode := by
          change iso.toEquiv.symm rightLeftNode = leftLeftNode
          rw [← leftNode_eq]
          exact iso.toEquiv.symm_apply_apply leftLeftNode
        have inverseRightNode : iso.symm.toEquiv rightRightNode = leftRightNode := by
          change iso.toEquiv.symm rightRightNode = leftRightNode
          rw [← rightNode_eq]
          exact iso.toEquiv.symm_apply_apply leftRightNode
        exact ⟨represents,
          (RootedDigraph.faithfulExactExpansion_iso_iff molecule externalParent ligand iso).mpr
            faithful,
          bondOrder,
          multipleBondDuplicateChildrenExact_of_iso_perm atomCount molecule externalParent ligand
            rightGraph leftGraph iso.symm rightLeftNode leftLeftNode inverseLeftNode leftAtom
              rightAtom rightDuplicatesAtLeft leftDuplicatesAtLeft inverseLeftPerm leftExact,
          multipleBondDuplicateChildrenExact_of_iso_perm atomCount molecule externalParent ligand
            rightGraph leftGraph iso.symm rightRightNode leftRightNode inverseRightNode rightAtom
              leftAtom rightDuplicatesAtRight leftDuplicatesAtRight inverseRightPerm rightExact⟩

private theorem saturatedRings_judges_iff
    {left right : P92Rule1aSaturatedRingsAuthorityObservation}
    (equivalent : P92Rule1aSaturatedRingsObservationEquivalent left right)
    (source : AuthoritativeChemicalInput) :
    p92Rule1aSaturatedRingsReference.Judges source left ↔
      p92Rule1aSaturatedRingsReference.Judges source right := by
  cases equivalent with
  | ofIso atomCount molecule externalParent ligand leftGraph rightGraph iso ringAtoms
      leftRingNodes rightRingNodes ringNodes_eq leftClosing rightClosing closing_eq =>
      constructor
      · intro leftJudged
        have rightFaithful : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand
            rightGraph.toRootedDigraph :=
          (RootedDigraph.faithfulExactExpansion_iso_iff molecule externalParent ligand iso).mp
            leftJudged.2.1
        have transported := p92Rule1aSaturatedRings_judged_transport source atomCount molecule
          externalParent ligand rightGraph leftGraph iso.symm rightFaithful ringAtoms
            leftRingNodes leftClosing leftJudged
        simpa [p92Rule1aSaturatedRingsTransport, RootedDigraph.Iso.symm,
          ringNodes_eq, closing_eq] using transported
      · intro rightJudged
        have leftFaithful : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand
            leftGraph.toRootedDigraph :=
          (RootedDigraph.faithfulExactExpansion_iso_iff molecule externalParent ligand iso).mpr
            rightJudged.2.1
        have transported := p92Rule1aSaturatedRings_judged_transport source atomCount molecule
          externalParent ligand leftGraph rightGraph iso leftFaithful ringAtoms
            rightRingNodes rightClosing rightJudged
        have inverseRingNodes : rightRingNodes.map iso.toEquiv.symm = leftRingNodes := by
          rw [← ringNodes_eq, List.map_map]
          simp
        have inverseClosing : iso.toEquiv.symm rightClosing = leftClosing := by
          rw [← closing_eq]
          exact iso.toEquiv.symm_apply_apply leftClosing
        simpa [p92Rule1aSaturatedRingsTransport, RootedDigraph.Iso.symm,
          inverseRingNodes, inverseClosing] using transported

/-- Observationally equivalent observations satisfy the same independent reviewed judgment. -/
theorem judges_iff
    {row : Next54P92DigraphRule1aAuthorityRow}
    {left right : row.reference.Observation}
    (equivalent : Next54P92ObservationEquivalent row left right)
    (source : AuthoritativeChemicalInput) :
    row.reference.Judges source left ↔ row.reference.Judges source right := by
  cases row with
  | acyclicDigraph => exact exactDigraph_acyclic_judges_iff equivalent source
  | multipleBondDigraph => exact exactDigraph_multipleBond_judges_iff equivalent source
  | cyclicDigraph => exact exactDigraph_cyclic_judges_iff equivalent source
  | mancudeDigraph => exact mancudeDigraph_judges_iff equivalent source
  | sphereExploration | ruleExhaustivity | rule1aMancude | rule1aSaturatedCompounds =>
      subst right
      rfl
  | rule1aMultipleBondDuplicates => exact multipleBondDuplicates_judges_iff equivalent source
  | rule1aDoubleTripleBonds => exact doubleTripleBonds_judges_iff equivalent source
  | rule1aSaturatedRings => exact saturatedRings_judges_iff equivalent source

end Next54P92ObservationEquivalent

end


end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92ObservationEquivalent.refl
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92ObservationEquivalent.canonicalize
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92ObservationEquivalent.judges_iff
