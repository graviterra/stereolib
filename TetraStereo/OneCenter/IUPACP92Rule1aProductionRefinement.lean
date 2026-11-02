import TetraStereo.OneCenter.IUPACP92ExactDigraphProductionRefinement
import TetraStereo.OneCenter.IUPACP92SemanticGraphProductionCore

set_option autoImplicit false

/-!
# Production refinement for the P-92 Rule-1a duplicate rows

The reviewed Rule-1a references require concrete, exhaustive lists of multiple-bond duplicate
children.  This module generates those lists from the production digraph itself.  The construction
enumerates the exact complete-label child fiber; faithful expansion equates its cardinality with
the constitutional `bondOrder - 1` multiplicity.  Consequently the witnesses are neither detached
caller data nor manually chosen proof lists.

One generic generator discharges both the single-parent multiple-bond-duplicate row and the
two-ended double/triple-bond replacement row.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open DeclarativeCIP
open DeclarativeCIP.RootedDigraph
open RawMolecule

universe u

/-! ## Canonical enumeration of one exact duplicate-label fiber -/

noncomputable def p92MultipleBondDuplicateNodes
    {Atom : Type u} (graph : RootedDigraph Atom) (parent : graph.Node) (atom : Atom) :
    List graph.Node := by
  classical
  letI : Fintype graph.Node := graph.nodeFintype
  exact ((Finset.univ.filter fun node =>
    graph.child parent node ∧
      graph.label node =
        ⟨some atom, NodeProvenance.multipleBondDuplicate (graph.depth parent + 1)⟩).toList)

theorem p92MultipleBondDuplicateNodes_nodup
    {Atom : Type u} (graph : RootedDigraph Atom) (parent : graph.Node) (atom : Atom) :
    (p92MultipleBondDuplicateNodes graph parent atom).Nodup := by
  classical
  letI : Fintype graph.Node := graph.nodeFintype
  exact Finset.nodup_toList _

theorem p92MultipleBondDuplicateNodes_mem_iff_label
    {Atom : Type u} (graph : RootedDigraph Atom) (parent node : graph.Node) (atom : Atom) :
    node ∈ p92MultipleBondDuplicateNodes graph parent atom ↔
      graph.child parent node ∧
        graph.label node =
          ⟨some atom, NodeProvenance.multipleBondDuplicate (graph.depth parent + 1)⟩ := by
  classical
  letI : Fintype graph.Node := graph.nodeFintype
  simp [p92MultipleBondDuplicateNodes]

theorem p92MultipleBondDuplicateNodes_mem_iff_child
    (expansion : P92ExactDigraphAuthorityObservation)
    (parent node : expansion.graph.Node) (atom : Fin expansion.atomCount) :
    node ∈ p92MultipleBondDuplicateNodes expansion.graph.toRootedDigraph parent atom ↔
      P92MultipleBondDuplicateChild expansion parent atom node := by
  rw [p92MultipleBondDuplicateNodes_mem_iff_label]
  constructor
  · rintro ⟨edge, labelEq⟩
    exact ⟨edge, expansion.graph.depth parent + 1, labelEq, rfl⟩
  · rintro ⟨edge, distance, labelEq, distanceEq⟩
    exact ⟨edge, by simpa [distanceEq] using labelEq⟩

theorem p92MultipleBondDuplicateNodes_length_eq_childLabelCount
    {Atom : Type u} (graph : RootedDigraph Atom) (parent : graph.Node) (atom : Atom) :
    (p92MultipleBondDuplicateNodes graph parent atom).length =
      ChildLabelCount graph parent
        ⟨some atom, NodeProvenance.multipleBondDuplicate (graph.depth parent + 1)⟩ := by
  classical
  letI : Fintype graph.Node := graph.nodeFintype
  unfold ChildLabelCount ChildCountWhere
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [p92MultipleBondDuplicateNodes]

/-- Faithful expansion turns the canonical finite label fiber into the exact concrete witness list
required by the independent Rule-1a reference. -/
theorem P92ExactDigraphAuthorityObservation.generatedMultipleBondDuplicateChildrenExact
    (expansion : P92ExactDigraphAuthorityObservation)
    (faithful : expansion.Faithful)
    (parent : expansion.graph.Node)
    (parentAtom duplicatedAtom : Fin expansion.atomCount)
    (parentLabel : expansion.graph.label parent =
      ⟨some parentAtom, NodeProvenance.realAtom⟩)
    (multipleBond : 1 < expansion.molecule.bond parentAtom duplicatedAtom) :
    P92MultipleBondDuplicateChildrenExact expansion parent parentAtom duplicatedAtom
      (p92MultipleBondDuplicateNodes expansion.graph.toRootedDigraph parent duplicatedAtom) := by
  rcases faithful.1.2 with ⟨_addressing, multiplicities⟩
  have parentAtomEq : (expansion.graph.label parent).atom? = some parentAtom := by
    simp [parentLabel]
  have parentReal : ProvenanceRealAtom (expansion.graph.label parent).provenance := by
    simp [parentLabel, ProvenanceRealAtom]
  have categoryCount :=
    (multiplicities parent parentAtom parentAtomEq parentReal duplicatedAtom).2.1
  refine ⟨parentLabel, multipleBond,
    p92MultipleBondDuplicateNodes_nodup expansion.graph.toRootedDigraph parent duplicatedAtom,
      ?_, ?_⟩
  · calc
      (p92MultipleBondDuplicateNodes expansion.graph.toRootedDigraph parent duplicatedAtom).length =
          ChildLabelCount expansion.graph.toRootedDigraph parent
            ⟨some duplicatedAtom, NodeProvenance.multipleBondDuplicate
              (expansion.graph.depth parent + 1)⟩ :=
        p92MultipleBondDuplicateNodes_length_eq_childLabelCount expansion.graph.toRootedDigraph parent
          duplicatedAtom
      _ = ChildAtomProvenanceCount expansion.graph.toRootedDigraph parent duplicatedAtom
          ProvenanceMultipleBondDuplicate :=
        faithful.childMultipleBondLabelCount_eq_category expansion.molecule
          expansion.externalParent expansion.ligand expansion.graph.toRootedDigraph parent duplicatedAtom
          (expansion.graph.depth parent + 1) rfl
      _ = expansion.molecule.bond parentAtom duplicatedAtom - 1 := categoryCount
  · intro node
    exact p92MultipleBondDuplicateNodes_mem_iff_child expansion parent node duplicatedAtom

/-! ## Executable source-semantic duplicate enumeration -/

/-- Boolean recognition of one exact multiple-bond duplicate label.  Matching the provenance by
constructor avoids requiring a global `DecidableEq NodeProvenance` instance. -/
def p92MultipleBondDuplicateLabelAt? {Atom : Type} [DecidableEq Atom]
    (label : NodeLabel Atom) (atom : Atom) (distance : Nat) : Bool :=
  decide (label.atom? = some atom) &&
    match label.provenance with
    | .multipleBondDuplicate observed => decide (observed = distance)
    | _ => false

@[simp] theorem p92MultipleBondDuplicateLabelAt?_eq_true_iff
    {Atom : Type} [DecidableEq Atom]
    (label : NodeLabel Atom) (atom : Atom) (distance : Nat) :
    p92MultipleBondDuplicateLabelAt? label atom distance = true ↔
      label = ⟨some atom, NodeProvenance.multipleBondDuplicate distance⟩ := by
  rcases label with ⟨atom?, provenance⟩
  cases provenance <;> simp [p92MultipleBondDuplicateLabelAt?]

/-- Executable enumeration of one duplicate-label child fiber in the canonical semantic tree. -/
def p92SemanticMultipleBondDuplicateNodes
    {vertex : Type} [DecidableEq vertex]
    (tree : OfficialCIPSourceTree vertex)
    (parent : (p92SemanticFiniteRootedDigraph tree).Node)
    (atom : vertex) : List (p92SemanticFiniteRootedDigraph tree).Node :=
  let graph := p92SemanticFiniteRootedDigraph tree
  letI : DecidableRel graph.child := p92SemanticFiniteRootedDigraph_childDecidable tree
  (List.finRange graph.nodeCount).filter fun node =>
    decide (graph.child parent node) &&
      p92MultipleBondDuplicateLabelAt? (graph.label node) atom (graph.depth parent + 1)

theorem p92SemanticMultipleBondDuplicateNodes_nodup
    {vertex : Type} [DecidableEq vertex]
    (tree : OfficialCIPSourceTree vertex)
    (parent : (p92SemanticFiniteRootedDigraph tree).Node)
    (atom : vertex) :
    (p92SemanticMultipleBondDuplicateNodes tree parent atom).Nodup := by
  unfold p92SemanticMultipleBondDuplicateNodes
  exact List.Nodup.filter _ (List.nodup_finRange _)

theorem p92SemanticMultipleBondDuplicateNodes_mem_iff_label
    {vertex : Type} [DecidableEq vertex]
    (tree : OfficialCIPSourceTree vertex)
    (parent node : (p92SemanticFiniteRootedDigraph tree).Node)
    (atom : vertex) :
    node ∈ p92SemanticMultipleBondDuplicateNodes tree parent atom ↔
      (p92SemanticFiniteRootedDigraph tree).child parent node ∧
        (p92SemanticFiniteRootedDigraph tree).label node =
          ⟨some atom, NodeProvenance.multipleBondDuplicate
            ((p92SemanticFiniteRootedDigraph tree).depth parent + 1)⟩ := by
  letI : DecidableRel (p92SemanticFiniteRootedDigraph tree).child :=
    p92SemanticFiniteRootedDigraph_childDecidable tree
  simp [p92SemanticMultipleBondDuplicateNodes, Bool.and_eq_true]

theorem p92SemanticMultipleBondDuplicateNodes_mem_iff_child
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount)
    (parent node : (p92SemanticExactDigraphObservation source center ligand).graph.Node)
    (atom : Fin source.molecule.atomCount) :
    node ∈ p92SemanticMultipleBondDuplicateNodes
        (p92SemanticOfficialSourceTree source center ligand) parent atom ↔
      P92MultipleBondDuplicateChild
        (p92SemanticExactDigraphObservation source center ligand) parent atom node := by
  rw [p92SemanticMultipleBondDuplicateNodes_mem_iff_label]
  constructor
  · rintro ⟨edge, label⟩
    exact ⟨edge, _, label, rfl⟩
  · rintro ⟨edge, distance, label, distanceEq⟩
    exact ⟨edge, by simpa [distanceEq] using label⟩

/-- Exact child-fiber evidence is invariant under permutation of its concrete enumeration. -/
theorem P92MultipleBondDuplicateChildrenExact.perm
    {expansion : P92ExactDigraphAuthorityObservation}
    {parent : expansion.graph.Node}
    {parentAtom duplicatedAtom : Fin expansion.atomCount}
    {left right : List expansion.graph.Node}
    (exact : P92MultipleBondDuplicateChildrenExact expansion parent parentAtom duplicatedAtom left)
    (permutation : left.Perm right) :
    P92MultipleBondDuplicateChildrenExact expansion parent parentAtom duplicatedAtom right := by
  rcases exact with ⟨parentLabel, multipleBond, nodup, lengthEq, member⟩
  exact ⟨parentLabel, multipleBond, permutation.nodup_iff.mp nodup,
    permutation.length_eq.symm.trans lengthEq, fun node => by
      rw [← permutation.mem_iff]
      exact member node⟩

/-- The executable finite-range scan yields exactly the complete duplicate-child observation. -/
theorem P92ExactDigraphAuthorityObservation.generatedSemanticMultipleBondDuplicateChildrenExact
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount)
    (faithful : (p92SemanticExactDigraphObservation source center ligand).Faithful)
    (parent : (p92SemanticExactDigraphObservation source center ligand).graph.Node)
    (parentAtom duplicatedAtom : Fin source.molecule.atomCount)
    (parentLabel : (p92SemanticExactDigraphObservation source center ligand).graph.label parent =
      ⟨some parentAtom, NodeProvenance.realAtom⟩)
    (multipleBond : 1 < (p92SemanticExactDigraphObservation source center ligand).molecule.bond
      parentAtom duplicatedAtom) :
    P92MultipleBondDuplicateChildrenExact
      (p92SemanticExactDigraphObservation source center ligand) parent parentAtom duplicatedAtom
      (p92SemanticMultipleBondDuplicateNodes
        (p92SemanticOfficialSourceTree source center ligand) parent duplicatedAtom) := by
  let expansion := p92SemanticExactDigraphObservation source center ligand
  let oldNodes := p92MultipleBondDuplicateNodes expansion.graph.toRootedDigraph parent duplicatedAtom
  let newNodes := p92SemanticMultipleBondDuplicateNodes
    (p92SemanticOfficialSourceTree source center ligand) parent duplicatedAtom
  have oldExact := expansion.generatedMultipleBondDuplicateChildrenExact faithful parent
    parentAtom duplicatedAtom parentLabel multipleBond
  have oldNodup := p92MultipleBondDuplicateNodes_nodup
    expansion.graph.toRootedDigraph parent duplicatedAtom
  have newNodup := p92SemanticMultipleBondDuplicateNodes_nodup
    (p92SemanticOfficialSourceTree source center ligand) parent duplicatedAtom
  have sameMembers : ∀ node, node ∈ oldNodes ↔ node ∈ newNodes := by
    intro node
    rw [p92MultipleBondDuplicateNodes_mem_iff_child,
      p92SemanticMultipleBondDuplicateNodes_mem_iff_child]
  have permutation : oldNodes.Perm newNodes :=
    (List.perm_ext_iff_of_nodup oldNodup newNodup).mpr sameMembers
  exact oldExact.perm permutation

/-! ## Production observations and authority-row projections -/

noncomputable def p92ProductionRule1aMultipleBondDuplicatesObservation
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (parentNode : (key.toDeclarativeDigraph mol).Node)
    (parentAtom duplicatedAtom : Fin mol.atomCount) :
    P92Rule1aMultipleBondDuplicatesAuthorityObservation where
  expansion := p92ProductionExactDigraphObservation mol center ligand key
  parentNode := (P92FiniteRootedDigraph.ofRootedDigraphIso
    (key.toDeclarativeDigraph mol)).toEquiv parentNode
  parentAtom := parentAtom
  duplicatedAtom := duplicatedAtom
  duplicateNodes :=
    p92MultipleBondDuplicateNodes
      (P92FiniteRootedDigraph.ofRootedDigraph
        (key.toDeclarativeDigraph mol)).toRootedDigraph
      ((P92FiniteRootedDigraph.ofRootedDigraphIso
        (key.toDeclarativeDigraph mol)).toEquiv parentNode) duplicatedAtom

theorem p92ProductionRule1aMultipleBondDuplicates_judged
    (source : AuthoritativeChemicalInput)
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (represents : P92CanonicalConstitutionRepresents source center ligand
      (mol.canonicalHierarchyMoleculeGraph center ligand))
    (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (built : branchCanonicalKey? mol center ligand = some key)
    (complete : key.complete = true)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (parentNode : (key.toDeclarativeDigraph mol).Node)
    (parentAtom duplicatedAtom : Fin mol.atomCount)
    (parentLabel : (key.toDeclarativeDigraph mol).label parentNode =
      ⟨some parentAtom, NodeProvenance.realAtom⟩)
    (multipleBond :
      1 < (mol.canonicalHierarchyMoleculeGraph center ligand).bond parentAtom duplicatedAtom) :
    p92Rule1aMultipleBondDuplicatesReference.Judges source
      (p92ProductionRule1aMultipleBondDuplicatesObservation mol center ligand key parentNode
        parentAtom duplicatedAtom) := by
  let faithful := p92ProductionExactDigraphObservation_faithful mol center ligand key wellFormed
    bondRecordsUnique built complete rootBond
  let graphIso := P92FiniteRootedDigraph.ofRootedDigraphIso (key.toDeclarativeDigraph mol)
  have encodedParentLabel :
      (P92FiniteRootedDigraph.ofRootedDigraph
        (key.toDeclarativeDigraph mol)).label (graphIso.toEquiv parentNode) =
          ⟨some parentAtom, NodeProvenance.realAtom⟩ :=
    (graphIso.map_label parentNode).symm.trans parentLabel
  exact ⟨represents, faithful,
    P92ExactDigraphAuthorityObservation.generatedMultipleBondDuplicateChildrenExact
      (p92ProductionExactDigraphObservation mol center ligand key) faithful
      (graphIso.toEquiv parentNode) parentAtom duplicatedAtom encodedParentLabel multipleBond⟩

noncomputable def p92ProductionRule1aDoubleTripleBondsObservation
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (leftNode rightNode : (key.toDeclarativeDigraph mol).Node)
    (leftAtom rightAtom : Fin mol.atomCount) :
    P92Rule1aDoubleTripleBondsAuthorityObservation where
  expansion := p92ProductionExactDigraphObservation mol center ligand key
  leftNode := (P92FiniteRootedDigraph.ofRootedDigraphIso
    (key.toDeclarativeDigraph mol)).toEquiv leftNode
  rightNode := (P92FiniteRootedDigraph.ofRootedDigraphIso
    (key.toDeclarativeDigraph mol)).toEquiv rightNode
  leftAtom := leftAtom
  rightAtom := rightAtom
  duplicatesAtLeft :=
    p92MultipleBondDuplicateNodes
      (P92FiniteRootedDigraph.ofRootedDigraph
        (key.toDeclarativeDigraph mol)).toRootedDigraph
      ((P92FiniteRootedDigraph.ofRootedDigraphIso
        (key.toDeclarativeDigraph mol)).toEquiv leftNode) rightAtom
  duplicatesAtRight :=
    p92MultipleBondDuplicateNodes
      (P92FiniteRootedDigraph.ofRootedDigraph
        (key.toDeclarativeDigraph mol)).toRootedDigraph
      ((P92FiniteRootedDigraph.ofRootedDigraphIso
        (key.toDeclarativeDigraph mol)).toEquiv rightNode) leftAtom

theorem p92ProductionRule1aDoubleTripleBonds_judged
    (source : AuthoritativeChemicalInput)
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (represents : P92CanonicalConstitutionRepresents source center ligand
      (mol.canonicalHierarchyMoleculeGraph center ligand))
    (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (built : branchCanonicalKey? mol center ligand = some key)
    (complete : key.complete = true)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (leftNode rightNode : (key.toDeclarativeDigraph mol).Node)
    (leftAtom rightAtom : Fin mol.atomCount)
    (leftLabel : (key.toDeclarativeDigraph mol).label leftNode =
      ⟨some leftAtom, NodeProvenance.realAtom⟩)
    (rightLabel : (key.toDeclarativeDigraph mol).label rightNode =
      ⟨some rightAtom, NodeProvenance.realAtom⟩)
    (bondOrder :
      (mol.canonicalHierarchyMoleculeGraph center ligand).bond leftAtom rightAtom = 2 ∨
        (mol.canonicalHierarchyMoleculeGraph center ligand).bond leftAtom rightAtom = 3) :
    p92Rule1aDoubleTripleBondsReference.Judges source
      (p92ProductionRule1aDoubleTripleBondsObservation mol center ligand key leftNode rightNode
        leftAtom rightAtom) := by
  let molecule := mol.canonicalHierarchyMoleculeGraph center ligand
  let expansion := p92ProductionExactDigraphObservation mol center ligand key
  let faithful := p92ProductionExactDigraphObservation_faithful mol center ligand key wellFormed
    bondRecordsUnique built complete rootBond
  let graphIso := P92FiniteRootedDigraph.ofRootedDigraphIso (key.toDeclarativeDigraph mol)
  have encodedLeftLabel :
      (P92FiniteRootedDigraph.ofRootedDigraph
        (key.toDeclarativeDigraph mol)).label (graphIso.toEquiv leftNode) =
          ⟨some leftAtom, NodeProvenance.realAtom⟩ :=
    (graphIso.map_label leftNode).symm.trans leftLabel
  have encodedRightLabel :
      (P92FiniteRootedDigraph.ofRootedDigraph
        (key.toDeclarativeDigraph mol)).label (graphIso.toEquiv rightNode) =
          ⟨some rightAtom, NodeProvenance.realAtom⟩ :=
    (graphIso.map_label rightNode).symm.trans rightLabel
  have leftMultiple : 1 < molecule.bond leftAtom rightAtom := by
    change 1 < (mol.canonicalHierarchyMoleculeGraph center ligand).bond leftAtom rightAtom
    rcases bondOrder with bondOrder | bondOrder
    · rw [bondOrder]
      decide
    · rw [bondOrder]
      decide
  have rightMultiple : 1 < molecule.bond rightAtom leftAtom := by
    rw [← molecule.bond_symm leftAtom rightAtom]
    exact leftMultiple
  have leftExact :=
    P92ExactDigraphAuthorityObservation.generatedMultipleBondDuplicateChildrenExact
      expansion faithful (graphIso.toEquiv leftNode) leftAtom rightAtom encodedLeftLabel leftMultiple
  have rightExact :=
    P92ExactDigraphAuthorityObservation.generatedMultipleBondDuplicateChildrenExact
      expansion faithful (graphIso.toEquiv rightNode) rightAtom leftAtom encodedRightLabel rightMultiple
  exact ⟨represents, faithful, bondOrder, leftExact, rightExact⟩

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92MultipleBondDuplicateNodes_mem_iff_child
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92MultipleBondDuplicateNodes_length_eq_childLabelCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.P92ExactDigraphAuthorityObservation.generatedMultipleBondDuplicateChildrenExact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ProductionRule1aMultipleBondDuplicates_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ProductionRule1aDoubleTripleBonds_judged
