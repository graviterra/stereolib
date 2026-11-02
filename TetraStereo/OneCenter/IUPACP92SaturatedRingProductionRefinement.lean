import TetraStereo.OneCenter.IUPACP92ScheduleAndScalarProductionRefinement
import TetraStereo.OneCenter.IUPACP92SemanticGraphProductionCore

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Production refinement for the P-92 saturated-ring row

The independent saturated-ring reference names a concrete real-node ancestry path and a closing
ring duplicate.  These witnesses are representation data, so production conformance must not
require byte-for-byte node identity.  This module transports the complete observation through the
faithful production/reference `RootedDigraph.Iso`, preserving real labels, path edges, closing
labels, and intrinsic duplicate distance.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open DeclarativeCIP
open RawMolecule

/-! ## Uniform graph-backed observations -/

def p92ExactDigraphObservationOfGraph
    (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
    (externalParent ligand : Fin atomCount)
    (graph : P92FiniteRootedDigraph (Fin atomCount)) : P92ExactDigraphAuthorityObservation where
  atomCount := atomCount
  molecule := molecule
  externalParent := externalParent
  ligand := ligand
  graph := graph

def p92Rule1aSaturatedRingsObservationOfGraph
    (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
    (externalParent ligand : Fin atomCount)
    (graph : P92FiniteRootedDigraph (Fin atomCount))
    (ringAtoms : List (Fin atomCount))
    (ringNodes : List graph.Node) (closingDuplicate : graph.Node) :
    P92Rule1aSaturatedRingsAuthorityObservation where
  expansion := p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand graph
  ringAtoms := ringAtoms
  ringNodes := ringNodes
  closingDuplicate := closingDuplicate

/-! ## Exhaustive executable source-semantic ring realizations -/

/-- Every possible ordered distinct atom cycle occurs in this finite source-only carrier. -/
def p92CandidateRingAtomLists (atomCount : Nat) : List (List (Fin atomCount)) :=
  (List.finRange atomCount).sublists.flatMap List.permutations

theorem mem_p92CandidateRingAtomLists_of_nodup
    {atomCount : Nat} (atoms : List (Fin atomCount)) (nodup : atoms.Nodup) :
    atoms ∈ p92CandidateRingAtomLists atomCount := by
  rcases List.subperm_of_subset nodup (fun atom _ => List.mem_finRange atom) with
    ⟨candidate, candidatePerm, candidateSublist⟩
  simp only [p92CandidateRingAtomLists, List.mem_flatMap]
  exact ⟨candidate, List.mem_sublists.mpr candidateSublist,
    List.mem_permutations.mpr candidatePerm.symm⟩

/-- Cartesian power of a finite list, retaining order and repetition. -/
def p92ListsOfLength {alpha : Type} (values : List alpha) : Nat → List (List alpha)
  | 0 => [[]]
  | length + 1 => values.flatMap fun value =>
      (p92ListsOfLength values length).map (List.cons value)

theorem mem_p92ListsOfLength_iff {alpha : Type} (values : List alpha) :
    ∀ (length : Nat) (items : List alpha),
      items ∈ p92ListsOfLength values length ↔
        items.length = length ∧ ∀ item, item ∈ items → item ∈ values
  | 0, [] => by simp [p92ListsOfLength]
  | 0, _ :: _ => by simp [p92ListsOfLength]
  | _ + 1, [] => by simp [p92ListsOfLength]
  | length + 1, item :: items => by
      simp [p92ListsOfLength, mem_p92ListsOfLength_iff, and_comm, and_left_comm, and_assoc]

def p92FiniteRootedDigraphNodes {Atom : Type}
    (graph : P92FiniteRootedDigraph Atom) : List graph.Node :=
  List.finRange graph.nodeCount

@[simp] theorem mem_p92FiniteRootedDigraphNodes {Atom : Type}
    (graph : P92FiniteRootedDigraph Atom) (node : graph.Node) :
    node ∈ p92FiniteRootedDigraphNodes graph :=
  List.mem_finRange node

/-- Boolean recognition of one exact real-atom label. -/
def p92RealAtomLabel? {Atom : Type} [DecidableEq Atom]
    (label : NodeLabel Atom) (atom : Atom) : Bool :=
  decide (label.atom? = some atom) &&
    match label.provenance with
    | .realAtom => true
    | _ => false

@[simp] theorem p92RealAtomLabel?_eq_true_iff
    {Atom : Type} [DecidableEq Atom]
    (label : NodeLabel Atom) (atom : Atom) :
    p92RealAtomLabel? label atom = true ↔
      label = ⟨some atom, NodeProvenance.realAtom⟩ := by
  rcases label with ⟨atom?, provenance⟩
  cases provenance <;> simp [p92RealAtomLabel?]

/-- Executable atom-for-atom real-node check. -/
def p92RealNodesRepresentAtoms?
    (expansion : P92ExactDigraphAuthorityObservation) :
    List (Fin expansion.atomCount) → List expansion.graph.Node → Bool
  | [], [] => true
  | atom :: atoms, node :: nodes =>
      p92RealAtomLabel? (expansion.graph.label node) atom &&
        p92RealNodesRepresentAtoms? expansion atoms nodes
  | _, _ => false

@[simp] theorem p92RealNodesRepresentAtoms?_eq_true_iff
    (expansion : P92ExactDigraphAuthorityObservation)
    (atoms : List (Fin expansion.atomCount)) (nodes : List expansion.graph.Node) :
    p92RealNodesRepresentAtoms? expansion atoms nodes = true ↔
      P92RealNodesRepresentAtoms expansion atoms nodes := by
  induction atoms generalizing nodes with
  | nil => cases nodes <;> simp [p92RealNodesRepresentAtoms?, P92RealNodesRepresentAtoms]
  | cons atom atoms inductionHypothesis =>
      cases nodes with
      | nil => simp [p92RealNodesRepresentAtoms?, P92RealNodesRepresentAtoms]
      | cons node nodes =>
          simp [p92RealNodesRepresentAtoms?, P92RealNodesRepresentAtoms,
            inductionHypothesis]

/-- Executable directed path check on a finite graph carrying a concrete edge decider. -/
def p92DigraphNodePath? {Atom : Type} (graph : RootedDigraph Atom)
    [DecidableRel graph.child] : List graph.Node → Bool
  | [] | [_] => true
  | first :: second :: rest =>
      decide (graph.child first second) && p92DigraphNodePath? graph (second :: rest)

@[simp] theorem p92DigraphNodePath?_eq_true_iff
    {Atom : Type} (graph : RootedDigraph Atom) [DecidableRel graph.child]
    (nodes : List graph.Node) :
    p92DigraphNodePath? graph nodes = true ↔ P92DigraphNodePath graph nodes := by
  induction nodes with
  | nil => simp [p92DigraphNodePath?, P92DigraphNodePath]
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil => simp [p92DigraphNodePath?, P92DigraphNodePath]
      | cons second rest =>
          simp [p92DigraphNodePath?, P92DigraphNodePath, inductionHypothesis]

/-- Boolean recognition of the exact distance-bearing closing ring-duplicate label. -/
def p92RingDuplicateLabelAt? {Atom : Type} [DecidableEq Atom]
    (label : NodeLabel Atom) (atom : Atom) (distance : Nat) : Bool :=
  decide (label.atom? = some atom) &&
    match label.provenance with
    | .ringDuplicate observed => decide (observed = distance)
    | _ => false

@[simp] theorem p92RingDuplicateLabelAt?_eq_true_iff
    {Atom : Type} [DecidableEq Atom]
    (label : NodeLabel Atom) (atom : Atom) (distance : Nat) :
    p92RingDuplicateLabelAt? label atom distance = true ↔
      label = ⟨some atom, NodeProvenance.ringDuplicate distance⟩ := by
  rcases label with ⟨atom?, provenance⟩
  cases provenance <;> simp [p92RingDuplicateLabelAt?]

/-- Executable check of the selected ancestry path's closing duplicate. -/
def p92SelectedRingClosureWitness?
    (expansion : P92ExactDigraphAuthorityObservation)
    [DecidableRel expansion.graph.child]
    (ringAtoms : List (Fin expansion.atomCount))
    (ringNodes : List expansion.graph.Node)
    (closing : expansion.graph.Node) : Bool :=
  match ringAtoms.head?, ringNodes.head?, ringNodes.getLast? with
  | some firstAtom, some firstNode, some lastNode =>
      decide (expansion.graph.child lastNode closing) &&
        p92RingDuplicateLabelAt? (expansion.graph.label closing) firstAtom
          (expansion.graph.depth firstNode + 1)
  | _, _, _ => false

@[simp] theorem p92SelectedRingClosureWitness?_eq_true_iff
    (expansion : P92ExactDigraphAuthorityObservation)
    [DecidableRel expansion.graph.child]
    (ringAtoms : List (Fin expansion.atomCount))
    (ringNodes : List expansion.graph.Node)
    (closing : expansion.graph.Node) :
    p92SelectedRingClosureWitness? expansion ringAtoms ringNodes closing = true ↔
      P92SelectedRingClosureWitness
        (p92Rule1aSaturatedRingsObservationOfGraph expansion.atomCount expansion.molecule
          expansion.externalParent expansion.ligand expansion.graph ringAtoms ringNodes closing) := by
  cases ringAtoms with
  | nil =>
      simp [p92SelectedRingClosureWitness?, P92SelectedRingClosureWitness,
        p92Rule1aSaturatedRingsObservationOfGraph]
  | cons firstAtom atoms =>
      cases ringNodes with
      | nil =>
          simp [p92SelectedRingClosureWitness?, P92SelectedRingClosureWitness,
            p92Rule1aSaturatedRingsObservationOfGraph]
      | cons firstNode nodes =>
          cases last : (firstNode :: nodes).getLast? with
          | none =>
              simp [p92SelectedRingClosureWitness?, P92SelectedRingClosureWitness,
                p92Rule1aSaturatedRingsObservationOfGraph, last]
          | some lastNode =>
              simp [p92SelectedRingClosureWitness?, P92SelectedRingClosureWitness,
                p92Rule1aSaturatedRingsObservationOfGraph, last]
              rfl

/-- All valid concrete node-path/closing-node realizations of one candidate atom cycle in the
fixed semantic graph. -/
def p92SemanticSaturatedRingRealizations
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount)
    (ringAtoms : List (Fin source.molecule.atomCount)) :
    List (List (p92SemanticExactDigraphObservation source center ligand).graph.Node ×
      (p92SemanticExactDigraphObservation source center ligand).graph.Node) :=
  let expansion := p92SemanticExactDigraphObservation source center ligand
  let graph := expansion.graph
  letI : DecidableRel graph.child := p92SemanticFiniteRootedDigraph_childDecidable
    (p92SemanticOfficialSourceTree source center ligand)
  letI : DecidableRel graph.toRootedDigraph.child := by
    change DecidableRel graph.child
    infer_instance
  ((p92ListsOfLength (p92FiniteRootedDigraphNodes graph) ringAtoms.length).product
      (p92FiniteRootedDigraphNodes graph)).filter fun realization =>
    p92RealNodesRepresentAtoms? expansion ringAtoms realization.1 &&
      p92DigraphNodePath? graph.toRootedDigraph realization.1 &&
        p92SelectedRingClosureWitness? expansion ringAtoms realization.1 realization.2

theorem mem_p92SemanticSaturatedRingRealizations_iff
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount)
    (ringAtoms : List (Fin source.molecule.atomCount))
    (ringNodes : List (p92SemanticExactDigraphObservation source center ligand).graph.Node)
    (closing : (p92SemanticExactDigraphObservation source center ligand).graph.Node) :
    (ringNodes, closing) ∈
        p92SemanticSaturatedRingRealizations source center ligand ringAtoms ↔
      P92RealNodesRepresentAtoms (p92SemanticExactDigraphObservation source center ligand)
          ringAtoms ringNodes ∧
        P92DigraphNodePath
          (p92SemanticExactDigraphObservation source center ligand).graph.toRootedDigraph
          ringNodes ∧
        P92SelectedRingClosureWitness
          (p92Rule1aSaturatedRingsObservationOfGraph source.molecule.atomCount
            (p92CanonicalLocalizedMoleculeGraph source center ligand) center ligand
            (p92SemanticExactDigraphObservation source center ligand).graph
            ringAtoms ringNodes closing) := by
  let expansion := p92SemanticExactDigraphObservation source center ligand
  let graph := expansion.graph
  letI : DecidableRel graph.child := p92SemanticFiniteRootedDigraph_childDecidable
    (p92SemanticOfficialSourceTree source center ligand)
  letI : DecidableRel graph.toRootedDigraph.child := by
    change DecidableRel graph.child
    infer_instance
  constructor
  · intro member
    simp only [p92SemanticSaturatedRingRealizations, List.mem_filter,
      Bool.and_eq_true] at member
    exact ⟨(p92RealNodesRepresentAtoms?_eq_true_iff expansion ringAtoms ringNodes).mp
        member.2.1.1,
      (p92DigraphNodePath?_eq_true_iff graph.toRootedDigraph ringNodes).mp member.2.1.2,
      (p92SelectedRingClosureWitness?_eq_true_iff expansion ringAtoms ringNodes closing).mp
        member.2.2⟩
  · rintro ⟨represented, path, closure⟩
    have representedLength : ringAtoms.length = ringNodes.length :=
      List.Forall₂.length_eq represented
    have lengthEq : ringNodes.length = ringAtoms.length := representedLength.symm
    simp only [p92SemanticSaturatedRingRealizations, List.mem_filter,
      Bool.and_eq_true]
    refine ⟨List.mem_product.mpr ⟨?_, mem_p92FiniteRootedDigraphNodes graph closing⟩,
      ⟨?_, ?_⟩, ?_⟩
    · exact (mem_p92ListsOfLength_iff (p92FiniteRootedDigraphNodes graph)
        ringAtoms.length ringNodes).mpr
          ⟨lengthEq, fun node _ => mem_p92FiniteRootedDigraphNodes graph node⟩
    · exact (p92RealNodesRepresentAtoms?_eq_true_iff expansion ringAtoms ringNodes).mpr represented
    · exact (p92DigraphNodePath?_eq_true_iff graph.toRootedDigraph ringNodes).mpr path
    · exact (p92SelectedRingClosureWitness?_eq_true_iff expansion ringAtoms ringNodes closing).mpr
        closure

def p92Rule1aSaturatedRingsTransport
    (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
    (externalParent ligand : Fin atomCount)
    (production reference : P92FiniteRootedDigraph (Fin atomCount))
    (iso : RootedDigraph.Iso production.toRootedDigraph reference.toRootedDigraph)
    (ringAtoms : List (Fin atomCount))
    (referenceRingNodes : List reference.Node)
    (referenceClosingDuplicate : reference.Node) :
    P92Rule1aSaturatedRingsAuthorityObservation :=
  p92Rule1aSaturatedRingsObservationOfGraph atomCount molecule externalParent ligand production
    ringAtoms (referenceRingNodes.map iso.toEquiv.symm)
      (iso.toEquiv.symm referenceClosingDuplicate)

/-! ## Transport of every representation-bearing clause -/

theorem p92RealNodesRepresentAtoms_map_equivSymm
    (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
    (externalParent ligand : Fin atomCount)
    (production reference : P92FiniteRootedDigraph (Fin atomCount))
    (iso : RootedDigraph.Iso production.toRootedDigraph reference.toRootedDigraph)
    (atoms : List (Fin atomCount)) (nodes : List reference.Node)
    (represented : P92RealNodesRepresentAtoms
      (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand reference)
      atoms nodes) :
    P92RealNodesRepresentAtoms
      (p92ExactDigraphObservationOfGraph atomCount molecule externalParent ligand production)
      atoms (nodes.map iso.toEquiv.symm) := by
  induction represented with
  | nil => exact List.Forall₂.nil
  | @cons atom node atoms nodes head tail inductionHypothesis =>
      apply List.Forall₂.cons
      · have labelMap := iso.map_label (iso.toEquiv.symm node)
        have mappedNode : iso.toEquiv (iso.toEquiv.symm node) = node := by simp
        rw [mappedNode] at labelMap
        exact labelMap.trans head
      · exact inductionHypothesis

theorem p92DigraphNodePath_map_equivSymm
    {Atom : Type} {production reference : RootedDigraph Atom}
    (iso : RootedDigraph.Iso production reference) :
    ∀ nodes,
      P92DigraphNodePath reference nodes →
        P92DigraphNodePath production (nodes.map iso.toEquiv.symm)
  | [], _path => trivial
  | [node], _path => trivial
  | first :: second :: rest, path => by
      simp only [P92DigraphNodePath, List.map_cons] at path ⊢
      refine ⟨?_, p92DigraphNodePath_map_equivSymm iso (second :: rest) path.2⟩
      apply (iso.map_child (iso.toEquiv.symm first) (iso.toEquiv.symm second)).2
      simpa using path.1

theorem p92SelectedRingClosureWitness_transport
    (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
    (externalParent ligand : Fin atomCount)
    (production reference : P92FiniteRootedDigraph (Fin atomCount))
    (iso : RootedDigraph.Iso production.toRootedDigraph reference.toRootedDigraph)
    (ringAtoms : List (Fin atomCount))
    (referenceRingNodes : List reference.Node)
    (referenceClosingDuplicate : reference.Node)
    (closure : P92SelectedRingClosureWitness
      (p92Rule1aSaturatedRingsObservationOfGraph atomCount molecule externalParent ligand
        reference ringAtoms referenceRingNodes referenceClosingDuplicate)) :
    P92SelectedRingClosureWitness
      (p92Rule1aSaturatedRingsTransport atomCount molecule externalParent ligand production
        reference iso ringAtoms referenceRingNodes referenceClosingDuplicate) := by
  rcases closure with
    ⟨firstAtom, firstNode, lastNode, distance, atomsHead, nodesHead, nodesLast,
      closingEdge, closingLabel, distanceEq⟩
  refine ⟨firstAtom, iso.toEquiv.symm firstNode, iso.toEquiv.symm lastNode, distance,
    atomsHead, ?_, ?_, ?_, ?_, ?_⟩
  · have rawNodesHead : referenceRingNodes.head? = some firstNode := by
      simpa [p92Rule1aSaturatedRingsObservationOfGraph] using nodesHead
    simp [p92Rule1aSaturatedRingsTransport,
      p92Rule1aSaturatedRingsObservationOfGraph]
    exact ⟨firstNode, rawNodesHead, rfl⟩
  · have rawNodesLast : referenceRingNodes.getLast? = some lastNode := by
      simpa [p92Rule1aSaturatedRingsObservationOfGraph] using nodesLast
    simp [p92Rule1aSaturatedRingsTransport,
      p92Rule1aSaturatedRingsObservationOfGraph]
    exact ⟨lastNode, rawNodesLast, rfl⟩
  · apply (iso.map_child (iso.toEquiv.symm lastNode)
      (iso.toEquiv.symm referenceClosingDuplicate)).2
    simpa using closingEdge
  · have labelMap := iso.map_label (iso.toEquiv.symm referenceClosingDuplicate)
    have mappedNode : iso.toEquiv (iso.toEquiv.symm referenceClosingDuplicate) =
        referenceClosingDuplicate := by simp
    rw [mappedNode] at labelMap
    exact labelMap.trans closingLabel
  · have depthMap := iso.map_depth (iso.toEquiv.symm firstNode)
    have mappedNode : iso.toEquiv (iso.toEquiv.symm firstNode) = firstNode := by simp
    rw [mappedNode] at depthMap
    calc
      distance = reference.depth firstNode + 1 := distanceEq
      _ = production.depth (iso.toEquiv.symm firstNode) + 1 :=
        congrArg (fun depth => depth + 1) depthMap.symm

/-- Every independently judged saturated-ring observation transports to the production
representation along the faithful-expansion isomorphism. -/
theorem p92Rule1aSaturatedRings_judged_transport
    (source : AuthoritativeChemicalInput)
    (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
    (externalParent ligand : Fin atomCount)
    (production reference : P92FiniteRootedDigraph (Fin atomCount))
    (iso : RootedDigraph.Iso production.toRootedDigraph reference.toRootedDigraph)
    (productionFaithful : RootedDigraph.FaithfulExactExpansion
      molecule externalParent ligand production.toRootedDigraph)
    (ringAtoms : List (Fin atomCount))
    (referenceRingNodes : List reference.Node)
    (referenceClosingDuplicate : reference.Node)
    (referenceJudged : p92Rule1aSaturatedRingsReference.Judges source
      (p92Rule1aSaturatedRingsObservationOfGraph atomCount molecule externalParent ligand
        reference ringAtoms referenceRingNodes referenceClosingDuplicate)) :
    p92Rule1aSaturatedRingsReference.Judges source
      (p92Rule1aSaturatedRingsTransport atomCount molecule externalParent ligand production
        reference iso ringAtoms referenceRingNodes referenceClosingDuplicate) := by
  rcases referenceJudged with
    ⟨represents, _referenceFaithful, saturatedRing, represented, path, closure⟩
  exact ⟨represents, productionFaithful, saturatedRing,
    p92RealNodesRepresentAtoms_map_equivSymm atomCount molecule externalParent ligand production
      reference iso ringAtoms referenceRingNodes represented,
    p92DigraphNodePath_map_equivSymm iso referenceRingNodes path,
    p92SelectedRingClosureWitness_transport atomCount molecule externalParent ligand production
      reference iso ringAtoms referenceRingNodes referenceClosingDuplicate closure⟩

/-! ## Concrete complete-hierarchy projection -/

/-- The exact production/reference isomorphism selected from the two faithful expansions.  This
choice is representation data only: all transported propositions are invariant under every such
isomorphism by the preceding theorems. -/
noncomputable def p92ProductionReferenceIso
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (built : branchCanonicalKey? mol center ligand = some key)
    (complete : key.complete = true)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (reference : RootedDigraph (Fin mol.atomCount))
    (referenceFaithful : RootedDigraph.FaithfulExactExpansion
      (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand reference) :
    RootedDigraph.Iso (key.toDeclarativeDigraph mol) reference :=
  Classical.choice
    (RootedDigraph.faithfulExactExpansion_unique_up_to_iso
      (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
      (key.toDeclarativeDigraph mol) reference
      (mol.branchCanonicalKey?_faithfulExactExpansion center ligand key wellFormed
        bondRecordsUnique built complete rootBond)
      referenceFaithful)

noncomputable def p92ProductionRule1aSaturatedRingsObservation
    (source : AuthoritativeChemicalInput)
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (built : branchCanonicalKey? mol center ligand = some key)
    (complete : key.complete = true)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (reference : P92FiniteRootedDigraph (Fin mol.atomCount))
    (ringAtoms : List (Fin mol.atomCount))
    (referenceRingNodes : List reference.Node)
    (referenceClosingDuplicate : reference.Node)
    (referenceJudged : p92Rule1aSaturatedRingsReference.Judges source
      (p92Rule1aSaturatedRingsObservationOfGraph mol.atomCount
        (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand reference ringAtoms
        referenceRingNodes referenceClosingDuplicate)) :
    P92Rule1aSaturatedRingsAuthorityObservation :=
  let production := P92FiniteRootedDigraph.ofRootedDigraph (key.toDeclarativeDigraph mol)
  let productionIso := P92FiniteRootedDigraph.ofRootedDigraphIso (key.toDeclarativeDigraph mol)
  let referenceIso := p92ProductionReferenceIso mol center ligand key wellFormed
    bondRecordsUnique built complete rootBond reference.toRootedDigraph referenceJudged.2.1
  let transportIso := productionIso.symm.trans referenceIso
  p92Rule1aSaturatedRingsTransport mol.atomCount
    (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
      production reference transportIso ringAtoms referenceRingNodes
        referenceClosingDuplicate

theorem p92ProductionRule1aSaturatedRings_judged
    (source : AuthoritativeChemicalInput)
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (built : branchCanonicalKey? mol center ligand = some key)
    (complete : key.complete = true)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (reference : P92FiniteRootedDigraph (Fin mol.atomCount))
    (ringAtoms : List (Fin mol.atomCount))
    (referenceRingNodes : List reference.Node)
    (referenceClosingDuplicate : reference.Node)
    (referenceJudged : p92Rule1aSaturatedRingsReference.Judges source
      (p92Rule1aSaturatedRingsObservationOfGraph mol.atomCount
        (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand reference ringAtoms
        referenceRingNodes referenceClosingDuplicate)) :
    p92Rule1aSaturatedRingsReference.Judges source
      (p92ProductionRule1aSaturatedRingsObservation source mol center ligand key wellFormed
        bondRecordsUnique built complete rootBond reference ringAtoms referenceRingNodes
        referenceClosingDuplicate referenceJudged) := by
  let production := P92FiniteRootedDigraph.ofRootedDigraph (key.toDeclarativeDigraph mol)
  let productionIso := P92FiniteRootedDigraph.ofRootedDigraphIso (key.toDeclarativeDigraph mol)
  let referenceIso := p92ProductionReferenceIso mol center ligand key wellFormed
    bondRecordsUnique built complete rootBond reference.toRootedDigraph referenceJudged.2.1
  let transportIso := productionIso.symm.trans referenceIso
  have productionFaithful : RootedDigraph.FaithfulExactExpansion
      (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
        production.toRootedDigraph :=
    p92ProductionExactDigraphObservation_faithful mol center ligand key wellFormed
      bondRecordsUnique built complete rootBond
  exact p92Rule1aSaturatedRings_judged_transport source mol.atomCount
    (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
    production reference transportIso productionFaithful
    ringAtoms referenceRingNodes referenceClosingDuplicate referenceJudged

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92RealNodesRepresentAtoms_map_equivSymm
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92DigraphNodePath_map_equivSymm
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92SelectedRingClosureWitness_transport
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92Rule1aSaturatedRings_judged_transport
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ProductionRule1aSaturatedRings_judged
