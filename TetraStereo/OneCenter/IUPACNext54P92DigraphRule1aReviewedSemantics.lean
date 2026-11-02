import TetraStereo.OneCenter.IUPACNext54ProvisionInventory
import TetraStereo.OneCenter.DeclarativeCIPConstitutional
import TetraStereo.OneCenter.DeclarativeCIPFirstDifferenceSchedule

set_option autoImplicit false

/-!
# Independent reviewed targets for the 11 P-92 digraph and Rule-1a provisions

This module closes the remaining P-92 part of the exact next-54 work unit.  The references are
source-facing relations over the independent declarative CIP model:

* exact finite rooted-digraph expansion for acyclic, multiple-bond, and cyclic cases;
* the all-maximum-matching rational observation for mancude systems;
* sphere-major first-difference comparison; and
* explicit Rule-1a duplicate, saturated, multiple-bond, ring, and mancude observations.

No reference calls a production hierarchy builder, comparator, scheduler, or descriptor pipeline.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open DeclarativeCIP

noncomputable section

/-! ## Format-neutral constitutional observation boundary -/

/-- Exact atom datum consumed by the constitutional P-92 graph.  The graph's `atomMass` field is
the frozen Rule-2 picodalton key, not the isotope mass number printed in the source spelling. -/
def P92SemanticAtomRepresents {atomCount : Nat}
    (molecule : MoleculeGraph (Fin atomCount)) (atom : Fin atomCount)
    (sourceAtom : SemanticAtom) : Prop :=
  molecule.atomZ atom = sourceAtom.element.atomicNumber ∧
    ∃ mass,
      CIPRule2MassData.rule2MassPico? sourceAtom.element.atomicNumber
          sourceAtom.isotopeMassNumber? = some mass ∧
        molecule.atomMass atom = mass ∧
        molecule.formalCharge atom = sourceAtom.formalCharge ∧
        sourceAtom.unpairedElectrons = 0 ∧
        sourceAtom.aromaticInput = false

/-- One pairwise covalent interaction in the format-neutral authority input is represented by
the corresponding unordered edge and exact bond order of a finite CIP molecule graph. -/
def P92PairInteractionRepresents {atomCount : Nat}
    (molecule : MoleculeGraph (Fin atomCount))
    (left right : Fin atomCount) (interaction : SemanticInteraction) : Prop :=
  (interaction.participants = [left.val, right.val] ∨
      interaction.participants = [right.val, left.val]) ∧
    interaction.kind = .covalent (molecule.bond left right)

/-- Exact admitted bridge from the universal semantic molecule to the deliberately smaller
constitutional graph used by the P-92 implementation.

This is a relation, not a claimed total encoder.  It deliberately admits precisely the classical
pairwise-covalent subdomain represented by `MoleculeGraph`: atom identity, isotope, and charge are
preserved; unsupported radical/aromatic atom flags are absent; every semantic interaction is one
positive graph edge; and every positive graph edge has exactly one semantic interaction.  Hence a
P-92 observation cannot be judged against an unrelated `AuthoritativeChemicalInput`, while inputs
using the wider 118-element/interaction vocabulary remain valid authority inputs for other
families. -/
structure P92ClassicalConstitutionRepresents
    (source : AuthoritativeChemicalInput) {atomCount : Nat}
    (molecule : MoleculeGraph (Fin atomCount)) : Prop where
  atomCount_exact : source.molecule.atomCount = atomCount
  interaction_records_nodup : source.molecule.interactions.Nodup
  atom_exact : ∀ atom : Fin atomCount, ∃ sourceAtom : SemanticAtom,
    listGet? source.molecule.atoms atom.val = some sourceAtom ∧
      P92SemanticAtomRepresents molecule atom sourceAtom
  interaction_supported : ∀ interaction,
    interaction ∈ source.molecule.interactions →
      ∃ left right : Fin atomCount,
        left ≠ right ∧ 0 < molecule.bond left right ∧
          P92PairInteractionRepresents molecule left right interaction
  bond_exact : ∀ left right : Fin atomCount, left ≠ right →
    (0 < molecule.bond left right ↔
      ∃! interaction : SemanticInteraction,
        interaction ∈ source.molecule.interactions ∧
          P92PairInteractionRepresents molecule left right interaction)

/-! ### Independent P/S oxido root normalization -/

/-- The unordered distinguished root pair, stated independently of production. -/
def P92RootPair {atomCount : Nat} (center ligand left right : Fin atomCount) : Prop :=
  (left = center ∧ right = ligand) ∨ (left = ligand ∧ right = center)

/-- Independent graph-level characterization of the P/S oxido convention: a phosphorus or
sulfur center, oxygen ligand, and written/source double bond. -/
def P92OxidoRootEligible {atomCount : Nat}
    (molecule : MoleculeGraph (Fin atomCount)) (center ligand : Fin atomCount) : Prop :=
  (molecule.atomZ center = 15 ∨ molecule.atomZ center = 16) ∧
    molecule.atomZ ligand = 8 ∧ molecule.bond center ligand = 2

/-- Independent root-normalized bond order.  Only an eligible distinguished oxido root pair is
rewritten to one coordination-sphere edge; the diagonal is zero and every other edge is exact. -/
def P92CanonicalRootBond {atomCount : Nat}
    (molecule : MoleculeGraph (Fin atomCount)) (center ligand left right : Fin atomCount) : Nat :=
  by
    classical
    exact if left = right then 0
      else if P92RootPair center ligand left right ∧
          P92OxidoRootEligible molecule center ligand then 1
      else molecule.bond left right

/-- Exact source constitution followed by the one independently specified canonical-root
normalization used by the P-92 hierarchical digraph. -/
inductive P92CanonicalConstitutionRepresents
    (source : AuthoritativeChemicalInput) {atomCount : Nat}
    (center ligand : Fin atomCount) (canonical : MoleculeGraph (Fin atomCount)) : Prop where
  | intro
      (sourceGraph : MoleculeGraph (Fin atomCount))
      (sourceGraph_represents : P92ClassicalConstitutionRepresents source sourceGraph)
      (atomZ_exact : ∀ atom, canonical.atomZ atom = sourceGraph.atomZ atom)
      (atomMass_exact : ∀ atom, canonical.atomMass atom = sourceGraph.atomMass atom)
      (formalCharge_exact : ∀ atom,
        canonical.formalCharge atom = sourceGraph.formalCharge atom)
      (bond_exact : ∀ left right,
        canonical.bond left right = P92CanonicalRootBond sourceGraph center ligand left right) :
      P92CanonicalConstitutionRepresents source center ligand canonical

/-! ## Exact constitutional digraph references -/

/-- A universe-small code for an exact finite rooted digraph.  The node type is explicitly
`Fin nodeCount`, so the code itself lives in `Type` and can be carried by `ProvisionReference`
without erasing any node, edge, label, depth, or reachability evidence. -/
structure P92FiniteRootedDigraph (Atom : Type) where
  nodeCount : Nat
  root : Fin nodeCount
  child : Fin nodeCount → Fin nodeCount → Prop
  label : Fin nodeCount → NodeLabel Atom
  depth : Fin nodeCount → Nat
  root_depth : depth root = 0
  child_depth : ∀ {parent node}, child parent node → depth node = depth parent + 1
  reachable : ∀ node, Relation.ReflTransGen child root node

namespace P92FiniteRootedDigraph

abbrev Node {Atom : Type} (graph : P92FiniteRootedDigraph Atom) : Type := Fin graph.nodeCount

instance {Atom : Type} (graph : P92FiniteRootedDigraph Atom) : Fintype graph.Node :=
  inferInstance

def toRootedDigraph {Atom : Type} (graph : P92FiniteRootedDigraph Atom) :
    RootedDigraph Atom where
  Node := graph.Node
  nodeFintype := inferInstance
  root := graph.root
  child := graph.child
  label := graph.label
  depth := graph.depth
  root_depth := graph.root_depth
  child_depth := graph.child_depth
  reachable := graph.reachable

instance {Atom : Type} : Coe (P92FiniteRootedDigraph Atom) (RootedDigraph Atom) :=
  ⟨toRootedDigraph⟩

/-- Reindex any finite rooted digraph onto its canonical `Fin` node type.  This changes only node
names; the relation, labels, depths, root, and reachability witnesses are transported exactly. -/
noncomputable def ofRootedDigraph {Atom : Type} (graph : RootedDigraph Atom) :
    P92FiniteRootedDigraph Atom := by
  classical
  letI : Fintype graph.Node := graph.nodeFintype
  let nodeEquiv : graph.Node ≃ Fin (Fintype.card graph.Node) := Fintype.equivFin graph.Node
  refine
    { nodeCount := Fintype.card graph.Node
      root := nodeEquiv graph.root
      child := fun parent node => graph.child (nodeEquiv.symm parent) (nodeEquiv.symm node)
      label := fun node => graph.label (nodeEquiv.symm node)
      depth := fun node => graph.depth (nodeEquiv.symm node)
      root_depth := by simpa using graph.root_depth
      child_depth := ?_
      reachable := ?_ }
  · intro parent node edge
    simpa using graph.child_depth edge
  · intro node
    have sourceReachable := graph.reachable (nodeEquiv.symm node)
    have mapReachable : ∀ {target}, Relation.ReflTransGen graph.child graph.root target →
        Relation.ReflTransGen
          (fun parent child => graph.child (nodeEquiv.symm parent) (nodeEquiv.symm child))
          (nodeEquiv graph.root) (nodeEquiv target) := by
      intro target path
      induction path with
      | refl => exact .refl
      | tail path edge inductionHypothesis =>
          exact .tail inductionHypothesis (by simpa using edge)
    simpa using mapReachable sourceReachable

/-- The canonical finite-node encoding is an exact rooted-digraph isomorphism, not a quotient or
an observational approximation. -/
noncomputable def ofRootedDigraphIso {Atom : Type} (graph : RootedDigraph Atom) :
    RootedDigraph.Iso graph (ofRootedDigraph graph).toRootedDigraph := by
  classical
  letI : Fintype graph.Node := graph.nodeFintype
  let nodeEquiv : graph.Node ≃ Fin (Fintype.card graph.Node) := Fintype.equivFin graph.Node
  exact
    { toEquiv := nodeEquiv
      map_root := rfl
      map_child := by simp [ofRootedDigraph, toRootedDigraph, nodeEquiv]
      map_label := by simp [ofRootedDigraph, toRootedDigraph, nodeEquiv]
      map_depth := by simp [ofRootedDigraph, toRootedDigraph, nodeEquiv] }

end P92FiniteRootedDigraph

/-- A finite molecular constitution paired with an independently supplied rooted ligand digraph. -/
structure P92ExactDigraphAuthorityObservation where
  atomCount : Nat
  molecule : MoleculeGraph (Fin atomCount)
  externalParent : Fin atomCount
  ligand : Fin atomCount
  graph : P92FiniteRootedDigraph (Fin atomCount)

def P92ExactDigraphAuthorityObservation.Represents
    (source : AuthoritativeChemicalInput)
    (observation : P92ExactDigraphAuthorityObservation) : Prop :=
  P92CanonicalConstitutionRepresents source observation.externalParent observation.ligand
    observation.molecule

def P92ExactDigraphAuthorityObservation.Faithful
    (observation : P92ExactDigraphAuthorityObservation) : Prop :=
  RootedDigraph.FaithfulExactExpansion observation.molecule observation.externalParent
    observation.ligand observation.graph.toRootedDigraph

def P92ExactDigraphAuthorityObservation.HasMultipleBondDuplicate
    (observation : P92ExactDigraphAuthorityObservation) : Prop :=
  ∃ node distance,
    (observation.graph.label node).provenance =
      NodeProvenance.multipleBondDuplicate distance

def P92ExactDigraphAuthorityObservation.HasRingDuplicate
    (observation : P92ExactDigraphAuthorityObservation) : Prop :=
  ∃ node distance,
    (observation.graph.label node).provenance = NodeProvenance.ringDuplicate distance

def P92ExactDigraphAuthorityObservation.HasNoRingDuplicate
    (observation : P92ExactDigraphAuthorityObservation) : Prop :=
  ∀ node distance,
    (observation.graph.label node).provenance ≠ NodeProvenance.ringDuplicate distance

def p92AcyclicDigraphReference : ProvisionReference where
  Observation := P92ExactDigraphAuthorityObservation
  Applicable := fun input => ∃ observation : P92ExactDigraphAuthorityObservation,
    observation.Represents input ∧ observation.Faithful ∧ observation.HasNoRingDuplicate
  Judges := fun input observation =>
    observation.Represents input ∧
      observation.Faithful ∧ observation.HasNoRingDuplicate

def p92MultipleBondDigraphReference : ProvisionReference where
  Observation := P92ExactDigraphAuthorityObservation
  Applicable := fun input => ∃ observation : P92ExactDigraphAuthorityObservation,
    observation.Represents input ∧ observation.Faithful ∧ observation.HasMultipleBondDuplicate
  Judges := fun input observation =>
    observation.Represents input ∧
      observation.Faithful ∧ observation.HasMultipleBondDuplicate

def p92CyclicDigraphReference : ProvisionReference where
  Observation := P92ExactDigraphAuthorityObservation
  Applicable := fun input => ∃ observation : P92ExactDigraphAuthorityObservation,
    observation.Represents input ∧ observation.Faithful ∧ observation.HasRingDuplicate
  Judges := fun input observation =>
    observation.Represents input ∧
      observation.Faithful ∧ observation.HasRingDuplicate

/-! ## Mancude and sphere references -/

structure P92MancudeDigraphAuthorityObservation where
  atomCount : Nat
  molecule : MoleculeGraph (Fin atomCount)
  attached : Fin atomCount
  representedAtomicNumber : ExactAtomicNumber

def P92MancudeDigraphAuthorityObservation.Represents
    (source : AuthoritativeChemicalInput)
    (observation : P92MancudeDigraphAuthorityObservation) : Prop :=
  P92ClassicalConstitutionRepresents source observation.molecule

/-- The selected attachment occurs in a nontrivial localized mancude component and is saturated
in at least one maximum matching.  This excludes the total-function value at arbitrary atoms from
serving as a mancude observation. -/
def P92MancudeAttachmentRepresented {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (attached : Atom) : Prop :=
  ∃ partner matching,
    partner ≠ attached ∧
      molecule.InMancudeComponent attached partner ∧
      matching ∈ molecule.maximumMancudeMatchings attached ∧
      matching attached = some partner

/-- Mancude atomic numbers are rational values.  `ExactAtomicNumber` intentionally retains an
unreduced numerator/denominator representation, so record equality would incorrectly distinguish
chemically identical values such as `1/2` and `2/4`. -/
def p92MancudeDigraphReference : ProvisionReference where
  Observation := P92MancudeDigraphAuthorityObservation
  Applicable := fun input => ∃ observation : P92MancudeDigraphAuthorityObservation,
    observation.Represents input ∧
      P92MancudeAttachmentRepresented observation.molecule observation.attached
  Judges := fun input observation =>
    observation.Represents input ∧
      P92MancudeAttachmentRepresented observation.molecule observation.attached ∧
      observation.representedAtomicNumber.value =
        (observation.molecule.exactMancudeAverage observation.attached).value

/-- Independent source-backed context for comparing two distinct ligands of one center.  The
shared molecular constitution is represented exactly, both ligand bonds exist, and both rooted
digraphs are faithful exact expansions.  This is the structural domain on which sphere traversal
and exhaustive sequence-rule comparison have chemical meaning. -/
structure P92LigandComparisonAuthorityContext where
  left : P92ExactDigraphAuthorityObservation
  right : P92ExactDigraphAuthorityObservation

def P92LigandComparisonAuthorityContext.Represents
    (context : P92LigandComparisonAuthorityContext)
    (source : AuthoritativeChemicalInput) : Prop :=
  context.left.Represents source ∧ context.right.Represents source

def P92LigandComparisonAuthorityContext.Ready
    (context : P92LigandComparisonAuthorityContext)
    (source : AuthoritativeChemicalInput) : Prop :=
  context.Represents source ∧
    context.left.externalParent.val = context.right.externalParent.val ∧
    context.left.ligand.val ≠ context.right.ligand.val ∧
    context.left.Faithful ∧ context.right.Faithful

/-- A source-level comparison schedule.  Addresses are ordered by sphere and then by their
within-sphere semantic address; omitted addresses must tie. -/
structure P92SphereExplorationAuthorityObservation where
  comparison : P92LigandComparisonAuthorityContext
  positions : List (List Nat)
  comparisonAt : List Nat → Ordering
  outcome : Ordering

def P92SphereExplorationJudged
    (observation : P92SphereExplorationAuthorityObservation) : Prop :=
  observation.positions.Pairwise HierarchyAddressBefore ∧
    (∀ position, position ∉ observation.positions →
      observation.comparisonAt position = Ordering.eq) ∧
    FirstDifferenceOutcome
      (fun position result => observation.comparisonAt position = result)
      observation.outcome

def p92SphereExplorationReference : ProvisionReference where
  Observation := P92SphereExplorationAuthorityObservation
  Applicable := fun input => ∃ observation : P92SphereExplorationAuthorityObservation,
    observation.comparison.Ready input ∧
      observation.positions.Pairwise HierarchyAddressBefore
  Judges := fun input observation =>
    observation.comparison.Ready input ∧ P92SphereExplorationJudged observation

/-! ## Exhaustive rule-order reference -/

def P92OrderingStrict : Ordering → Prop
  | .lt | .gt => True
  | .eq => False

structure P92RuleExhaustivityAuthorityObservation where
  comparison : P92LigandComparisonAuthorityContext
  outcomeAt : SequenceRule → Ordering
  firstDecisive? : Option SequenceRule
  outcome : Ordering

def P92RuleExhaustivityJudged
    (observation : P92RuleExhaustivityAuthorityObservation) : Prop :=
  match observation.firstDecisive? with
  | none =>
      observation.outcome = Ordering.eq ∧
        ∀ rule, observation.outcomeAt rule = Ordering.eq
  | some rule =>
      P92OrderingStrict observation.outcome ∧
        observation.outcomeAt rule = observation.outcome ∧
        ∀ earlier, earlier.Before rule →
          observation.outcomeAt earlier = Ordering.eq

def p92RuleExhaustivityReference : ProvisionReference where
  Observation := P92RuleExhaustivityAuthorityObservation
  Applicable := fun input => ∃ observation : P92RuleExhaustivityAuthorityObservation,
    observation.comparison.Ready input
  Judges := fun input observation =>
    observation.comparison.Ready input ∧ P92RuleExhaustivityJudged observation

/-! ## Rule-1a references -/

/-- Concrete multiple-bond duplicate children at one real parent of a faithful independent
expansion.  The list must enumerate exactly the duplicate children representing `duplicatedAtom`;
it is not a caller-supplied list of detached labels. -/
structure P92Rule1aMultipleBondDuplicatesAuthorityObservation where
  expansion : P92ExactDigraphAuthorityObservation
  parentNode : expansion.graph.Node
  parentAtom : Fin expansion.atomCount
  duplicatedAtom : Fin expansion.atomCount
  duplicateNodes : List expansion.graph.Node

def P92MultipleBondDuplicateChild
    (expansion : P92ExactDigraphAuthorityObservation)
    (parentNode : expansion.graph.Node)
    (duplicatedAtom : Fin expansion.atomCount)
    (node : expansion.graph.Node) : Prop :=
  expansion.graph.child parentNode node ∧
    ∃ distance,
      expansion.graph.label node =
        ⟨some duplicatedAtom, NodeProvenance.multipleBondDuplicate distance⟩ ∧
      distance = expansion.graph.depth parentNode + 1

def P92MultipleBondDuplicateChildrenExact
    (expansion : P92ExactDigraphAuthorityObservation)
    (parentNode : expansion.graph.Node)
    (parentAtom duplicatedAtom : Fin expansion.atomCount)
    (duplicateNodes : List expansion.graph.Node) : Prop :=
  expansion.graph.label parentNode = ⟨some parentAtom, NodeProvenance.realAtom⟩ ∧
    1 < expansion.molecule.bond parentAtom duplicatedAtom ∧
    duplicateNodes.Nodup ∧
    duplicateNodes.length = expansion.molecule.bond parentAtom duplicatedAtom - 1 ∧
    ∀ node, node ∈ duplicateNodes ↔
      P92MultipleBondDuplicateChild expansion parentNode duplicatedAtom node

def P92Rule1aMultipleBondDuplicatesJudged
    (observation : P92Rule1aMultipleBondDuplicatesAuthorityObservation) : Prop :=
  observation.expansion.Faithful ∧
    P92MultipleBondDuplicateChildrenExact observation.expansion observation.parentNode
      observation.parentAtom observation.duplicatedAtom observation.duplicateNodes

def p92Rule1aMultipleBondDuplicatesReference : ProvisionReference where
  Observation := P92Rule1aMultipleBondDuplicatesAuthorityObservation
  Applicable := fun input => ∃ observation : P92Rule1aMultipleBondDuplicatesAuthorityObservation,
    observation.expansion.Represents input ∧ observation.expansion.Faithful ∧
      observation.expansion.graph.label observation.parentNode =
        ⟨some observation.parentAtom, NodeProvenance.realAtom⟩ ∧
      1 < observation.expansion.molecule.bond observation.parentAtom observation.duplicatedAtom
  Judges := fun input observation =>
    observation.expansion.Represents input ∧
      P92Rule1aMultipleBondDuplicatesJudged observation

structure P92Rule1aMancudeAuthorityObservation where
  atomCount : Nat
  molecule : MoleculeGraph (Fin atomCount)
  leftAttached : Fin atomCount
  rightAttached : Fin atomCount
  outcome : Ordering

def P92Rule1aMancudeAuthorityObservation.Represents
    (source : AuthoritativeChemicalInput)
    (observation : P92Rule1aMancudeAuthorityObservation) : Prop :=
  P92ClassicalConstitutionRepresents source observation.molecule

def p92Rule1aMancudeReference : ProvisionReference where
  Observation := P92Rule1aMancudeAuthorityObservation
  Applicable := fun input => ∃ observation : P92Rule1aMancudeAuthorityObservation,
    observation.Represents input ∧
      P92MancudeAttachmentRepresented observation.molecule observation.leftAttached ∧
      P92MancudeAttachmentRepresented observation.molecule observation.rightAttached
  Judges := fun input observation =>
    observation.Represents input ∧
      P92MancudeAttachmentRepresented observation.molecule observation.leftAttached ∧
      P92MancudeAttachmentRepresented observation.molecule observation.rightAttached ∧
      ExactAtomicNumber.Outcome
        (observation.molecule.exactMancudeAverage observation.leftAttached)
        (observation.molecule.exactMancudeAverage observation.rightAttached)
        observation.outcome

def P92AtomSaturated {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (atom : Atom) : Prop :=
  ∀ other, molecule.bond atom other ≤ 1

structure P92Rule1aSaturatedCompoundsAuthorityObservation where
  atomCount : Nat
  molecule : MoleculeGraph (Fin atomCount)
  left : Fin atomCount
  right : Fin atomCount
  outcome : Ordering

def P92Rule1aSaturatedCompoundsAuthorityObservation.Represents
    (source : AuthoritativeChemicalInput)
    (observation : P92Rule1aSaturatedCompoundsAuthorityObservation) : Prop :=
  P92ClassicalConstitutionRepresents source observation.molecule

def P92Rule1aSaturatedCompoundsJudged
    (observation : P92Rule1aSaturatedCompoundsAuthorityObservation) : Prop :=
  P92AtomSaturated observation.molecule observation.left ∧
    P92AtomSaturated observation.molecule observation.right ∧
    ExactAtomicNumber.Outcome
      (ExactAtomicNumber.ofNat (observation.molecule.atomZ observation.left))
      (ExactAtomicNumber.ofNat (observation.molecule.atomZ observation.right))
      observation.outcome

def p92Rule1aSaturatedCompoundsReference : ProvisionReference where
  Observation := P92Rule1aSaturatedCompoundsAuthorityObservation
  Applicable := fun input => ∃ observation : P92Rule1aSaturatedCompoundsAuthorityObservation,
    observation.Represents input ∧ P92AtomSaturated observation.molecule observation.left ∧
      P92AtomSaturated observation.molecule observation.right
  Judges := fun input observation =>
    observation.Represents input ∧
      P92Rule1aSaturatedCompoundsJudged observation

/-- The replacement convention at both ends of a double or triple bond.  Each endpoint receives
`bondOrder - 1` duplicate labels carrying the atomic number of the opposite endpoint. -/
structure P92Rule1aDoubleTripleBondsAuthorityObservation where
  expansion : P92ExactDigraphAuthorityObservation
  leftNode : expansion.graph.Node
  rightNode : expansion.graph.Node
  leftAtom : Fin expansion.atomCount
  rightAtom : Fin expansion.atomCount
  duplicatesAtLeft : List expansion.graph.Node
  duplicatesAtRight : List expansion.graph.Node

def P92Rule1aDoubleTripleBondsJudged
    (observation : P92Rule1aDoubleTripleBondsAuthorityObservation) : Prop :=
  observation.expansion.Faithful ∧
    (observation.expansion.molecule.bond observation.leftAtom observation.rightAtom = 2 ∨
      observation.expansion.molecule.bond observation.leftAtom observation.rightAtom = 3) ∧
    P92MultipleBondDuplicateChildrenExact observation.expansion observation.leftNode
      observation.leftAtom observation.rightAtom observation.duplicatesAtLeft ∧
    P92MultipleBondDuplicateChildrenExact observation.expansion observation.rightNode
      observation.rightAtom observation.leftAtom observation.duplicatesAtRight

def p92Rule1aDoubleTripleBondsReference : ProvisionReference where
  Observation := P92Rule1aDoubleTripleBondsAuthorityObservation
  Applicable := fun input => ∃ observation : P92Rule1aDoubleTripleBondsAuthorityObservation,
    observation.expansion.Represents input ∧ observation.expansion.Faithful ∧
      (observation.expansion.molecule.bond observation.leftAtom observation.rightAtom = 2 ∨
        observation.expansion.molecule.bond observation.leftAtom observation.rightAtom = 3)
  Judges := fun input observation =>
    observation.expansion.Represents input ∧
      P92Rule1aDoubleTripleBondsJudged observation

def P92ConsecutiveInCycle {Atom : Type} [DecidableEq Atom]
    (ringAtoms : List Atom) (left right : Atom) : Prop :=
  (∃ before after, ringAtoms = before ++ left :: right :: after) ∨
    (ringAtoms.getLast? = some left ∧ ringAtoms.head? = some right)

/-- A concrete saturated ring: at least three distinct atoms, with every consecutive edge and the
closing edge explicitly single.  Bonds outside this ring are deliberately unconstrained. -/
def P92IsSaturatedRing {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (ringAtoms : List Atom) : Prop :=
  3 ≤ ringAtoms.length ∧
    ringAtoms.Nodup ∧
    ∀ left right, P92ConsecutiveInCycle ringAtoms left right →
      molecule.bond left right = 1

structure P92Rule1aSaturatedRingsAuthorityObservation where
  expansion : P92ExactDigraphAuthorityObservation
  ringAtoms : List (Fin expansion.atomCount)
  ringNodes : List expansion.graph.Node
  closingDuplicate : expansion.graph.Node

/-- The selected real nodes form one directed ancestry path in the independent expansion. -/
def P92DigraphNodePath {Atom : Type} (graph : RootedDigraph Atom) :
    List graph.Node → Prop
  | [] | [_] => True
  | first :: second :: rest =>
      graph.child first second ∧ P92DigraphNodePath graph (second :: rest)

/-- The real-node path represents the selected ordered ring atom-for-atom. -/
def P92RealNodesRepresentAtoms
    (expansion : P92ExactDigraphAuthorityObservation)
    (atoms : List (Fin expansion.atomCount))
    (nodes : List expansion.graph.Node) : Prop :=
  List.Forall₂
    (fun atom node =>
      expansion.graph.label node = ⟨some atom, NodeProvenance.realAtom⟩)
    atoms nodes

/-- The final real node closes the exact selected ancestry path by a ring-duplicate child of the
path's first atom.  Its distance points back to that concrete first real node, so a duplicate from
another fused cycle cannot witness this relation merely by sharing an atom label. -/
def P92SelectedRingClosureWitness
    (observation : P92Rule1aSaturatedRingsAuthorityObservation) : Prop :=
  ∃ firstAtom firstNode lastNode distance,
    observation.ringAtoms.head? = some firstAtom ∧
      observation.ringNodes.head? = some firstNode ∧
      observation.ringNodes.getLast? = some lastNode ∧
      observation.expansion.graph.child lastNode observation.closingDuplicate ∧
      observation.expansion.graph.label observation.closingDuplicate =
        ⟨some firstAtom, NodeProvenance.ringDuplicate distance⟩ ∧
      distance = observation.expansion.graph.depth firstNode + 1

def p92Rule1aSaturatedRingsReference : ProvisionReference where
  Observation := P92Rule1aSaturatedRingsAuthorityObservation
  Applicable := fun input => ∃ observation : P92Rule1aSaturatedRingsAuthorityObservation,
    observation.expansion.Represents input ∧ observation.expansion.Faithful ∧
      P92IsSaturatedRing observation.expansion.molecule observation.ringAtoms
  Judges := fun input observation =>
    observation.expansion.Represents input ∧
      observation.expansion.Faithful ∧
      P92IsSaturatedRing observation.expansion.molecule observation.ringAtoms ∧
      P92RealNodesRepresentAtoms observation.expansion observation.ringAtoms
        observation.ringNodes ∧
      P92DigraphNodePath observation.expansion.graph.toRootedDigraph observation.ringNodes ∧
      P92SelectedRingClosureWitness observation

/-! ## Exact 11-row compiler table -/

def next54P92DigraphRule1aProvisions : List IUPACNormativeProvision :=
  p92DigraphAndRule1aSemanticsSlice

inductive Next54P92DigraphRule1aAuthorityRow where
  | acyclicDigraph
  | multipleBondDigraph
  | cyclicDigraph
  | mancudeDigraph
  | sphereExploration
  | ruleExhaustivity
  | rule1aMultipleBondDuplicates
  | rule1aMancude
  | rule1aSaturatedCompounds
  | rule1aDoubleTripleBonds
  | rule1aSaturatedRings
  deriving DecidableEq, Repr

namespace Next54P92DigraphRule1aAuthorityRow

def all : List Next54P92DigraphRule1aAuthorityRow :=
  [ .acyclicDigraph
  , .multipleBondDigraph
  , .cyclicDigraph
  , .mancudeDigraph
  , .sphereExploration
  , .ruleExhaustivity
  , .rule1aMultipleBondDuplicates
  , .rule1aMancude
  , .rule1aSaturatedCompounds
  , .rule1aDoubleTripleBonds
  , .rule1aSaturatedRings
  ]

def provision : Next54P92DigraphRule1aAuthorityRow → IUPACNormativeProvision
  | .acyclicDigraph => .p92AcyclicDigraph
  | .multipleBondDigraph => .p92MultipleBondDigraph
  | .cyclicDigraph => .p92CyclicDigraph
  | .mancudeDigraph => .p92MancudeDigraph
  | .sphereExploration => .p92SphereExploration
  | .ruleExhaustivity => .p92RuleExhaustivity
  | .rule1aMultipleBondDuplicates => .p92Rule1aMultipleBondDuplicates
  | .rule1aMancude => .p92Rule1aMancude
  | .rule1aSaturatedCompounds => .p92Rule1aSaturatedCompounds
  | .rule1aDoubleTripleBonds => .p92Rule1aDoubleTripleBonds
  | .rule1aSaturatedRings => .p92Rule1aSaturatedRings

def kind : Next54P92DigraphRule1aAuthorityRow → ProvisionKind
  | .acyclicDigraph | .multipleBondDigraph | .cyclicDigraph | .mancudeDigraph |
      .sphereExploration => .perception
  | _ => .sequenceRule

def reference : Next54P92DigraphRule1aAuthorityRow → ProvisionReference
  | .acyclicDigraph => p92AcyclicDigraphReference
  | .multipleBondDigraph => p92MultipleBondDigraphReference
  | .cyclicDigraph => p92CyclicDigraphReference
  | .mancudeDigraph => p92MancudeDigraphReference
  | .sphereExploration => p92SphereExplorationReference
  | .ruleExhaustivity => p92RuleExhaustivityReference
  | .rule1aMultipleBondDuplicates => p92Rule1aMultipleBondDuplicatesReference
  | .rule1aMancude => p92Rule1aMancudeReference
  | .rule1aSaturatedCompounds => p92Rule1aSaturatedCompoundsReference
  | .rule1aDoubleTripleBonds => p92Rule1aDoubleTripleBondsReference
  | .rule1aSaturatedRings => p92Rule1aSaturatedRingsReference

/-- The exact observation/input identity condition for every row in this 11-provision family.
This is intentionally weaker than the complete authority judgment: it retains only the
constitutional/source anchoring needed to rule out cross-input observations. -/
def observationAdmitted :
    (row : Next54P92DigraphRule1aAuthorityRow) →
      (input : AuthoritativeChemicalInput) → row.reference.Observation → Prop
  | .acyclicDigraph, input, observation => observation.Represents input
  | .multipleBondDigraph, input, observation => observation.Represents input
  | .cyclicDigraph, input, observation => observation.Represents input
  | .mancudeDigraph, input, observation => observation.Represents input
  | .sphereExploration, input, observation => observation.comparison.Represents input
  | .ruleExhaustivity, input, observation => observation.comparison.Represents input
  | .rule1aMultipleBondDuplicates, input, observation =>
      observation.expansion.Represents input
  | .rule1aMancude, input, observation => observation.Represents input
  | .rule1aSaturatedCompounds, input, observation => observation.Represents input
  | .rule1aDoubleTripleBonds, input, observation => observation.expansion.Represents input
  | .rule1aSaturatedRings, input, observation => observation.expansion.Represents input

/-- Row-specific source applicability with computed outcomes removed.  Each branch retains the
exact authority-input anchor and the chemical or structural premise which makes that P-92 clause
relevant.  Comparison outcomes, exact duplicate lists, and ring-closure emissions remain in
`Judges`. -/
def applicabilityWitness :
    (row : Next54P92DigraphRule1aAuthorityRow) →
      (input : AuthoritativeChemicalInput) → row.reference.Observation → Prop
  | .acyclicDigraph, input, observation =>
      observation.Represents input ∧ observation.Faithful ∧ observation.HasNoRingDuplicate
  | .multipleBondDigraph, input, observation =>
      observation.Represents input ∧ observation.Faithful ∧
        observation.HasMultipleBondDuplicate
  | .cyclicDigraph, input, observation =>
      observation.Represents input ∧ observation.Faithful ∧ observation.HasRingDuplicate
  | .mancudeDigraph, input, observation =>
      observation.Represents input ∧
        P92MancudeAttachmentRepresented observation.molecule observation.attached
  | .sphereExploration, input, observation =>
      observation.comparison.Ready input ∧
        observation.positions.Pairwise HierarchyAddressBefore
  | .ruleExhaustivity, input, observation => observation.comparison.Ready input
  | .rule1aMultipleBondDuplicates, input, observation =>
      observation.expansion.Represents input ∧ observation.expansion.Faithful ∧
        observation.expansion.graph.label observation.parentNode =
          ⟨some observation.parentAtom, NodeProvenance.realAtom⟩ ∧
        1 < observation.expansion.molecule.bond observation.parentAtom
          observation.duplicatedAtom
  | .rule1aMancude, input, observation =>
      observation.Represents input ∧
        P92MancudeAttachmentRepresented observation.molecule observation.leftAttached ∧
        P92MancudeAttachmentRepresented observation.molecule observation.rightAttached
  | .rule1aSaturatedCompounds, input, observation =>
      observation.Represents input ∧ P92AtomSaturated observation.molecule observation.left ∧
        P92AtomSaturated observation.molecule observation.right
  | .rule1aDoubleTripleBonds, input, observation =>
      observation.expansion.Represents input ∧ observation.expansion.Faithful ∧
        (observation.expansion.molecule.bond observation.leftAtom observation.rightAtom = 2 ∨
          observation.expansion.molecule.bond observation.leftAtom observation.rightAtom = 3)
  | .rule1aSaturatedRings, input, observation =>
      observation.expansion.Represents input ∧ observation.expansion.Faithful ∧
        P92IsSaturatedRing observation.expansion.molecule observation.ringAtoms

/-- All 11 independent references are closed over the exact observation domain by construction. -/
theorem observationAdmitted_of_judged
    (row : Next54P92DigraphRule1aAuthorityRow)
    (input : AuthoritativeChemicalInput)
    (observation : row.reference.Observation)
    (judged : row.reference.Judges input observation) :
    row.observationAdmitted input observation := by
  cases row with
  | sphereExploration | ruleExhaustivity => exact judged.1.1
  | _ => exact judged.1

/-- Applicability is exactly existence of a source-anchored observation satisfying the row's
feature premises. -/
theorem applicable_iff_exists_applicabilityWitness
    (row : Next54P92DigraphRule1aAuthorityRow)
    (input : AuthoritativeChemicalInput) :
    row.reference.Applicable input ↔
      ∃ observation : row.reference.Observation,
        row.applicabilityWitness input observation := by
  cases row <;> rfl

/-- Feature applicability always retains exact input/observation anchoring. -/
theorem applicabilityWitness_observationAdmitted
    (row : Next54P92DigraphRule1aAuthorityRow)
    (input : AuthoritativeChemicalInput)
    (observation : row.reference.Observation)
    (applicable : row.applicabilityWitness input observation) :
    row.observationAdmitted input observation := by
  cases row with
  | sphereExploration => exact applicable.1.1
  | ruleExhaustivity => exact applicable.1
  | _ => first | exact applicable | exact applicable.1

/-- Every independent judgment contains the feature premises, while its computed conclusion may
carry strictly more information. -/
theorem applicabilityWitness_of_judged
    (row : Next54P92DigraphRule1aAuthorityRow)
    (input : AuthoritativeChemicalInput)
    (observation : row.reference.Observation)
    (judged : row.reference.Judges input observation) :
    row.applicabilityWitness input observation := by
  cases row with
  | acyclicDigraph | multipleBondDigraph | cyclicDigraph => exact judged
  | mancudeDigraph => exact ⟨judged.1, judged.2.1⟩
  | sphereExploration => exact ⟨judged.1, judged.2.1⟩
  | ruleExhaustivity => exact judged.1
  | rule1aMultipleBondDuplicates =>
      exact ⟨judged.1, judged.2.1, judged.2.2.1, judged.2.2.2.1⟩
  | rule1aMancude => exact ⟨judged.1, judged.2.1, judged.2.2.1⟩
  | rule1aSaturatedCompounds => exact ⟨judged.1, judged.2.1, judged.2.2.1⟩
  | rule1aDoubleTripleBonds => exact ⟨judged.1, judged.2.1, judged.2.2.1⟩
  | rule1aSaturatedRings => exact ⟨judged.1, judged.2.1, judged.2.2.1⟩

/-- A positive provision decision therefore also has a weaker exact source anchor. -/
theorem applicable_implies_exists_observationAdmitted
    (row : Next54P92DigraphRule1aAuthorityRow)
    (input : AuthoritativeChemicalInput)
    (applicable : row.reference.Applicable input) :
    ∃ observation : row.reference.Observation,
      row.observationAdmitted input observation := by
  rw [row.applicable_iff_exists_applicabilityWitness input] at applicable
  obtain ⟨observation, witness⟩ := applicable
  exact ⟨observation, row.applicabilityWitness_observationAdmitted input observation witness⟩

/-- Every successful independent P-92 judgment supplies its own exact applicability witness. -/
theorem applicable_of_judged
    (row : Next54P92DigraphRule1aAuthorityRow)
    (input : AuthoritativeChemicalInput)
    (observation : row.reference.Observation)
    (judged : row.reference.Judges input observation) :
    row.reference.Applicable input := by
  rw [row.applicable_iff_exists_applicabilityWitness input]
  exact ⟨observation, row.applicabilityWitness_of_judged input observation judged⟩

def semantics (row : Next54P92DigraphRule1aAuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference

@[simp] theorem all_length : all.length = 11 := by rfl

theorem all_nodup : all.Nodup := by decide

@[simp] theorem all_provisions_exact :
    all.map provision = next54P92DigraphRule1aProvisions := by
  rfl

@[simp] theorem classifier_exact (row : Next54P92DigraphRule1aAuthorityRow) :
    next54Kind? row.provision = some row.kind := by
  cases row <;>
    simp [next54Kind?, next54SequenceRuleProvisions, next54PerceptionProvisions,
      provision, kind]

end Next54P92DigraphRule1aAuthorityRow

theorem next54P92DigraphRule1a_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P92DigraphRule1aProvisions) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : next54P92DigraphRule1aProvisions.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem next54P92DigraphRule1a_mem_next54
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P92DigraphRule1aProvisions) :
    provision ∈ next54Provisions := by
  have p92Member : provision ∈ next54P92ResidualProvisions := by
    exact List.mem_append_right p92FoundationalSemanticsSlice member
  have blueBookMember : provision ∈ next54BlueBookProvisions := by
    apply List.mem_append_right next54P91Provisions
    exact List.mem_append_left next54P93PolyhedralResidualProvisions p92Member
  exact List.mem_append_left next54IR9ResidualProvisions blueBookMember

theorem exists_next54P92DigraphRule1aAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P92DigraphRule1aProvisions) :
    ∃ row, row ∈ Next54P92DigraphRule1aAuthorityRow.all ∧
      row.provision = provision := by
  rw [← Next54P92DigraphRule1aAuthorityRow.all_provisions_exact] at member
  simpa only [List.mem_map] using member

noncomputable def next54P92DigraphRule1aAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54P92DigraphRule1aProvisions) :
    Next54P92DigraphRule1aAuthorityRow :=
  Classical.choose (exists_next54P92DigraphRule1aAuthorityRow member)

theorem next54P92DigraphRule1aAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54P92DigraphRule1aProvisions) :
    (next54P92DigraphRule1aAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_next54P92DigraphRule1aAuthorityRow member)).2

structure Next54P92DigraphRule1aReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch next54P92DigraphRule1aProvisions.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P92DigraphRule1aProvisions.toFinset),
      (reviewed.row provision member).kind =
        next54Kind provision (next54P92DigraphRule1a_mem_next54 (by simpa using member))

noncomputable def next54P92DigraphRule1aReviewedSemantics :
    Next54P92DigraphRule1aReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        (next54P92DigraphRule1aAuthorityRowOf provision (by simpa using member)).semantics
      sourceAudited := by
        intro provision member
        exact next54P92DigraphRule1a_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := next54P92DigraphRule1aAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      next54P92DigraphRule1aAuthorityRowOf_provision provision (by simpa using member)
    have rowClassifier := Next54P92DigraphRule1aAuthorityRow.classifier_exact row
    have totalClassifier := next54Kind?_eq_some provision
      (next54P92DigraphRule1a_mem_next54 (by simpa using member))
    rw [rowProvision] at rowClassifier
    change row.kind = next54Kind provision _
    exact Option.some.inj (rowClassifier.symm.trans totalClassifier)

end

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92DigraphRule1aAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92DigraphRule1aAuthorityRow.classifier_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92DigraphRule1aAuthorityRow.observationAdmitted_of_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92DigraphRule1aAuthorityRow.applicable_iff_exists_applicabilityWitness
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92DigraphRule1aAuthorityRow.applicabilityWitness_observationAdmitted
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92DigraphRule1aAuthorityRow.applicabilityWitness_of_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92DigraphRule1aAuthorityRow.applicable_implies_exists_observationAdmitted
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92DigraphRule1aAuthorityRow.applicable_of_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P92DigraphRule1a_sourceAuditComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P92DigraphRule1a_mem_next54
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P92DigraphRule1aAuthorityRowOf_provision
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P92DigraphRule1aReviewedSemantics
