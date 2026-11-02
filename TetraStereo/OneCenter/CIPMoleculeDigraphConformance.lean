import TetraStereo.OneCenter.CIPBlueBookConformance
import TetraStereo.OneCenter.ProductionCIPOccurrenceDiscovery
import TetraStereo.OneCenter.ProductionCIPRule1aSoundness

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open DeclarativeCIP
open ProductionCIPOccurrenceDiscovery

/-!
# Molecule-to-CIP-digraph conformance

`DeclarativeCIP.RootedDigraph.FaithfulExactExpansion` is the independent constitutional
specification.  It does not execute the production branch compiler: it requires a root bond,
the correct ligand root, terminal duplicate nodes, exact real/multiple-bond/ring child
multiplicities, atom-bearing children, and correct Rule-1b duplicate distances under every
parent-preserving addressing.

This file lifts the existing branch-local realization proof to every automatically discovered
tetrahedral center and every physical ligand slot.  A lone pair is not a molecular-graph atom, so
its phantom cursor has a separate exact observation theorem below.
-/

namespace BlueBookP92.Digraph

/-- Every entry in the stored/fallback written-neighbor order is a genuine molecular neighbor.
Parser-produced `neighborOrder` is intended to satisfy this property; unlike `Admissible`, the
property also constrains the per-atom order table. -/
def WrittenNeighborSound (mol : RawMolecule) : Prop :=
  ∀ center : Fin mol.atomCount, ∀ ligand,
    ligand ∈ mol.writtenNeighbors center.val → 0 < mol.bondOrder center.val ligand

/-- The exact executable stereochemical intake contract entails the local soundness premise used
by molecule-to-digraph conformance. -/
theorem writtenNeighborSound_of_exact
    (mol : RawMolecule) (exact : mol.WrittenNeighborExact) :
    WrittenNeighborSound mol := by
  intro center ligand member
  have ligand_lt : ligand < mol.atomCount :=
    (RawMolecule.WrittenNeighborExact.at mol exact center).2.1 ligand member
  exact ((RawMolecule.WrittenNeighborExact.at mol exact center).2.2
    ⟨ligand, ligand_lt⟩).mp member

/-- Input-integrity boundary missing from `RawMolecule.Admissible`: every in-range ligand listed
for an automatically discovered final unit is joined to that center in the proof-facing molecular
graph.  This is explicit because a hand-built `neighborOrder` is not currently validated by
`RawMolecule.WellFormed`. -/
def PhysicalLigandRootsBonded (mol : RawMolecule) : Prop :=
  ∀ (root : Root mol) (slot : Fin 4) (ligand : Fin mol.atomCount),
    ligand.val = ligandAtom root slot →
      (mol.canonicalHierarchyMoleculeGraph (centerAtom root) ligand).Adj
        (centerAtom root) ligand

/-- Exact production observations required of the atomless lone-pair cursor. -/
structure PhantomCursorConformance (mol : RawMolecule)
    (parent distance : Nat) (cursor : CanonicalRerootCursor) : Prop where
  node_eq : cursor.node = mol.canonicalPhantom parent distance
  previous_atom : cursor.previous?.map RawMolecule.CanonicalBranchNode.atom = some parent
  atom_sentinel : cursor.node.atom = mol.atomCount
  provenance : cursor.node.provenance = .phantom distance
  terminal : mol.canonicalTerminal cursor.node = true
  rule1a_zero : mol.canonicalRule1aLabel? cursor.node =
    some { numerator := 0, denominator := 1 }
  rule1b_distance : cursor.node.rule1bCode = distance
  rule2_mass_zero :
    mol.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule2 cursor.node cursor.node =
      Ordering.eq

/-- Molecule-wide certificate for the atom-bearing constitutional hierarchy layer. -/
structure MoleculeConformance (mol : RawMolecule) (discovery : Discovery mol) : Prop where
  rootCoverage : ∀ center : Fin mol.atomCount,
    FinalUnitEligible mol center → ∃! root : Root mol, centerAtom root = center
  centerHierarchies : ∀ root : Root mol, CompleteCenterHierarchy (discovery.center root)
  physicalBranches : ∀ (root : Root mol) (slot : Fin 4)
      (ligand : Fin mol.atomCount),
    ligand.val = ligandAtom root slot →
      RootedDigraph.FaithfulExactExpansion
        (mol.canonicalHierarchyMoleculeGraph (centerAtom root) ligand)
        (centerAtom root) ligand
        (((discovery.center root).branch slot).key.toDeclarativeDigraph mol)

end BlueBookP92.Digraph

/-- Inserting the atom-count lone-pair sentinel never creates a new physical written neighbor. -/
theorem mem_writtenNeighbors_of_mem_ligandsWithLonePair_of_ne
    (mol : RawMolecule) (center ligand : Nat)
    (member : ligand ∈ mol.ligandsWithLonePair center)
    (notPhantom : ligand ≠ mol.atomCount) :
    ligand ∈ mol.writtenNeighbors center := by
  unfold RawMolecule.ligandsWithLonePair at member
  cases atomEq : mol.atomAt? center with
  | none => simpa [atomEq] using member
  | some spec =>
      simp only [atomEq] at member
      split at member
      · rename_i usesLonePair
        split at member
        · rename_i hasPreceding
          cases writtenEq : mol.writtenNeighbors center with
          | nil => simp [writtenEq, notPhantom] at member
          | cons first rest =>
              simp [writtenEq, notPhantom] at member ⊢
              exact member
        · rename_i opensString
          simp [notPhantom] at member
          exact member
      · exact member

/-- Sound written-neighbor storage discharges the physical-root-bond premise used by the
molecule-wide digraph certificate. -/
theorem physicalLigandRootsBonded_of_writtenNeighborSound
    (mol : RawMolecule) (hsound : BlueBookP92.Digraph.WrittenNeighborSound mol) :
    BlueBookP92.Digraph.PhysicalLigandRootsBonded mol := by
  intro root slot ligand ligand_eq
  have ligand_mem : ligand.val ∈ mol.ligandsWithLonePair (centerAtom root).val := by
    rw [ligand_eq]
    exact ligandAtom_mem root slot
  have notPhantom : ligand.val ≠ mol.atomCount := Nat.ne_of_lt ligand.isLt
  have written_mem : ligand.val ∈ mol.writtenNeighbors (centerAtom root).val :=
    mem_writtenNeighbors_of_mem_ligandsWithLonePair_of_ne mol _ _ ligand_mem notPhantom
  have bondPositive : 0 < mol.bondOrder (centerAtom root).val ligand.val :=
    hsound (centerAtom root) _ written_mem
  have distinct : (centerAtom root).val ≠ ligand.val := by
    intro equal
    rw [equal, mol.bondOrder_self] at bondPositive
    simp at bondPositive
  by_cases oxido :
      mol.isTrigonalPyramidalOxidoRootEdge (centerAtom root).val ligand.val = true
  · simp [MoleculeGraph.Adj, RawMolecule.canonicalHierarchyMoleculeGraph,
      RawMolecule.canonicalHierarchyBond, distinct, RawMolecule.IsRootPair, oxido]
  · simp [MoleculeGraph.Adj, RawMolecule.canonicalHierarchyMoleculeGraph,
      RawMolecule.canonicalHierarchyBond, distinct, RawMolecule.IsRootPair, oxido,
      bondPositive]

namespace ProductionCIPOccurrenceDiscovery.CompleteBranchDiscovery

/-- Every complete automatically retained physical branch realizes the independent exact
constitutional digraph specification. -/
theorem faithfulExactExpansion
    {mol : RawMolecule} {center : Fin mol.atomCount} {ligandIndex : Nat}
    (branch : CompleteBranchDiscovery mol center ligandIndex)
    (ligand : Fin mol.atomCount) (ligand_eq : ligand.val = ligandIndex)
    (hadmissible : mol.Admissible)
    (hrootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand) :
    RootedDigraph.FaithfulExactExpansion
      (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
      (branch.key.toDeclarativeDigraph mol) := by
  have accepted : branchCanonicalKey? mol center.val ligand.val = some branch.key := by
    simpa [ligand_eq] using branch.accepted
  exact mol.branchCanonicalKey?_faithfulExactExpansion center ligand branch.key
    hadmissible.1 hadmissible.2 accepted branch.complete hrootBond

end ProductionCIPOccurrenceDiscovery.CompleteBranchDiscovery

namespace ProductionCIPOccurrenceDiscovery.Discovery

/-- Exhaustive automatic discovery lifts branch-local conformance to every physical ligand of
every molecule-derived tetrahedral final unit. -/
theorem moleculeConformance
    {mol : RawMolecule} (discovery : Discovery mol)
    (hadmissible : mol.Admissible)
    (hrootBonds : BlueBookP92.Digraph.PhysicalLigandRootsBonded mol) :
    BlueBookP92.Digraph.MoleculeConformance mol discovery where
  rootCoverage := fun center eligible => root_coverage_unique mol center eligible
  centerHierarchies := fun root => completeCenterHierarchy (discovery.center root)
  physicalBranches := by
    intro root slot ligand ligand_eq
    exact ((discovery.center root).branch slot).faithfulExactExpansion ligand ligand_eq
      hadmissible (hrootBonds root slot ligand ligand_eq)

/-- The molecule-wide certificate follows from admissibility plus sound written-neighbor
storage, without requiring callers to prove the derived root-bond condition separately. -/
theorem moleculeConformance_of_writtenNeighborSound
    {mol : RawMolecule} (discovery : Discovery mol)
    (hadmissible : mol.Admissible)
    (hsound : BlueBookP92.Digraph.WrittenNeighborSound mol) :
    BlueBookP92.Digraph.MoleculeConformance mol discovery :=
  discovery.moleculeConformance hadmissible
    (physicalLigandRootsBonded_of_writtenNeighborSound mol hsound)

/-- The complete checked stereochemical admission boundary automatically entails the full
molecule-to-CIP-digraph certificate; callers no longer supply a separate graph-soundness premise. -/
theorem moleculeConformance_of_stereochemicalAdmissible
    {mol : RawMolecule} (discovery : Discovery mol)
    (hadmissible : mol.StereochemicalAdmissible) :
    BlueBookP92.Digraph.MoleculeConformance mol discovery :=
  discovery.moleculeConformance_of_writtenNeighborSound hadmissible.1
    (BlueBookP92.Digraph.writtenNeighborSound_of_exact mol hadmissible.2)

end ProductionCIPOccurrenceDiscovery.Discovery

/-- When the occurrence frame takes its lone-pair branch, its returned list is exactly the three
physical cursors followed by the production phantom cursor. -/
theorem occurrenceLigandFrame?_eq_phantom_frame
    (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (four : (mol.ligandsWithLonePair node.atom).length = 4)
    (three : (occurrenceLigandCursors mol node).length = 3)
    (hasPhantom : (mol.ligandsWithLonePair node.atom).contains mol.atomCount = true) :
    occurrenceLigandFrame? mol node =
      some (occurrenceLigandCursors mol node ++
        [{ node := mol.canonicalPhantom node.atom (node.depth + 1), previous? := some node }]) := by
  have phantom_mem : mol.atomCount ∈ mol.ligandsWithLonePair node.atom := by
    simpa using hasPhantom
  simp [occurrenceLigandFrame?, four, three, phantom_mem]

/-- The appended lone-pair cursor has exactly the atomless, terminal, zero-priority observations
required by the independent phantom boundary. -/
theorem occurrence_phantom_cursor_conforms
    (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode) :
    BlueBookP92.Digraph.PhantomCursorConformance mol node.atom (node.depth + 1)
      { node := mol.canonicalPhantom node.atom (node.depth + 1), previous? := some node } := by
  constructor <;>
    simp [RawMolecule.canonicalPhantom, RawMolecule.CanonicalBranchNode.rule1bCode,
      RawMolecule.CanonicalBranchNode.rule1bRootDistance, RawMolecule.canonicalTerminal,
      RawMolecule.CanonicalBranchNode.forcedLeaf, RawMolecule.canonicalRule1aLabel?,
      RawMolecule.compareCanonicalNodeRule]

end

end TetraStereo.OneCenter
