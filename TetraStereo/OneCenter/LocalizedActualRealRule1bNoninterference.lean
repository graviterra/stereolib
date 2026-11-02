import TetraStereo.OneCenter.AuthoritativeLocalizedCIPAnalysis
import TetraStereo.OneCenter.LocalizedCyclicInputWitness
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEmbedding
import TetraStereo.OneCenter.LocalizedRetainedConstitutionalReaderIndependence
import TetraStereo.OneCenter.LocalizedRetainedDigraphSphereCorrespondence
import TetraStereo.OneCenter.LocalizedRerootContextRule1bWitness
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeBuilder
import TetraStereo.OneCenter.LocalizedSimpleBondFourLigandFrames
import TetraStereo.OneCenter.OfficialRuleMajorObservation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Retained Rule 1b comparison, and a separate auxiliary observer

The molecule is the admitted explicit-hydrogen chain
`C(F)(Cl)(H)–C(F)(H)–C(F)(Cl)(H)`.  Three readings stay separate.

* Expansion structure is the executable reroot cursor, including its incoming cut.
* Retained history is the original-root occurrence.  A fresh auxiliary `extend`
  back to the original root is a different history.
* Metric origin is the retained constitutional table and the outer-digraph sphere
  of that occurrence.  `originalRootDepth` is only an atom-index observer.

The fresh auxiliary fuel-2 trees are an observer experiment.  Both proximal nodes
have auxiliary `rule1bRootDistance` 1, so that observer and `fun _ => 0` tie after
Rule 1a.  `originalRootDepth` agrees with the two proximal occurrence depths and
makes the inward key senior.  It is not the retained bridge.

The retained bridge uses the original-root auxiliary occurrence, the real parent
cursor and the real outward cursor, and `buildRuleMajorCumulativeWithRead?`.
Reader independence transports the constitutional comparison.  The sphere theorem
identifies each arm root’s retained Rule 1b value with that occurrence depth.
No source profile is installed.

On the nine-atom cyclic fixture, atom 0’s neighbors are atoms 1, 2, 4, and 5.
Atom 3 is chlorine on atom 2, not a root ligand.
-/

namespace TetraStereo.OneCenter.ActualRealRule1bNoninterference

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.SemanticMolecule
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedCyclicInputWitness
open TetraStereo.OneCenter.LocalizedRerootContextRule1bWitness

/-- Bracket atom with charge zero and no inferred hydrogen. -/
def bare (element : Element) : AtomSpec where
  element := element
  charge := 0
  explicitHydrogens? := some 0

/-- Explicit-hydrogen 1,3-dichloro-1,2,3-trifluoropropane, written without implicit hydrogen. -/
def raw : RawMolecule where
  atoms :=
    [ bare .C, bare .F, bare .Cl, bare .H
    , bare .C, bare .F, bare .H
    , bare .C, bare .F, bare .Cl, bare .H ]
  bonds :=
    [ { source := 0, target := 1, kind := .single }
    , { source := 0, target := 2, kind := .single }
    , { source := 0, target := 3, kind := .single }
    , { source := 0, target := 4, kind := .single }
    , { source := 4, target := 5, kind := .single }
    , { source := 4, target := 6, kind := .single }
    , { source := 4, target := 7, kind := .single }
    , { source := 7, target := 8, kind := .single }
    , { source := 7, target := 9, kind := .single }
    , { source := 7, target := 10, kind := .single } ]

theorem raw_no_wildcard : ∀ spec ∈ raw.atoms, spec.element ≠ .wildcard := by
  decide

def source : AuthoritativeChemicalInput :=
  raw.toAuthoritativeChemicalInput?.getD
    { molecule := { atoms := [], interactions := [] } }

theorem source_conversion : raw.toAuthoritativeChemicalInput? = some source := by
  have present := (raw.toAuthoritativeChemicalInput?_isSome).mpr raw_no_wildcard
  cases converted : raw.toAuthoritativeChemicalInput? with
  | none => simp [converted] at present
  | some found => simp [source, converted]

theorem source_wellFormed : source.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp
    (by decide +kernel)

theorem source_graphReady : source.molecule.LocalizedCIPGraphReady :=
  (SemanticMolecule.localizedCIPGraphReady?_eq_true_iff source.molecule).mp
    (by decide +kernel)

def admitted : CertifiedLocalizedCIPInput where
  certified :=
    { input := source
      structurallyWellFormed := source_wellFormed }
  graphReady := source_graphReady

theorem atomCount_eq : admitted.certified.input.molecule.atomCount = 11 := by
  have converted := raw.toSemanticMolecule?_atomCount source.molecule
    (raw.toAuthoritativeChemicalInput?_molecule source source_conversion)
  simpa [admitted, source, RawMolecule.atomCount] using converted

def ix (index : Fin 11) : admitted.Atom :=
  ⟨index.val, atomCount_eq.symm ▸ index.isLt⟩

def rootA : admitted.Atom := ix 0
def auxA : admitted.Atom := ix 4
def outA : admitted.Atom := ix 7

theorem physical_domain :
    raw.ValenceOK ∧
      (∀ spec ∈ raw.atoms, spec.charge = 0) ∧
      (∀ index : Fin 11, raw.implicitHydrogensAt? index.val = some 0) ∧
      (∀ bond ∈ raw.bonds, bond.kind = ParsedBondKind.single) ∧
      (∀ atom : admitted.Atom, admitted.moleculeGraph.formalCharge atom = 0) ∧
      (∀ left right : admitted.Atom,
        admitted.moleculeGraph.bond left right = 0 ∨
          admitted.moleculeGraph.bond left right = 1) := by
  refine ⟨(raw.valenceOK?_eq_true_iff).mp (by decide +kernel), ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel +revert
  · intro index
    fin_cases index <;> decide +kernel
  · decide +kernel +revert
  · decide +kernel +revert
  · decide +kernel +revert

theorem four_ligand_centers :
    (admitted.moleculeGraph.neighborFinset rootA).card = 4 ∧
      (admitted.moleculeGraph.neighborFinset auxA).card = 4 ∧
      (admitted.moleculeGraph.neighborFinset outA).card = 4 := by
  decide +kernel

def auxRoot : OfficialCIPNode admitted.Atom :=
  OfficialCIPNode.root auxA

def inwardNode : OfficialCIPNode admitted.Atom :=
  auxRoot.extend rootA 0

def outwardNode : OfficialCIPNode admitted.Atom :=
  auxRoot.extend outA 0

def originalRoot : OfficialCIPNode admitted.Atom :=
  OfficialCIPNode.root rootA

def originalAux : OfficialCIPNode admitted.Atom :=
  originalRoot.extend auxA 0

def originalOut : OfficialCIPNode admitted.Atom :=
  originalAux.extend outA 0

private theorem bond_aux (atom : admitted.Atom) :
    admitted.moleculeGraph.bond auxA atom =
      if atom = rootA ∨ atom = ix 5 ∨ atom = ix 6 ∨ atom = outA then 1 else 0 := by
  decide +kernel +revert

private theorem bond_root (atom : admitted.Atom) :
    admitted.moleculeGraph.bond rootA atom =
      if atom = ix 1 ∨ atom = ix 2 ∨ atom = ix 3 ∨ atom = auxA then 1 else 0 := by
  decide +kernel +revert

private theorem bond_out (atom : admitted.Atom) :
    admitted.moleculeGraph.bond outA atom =
      if atom = auxA ∨ atom = ix 8 ∨ atom = ix 9 ∨ atom = ix 10 then 1 else 0 := by
  decide +kernel +revert

private theorem neighbor_iff_bond (center atom : admitted.Atom) :
    atom ∈ admitted.moleculeGraph.neighborFinset center ↔
      admitted.moleculeGraph.bond center atom = 1 := by
  rw [MoleculeGraph.mem_neighborFinset, MoleculeGraph.Adj]
  constructor
  · intro positive
    rcases physical_domain.2.2.2.2.2 center atom with zero | one
    · rw [zero] at positive
      exact absurd positive (Nat.not_lt_zero 0)
    · exact one
  · intro one
    rw [one]
    exact Nat.zero_lt_one

private theorem neighborFinset_of_bond (center a b c d : admitted.Atom)
    (equation : ∀ atom : admitted.Atom, admitted.moleculeGraph.bond center atom =
      if atom = a ∨ atom = b ∨ atom = c ∨ atom = d then 1 else 0) :
    admitted.moleculeGraph.neighborFinset center = {a, b, c, d} := by
  ext atom
  simp only [neighbor_iff_bond, equation, Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> simp [*]

private theorem neighborFinset_singleton (center ligand : admitted.Atom)
    (equation : ∀ atom : admitted.Atom, admitted.moleculeGraph.bond ligand atom =
      if atom = center then 1 else 0) :
    admitted.moleculeGraph.neighborFinset ligand = {center} := by
  ext atom
  simp only [neighbor_iff_bond, equation, Finset.mem_singleton]
  split_ifs <;> simp [*]

private theorem sort_four {a b c d : admitted.Atom}
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ({a, b, c, d} : Finset admitted.Atom).sort (· ≤ ·) = [a, b, c, d] := by
  rw [Finset.sort_insert]
  · rw [Finset.sort_insert]
    · rw [Finset.sort_insert]
      · simp [Finset.sort_singleton]
      · intro atom member
        simp only [Finset.mem_singleton] at member
        subst atom
        exact le_of_lt hcd
      · intro member
        simp only [Finset.mem_singleton] at member
        exact ne_of_lt hcd member
    · intro atom member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl
      · exact le_of_lt hbc
      · exact le_of_lt (hbc.trans hcd)
    · intro member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl
      · exact ne_of_lt hbc rfl
      · exact ne_of_lt (hbc.trans hcd) rfl
  · intro atom member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl
    · exact le_of_lt hab
    · exact le_of_lt (hab.trans hbc)
    · exact le_of_lt (hab.trans (hbc.trans hcd))
  · intro member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl
    · exact ne_of_lt hab rfl
    · exact ne_of_lt (hab.trans hbc) rfl
    · exact ne_of_lt (hab.trans (hbc.trans hcd)) rfl

theorem auxiliary_neighbor_frame :
    (admitted.moleculeGraph.neighborFinset auxA).sort (· ≤ ·) =
      [rootA, ix 5, ix 6, outA] := by
  rw [neighborFinset_of_bond auxA rootA (ix 5) (ix 6) outA bond_aux]
  exact sort_four (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem root_neighbor_frame :
    (admitted.moleculeGraph.neighborFinset rootA).sort (· ≤ ·) =
      [ix 1, ix 2, ix 3, auxA] := by
  rw [neighborFinset_of_bond rootA (ix 1) (ix 2) (ix 3) auxA bond_root]
  exact sort_four (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem outward_neighbor_frame :
    (admitted.moleculeGraph.neighborFinset outA).sort (· ≤ ·) =
      [auxA, ix 8, ix 9, ix 10] := by
  rw [neighborFinset_of_bond outA auxA (ix 8) (ix 9) (ix 10) bond_out]
  exact sort_four (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem bond_ix1 (atom : admitted.Atom) :
    admitted.moleculeGraph.bond (ix 1) atom = if atom = rootA then 1 else 0 := by
  decide +kernel +revert

private theorem bond_ix2 (atom : admitted.Atom) :
    admitted.moleculeGraph.bond (ix 2) atom = if atom = rootA then 1 else 0 := by
  decide +kernel +revert

private theorem bond_ix3 (atom : admitted.Atom) :
    admitted.moleculeGraph.bond (ix 3) atom = if atom = rootA then 1 else 0 := by
  decide +kernel +revert

private theorem bond_ix8 (atom : admitted.Atom) :
    admitted.moleculeGraph.bond (ix 8) atom = if atom = outA then 1 else 0 := by
  decide +kernel +revert

private theorem bond_ix9 (atom : admitted.Atom) :
    admitted.moleculeGraph.bond (ix 9) atom = if atom = outA then 1 else 0 := by
  decide +kernel +revert

private theorem bond_ix10 (atom : admitted.Atom) :
    admitted.moleculeGraph.bond (ix 10) atom = if atom = outA then 1 else 0 := by
  decide +kernel +revert

private theorem ix1_sorted :
    (admitted.moleculeGraph.neighborFinset (ix 1)).sort (· ≤ ·) = [rootA] := by
  rw [neighborFinset_singleton rootA (ix 1) bond_ix1, Finset.sort_singleton]

private theorem ix2_sorted :
    (admitted.moleculeGraph.neighborFinset (ix 2)).sort (· ≤ ·) = [rootA] := by
  rw [neighborFinset_singleton rootA (ix 2) bond_ix2, Finset.sort_singleton]

private theorem ix3_sorted :
    (admitted.moleculeGraph.neighborFinset (ix 3)).sort (· ≤ ·) = [rootA] := by
  rw [neighborFinset_singleton rootA (ix 3) bond_ix3, Finset.sort_singleton]

private theorem ix8_sorted :
    (admitted.moleculeGraph.neighborFinset (ix 8)).sort (· ≤ ·) = [outA] := by
  rw [neighborFinset_singleton outA (ix 8) bond_ix8, Finset.sort_singleton]

private theorem ix9_sorted :
    (admitted.moleculeGraph.neighborFinset (ix 9)).sort (· ≤ ·) = [outA] := by
  rw [neighborFinset_singleton outA (ix 9) bond_ix9, Finset.sort_singleton]

private theorem ix10_sorted :
    (admitted.moleculeGraph.neighborFinset (ix 10)).sort (· ≤ ·) = [outA] := by
  rw [neighborFinset_singleton outA (ix 10) bond_ix10, Finset.sort_singleton]

private theorem root_copies :
    admitted.executableOfficialNeighborCopies rootA =
      [(ix 1, 0), (ix 2, 0), (ix 3, 0), (auxA, 0)] := by
  simp only [executableOfficialNeighborCopies, root_neighbor_frame]
  decide +kernel

private theorem aux_copies :
    admitted.executableOfficialNeighborCopies auxA =
      [(rootA, 0), (ix 5, 0), (ix 6, 0), (outA, 0)] := by
  simp only [executableOfficialNeighborCopies, auxiliary_neighbor_frame]
  decide +kernel

private theorem out_copies :
    admitted.executableOfficialNeighborCopies outA =
      [(auxA, 0), (ix 8, 0), (ix 9, 0), (ix 10, 0)] := by
  simp only [executableOfficialNeighborCopies, outward_neighbor_frame]
  decide +kernel

private theorem ix1_copies :
    admitted.executableOfficialNeighborCopies (ix 1) = [(rootA, 0)] := by
  simp only [executableOfficialNeighborCopies, ix1_sorted]
  decide +kernel

private theorem ix2_copies :
    admitted.executableOfficialNeighborCopies (ix 2) = [(rootA, 0)] := by
  simp only [executableOfficialNeighborCopies, ix2_sorted]
  decide +kernel

private theorem ix3_copies :
    admitted.executableOfficialNeighborCopies (ix 3) = [(rootA, 0)] := by
  simp only [executableOfficialNeighborCopies, ix3_sorted]
  decide +kernel

private theorem ix8_copies :
    admitted.executableOfficialNeighborCopies (ix 8) = [(outA, 0)] := by
  simp only [executableOfficialNeighborCopies, ix8_sorted]
  decide +kernel

private theorem ix9_copies :
    admitted.executableOfficialNeighborCopies (ix 9) = [(outA, 0)] := by
  simp only [executableOfficialNeighborCopies, ix9_sorted]
  decide +kernel

private theorem ix10_copies :
    admitted.executableOfficialNeighborCopies (ix 10) = [(outA, 0)] := by
  simp only [executableOfficialNeighborCopies, ix10_sorted]
  decide +kernel

private theorem adj_bond (a b : admitted.Atom)
    (equation : admitted.moleculeGraph.bond a b = 1) :
    admitted.moleculeGraph.Adj a b := by
  rw [MoleculeGraph.Adj, equation]
  exact Nat.zero_lt_one

private theorem occurrence_step {root : admitted.Atom}
    {node : OfficialCIPNode admitted.Atom} {address : List Nat}
    {current next : admitted.Atom}
    (path : SimpleOccurrencePath admitted root node address)
    (currentObserved : node.current? = some current)
    (bond : admitted.moleculeGraph.bond current next = 1)
    (notParent : node.parent? ≠ some next)
    (fresh : next ∉ node.history) :
    SimpleOccurrencePath admitted root (node.extend next 0)
      (address ++ [admitted.executableOfficialChildCopySlot node next 0]) :=
  SimpleOccurrencePath.step path currentObserved (adj_bond current next bond) notParent fresh

theorem auxiliary_children :
    admitted.executableOfficialCIPChildren auxRoot =
      [inwardNode, auxRoot.extend (ix 5) 0, auxRoot.extend (ix 6) 0, outwardNode] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, auxRoot,
    OfficialCIPNode.root, OfficialCIPNode.parent?, aux_copies, inwardNode, outwardNode]
  decide +kernel

def inwardFluorine : OfficialCIPNode admitted.Atom :=
  inwardNode.extend (ix 1) 0

def inwardChlorine : OfficialCIPNode admitted.Atom :=
  inwardNode.extend (ix 2) 0

def inwardHydrogen : OfficialCIPNode admitted.Atom :=
  inwardNode.extend (ix 3) 0

def outwardFluorine : OfficialCIPNode admitted.Atom :=
  outwardNode.extend (ix 8) 0

def outwardChlorine : OfficialCIPNode admitted.Atom :=
  outwardNode.extend (ix 9) 0

def outwardHydrogen : OfficialCIPNode admitted.Atom :=
  outwardNode.extend (ix 10) 0

private theorem inward_copies :
    admitted.executableOfficialChildCopies inwardNode =
      [(ix 1, 0), (ix 2, 0), (ix 3, 0)] := by
  simp only [executableOfficialChildCopies, inwardNode, auxRoot, OfficialCIPNode.extend,
    OfficialCIPNode.root, OfficialCIPNode.parent?, root_copies]
  decide +kernel

private theorem outward_copies :
    admitted.executableOfficialChildCopies outwardNode =
      [(ix 8, 0), (ix 9, 0), (ix 10, 0)] := by
  simp only [executableOfficialChildCopies, outwardNode, auxRoot, OfficialCIPNode.extend,
    OfficialCIPNode.root, OfficialCIPNode.parent?, out_copies]
  decide +kernel

theorem inward_branch_children :
    admitted.executableOfficialCIPChildren inwardNode =
      [inwardFluorine, inwardChlorine, inwardHydrogen] := by
  simp only [executableOfficialCIPChildren, inward_copies, inwardFluorine, inwardChlorine,
    inwardHydrogen]
  decide +kernel

theorem outward_branch_children :
    admitted.executableOfficialCIPChildren outwardNode =
      [outwardFluorine, outwardChlorine, outwardHydrogen] := by
  simp only [executableOfficialCIPChildren, outward_copies, outwardFluorine, outwardChlorine,
    outwardHydrogen]
  decide +kernel

private theorem inward_fluorine_children :
    admitted.executableOfficialCIPChildren inwardFluorine = [] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, inwardFluorine,
    inwardNode, auxRoot, OfficialCIPNode.extend, OfficialCIPNode.root,
    OfficialCIPNode.parent?, ix1_copies]
  split_ifs <;> rfl

private theorem inward_chlorine_children :
    admitted.executableOfficialCIPChildren inwardChlorine = [] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, inwardChlorine,
    inwardNode, auxRoot, OfficialCIPNode.extend, OfficialCIPNode.root,
    OfficialCIPNode.parent?, ix2_copies]
  split_ifs <;> rfl

private theorem inward_hydrogen_children :
    admitted.executableOfficialCIPChildren inwardHydrogen = [] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, inwardHydrogen,
    inwardNode, auxRoot, OfficialCIPNode.extend, OfficialCIPNode.root,
    OfficialCIPNode.parent?, ix3_copies]
  split_ifs <;> rfl

private theorem outward_fluorine_children :
    admitted.executableOfficialCIPChildren outwardFluorine = [] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, outwardFluorine,
    outwardNode, auxRoot, OfficialCIPNode.extend, OfficialCIPNode.root,
    OfficialCIPNode.parent?, ix8_copies]
  split_ifs <;> rfl

private theorem outward_chlorine_children :
    admitted.executableOfficialCIPChildren outwardChlorine = [] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, outwardChlorine,
    outwardNode, auxRoot, OfficialCIPNode.extend, OfficialCIPNode.root,
    OfficialCIPNode.parent?, ix9_copies]
  split_ifs <;> rfl

private theorem outward_hydrogen_children :
    admitted.executableOfficialCIPChildren outwardHydrogen = [] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, outwardHydrogen,
    outwardNode, auxRoot, OfficialCIPNode.extend, OfficialCIPNode.root,
    OfficialCIPNode.parent?, ix10_copies]
  split_ifs <;> rfl

theorem compared_nodes_are_real :
    inwardNode.isDuplicateLeaf = false ∧ outwardNode.isDuplicateLeaf = false := by
  decide +kernel

theorem inward_simple_occurrence :
    SimpleOccurrencePath admitted auxA inwardNode
      [admitted.executableOfficialChildCopySlot auxRoot rootA 0] := by
  simpa [inwardNode, auxRoot] using
    occurrence_step (root := auxA) (node := auxRoot) (address := [])
      (current := auxA) (next := rootA) SimpleOccurrencePath.root
      (by simp [auxRoot, OfficialCIPNode.root])
      (by simpa using bond_aux rootA)
      (by simp [auxRoot, OfficialCIPNode.root, OfficialCIPNode.parent?])
      (by decide +kernel)

theorem outward_simple_occurrence :
    SimpleOccurrencePath admitted auxA outwardNode
      [admitted.executableOfficialChildCopySlot auxRoot outA 0] := by
  simpa [outwardNode, auxRoot] using
    occurrence_step (root := auxA) (node := auxRoot) (address := [])
      (current := auxA) (next := outA) SimpleOccurrencePath.root
      (by simp [auxRoot, OfficialCIPNode.root])
      (by simpa using bond_aux outA)
      (by simp [auxRoot, OfficialCIPNode.root, OfficialCIPNode.parent?])
      (by decide +kernel)

theorem original_outward_occurrence :
    SimpleOccurrencePath admitted rootA originalOut
      [admitted.executableOfficialChildCopySlot originalRoot auxA 0,
       admitted.executableOfficialChildCopySlot originalAux outA 0] := by
  have first :=
    occurrence_step (root := rootA) (node := originalRoot) (address := [])
      (current := rootA) (next := auxA) SimpleOccurrencePath.root
      (by simp [originalRoot, OfficialCIPNode.root])
      (by simpa using bond_root auxA)
      (by simp [originalRoot, OfficialCIPNode.root, OfficialCIPNode.parent?])
      (by decide +kernel)
  exact
    occurrence_step (root := rootA) (node := originalRoot.extend auxA 0)
      (address := [admitted.executableOfficialChildCopySlot originalRoot auxA 0])
      (current := auxA) (next := outA) first
      (OfficialCIPNode.extend_current? originalRoot auxA 0)
      (by simpa using bond_aux outA)
      (by
        simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, originalRoot, OfficialCIPNode.root]
        decide +kernel)
      (by decide +kernel)

theorem auxiliary_sphere_depths :
    inwardNode.rule1bRootDistance = 1 ∧ outwardNode.rule1bRootDistance = 1 := by
  decide +kernel

theorem original_occurrence_depths :
    originalRoot.rule1bRootDistance = 0 ∧ originalOut.rule1bRootDistance = 2 ∧
      inwardNode.current? = some rootA ∧ outwardNode.current? = some outA ∧
      originalRoot.current? = some rootA ∧ originalOut.current? = some outA := by
  decide +kernel

/-- Atom-index observer. It matches occurrence depth on the two proximal nodes only. -/
def originalRootDepth (node : OfficialCIPNode admitted.Atom) : Nat :=
  match node.current? with
  | none => 0
  | some atom =>
      if atom = rootA then 0
      else if atom = ix 1 ∨ atom = ix 2 ∨ atom = ix 3 ∨ atom = auxA then 1
      else if atom = ix 5 ∨ atom = ix 6 ∨ atom = outA then 2
      else 3

theorem originalRootDepth_on_compared_nodes :
    originalRootDepth inwardNode = originalRoot.rule1bRootDistance ∧
      originalRootDepth outwardNode = originalOut.rule1bRootDistance := by
  decide +kernel

private def expansion : OfficialCIPNode admitted.Atom → List (OfficialCIPNode admitted.Atom) :=
  admitted.executableOfficialCIPChildren

private def compiled (observe : OfficialCIPNode admitted.Atom → Nat)
    (node : OfficialCIPNode admitted.Atom) : Option (OfficialRuleMajorKey admitted.Atom) :=
  MoleculeGraph.buildOfficialRuleMajorKeyWith observe admitted.moleculeGraph expansion 2 node

def sphereInward : OfficialRuleMajorKey admitted.Atom :=
  (compiled OfficialCIPNode.rule1bRootDistance inwardNode).getD
    (admitted.moleculeGraph.officialRuleMajorRootKey inwardNode true)

def sphereOutward : OfficialRuleMajorKey admitted.Atom :=
  (compiled OfficialCIPNode.rule1bRootDistance outwardNode).getD
    (admitted.moleculeGraph.officialRuleMajorRootKey outwardNode true)

def neutralInward : OfficialRuleMajorKey admitted.Atom :=
  (compiled (fun _ => 0) inwardNode).getD
    (admitted.moleculeGraph.officialRuleMajorRootKey inwardNode true)

def neutralOutward : OfficialRuleMajorKey admitted.Atom :=
  (compiled (fun _ => 0) outwardNode).getD
    (admitted.moleculeGraph.officialRuleMajorRootKey outwardNode true)

def originalInward : OfficialRuleMajorKey admitted.Atom :=
  (compiled originalRootDepth inwardNode).getD
    (admitted.moleculeGraph.officialRuleMajorRootKey inwardNode true)

def originalOutward : OfficialRuleMajorKey admitted.Atom :=
  (compiled originalRootDepth outwardNode).getD
    (admitted.moleculeGraph.officialRuleMajorRootKey outwardNode true)

theorem auxiliary_sphere_and_constant_tie :
    (compiled OfficialCIPNode.rule1bRootDistance inwardNode).isSome = true ∧
      (compiled OfficialCIPNode.rule1bRootDistance outwardNode).isSome = true ∧
      (compiled (fun _ => 0) inwardNode).isSome = true ∧
      (compiled (fun _ => 0) outwardNode).isSome = true ∧
      sphereInward.complete = true ∧ sphereOutward.complete = true ∧
      neutralInward.complete = true ∧ neutralOutward.complete = true ∧
      OfficialRuleMajorKey.compare sphereInward sphereOutward = .eq ∧
      OfficialRuleMajorKey.compare neutralInward neutralOutward = .eq ∧
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        sphereInward.rule1a sphereOutward.rule1a = .eq := by
  simp only [sphereInward, sphereOutward, neutralInward, neutralOutward, compiled, expansion,
    MoleculeGraph.buildOfficialRuleMajorKeyWith, inward_branch_children, outward_branch_children,
    List.isEmpty_cons]
  decide +kernel

theorem original_root_depth_decides_after_rule1a_tie :
    (compiled originalRootDepth inwardNode).isSome = true ∧
      (compiled originalRootDepth outwardNode).isSome = true ∧
      originalInward.complete = true ∧ originalOutward.complete = true ∧
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        originalInward.rule1a originalOutward.rule1a = .eq ∧
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        originalInward.rule1b originalOutward.rule1b = .gt ∧
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        originalInward.rule2 originalOutward.rule2 = .eq ∧
      OfficialRuleMajorKey.compare originalInward originalOutward = .gt := by
  simp only [originalInward, originalOutward, compiled, expansion,
    MoleculeGraph.buildOfficialRuleMajorKeyWith, inward_branch_children, outward_branch_children,
    List.isEmpty_cons]
  decide +kernel

private def cyclicIx (index : Fin 9) : cyclicCertified.Atom :=
  ⟨index.val, LocalizedCyclicInputWitness.atomCount_eq.symm ▸ index.isLt⟩

/-- Atom 0’s neighbors are 1, 2, 4, and 5. Atom 3 is chlorine on atom 2. -/
theorem cyclic_fixture_root_neighbors :
    (∀ atom : cyclicCertified.Atom,
        cyclicCertified.moleculeGraph.bond (cyclicIx 0) atom =
          if atom = cyclicIx 1 ∨ atom = cyclicIx 2 ∨ atom = cyclicIx 4 ∨ atom = cyclicIx 5
            then 1 else 0) ∧
      cyclicCertified.moleculeGraph.atomZ (cyclicIx 1) = 9 ∧
      cyclicCertified.moleculeGraph.atomZ (cyclicIx 2) = 6 ∧
      cyclicCertified.moleculeGraph.atomZ (cyclicIx 3) = 17 ∧
      cyclicCertified.moleculeGraph.atomZ (cyclicIx 4) = 6 ∧
      cyclicCertified.moleculeGraph.atomZ (cyclicIx 5) = 1 := by
  refine ⟨?_, ?_⟩
  · decide +kernel +revert
  · decide +kernel

/-- The fabricated-key witness, restated on its public nodes. Its private `keyAt` is not an
admitted molecule; the same 0-versus-2 distances break an equal Rule 1a table there. -/
private def fabricatedKey (node : OfficialCIPNode Nat) (mass : Nat) : OfficialRuleMajorKey Nat :=
  { rule1a := [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]]
    rule1b := [[([], node.rule1bRootDistance)]]
    rule2 := [[([], mass)]]
    sourceNodes := []
    complete := true }

theorem abstract_key_witness_breaks_neutral_tie :
    originalContextRoot.rule1bRootDistance = 0 ∧
      auxiliaryOutwardNode.rule1bRootDistance = 2 ∧
      freshParentLigandRoot.rule1bRootDistance = 1 ∧
      freshOutwardLigandRoot.rule1bRootDistance = 1 ∧
      OfficialRuleMajorKey.compare (fabricatedKey originalContextRoot 12)
        (fabricatedKey auxiliaryOutwardNode 12) = .gt ∧
      OfficialRuleMajorKey.compare (fabricatedKey freshParentLigandRoot 12)
        (fabricatedKey freshOutwardLigandRoot 12) = .eq := by
  decide +kernel

/-! ## Retained original-root comparison

Expansion structure is the executable cursor. Retained history is the
original-root occurrence. Metric origin is that occurrence’s constitutional
`rule1bRootDistance`, identified with the outer-digraph sphere. `originalRootDepth`
is not used here.
-/

open TetraStereo.OneCenter.RetainedConstitutionalReaderIndependence
open TetraStereo.OneCenter.RetainedDigraphSphereCorrespondence
open Rule4aTableBridge
open DeclarativeCIP

abbrev carrierFuel : Nat := admitted.certified.input.molecule.atomCount

theorem simple_bonded : admitted.moleculeGraph.SimpleBonded := by
  intro u v adjacent
  rcases physical_domain.2.2.2.2.2 u v with zero | one
  · rw [MoleculeGraph.Adj, zero] at adjacent
    exact absurd adjacent (Nat.not_lt_zero 0)
  · exact one

private theorem rootLigandSlots :
    admitted.executableOfficialChildCopySlot originalRoot (ix 1) 0 = 0 ∧
      admitted.executableOfficialChildCopySlot originalRoot (ix 2) 0 = 1 ∧
      admitted.executableOfficialChildCopySlot originalRoot (ix 3) 0 = 2 ∧
      admitted.executableOfficialChildCopySlot originalRoot auxA 0 = 3 := by
  simp only [executableOfficialChildCopySlot, executableOfficialChildCopies, originalRoot,
    OfficialCIPNode.root, OfficialCIPNode.parent?, root_copies]
  decide +kernel

private theorem auxOutSlot :
    admitted.executableOfficialChildCopySlot originalAux outA 0 = 2 := by
  simp only [executableOfficialChildCopySlot, executableOfficialChildCopies, originalAux,
    originalRoot, OfficialCIPNode.extend, OfficialCIPNode.root, OfficialCIPNode.parent?,
    aux_copies]
  decide +kernel

private theorem outLigandSlots :
    admitted.executableOfficialChildCopySlot originalOut (ix 8) 0 = 0 ∧
      admitted.executableOfficialChildCopySlot originalOut (ix 9) 0 = 1 ∧
      admitted.executableOfficialChildCopySlot originalOut (ix 10) 0 = 2 := by
  simp only [executableOfficialChildCopySlot, executableOfficialChildCopies, originalOut,
    originalAux, originalRoot, OfficialCIPNode.extend, OfficialCIPNode.root,
    OfficialCIPNode.parent?, out_copies]
  decide +kernel

def retainedRootFluorine : OfficialCIPNode admitted.Atom :=
  originalRoot.extend (ix 1) 0

def retainedRootChlorine : OfficialCIPNode admitted.Atom :=
  originalRoot.extend (ix 2) 0

def retainedRootHydrogen : OfficialCIPNode admitted.Atom :=
  originalRoot.extend (ix 3) 0

def retainedOutFluorine : OfficialCIPNode admitted.Atom :=
  originalOut.extend (ix 8) 0

def retainedOutChlorine : OfficialCIPNode admitted.Atom :=
  originalOut.extend (ix 9) 0

def retainedOutHydrogen : OfficialCIPNode admitted.Atom :=
  originalOut.extend (ix 10) 0

private theorem retained_root_children :
    admitted.executableOfficialCIPChildren originalRoot =
      [retainedRootFluorine, retainedRootChlorine, retainedRootHydrogen, originalAux] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, originalRoot,
    OfficialCIPNode.root, OfficialCIPNode.parent?, root_copies, retainedRootFluorine,
    retainedRootChlorine, retainedRootHydrogen, originalAux]
  decide +kernel

private theorem retained_out_children :
    admitted.executableOfficialCIPChildren originalOut =
      [retainedOutFluorine, retainedOutChlorine, retainedOutHydrogen] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, originalOut,
    originalAux, originalRoot, OfficialCIPNode.extend, OfficialCIPNode.root,
    OfficialCIPNode.parent?, out_copies, retainedOutFluorine, retainedOutChlorine,
    retainedOutHydrogen]
  decide +kernel

private theorem retained_root_fluorine_children :
    admitted.executableOfficialCIPChildren retainedRootFluorine = [] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, retainedRootFluorine,
    originalRoot, OfficialCIPNode.extend, OfficialCIPNode.root, OfficialCIPNode.parent?,
    ix1_copies]
  split_ifs <;> rfl

private theorem retained_root_chlorine_children :
    admitted.executableOfficialCIPChildren retainedRootChlorine = [] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, retainedRootChlorine,
    originalRoot, OfficialCIPNode.extend, OfficialCIPNode.root, OfficialCIPNode.parent?,
    ix2_copies]
  split_ifs <;> rfl

private theorem retained_root_hydrogen_children :
    admitted.executableOfficialCIPChildren retainedRootHydrogen = [] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, retainedRootHydrogen,
    originalRoot, OfficialCIPNode.extend, OfficialCIPNode.root, OfficialCIPNode.parent?,
    ix3_copies]
  split_ifs <;> rfl

private theorem retained_out_fluorine_children :
    admitted.executableOfficialCIPChildren retainedOutFluorine = [] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, retainedOutFluorine,
    originalOut, originalAux, originalRoot, OfficialCIPNode.extend, OfficialCIPNode.root,
    OfficialCIPNode.parent?, ix8_copies]
  split_ifs <;> rfl

private theorem retained_out_chlorine_children :
    admitted.executableOfficialCIPChildren retainedOutChlorine = [] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, retainedOutChlorine,
    originalOut, originalAux, originalRoot, OfficialCIPNode.extend, OfficialCIPNode.root,
    OfficialCIPNode.parent?, ix9_copies]
  split_ifs <;> rfl

private theorem retained_out_hydrogen_children :
    admitted.executableOfficialCIPChildren retainedOutHydrogen = [] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies, retainedOutHydrogen,
    originalOut, originalAux, originalRoot, OfficialCIPNode.extend, OfficialCIPNode.root,
    OfficialCIPNode.parent?, ix10_copies]
  split_ifs <;> rfl

def rootPath : SimpleOccurrencePath admitted rootA originalRoot [] :=
  SimpleOccurrencePath.root

def auxPath : SimpleOccurrencePath admitted rootA originalAux
    [admitted.executableOfficialChildCopySlot originalRoot auxA 0] :=
  occurrence_step (root := rootA) (node := originalRoot) (address := [])
    (current := rootA) (next := auxA) rootPath
    (by simp [originalRoot, OfficialCIPNode.root])
    (by simpa using bond_root auxA)
    (by simp [originalRoot, OfficialCIPNode.root, OfficialCIPNode.parent?])
    (by decide +kernel)

def outPath : SimpleOccurrencePath admitted rootA originalOut
    [admitted.executableOfficialChildCopySlot originalRoot auxA 0,
     admitted.executableOfficialChildCopySlot originalAux outA 0] :=
  occurrence_step (root := rootA) (node := originalAux)
    (address := [admitted.executableOfficialChildCopySlot originalRoot auxA 0])
    (current := auxA) (next := outA) auxPath
    (OfficialCIPNode.extend_current? originalRoot auxA 0)
    (by simpa using bond_aux outA)
    (by
      simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, originalAux, originalRoot,
        OfficialCIPNode.root]
      decide +kernel)
    (by decide +kernel)

private def rootFluorinePath : SimpleOccurrencePath admitted rootA retainedRootFluorine
    [admitted.executableOfficialChildCopySlot originalRoot (ix 1) 0] :=
  occurrence_step (root := rootA) (node := originalRoot) (address := [])
    (current := rootA) (next := ix 1) rootPath
    (by simp [originalRoot, OfficialCIPNode.root])
    (by simpa using bond_root (ix 1))
    (by simp [originalRoot, OfficialCIPNode.root, OfficialCIPNode.parent?])
    (by decide +kernel)

private def rootChlorinePath : SimpleOccurrencePath admitted rootA retainedRootChlorine
    [admitted.executableOfficialChildCopySlot originalRoot (ix 2) 0] :=
  occurrence_step (root := rootA) (node := originalRoot) (address := [])
    (current := rootA) (next := ix 2) rootPath
    (by simp [originalRoot, OfficialCIPNode.root])
    (by simpa using bond_root (ix 2))
    (by simp [originalRoot, OfficialCIPNode.root, OfficialCIPNode.parent?])
    (by decide +kernel)

private def rootHydrogenPath : SimpleOccurrencePath admitted rootA retainedRootHydrogen
    [admitted.executableOfficialChildCopySlot originalRoot (ix 3) 0] :=
  occurrence_step (root := rootA) (node := originalRoot) (address := [])
    (current := rootA) (next := ix 3) rootPath
    (by simp [originalRoot, OfficialCIPNode.root])
    (by simpa using bond_root (ix 3))
    (by simp [originalRoot, OfficialCIPNode.root, OfficialCIPNode.parent?])
    (by decide +kernel)

private def outFluorinePath : SimpleOccurrencePath admitted rootA retainedOutFluorine
    [admitted.executableOfficialChildCopySlot originalRoot auxA 0,
     admitted.executableOfficialChildCopySlot originalAux outA 0,
     admitted.executableOfficialChildCopySlot originalOut (ix 8) 0] :=
  occurrence_step (root := rootA) (node := originalOut)
    (address := [admitted.executableOfficialChildCopySlot originalRoot auxA 0,
      admitted.executableOfficialChildCopySlot originalAux outA 0])
    (current := outA) (next := ix 8) outPath
    (OfficialCIPNode.extend_current? originalAux outA 0)
    (by simpa using bond_out (ix 8))
    (by
      simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, originalOut, originalAux,
        originalRoot, OfficialCIPNode.root]
      decide +kernel)
    (by decide +kernel)

private def outChlorinePath : SimpleOccurrencePath admitted rootA retainedOutChlorine
    [admitted.executableOfficialChildCopySlot originalRoot auxA 0,
     admitted.executableOfficialChildCopySlot originalAux outA 0,
     admitted.executableOfficialChildCopySlot originalOut (ix 9) 0] :=
  occurrence_step (root := rootA) (node := originalOut)
    (address := [admitted.executableOfficialChildCopySlot originalRoot auxA 0,
      admitted.executableOfficialChildCopySlot originalAux outA 0])
    (current := outA) (next := ix 9) outPath
    (OfficialCIPNode.extend_current? originalAux outA 0)
    (by simpa using bond_out (ix 9))
    (by
      simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, originalOut, originalAux,
        originalRoot, OfficialCIPNode.root]
      decide +kernel)
    (by decide +kernel)

private def outHydrogenPath : SimpleOccurrencePath admitted rootA retainedOutHydrogen
    [admitted.executableOfficialChildCopySlot originalRoot auxA 0,
     admitted.executableOfficialChildCopySlot originalAux outA 0,
     admitted.executableOfficialChildCopySlot originalOut (ix 10) 0] :=
  occurrence_step (root := rootA) (node := originalOut)
    (address := [admitted.executableOfficialChildCopySlot originalRoot auxA 0,
      admitted.executableOfficialChildCopySlot originalAux outA 0])
    (current := outA) (next := ix 10) outPath
    (OfficialCIPNode.extend_current? originalAux outA 0)
    (by simpa using bond_out (ix 10))
    (by
      simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, originalOut, originalAux,
        originalRoot, OfficialCIPNode.root]
      decide +kernel)
    (by decide +kernel)

def rootOccurrence : admitted.LocalizedCIPOccurrence carrierFuel :=
  admitted.legitimateOccurrenceCarrier (LegitimateOccurrence.simple rootPath)

def auxOccurrence : admitted.LocalizedCIPOccurrence carrierFuel :=
  admitted.legitimateOccurrenceCarrier (LegitimateOccurrence.simple auxPath)

def outOccurrence : admitted.LocalizedCIPOccurrence carrierFuel :=
  admitted.legitimateOccurrenceCarrier (LegitimateOccurrence.simple outPath)

private def rootFluorineOccurrence : admitted.LocalizedCIPOccurrence carrierFuel :=
  admitted.legitimateOccurrenceCarrier (LegitimateOccurrence.simple rootFluorinePath)

private def rootChlorineOccurrence : admitted.LocalizedCIPOccurrence carrierFuel :=
  admitted.legitimateOccurrenceCarrier (LegitimateOccurrence.simple rootChlorinePath)

private def rootHydrogenOccurrence : admitted.LocalizedCIPOccurrence carrierFuel :=
  admitted.legitimateOccurrenceCarrier (LegitimateOccurrence.simple rootHydrogenPath)

private def outFluorineOccurrence : admitted.LocalizedCIPOccurrence carrierFuel :=
  admitted.legitimateOccurrenceCarrier (LegitimateOccurrence.simple outFluorinePath)

private def outChlorineOccurrence : admitted.LocalizedCIPOccurrence carrierFuel :=
  admitted.legitimateOccurrenceCarrier (LegitimateOccurrence.simple outChlorinePath)

private def outHydrogenOccurrence : admitted.LocalizedCIPOccurrence carrierFuel :=
  admitted.legitimateOccurrenceCarrier (LegitimateOccurrence.simple outHydrogenPath)

def auxiliaryOpenCursor : admitted.LocalizedRerootCursor carrierFuel :=
  { occurrence := auxOccurrence, previous? := none }

def inwardCursor : admitted.LocalizedRerootCursor carrierFuel :=
  { occurrence := rootOccurrence, previous? := some auxOccurrence }

def outwardCursor : admitted.LocalizedRerootCursor carrierFuel :=
  { occurrence := outOccurrence, previous? := some auxOccurrence }

private def rootFluorineCursor : admitted.LocalizedRerootCursor carrierFuel :=
  { occurrence := rootFluorineOccurrence, previous? := some rootOccurrence }

private def rootChlorineCursor : admitted.LocalizedRerootCursor carrierFuel :=
  { occurrence := rootChlorineOccurrence, previous? := some rootOccurrence }

private def rootHydrogenCursor : admitted.LocalizedRerootCursor carrierFuel :=
  { occurrence := rootHydrogenOccurrence, previous? := some rootOccurrence }

private def outFluorineCursor : admitted.LocalizedRerootCursor carrierFuel :=
  { occurrence := outFluorineOccurrence, previous? := some outOccurrence }

private def outChlorineCursor : admitted.LocalizedRerootCursor carrierFuel :=
  { occurrence := outChlorineOccurrence, previous? := some outOccurrence }

private def outHydrogenCursor : admitted.LocalizedRerootCursor carrierFuel :=
  { occurrence := outHydrogenOccurrence, previous? := some outOccurrence }

private theorem auxAddress : auxOccurrence.1.address = [3] := by
  have ⟨_, _, _, slot⟩ := rootLigandSlots
  simp only [auxOccurrence, legitimateOccurrenceCarrier_address, slot]

private theorem outAddress : outOccurrence.1.address = [3, 2] := by
  have ⟨_, _, _, auxSlot⟩ := rootLigandSlots
  simp only [outOccurrence, legitimateOccurrenceCarrier_address, auxSlot, auxOutSlot]

private theorem rootAddress : rootOccurrence.1.address = [] := by
  simp [rootOccurrence, legitimateOccurrenceCarrier_address]

private theorem parentFrames_nil {frame : admitted.LocalizedCIPOccurrenceFrame}
    (address : frame.address = []) :
    admitted.localizedCarrierParentFrames (fuel := carrierFuel) frame = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro candidate present
  rw [localizedCarrierParentFrames, List.mem_filter] at present
  obtain ⟨_, cond⟩ := present
  simp only [Bool.and_eq_true, beq_iff_eq] at cond
  rcases cond with ⟨⟨_, lengthEq⟩, _⟩
  rw [address, List.length_nil] at lengthEq
  exact Nat.succ_ne_zero _ lengthEq

private theorem parentFrames_singleton
    {child parent : admitted.LocalizedCIPOccurrence carrierFuel}
    (sameRoot : parent.1.root = child.1.root)
    (sameAddress : parent.1.address = child.1.address.dropLast)
    (lengthEq : parent.1.address.length + 1 = child.1.address.length) :
    admitted.localizedCarrierParentFrames (fuel := carrierFuel) child.1 = [parent.1] := by
  have parentPresent : parent.1 ∈
      admitted.localizedCarrierParentFrames (fuel := carrierFuel) child.1 := by
    rw [localizedCarrierParentFrames, List.mem_filter]
    refine ⟨parent.2, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨sameRoot, lengthEq⟩, sameAddress⟩
  have onlyParent : ∀ candidate,
      candidate ∈ admitted.localizedCarrierParentFrames (fuel := carrierFuel) child.1 →
        candidate = parent.1 := by
    intro candidate present
    rw [localizedCarrierParentFrames, List.mem_filter] at present
    obtain ⟨candidatePresent, cond⟩ := present
    simp only [Bool.and_eq_true, beq_iff_eq] at cond
    rcases cond with ⟨⟨rootEq, _lengthEq⟩, dropEq⟩
    have candidateDerived :=
      (admitted.mem_localizedOccurrences_iff carrierFuel candidate).mp candidatePresent
    have parentDerived :=
      (admitted.mem_localizedOccurrences_iff carrierFuel parent.1).mp parent.2
    exact admitted.declarativeLocalizedOccurrence_functional_at_root_address
      candidateDerived parentDerived (rootEq.trans sameRoot.symm) (dropEq.trans sameAddress.symm)
  have parentNodup :
      (admitted.localizedCarrierParentFrames (fuel := carrierFuel) child.1).Nodup := by
    unfold localizedCarrierParentFrames
    exact (admitted.localizedOccurrences_nodup carrierFuel).filter _
  have sameMembers : ∀ candidate,
      candidate ∈ admitted.localizedCarrierParentFrames (fuel := carrierFuel) child.1 ↔
        candidate ∈ [parent.1] := by
    intro candidate
    constructor
    · intro present
      simp [onlyParent candidate present]
    · intro present
      simp only [List.mem_singleton] at present
      subst candidate
      exact parentPresent
  exact List.perm_singleton.mp
    ((List.perm_ext_iff_of_nodup parentNodup (by simp)).mpr sameMembers)

private theorem frame_eq_canonical
    {parent : admitted.LocalizedCIPOccurrence carrierFuel}
    {node : OfficialCIPNode admitted.Atom} {address : List Nat}
    (occ : LegitimateOccurrence admitted parent.1.root node address)
    (slot : Nat)
    (addressEq : address = parent.1.address ++ [slot])
    (remainingEq : admitted.certified.input.molecule.atomCount + 1 - address.length =
      parent.1.remaining - 1) :
    (admitted.legitimateOccurrenceCarrier occ).1 =
      localizedOutwardCanonicalFrame admitted parent.1 (node, slot) := by
  apply LocalizedCIPOccurrenceFrame.ext admitted
  · simp [legitimateOccurrenceCarrier_root, localizedOutwardCanonicalFrame_root]
  · simp [legitimateOccurrenceCarrier_address, localizedOutwardCanonicalFrame_address, addressEq]
  · simp [legitimateOccurrenceCarrier_node, localizedOutwardCanonicalFrame_node]
  · simp [legitimateOccurrenceCarrier_remaining, localizedOutwardCanonicalFrame_remaining,
      remainingEq]

private theorem rootFluorineAddress : rootFluorineOccurrence.1.address = [0] := by
  have ⟨slot, _, _, _⟩ := rootLigandSlots
  simp only [rootFluorineOccurrence, legitimateOccurrenceCarrier_address, slot]

private theorem rootChlorineAddress : rootChlorineOccurrence.1.address = [1] := by
  have ⟨_, slot, _, _⟩ := rootLigandSlots
  simp only [rootChlorineOccurrence, legitimateOccurrenceCarrier_address, slot]

private theorem rootHydrogenAddress : rootHydrogenOccurrence.1.address = [2] := by
  have ⟨_, _, slot, _⟩ := rootLigandSlots
  simp only [rootHydrogenOccurrence, legitimateOccurrenceCarrier_address, slot]

private theorem remaining_step {parent : admitted.LocalizedCIPOccurrence carrierFuel}
    {address : List Nat}
    (addressLength : address.length = parent.1.address.length + 1)
    (parentRemaining : parent.1.remaining =
      admitted.certified.input.molecule.atomCount + 1 - parent.1.address.length) :
    admitted.certified.input.molecule.atomCount + 1 - address.length = parent.1.remaining - 1 := by
  rw [addressLength, parentRemaining]
  omega

private theorem root_parent_remaining :
    rootOccurrence.1.remaining =
      admitted.certified.input.molecule.atomCount + 1 - rootOccurrence.1.address.length := by
  simp [rootOccurrence, legitimateOccurrenceCarrier_remaining]

private theorem rootFluorine_frame :
    rootFluorineOccurrence.1 =
      localizedOutwardCanonicalFrame admitted rootOccurrence.1 (retainedRootFluorine, 0) :=
  frame_eq_canonical (parent := rootOccurrence)
    (LegitimateOccurrence.simple rootFluorinePath) 0
    (by
      have ⟨slot, _, _, _⟩ := rootLigandSlots
      simp [rootAddress, slot])
    (remaining_step (by simp [rootAddress]) root_parent_remaining)

private theorem rootChlorine_frame :
    rootChlorineOccurrence.1 =
      localizedOutwardCanonicalFrame admitted rootOccurrence.1 (retainedRootChlorine, 1) :=
  frame_eq_canonical (parent := rootOccurrence)
    (LegitimateOccurrence.simple rootChlorinePath) 1
    (by
      have ⟨_, slot, _, _⟩ := rootLigandSlots
      simp [rootAddress, slot])
    (remaining_step (by simp [rootAddress]) root_parent_remaining)

private theorem rootHydrogen_frame :
    rootHydrogenOccurrence.1 =
      localizedOutwardCanonicalFrame admitted rootOccurrence.1 (retainedRootHydrogen, 2) :=
  frame_eq_canonical (parent := rootOccurrence)
    (LegitimateOccurrence.simple rootHydrogenPath) 2
    (by
      have ⟨_, _, slot, _⟩ := rootLigandSlots
      simp [rootAddress, slot])
    (remaining_step (by simp [rootAddress]) root_parent_remaining)

private theorem aux_frame :
    auxOccurrence.1 =
      localizedOutwardCanonicalFrame admitted rootOccurrence.1 (originalAux, 3) :=
  frame_eq_canonical (parent := rootOccurrence) (LegitimateOccurrence.simple auxPath) 3
    (by
      have ⟨_, _, _, slot⟩ := rootLigandSlots
      simp [rootAddress, slot])
    (remaining_step (by simp [rootAddress]) root_parent_remaining)

private theorem outFluorineAddress : outFluorineOccurrence.1.address = [3, 2, 0] := by
  have ⟨slot, _, _⟩ := outLigandSlots
  have ⟨_, _, _, auxSlot⟩ := rootLigandSlots
  simp only [outFluorineOccurrence, legitimateOccurrenceCarrier_address, slot, auxSlot, auxOutSlot]

private theorem outChlorineAddress : outChlorineOccurrence.1.address = [3, 2, 1] := by
  have ⟨_, slot, _⟩ := outLigandSlots
  have ⟨_, _, _, auxSlot⟩ := rootLigandSlots
  simp only [outChlorineOccurrence, legitimateOccurrenceCarrier_address, slot, auxSlot, auxOutSlot]

private theorem outHydrogenAddress : outHydrogenOccurrence.1.address = [3, 2, 2] := by
  have ⟨_, _, slot⟩ := outLigandSlots
  have ⟨_, _, _, auxSlot⟩ := rootLigandSlots
  simp only [outHydrogenOccurrence, legitimateOccurrenceCarrier_address, slot, auxSlot, auxOutSlot]

private theorem out_parent_remaining :
    outOccurrence.1.remaining =
      admitted.certified.input.molecule.atomCount + 1 - outOccurrence.1.address.length := by
  simp [outOccurrence, legitimateOccurrenceCarrier_remaining]

private theorem outFluorine_frame :
    outFluorineOccurrence.1 =
      localizedOutwardCanonicalFrame admitted outOccurrence.1 (retainedOutFluorine, 0) :=
  frame_eq_canonical (parent := outOccurrence)
    (LegitimateOccurrence.simple outFluorinePath) 0
    (by
      have ⟨slot, _, _⟩ := outLigandSlots
      have ⟨_, _, _, auxSlot⟩ := rootLigandSlots
      simp [outAddress, slot, auxSlot, auxOutSlot])
    (remaining_step (by simp [outAddress]) out_parent_remaining)

private theorem outChlorine_frame :
    outChlorineOccurrence.1 =
      localizedOutwardCanonicalFrame admitted outOccurrence.1 (retainedOutChlorine, 1) :=
  frame_eq_canonical (parent := outOccurrence)
    (LegitimateOccurrence.simple outChlorinePath) 1
    (by
      have ⟨_, slot, _⟩ := outLigandSlots
      have ⟨_, _, _, auxSlot⟩ := rootLigandSlots
      simp [outAddress, slot, auxSlot, auxOutSlot])
    (remaining_step (by simp [outAddress]) out_parent_remaining)

private theorem outHydrogen_frame :
    outHydrogenOccurrence.1 =
      localizedOutwardCanonicalFrame admitted outOccurrence.1 (retainedOutHydrogen, 2) :=
  frame_eq_canonical (parent := outOccurrence)
    (LegitimateOccurrence.simple outHydrogenPath) 2
    (by
      have ⟨_, _, slot⟩ := outLigandSlots
      have ⟨_, _, _, auxSlot⟩ := rootLigandSlots
      simp [outAddress, slot, auxSlot, auxOutSlot])
    (remaining_step (by simp [outAddress]) out_parent_remaining)

private theorem root_zip {child : OfficialCIPNode admitted.Atom} {slot : Nat}
    (present : (child, slot) ∈ (admitted.executableOfficialCIPChildren originalRoot).zipIdx) :
    (child = retainedRootFluorine ∧ slot = 0) ∨
      (child = retainedRootChlorine ∧ slot = 1) ∨
      (child = retainedRootHydrogen ∧ slot = 2) ∨
      (child = originalAux ∧ slot = 3) := by
  rw [retained_root_children] at present
  simpa [List.zipIdx_cons, List.zipIdx_nil, List.mem_cons, List.mem_nil_iff, or_false,
    Prod.mk.injEq] using present

private theorem out_zip {child : OfficialCIPNode admitted.Atom} {slot : Nat}
    (present : (child, slot) ∈ (admitted.executableOfficialCIPChildren originalOut).zipIdx) :
    (child = retainedOutFluorine ∧ slot = 0) ∨
      (child = retainedOutChlorine ∧ slot = 1) ∨
      (child = retainedOutHydrogen ∧ slot = 2) := by
  rw [retained_out_children] at present
  simpa [List.zipIdx_cons, List.zipIdx_nil, List.mem_cons, List.mem_nil_iff, or_false,
    Prod.mk.injEq] using present

private theorem root_derived :
    admitted.DeclarativeLocalizedOccurrence carrierFuel rootOccurrence.1 :=
  (admitted.mem_localizedOccurrences_iff carrierFuel rootOccurrence.1).mp rootOccurrence.2

private theorem out_derived :
    admitted.DeclarativeLocalizedOccurrence carrierFuel outOccurrence.1 :=
  (admitted.mem_localizedOccurrences_iff carrierFuel outOccurrence.1).mp outOccurrence.2

private theorem aux_derived :
    admitted.DeclarativeLocalizedOccurrence carrierFuel auxOccurrence.1 :=
  (admitted.mem_localizedOccurrences_iff carrierFuel auxOccurrence.1).mp auxOccurrence.2

private theorem root_positive : 0 < rootOccurrence.1.remaining := by
  rw [root_parent_remaining, rootAddress, atomCount_eq, List.length_nil, Nat.sub_zero]
  exact Nat.succ_pos 11

private theorem out_positive : 0 < outOccurrence.1.remaining := by
  rw [out_parent_remaining, outAddress, atomCount_eq]
  decide

private theorem root_outward_cover (candidate : admitted.LocalizedCIPOccurrenceFrame)
    (present : candidate ∈ admitted.localizedCarrierOutwardChildFrames
      (fuel := carrierFuel) rootOccurrence.1) :
    candidate = rootFluorineOccurrence.1 ∨ candidate = rootChlorineOccurrence.1 ∨
      candidate = rootHydrogenOccurrence.1 ∨ candidate = auxOccurrence.1 := by
  have parts :=
    (admitted.mem_localizedCarrierOutwardChildFrames_iff rootOccurrence.1 candidate).mp present
  have candidateDerived :=
    (admitted.mem_localizedOccurrences_iff carrierFuel candidate).mp parts.1
  have nonempty : candidate.address ≠ [] := by
    intro empty
    rw [rootAddress, empty] at parts
    simp at parts
  let slot := candidate.address.getLast nonempty
  have addressEq : candidate.address = rootOccurrence.1.address ++ [slot] := by
    have split := (List.dropLast_concat_getLast nonempty).symm
    rw [parts.2.2.2] at split
    exact split
  obtain ⟨child, childAtSlot, candidateEq⟩ :=
    admitted.declarativeLocalizedOccurrence_immediate_child root_derived candidateDerived
      parts.2.1 slot addressEq
  rcases root_zip childAtSlot with ⟨nodeEq, slotEq⟩ | ⟨nodeEq, slotEq⟩ | ⟨nodeEq, slotEq⟩ |
      ⟨nodeEq, slotEq⟩
  · refine Or.inl ?_
    rw [candidateEq, nodeEq, slotEq]
    exact rootFluorine_frame.symm
  · refine Or.inr (Or.inl ?_)
    rw [candidateEq, nodeEq, slotEq]
    exact rootChlorine_frame.symm
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [candidateEq, nodeEq, slotEq]
    exact rootHydrogen_frame.symm
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [candidateEq, nodeEq, slotEq]
    exact aux_frame.symm

private theorem out_outward_cover (candidate : admitted.LocalizedCIPOccurrenceFrame)
    (present : candidate ∈ admitted.localizedCarrierOutwardChildFrames
      (fuel := carrierFuel) outOccurrence.1) :
    candidate = outFluorineOccurrence.1 ∨ candidate = outChlorineOccurrence.1 ∨
      candidate = outHydrogenOccurrence.1 := by
  have parts :=
    (admitted.mem_localizedCarrierOutwardChildFrames_iff outOccurrence.1 candidate).mp present
  have candidateDerived :=
    (admitted.mem_localizedOccurrences_iff carrierFuel candidate).mp parts.1
  have nonempty : candidate.address ≠ [] := by
    intro empty
    rw [outAddress, empty] at parts
    simp at parts
  let slot := candidate.address.getLast nonempty
  have addressEq : candidate.address = outOccurrence.1.address ++ [slot] := by
    have split := (List.dropLast_concat_getLast nonempty).symm
    rw [parts.2.2.2] at split
    exact split
  obtain ⟨child, childAtSlot, candidateEq⟩ :=
    admitted.declarativeLocalizedOccurrence_immediate_child out_derived candidateDerived
      parts.2.1 slot addressEq
  rcases out_zip childAtSlot with ⟨nodeEq, slotEq⟩ | ⟨nodeEq, slotEq⟩ | ⟨nodeEq, slotEq⟩
  · refine Or.inl ?_
    rw [candidateEq, nodeEq, slotEq]
    exact outFluorine_frame.symm
  · refine Or.inr (Or.inl ?_)
    rw [candidateEq, nodeEq, slotEq]
    exact outChlorine_frame.symm
  · refine Or.inr (Or.inr ?_)
    rw [candidateEq, nodeEq, slotEq]
    exact outHydrogen_frame.symm

private theorem mem_outward {parent child : admitted.LocalizedCIPOccurrence carrierFuel}
    (sameRoot : child.1.root = parent.1.root)
    (lengthEq : child.1.address.length = parent.1.address.length + 1)
    (dropEq : child.1.address.dropLast = parent.1.address) :
    child.1 ∈ admitted.localizedCarrierOutwardChildFrames (fuel := carrierFuel) parent.1 :=
  (admitted.mem_localizedCarrierOutwardChildFrames_iff parent.1 child.1).mpr
    ⟨child.2, sameRoot, lengthEq, dropEq⟩

private theorem rootFluorine_outward :
    rootFluorineOccurrence.1 ∈ admitted.localizedCarrierOutwardChildFrames
      (fuel := carrierFuel) rootOccurrence.1 :=
  mem_outward (by simp [rootFluorineOccurrence, rootOccurrence, legitimateOccurrenceCarrier_root])
    (by simp [rootFluorineAddress, rootAddress]) (by simp [rootFluorineAddress, rootAddress])

private theorem rootChlorine_outward :
    rootChlorineOccurrence.1 ∈ admitted.localizedCarrierOutwardChildFrames
      (fuel := carrierFuel) rootOccurrence.1 :=
  mem_outward (by simp [rootChlorineOccurrence, rootOccurrence, legitimateOccurrenceCarrier_root])
    (by simp [rootChlorineAddress, rootAddress]) (by simp [rootChlorineAddress, rootAddress])

private theorem rootHydrogen_outward :
    rootHydrogenOccurrence.1 ∈ admitted.localizedCarrierOutwardChildFrames
      (fuel := carrierFuel) rootOccurrence.1 :=
  mem_outward (by simp [rootHydrogenOccurrence, rootOccurrence, legitimateOccurrenceCarrier_root])
    (by simp [rootHydrogenAddress, rootAddress]) (by simp [rootHydrogenAddress, rootAddress])

private theorem aux_outward :
    auxOccurrence.1 ∈ admitted.localizedCarrierOutwardChildFrames
      (fuel := carrierFuel) rootOccurrence.1 :=
  mem_outward (by simp [auxOccurrence, rootOccurrence, legitimateOccurrenceCarrier_root])
    (by simp [auxAddress, rootAddress]) (by simp [auxAddress, rootAddress])

private theorem outFluorine_outward :
    outFluorineOccurrence.1 ∈ admitted.localizedCarrierOutwardChildFrames
      (fuel := carrierFuel) outOccurrence.1 :=
  mem_outward (by simp [outFluorineOccurrence, outOccurrence, legitimateOccurrenceCarrier_root])
    (by simp [outFluorineAddress, outAddress]) (by simp [outFluorineAddress, outAddress])

private theorem outChlorine_outward :
    outChlorineOccurrence.1 ∈ admitted.localizedCarrierOutwardChildFrames
      (fuel := carrierFuel) outOccurrence.1 :=
  mem_outward (by simp [outChlorineOccurrence, outOccurrence, legitimateOccurrenceCarrier_root])
    (by simp [outChlorineAddress, outAddress]) (by simp [outChlorineAddress, outAddress])

private theorem outHydrogen_outward :
    outHydrogenOccurrence.1 ∈ admitted.localizedCarrierOutwardChildFrames
      (fuel := carrierFuel) outOccurrence.1 :=
  mem_outward (by simp [outHydrogenOccurrence, outOccurrence, legitimateOccurrenceCarrier_root])
    (by simp [outHydrogenAddress, outAddress]) (by simp [outHydrogenAddress, outAddress])

private theorem out_mem_aux_outward :
    outOccurrence.1 ∈ admitted.localizedCarrierOutwardChildFrames
      (fuel := carrierFuel) auxOccurrence.1 :=
  mem_outward (by simp [outOccurrence, auxOccurrence, legitimateOccurrenceCarrier_root])
    (by simp [outAddress, auxAddress]) (by simp [outAddress, auxAddress])

private theorem root_parent_of_aux :
    admitted.localizedCarrierParentFrames (fuel := carrierFuel) auxOccurrence.1 =
      [rootOccurrence.1] :=
  parentFrames_singleton
    (by simp [rootOccurrence, auxOccurrence, legitimateOccurrenceCarrier_root])
    (by simp [rootAddress, auxAddress]) (by simp [rootAddress, auxAddress])

private theorem aux_not_duplicate : originalAux.isDuplicateLeaf = false := by
  decide +kernel

private theorem root_not_duplicate : originalRoot.isDuplicateLeaf = false := by
  simp [originalRoot, OfficialCIPNode.root, OfficialCIPNode.isDuplicateLeaf]

private theorem out_not_duplicate : originalOut.isDuplicateLeaf = false := by
  decide +kernel

private theorem leaf_not_duplicate (node : OfficialCIPNode admitted.Atom)
    (h : node = retainedRootFluorine ∨ node = retainedRootChlorine ∨
      node = retainedRootHydrogen ∨ node = retainedOutFluorine ∨
      node = retainedOutChlorine ∨ node = retainedOutHydrogen) :
    node.isDuplicateLeaf = false := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem mem_exec_of_frame {source child : admitted.LocalizedRerootCursor carrierFuel}
    (framePresent : child.occurrence.1 ∈ admitted.intendedLocalizedRerootChildFrames source)
    (prev : child.previous? = some source.occurrence) :
    child ∈ admitted.executableLocalizedRerootChildren source := by
  unfold executableLocalizedRerootChildren
  refine List.mem_map.mpr ⟨⟨child.occurrence.1, framePresent⟩, List.mem_attach _ _, ?_⟩
  apply LocalizedRerootCursor.ext admitted
  · exact Subtype.ext rfl
  · exact prev.symm

private theorem open_not_duplicate :
    auxiliaryOpenCursor.occurrence.1.node.isDuplicateLeaf = false := by
  simp [auxiliaryOpenCursor, auxOccurrence, legitimateOccurrenceCarrier_node, aux_not_duplicate]

private theorem root_in_open_intended :
    rootOccurrence.1 ∈ admitted.intendedLocalizedRerootChildFrames auxiliaryOpenCursor := by
  have parentPresent : rootOccurrence.1 ∈
      admitted.localizedCarrierParentFrames (fuel := carrierFuel) auxOccurrence.1 := by
    rw [root_parent_of_aux]
    simp
  simp only [intendedLocalizedRerootChildFrames, auxiliaryOpenCursor,
    localizedRerootNeighborFrames]
  exact List.mem_append_left _ parentPresent

private theorem out_in_open_intended :
    outOccurrence.1 ∈ admitted.intendedLocalizedRerootChildFrames auxiliaryOpenCursor := by
  simp only [intendedLocalizedRerootChildFrames, auxiliaryOpenCursor,
    localizedRerootNeighborFrames]
  exact List.mem_append_right _ out_mem_aux_outward

theorem retained_executable_cursors :
    inwardCursor ∈ admitted.executableLocalizedRerootChildren auxiliaryOpenCursor ∧
      outwardCursor ∈ admitted.executableLocalizedRerootChildren auxiliaryOpenCursor ∧
      rootOccurrence.1.node.history = [rootA] ∧
      auxOccurrence.1.node.history = [auxA, rootA] ∧
      outOccurrence.1.node.history = [outA, auxA, rootA] ∧
      inwardCursor.previous? = some auxOccurrence ∧
      outwardCursor.previous? = some auxOccurrence := by
  refine ⟨mem_exec_of_frame root_in_open_intended rfl,
    mem_exec_of_frame out_in_open_intended rfl, ?_, ?_, ?_, rfl, rfl⟩
  · simp [rootOccurrence, legitimateOccurrenceCarrier_node, originalRoot, OfficialCIPNode.root]
  · simp [auxOccurrence, legitimateOccurrenceCarrier_node, originalAux, originalRoot,
      OfficialCIPNode.extend, OfficialCIPNode.root]
  · simp [outOccurrence, legitimateOccurrenceCarrier_node, originalOut, originalAux, originalRoot,
      OfficialCIPNode.extend, OfficialCIPNode.root]

theorem auxiliary_occurrence_four_ligand_frame :
    ∃ frame : admitted.LocalizedOccurrenceFourLigandFrame carrierFuel,
      admitted.localizedOccurrenceFourLigandFrame? auxOccurrence = some frame := by
  have centerMem : auxA ∈ admitted.tetrahedralCenterSet := by
    rw [tetrahedralCenterSet, MoleculeGraph.mem_tetrahedralCenterSet,
      MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card]
    exact four_ligand_centers.2.1
  have realProvenance : auxOccurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
    simp [auxOccurrence, legitimateOccurrenceCarrier_node, originalAux, originalRoot,
      OfficialCIPNode.extend, OfficialCIPNode.root, OfficialCIPNode.childProvenance]
    decide +kernel
  have currentAtom : auxOccurrence.1.node.current? = some auxA := by
    simp [auxOccurrence, legitimateOccurrenceCarrier_node, originalAux,
      OfficialCIPNode.extend_current?]
  exact admitted.exists_simpleBond_localizedOccurrenceFourLigandFrame_of_realCenter
    simple_bonded (le_rfl) auxOccurrence ⟨auxA, centerMem⟩ ⟨realProvenance, currentAtom⟩

private theorem inward_not_duplicate :
    inwardCursor.occurrence.1.node.isDuplicateLeaf = false := by
  simp [inwardCursor, rootOccurrence, legitimateOccurrenceCarrier_node, root_not_duplicate]

private theorem outward_cursor_not_duplicate :
    outwardCursor.occurrence.1.node.isDuplicateLeaf = false := by
  simp [outwardCursor, outOccurrence, legitimateOccurrenceCarrier_node, out_not_duplicate]

private theorem root_parent_nil :
    admitted.localizedCarrierParentFrames (fuel := carrierFuel) rootOccurrence.1 = [] :=
  parentFrames_nil rootAddress

private theorem inward_intended_eq :
    admitted.intendedLocalizedRerootChildFrames inwardCursor =
      (admitted.localizedCarrierOutwardChildFrames (fuel := carrierFuel)
        rootOccurrence.1).filter (fun frame => frame.address != auxOccurrence.1.address) := by
  have notDup : rootOccurrence.1.node.isDuplicateLeaf = false := by
    simpa [inwardCursor, rootOccurrence, legitimateOccurrenceCarrier_node] using
      inward_not_duplicate
  simp [intendedLocalizedRerootChildFrames, inwardCursor, notDup, localizedRerootNeighborFrames,
    root_parent_nil]

private theorem inward_frame_cover (frame : admitted.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ admitted.intendedLocalizedRerootChildFrames inwardCursor) :
    frame = rootFluorineOccurrence.1 ∨ frame = rootChlorineOccurrence.1 ∨
      frame = rootHydrogenOccurrence.1 := by
  rw [inward_intended_eq, List.mem_filter] at present
  obtain ⟨outwardPresent, different⟩ := present
  have differentAddr : frame.address ≠ auxOccurrence.1.address := by
    simpa [bne_iff_ne] using different
  rcases root_outward_cover frame outwardPresent with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact absurd rfl differentAddr

private theorem proximal_address_ne_aux :
    ([0] : List Nat) ≠ auxOccurrence.1.address ∧ ([1] : List Nat) ≠ auxOccurrence.1.address ∧
      ([2] : List Nat) ≠ auxOccurrence.1.address := by
  rw [auxAddress]
  decide

private theorem rootFluorine_intended :
    rootFluorineOccurrence.1 ∈ admitted.intendedLocalizedRerootChildFrames inwardCursor := by
  rw [inward_intended_eq, List.mem_filter]
  exact ⟨rootFluorine_outward, by
    simpa [bne_iff_ne, rootFluorineAddress] using proximal_address_ne_aux.1⟩

private theorem rootChlorine_intended :
    rootChlorineOccurrence.1 ∈ admitted.intendedLocalizedRerootChildFrames inwardCursor := by
  rw [inward_intended_eq, List.mem_filter]
  exact ⟨rootChlorine_outward, by
    simpa [bne_iff_ne, rootChlorineAddress] using proximal_address_ne_aux.2.1⟩

private theorem rootHydrogen_intended :
    rootHydrogenOccurrence.1 ∈ admitted.intendedLocalizedRerootChildFrames inwardCursor := by
  rw [inward_intended_eq, List.mem_filter]
  exact ⟨rootHydrogen_outward, by
    simpa [bne_iff_ne, rootHydrogenAddress] using proximal_address_ne_aux.2.2⟩

private theorem outward_frames_perm :
    (admitted.intendedLocalizedRerootChildFrames outwardCursor).Perm
      (admitted.localizedCarrierOutwardChildFrames (fuel := carrierFuel) outOccurrence.1) :=
  admitted.intendedLocalizedRerootChildFrames_perm_outward outwardCursor auxOccurrence rfl
    (by simp [outwardCursor, outOccurrence, auxOccurrence, legitimateOccurrenceCarrier_root])
    (by simp [outwardCursor, auxAddress, outAddress])
    (by simp [outwardCursor, auxAddress, outAddress])
    outward_cursor_not_duplicate

private theorem outward_frame_cover (frame : admitted.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ admitted.intendedLocalizedRerootChildFrames outwardCursor) :
    frame = outFluorineOccurrence.1 ∨ frame = outChlorineOccurrence.1 ∨
      frame = outHydrogenOccurrence.1 := by
  have outwardPresent : frame ∈ admitted.localizedCarrierOutwardChildFrames
      (fuel := carrierFuel) outOccurrence.1 :=
    (outward_frames_perm.mem_iff).mp present
  exact out_outward_cover frame outwardPresent

private theorem outFluorine_intended :
    outFluorineOccurrence.1 ∈ admitted.intendedLocalizedRerootChildFrames outwardCursor :=
  (outward_frames_perm.mem_iff).mpr outFluorine_outward

private theorem outChlorine_intended :
    outChlorineOccurrence.1 ∈ admitted.intendedLocalizedRerootChildFrames outwardCursor :=
  (outward_frames_perm.mem_iff).mpr outChlorine_outward

private theorem outHydrogen_intended :
    outHydrogenOccurrence.1 ∈ admitted.intendedLocalizedRerootChildFrames outwardCursor :=
  (outward_frames_perm.mem_iff).mpr outHydrogen_outward

private theorem positive_of_length (remaining addressLength : Nat)
    (formula : remaining = 11 + 1 - addressLength)
    (lengthEq : addressLength = 1 ∨ addressLength = 3) : 0 < remaining := by
  rcases lengthEq with rfl | rfl <;> rw [formula] <;> omega

private theorem leaf_exec_nil {parent child : admitted.LocalizedCIPOccurrence carrierFuel}
    (cursor : admitted.LocalizedRerootCursor carrierFuel)
    (childrenNil : admitted.executableOfficialCIPChildren child.1.node = [])
    (notDup : child.1.node.isDuplicateLeaf = false)
    (cursorOcc : cursor.occurrence = child)
    (cursorPrev : cursor.previous? = some parent)
    (sameRoot : parent.1.root = child.1.root)
    (sameAddress : parent.1.address = child.1.address.dropLast)
    (lengthEq : parent.1.address.length + 1 = child.1.address.length)
    (positive : 0 < child.1.remaining) :
    admitted.executableLocalizedRerootChildren cursor = [] := by
  have derived := (admitted.mem_localizedOccurrences_iff carrierFuel child.1).mp child.2
  have nodePerm := admitted.localizedOutwardChildFrames_nodes_perm_executable child.1 derived
    positive
  rw [childrenNil] at nodePerm
  have outwardNil : admitted.localizedCarrierOutwardChildFrames (fuel := carrierFuel) child.1 =
      [] := by
    exact List.eq_nil_of_length_eq_zero (by
      have mappedNil := List.Perm.eq_nil nodePerm
      have lengthNil := congrArg List.length mappedNil
      simpa [List.length_map] using lengthNil)
  have parentList := parentFrames_singleton sameRoot sameAddress lengthEq
  have intendedNil : admitted.intendedLocalizedRerootChildFrames cursor = [] := by
    simp [intendedLocalizedRerootChildFrames, cursorOcc, cursorPrev, notDup,
      localizedRerootNeighborFrames, parentList, outwardNil]
  simp [executableLocalizedRerootChildren, intendedNil]

private theorem rootFluorine_exec_nil :
    admitted.executableLocalizedRerootChildren rootFluorineCursor = [] :=
  leaf_exec_nil (parent := rootOccurrence) (child := rootFluorineOccurrence)
    rootFluorineCursor retained_root_fluorine_children
    (by decide +kernel) rfl rfl
    (by simp [rootOccurrence, rootFluorineOccurrence])
    (by simp [rootAddress, rootFluorineAddress]) (by simp [rootAddress, rootFluorineAddress])
    (by simp [rootFluorineOccurrence, legitimateOccurrenceCarrier_remaining, atomCount_eq])

private theorem rootChlorine_exec_nil :
    admitted.executableLocalizedRerootChildren rootChlorineCursor = [] :=
  leaf_exec_nil (parent := rootOccurrence) (child := rootChlorineOccurrence)
    rootChlorineCursor retained_root_chlorine_children
    (by decide +kernel) rfl rfl
    (by simp [rootOccurrence, rootChlorineOccurrence])
    (by simp [rootAddress, rootChlorineAddress]) (by simp [rootAddress, rootChlorineAddress])
    (by simp [rootChlorineOccurrence, legitimateOccurrenceCarrier_remaining, atomCount_eq])

private theorem rootHydrogen_exec_nil :
    admitted.executableLocalizedRerootChildren rootHydrogenCursor = [] :=
  leaf_exec_nil (parent := rootOccurrence) (child := rootHydrogenOccurrence)
    rootHydrogenCursor retained_root_hydrogen_children
    (by decide +kernel) rfl rfl
    (by simp [rootOccurrence, rootHydrogenOccurrence])
    (by simp [rootAddress, rootHydrogenAddress]) (by simp [rootAddress, rootHydrogenAddress])
    (by simp [rootHydrogenOccurrence, legitimateOccurrenceCarrier_remaining, atomCount_eq])

private theorem outFluorine_exec_nil :
    admitted.executableLocalizedRerootChildren outFluorineCursor = [] :=
  leaf_exec_nil (parent := outOccurrence) (child := outFluorineOccurrence)
    outFluorineCursor retained_out_fluorine_children
    (by decide +kernel) rfl rfl
    (by simp [outOccurrence, outFluorineOccurrence])
    (by simp [outAddress, outFluorineAddress]) (by simp [outAddress, outFluorineAddress])
    (by simp [outFluorineOccurrence, legitimateOccurrenceCarrier_remaining, atomCount_eq])

private theorem outChlorine_exec_nil :
    admitted.executableLocalizedRerootChildren outChlorineCursor = [] :=
  leaf_exec_nil (parent := outOccurrence) (child := outChlorineOccurrence)
    outChlorineCursor retained_out_chlorine_children
    (by decide +kernel) rfl rfl
    (by simp [outOccurrence, outChlorineOccurrence])
    (by simp [outAddress, outChlorineAddress]) (by simp [outAddress, outChlorineAddress])
    (by simp [outChlorineOccurrence, legitimateOccurrenceCarrier_remaining, atomCount_eq])

private theorem outHydrogen_exec_nil :
    admitted.executableLocalizedRerootChildren outHydrogenCursor = [] :=
  leaf_exec_nil (parent := outOccurrence) (child := outHydrogenOccurrence)
    outHydrogenCursor retained_out_hydrogen_children
    (by decide +kernel) rfl rfl
    (by simp [outOccurrence, outHydrogenOccurrence])
    (by simp [outAddress, outHydrogenAddress]) (by simp [outAddress, outHydrogenAddress])
    (by simp [outHydrogenOccurrence, legitimateOccurrenceCarrier_remaining, atomCount_eq])

private def noneRead : admitted.LocalizedRerootCursor carrierFuel →
    Option LocalizedAuxiliaryLabel := fun _ => none

private theorem terminal_of_nil (cursor : admitted.LocalizedRerootCursor carrierFuel)
    (execNil : admitted.executableLocalizedRerootChildren cursor = []) :
    admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 cursor =
      some (localizedCumulativeRule45TerminalKey admitted .rule4a cursor none) := by
  unfold buildRuleMajorCumulativeWithRead?
  rw [admitted.localizedRerootChildren?_eq_some_executable, execNil]
  simp [noneRead]

private theorem rootFluorine_terminal :
    admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 rootFluorineCursor =
      some (localizedCumulativeRule45TerminalKey admitted .rule4a rootFluorineCursor none) :=
  terminal_of_nil rootFluorineCursor rootFluorine_exec_nil

private theorem rootChlorine_terminal :
    admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 rootChlorineCursor =
      some (localizedCumulativeRule45TerminalKey admitted .rule4a rootChlorineCursor none) :=
  terminal_of_nil rootChlorineCursor rootChlorine_exec_nil

private theorem rootHydrogen_terminal :
    admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 rootHydrogenCursor =
      some (localizedCumulativeRule45TerminalKey admitted .rule4a rootHydrogenCursor none) :=
  terminal_of_nil rootHydrogenCursor rootHydrogen_exec_nil

private theorem outFluorine_terminal :
    admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 outFluorineCursor =
      some (localizedCumulativeRule45TerminalKey admitted .rule4a outFluorineCursor none) :=
  terminal_of_nil outFluorineCursor outFluorine_exec_nil

private theorem outChlorine_terminal :
    admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 outChlorineCursor =
      some (localizedCumulativeRule45TerminalKey admitted .rule4a outChlorineCursor none) :=
  terminal_of_nil outChlorineCursor outChlorine_exec_nil

private theorem outHydrogen_terminal :
    admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 outHydrogenCursor =
      some (localizedCumulativeRule45TerminalKey admitted .rule4a outHydrogenCursor none) :=
  terminal_of_nil outHydrogenCursor outHydrogen_exec_nil

private theorem inward_exec_cover (child : admitted.LocalizedRerootCursor carrierFuel)
    (present : child ∈ admitted.executableLocalizedRerootChildren inwardCursor) :
    child = rootFluorineCursor ∨ child = rootChlorineCursor ∨ child = rootHydrogenCursor := by
  unfold executableLocalizedRerootChildren at present
  obtain ⟨frame, _framePresent, rfl⟩ := List.mem_map.mp present
  rcases inward_frame_cover frame.1 frame.2 with h | h | h
  · refine Or.inl ?_
    apply LocalizedRerootCursor.ext admitted
    · apply Subtype.ext
      simpa [rootFluorineCursor] using h
    · simp [rootFluorineCursor, inwardCursor]
  · refine Or.inr (Or.inl ?_)
    apply LocalizedRerootCursor.ext admitted
    · apply Subtype.ext
      simpa [rootChlorineCursor] using h
    · simp [rootChlorineCursor, inwardCursor]
  · refine Or.inr (Or.inr ?_)
    apply LocalizedRerootCursor.ext admitted
    · apply Subtype.ext
      simpa [rootHydrogenCursor] using h
    · simp [rootHydrogenCursor, inwardCursor]

private theorem outward_exec_cover (child : admitted.LocalizedRerootCursor carrierFuel)
    (present : child ∈ admitted.executableLocalizedRerootChildren outwardCursor) :
    child = outFluorineCursor ∨ child = outChlorineCursor ∨ child = outHydrogenCursor := by
  unfold executableLocalizedRerootChildren at present
  obtain ⟨frame, _framePresent, rfl⟩ := List.mem_map.mp present
  rcases outward_frame_cover frame.1 frame.2 with h | h | h
  · refine Or.inl ?_
    apply LocalizedRerootCursor.ext admitted
    · apply Subtype.ext
      simpa [outFluorineCursor] using h
    · simp [outFluorineCursor, outwardCursor]
  · refine Or.inr (Or.inl ?_)
    apply LocalizedRerootCursor.ext admitted
    · apply Subtype.ext
      simpa [outChlorineCursor] using h
    · simp [outChlorineCursor, outwardCursor]
  · refine Or.inr (Or.inr ?_)
    apply LocalizedRerootCursor.ext admitted
    · apply Subtype.ext
      simpa [outHydrogenCursor] using h
    · simp [outHydrogenCursor, outwardCursor]

private theorem cursor_ne_of_address {a b : admitted.LocalizedRerootCursor carrierFuel}
    (h : a.occurrence.1.address ≠ b.occurrence.1.address) : a ≠ b :=
  fun eq => h (congrArg (fun cursor => cursor.occurrence.1.address) eq)

private theorem three_nodup {α : Type} {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    [a, b, c].Nodup := by
  simp [List.nodup_cons, hab, hac, hbc]

private theorem inward_exec_perm :
    (admitted.executableLocalizedRerootChildren inwardCursor).Perm
      [rootFluorineCursor, rootChlorineCursor, rootHydrogenCursor] := by
  have leftNodup := admitted.executableLocalizedRerootChildren_nodup inwardCursor
  have fCl : rootFluorineCursor ≠ rootChlorineCursor := cursor_ne_of_address (by
    simp [rootFluorineCursor, rootChlorineCursor, rootFluorineAddress, rootChlorineAddress])
  have fH : rootFluorineCursor ≠ rootHydrogenCursor := cursor_ne_of_address (by
    simp [rootFluorineCursor, rootHydrogenCursor, rootFluorineAddress, rootHydrogenAddress])
  have clH : rootChlorineCursor ≠ rootHydrogenCursor := cursor_ne_of_address (by
    simp [rootChlorineCursor, rootHydrogenCursor, rootChlorineAddress, rootHydrogenAddress])
  apply (List.perm_ext_iff_of_nodup leftNodup (three_nodup fCl fH clH)).mpr
  intro child
  constructor
  · intro present
    rcases inward_exec_cover child present with rfl | rfl | rfl <;> simp
  · intro present
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at present
    rcases present with rfl | rfl | rfl
    · exact mem_exec_of_frame rootFluorine_intended rfl
    · exact mem_exec_of_frame rootChlorine_intended rfl
    · exact mem_exec_of_frame rootHydrogen_intended rfl

private theorem outward_exec_perm :
    (admitted.executableLocalizedRerootChildren outwardCursor).Perm
      [outFluorineCursor, outChlorineCursor, outHydrogenCursor] := by
  have leftNodup := admitted.executableLocalizedRerootChildren_nodup outwardCursor
  have fCl : outFluorineCursor ≠ outChlorineCursor := cursor_ne_of_address (by
    simp [outFluorineCursor, outChlorineCursor, outFluorineAddress, outChlorineAddress])
  have fH : outFluorineCursor ≠ outHydrogenCursor := cursor_ne_of_address (by
    simp [outFluorineCursor, outHydrogenCursor, outFluorineAddress, outHydrogenAddress])
  have clH : outChlorineCursor ≠ outHydrogenCursor := cursor_ne_of_address (by
    simp [outChlorineCursor, outHydrogenCursor, outChlorineAddress, outHydrogenAddress])
  apply (List.perm_ext_iff_of_nodup leftNodup (three_nodup fCl fH clH)).mpr
  intro child
  constructor
  · intro present
    rcases outward_exec_cover child present with rfl | rfl | rfl <;> simp
  · intro present
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at present
    rcases present with rfl | rfl | rfl
    · exact mem_exec_of_frame outFluorine_intended rfl
    · exact mem_exec_of_frame outChlorine_intended rfl
    · exact mem_exec_of_frame outHydrogen_intended rfl

/-! ## Fuel-2 retained constitutional comparison -/

private abbrev retainedCmp
    (left right : admitted.LocalizedRerootCumulativeRule45Key) : Ordering :=
  admitted.compareRuleMajorCumulativeDescriptor (ruleMajorStageWidth .rule4a) left right

private theorem node_rule1a (node : OfficialCIPNode admitted.Atom) (z : Nat) (flag : Bool)
    (fact : (admitted.moleculeGraph.officialRuleMajorRootKey node flag).rule1a = [[([], z)]]) :
    (admitted.moleculeGraph.officialRuleMajorRootKey node flag).rule1a = [[([], z)]] :=
  fact

private theorem root_rule1a (flag : Bool) :
    (admitted.moleculeGraph.officialRuleMajorRootKey originalRoot flag).rule1a = [[([], 6)]] := by
  decide +kernel +revert

private theorem out_rule1a (flag : Bool) :
    (admitted.moleculeGraph.officialRuleMajorRootKey originalOut flag).rule1a = [[([], 6)]] := by
  decide +kernel +revert

private theorem rootFluorine_rule1a :
    (admitted.moleculeGraph.officialRuleMajorRootKey retainedRootFluorine true).rule1a =
      [[([], 9)]] := by
  decide +kernel

private theorem rootChlorine_rule1a :
    (admitted.moleculeGraph.officialRuleMajorRootKey retainedRootChlorine true).rule1a =
      [[([], 17)]] := by
  decide +kernel

private theorem rootHydrogen_rule1a :
    (admitted.moleculeGraph.officialRuleMajorRootKey retainedRootHydrogen true).rule1a =
      [[([], 1)]] := by
  decide +kernel

private theorem outFluorine_rule1a :
    (admitted.moleculeGraph.officialRuleMajorRootKey retainedOutFluorine true).rule1a =
      [[([], 9)]] := by
  decide +kernel

private theorem outChlorine_rule1a :
    (admitted.moleculeGraph.officialRuleMajorRootKey retainedOutChlorine true).rule1a =
      [[([], 17)]] := by
  decide +kernel

private theorem outHydrogen_rule1a :
    (admitted.moleculeGraph.officialRuleMajorRootKey retainedOutHydrogen true).rule1a =
      [[([], 1)]] := by
  decide +kernel

private theorem head_of_rule1a {key : OfficialRuleMajorKey admitted.Atom} {z : Nat}
    (fact : key.rule1a = [[([], z)]]) : key.rule1a.head? = some [([], z)] := by
  simp [fact]

private theorem constitutional_gt_of_heads (left right : OfficialRuleMajorKey admitted.Atom)
    {leftZ rightZ : Nat}
    (leftHead : left.rule1a.head? = some [([], leftZ)])
    (rightHead : right.rule1a.head? = some [([], rightZ)])
    (higher : rightZ < leftZ) :
    OfficialRuleMajorKey.compare left right = .gt := by
  have layers := MoleculeGraph.officialRuleMajorKey_compare_rule1a_gt_of_heads_gt
    leftHead rightHead higher
  simp [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey, layers]

private theorem cumulative_gt {left right : admitted.LocalizedRerootCumulativeRule45Key}
    (strict : OfficialRuleMajorKey.compare left.constitutional right.constitutional = .gt) :
    retainedCmp left right = .gt := by
  unfold retainedCmp compareRuleMajorCumulativeDescriptor
  simp [compareLex, Ordering.byKey, strict]

private theorem insertKeyBy_of_gt {α : Type} (cmp : α → α → Ordering) (key head : α)
    (tail : List α) (senior : cmp key head = .gt) :
    insertKeyBy cmp key (head :: tail) = key :: head :: tail := by
  unfold insertKeyBy
  rw [senior]

private theorem insertKeyBy_of_lt {α : Type} (cmp : α → α → Ordering) (key head : α)
    (tail : List α) (junior : cmp key head = .lt) :
    insertKeyBy cmp key (head :: tail) = head :: insertKeyBy cmp key tail := by
  conv_lhs => unfold insertKeyBy
  rw [junior]

private theorem sort_ranked
    (senior mid junior : admitted.LocalizedRerootCumulativeRule45Key)
    (seniorMid : retainedCmp senior mid = .gt)
    (seniorJunior : retainedCmp senior junior = .gt)
    (midJunior : retainedCmp mid junior = .gt)
    (keys : List admitted.LocalizedRerootCumulativeRule45Key)
    (form : keys = [mid, senior, junior] ∨ keys = [mid, junior, senior] ∨
      keys = [senior, mid, junior] ∨ keys = [senior, junior, mid] ∨
      keys = [junior, mid, senior] ∨ keys = [junior, senior, mid]) :
    admitted.sortRuleMajorCumulativeKeys .rule4a keys = [senior, mid, junior] := by
  haveI : Std.OrientedCmp retainedCmp :=
    admitted.compareRuleMajorCumulativeDescriptor_orientedCmp (ruleMajorStageWidth .rule4a)
  have midSenior : retainedCmp mid senior = .lt := by
    rw [← Std.OrientedCmp.gt_iff_lt]
    exact seniorMid
  have juniorSenior : retainedCmp junior senior = .lt := by
    rw [← Std.OrientedCmp.gt_iff_lt]
    exact seniorJunior
  have juniorMid : retainedCmp junior mid = .lt := by
    rw [← Std.OrientedCmp.gt_iff_lt]
    exact midJunior
  simp only [sortRuleMajorCumulativeKeys]
  change sortKeysBy retainedCmp keys = [senior, mid, junior]
  rcases form with rfl | rfl | rfl | rfl | rfl | rfl
  · have sortedJunior : sortKeysBy retainedCmp [junior] = [junior] := by
      rw [sortKeysBy, sortKeysBy, insertKeyBy]
    have sortedPair : sortKeysBy retainedCmp [senior, junior] = [senior, junior] := by
      rw [sortKeysBy, sortedJunior]
      exact insertKeyBy_of_gt retainedCmp senior junior [] seniorJunior
    rw [sortKeysBy, sortedPair, insertKeyBy_of_lt retainedCmp mid senior [junior] midSenior,
      insertKeyBy_of_gt retainedCmp mid junior [] midJunior]
  · have sortedSenior : sortKeysBy retainedCmp [senior] = [senior] := by
      rw [sortKeysBy, sortKeysBy, insertKeyBy]
    have sortedPair : sortKeysBy retainedCmp [junior, senior] = [senior, junior] := by
      rw [sortKeysBy, sortedSenior]
      exact insertKeyBy_of_lt retainedCmp junior senior [] juniorSenior
    rw [sortKeysBy, sortedPair, insertKeyBy_of_lt retainedCmp mid senior [junior] midSenior,
      insertKeyBy_of_gt retainedCmp mid junior [] midJunior]
  · have sortedJunior : sortKeysBy retainedCmp [junior] = [junior] := by
      rw [sortKeysBy, sortKeysBy, insertKeyBy]
    have sortedPair : sortKeysBy retainedCmp [mid, junior] = [mid, junior] := by
      rw [sortKeysBy, sortedJunior]
      exact insertKeyBy_of_gt retainedCmp mid junior [] midJunior
    rw [sortKeysBy, sortedPair, insertKeyBy_of_gt retainedCmp senior mid [junior] seniorMid]
  · have sortedMid : sortKeysBy retainedCmp [mid] = [mid] := by
      rw [sortKeysBy, sortKeysBy, insertKeyBy]
    have sortedPair : sortKeysBy retainedCmp [junior, mid] = [mid, junior] := by
      rw [sortKeysBy, sortedMid]
      exact insertKeyBy_of_lt retainedCmp junior mid [] juniorMid
    rw [sortKeysBy, sortedPair, insertKeyBy_of_gt retainedCmp senior mid [junior] seniorMid]
  · have sortedSenior : sortKeysBy retainedCmp [senior] = [senior] := by
      rw [sortKeysBy, sortKeysBy, insertKeyBy]
    have sortedPair : sortKeysBy retainedCmp [mid, senior] = [senior, mid] := by
      rw [sortKeysBy, sortedSenior]
      exact insertKeyBy_of_lt retainedCmp mid senior [] midSenior
    rw [sortKeysBy, sortedPair, insertKeyBy_of_lt retainedCmp junior senior [mid] juniorSenior,
      insertKeyBy_of_lt retainedCmp junior mid [] juniorMid, insertKeyBy]
  · have sortedMid : sortKeysBy retainedCmp [mid] = [mid] := by
      rw [sortKeysBy, sortKeysBy, insertKeyBy]
    have sortedPair : sortKeysBy retainedCmp [senior, mid] = [senior, mid] := by
      rw [sortKeysBy, sortedMid]
      exact insertKeyBy_of_gt retainedCmp senior mid [] seniorMid
    rw [sortKeysBy, sortedPair, insertKeyBy_of_lt retainedCmp junior senior [mid] juniorSenior,
      insertKeyBy_of_lt retainedCmp junior mid [] juniorMid, insertKeyBy]

private theorem perm_three_forms {α : Type} {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {keys : List α}
    (perm : keys.Perm [a, b, c]) :
    keys = [a, b, c] ∨ keys = [a, c, b] ∨ keys = [b, a, c] ∨ keys = [b, c, a] ∨
      keys = [c, a, b] ∨ keys = [c, b, a] := by
  have nodupKeys : keys.Nodup := (perm.nodup_iff).mpr (three_nodup hab hac hbc)
  have mem3 (x : α) (hx : x ∈ keys) : x = a ∨ x = b ∨ x = c := by
    have := (perm.mem_iff).mp hx
    simpa [List.mem_cons, List.mem_singleton] using this
  have hlen : keys.length = 3 := by simpa using perm.length_eq
  cases keys with
  | nil =>
      simp at hlen
  | cons x xs =>
      cases xs with
      | nil =>
          simp at hlen
      | cons y ys =>
          cases ys with
          | nil =>
              simp at hlen
          | cons z zs =>
              cases zs with
              | cons _ _ =>
                  simp [List.length_cons] at hlen
              | nil =>
                  have hx := mem3 x (by simp)
                  have hy := mem3 y (by simp)
                  have hz := mem3 z (by simp)
                  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
                    rcases hz with rfl | rfl | rfl <;>
                      first
                        | exact Or.inl rfl
                        | exact Or.inr (Or.inl rfl)
                        | exact Or.inr (Or.inr (Or.inl rfl))
                        | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
                        | simp [List.nodup_cons, List.mem_cons] at nodupKeys

private theorem mapM_three
    (c1 c2 c3 : admitted.LocalizedRerootCursor carrierFuel)
    (k1 k2 k3 : admitted.LocalizedRerootCumulativeRule45Key)
    (h1 : admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 c1 = some k1)
    (h2 : admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 c2 = some k2)
    (h3 : admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 c3 = some k3) :
    [c1, c2, c3].mapM (admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1) =
      some [k1, k2, k3] := by
  simp [List.mapM_cons, h1, h2, h3]

private theorem fuel2_of_children
    (cursor : admitted.LocalizedRerootCursor carrierFuel)
    (children : List (admitted.LocalizedRerootCursor carrierFuel))
    (childrenEq : admitted.executableLocalizedRerootChildren cursor = children)
    (nonempty : children ≠ [])
    (mappedKeys sortedKeys : List admitted.LocalizedRerootCumulativeRule45Key)
    (mapped : children.mapM
        (admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1) = some mappedKeys)
    (sortedEq : admitted.sortRuleMajorCumulativeKeys .rule4a mappedKeys = sortedKeys) :
    admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 2 cursor =
      some (localizedCumulativeRule45StepKey admitted .rule4a cursor none sortedKeys) := by
  unfold buildRuleMajorCumulativeWithRead?
  rw [admitted.localizedRerootChildren?_eq_some_executable, childrenEq]
  simp [Option.bind_some, if_neg nonempty, mapped, sortedEq, noneRead]

private theorem fuel2_sorted
    (cursor cMid cSenior cJunior : admitted.LocalizedRerootCursor carrierFuel)
    (tMid tSenior tJunior : admitted.LocalizedRerootCumulativeRule45Key)
    (hMid : admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 cMid = some tMid)
    (hSenior : admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 cSenior =
      some tSenior)
    (hJunior : admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 1 cJunior =
      some tJunior)
    (hab : cMid ≠ cSenior) (hac : cMid ≠ cJunior) (hbc : cSenior ≠ cJunior)
    (perm : (admitted.executableLocalizedRerootChildren cursor).Perm
      [cMid, cSenior, cJunior])
    (seniorMid : retainedCmp tSenior tMid = .gt)
    (seniorJunior : retainedCmp tSenior tJunior = .gt)
    (midJunior : retainedCmp tMid tJunior = .gt) :
    admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 2 cursor =
      some (localizedCumulativeRule45StepKey admitted .rule4a cursor none
        [tSenior, tMid, tJunior]) := by
  rcases perm_three_forms hab hac hbc perm with h | h | h | h | h | h
  · exact fuel2_of_children cursor _ h (by simp) _ _
      (mapM_three cMid cSenior cJunior tMid tSenior tJunior hMid hSenior hJunior)
      (sort_ranked tSenior tMid tJunior seniorMid seniorJunior midJunior _ (Or.inl rfl))
  · exact fuel2_of_children cursor _ h (by simp) _ _
      (mapM_three cMid cJunior cSenior tMid tJunior tSenior hMid hJunior hSenior)
      (sort_ranked tSenior tMid tJunior seniorMid seniorJunior midJunior _
        (Or.inr (Or.inl rfl)))
  · exact fuel2_of_children cursor _ h (by simp) _ _
      (mapM_three cSenior cMid cJunior tSenior tMid tJunior hSenior hMid hJunior)
      (sort_ranked tSenior tMid tJunior seniorMid seniorJunior midJunior _
        (Or.inr (Or.inr (Or.inl rfl))))
  · exact fuel2_of_children cursor _ h (by simp) _ _
      (mapM_three cSenior cJunior cMid tSenior tJunior tMid hSenior hJunior hMid)
      (sort_ranked tSenior tMid tJunior seniorMid seniorJunior midJunior _
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact fuel2_of_children cursor _ h (by simp) _ _
      (mapM_three cJunior cMid cSenior tJunior tMid tSenior hJunior hMid hSenior)
      (sort_ranked tSenior tMid tJunior seniorMid seniorJunior midJunior _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact fuel2_of_children cursor _ h (by simp) _ _
      (mapM_three cJunior cSenior cMid tJunior tSenior tMid hJunior hSenior hMid)
      (sort_ranked tSenior tMid tJunior seniorMid seniorJunior midJunior _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

private abbrev inwardFluorineKey : admitted.LocalizedRerootCumulativeRule45Key :=
  localizedCumulativeRule45TerminalKey admitted .rule4a rootFluorineCursor none

private abbrev inwardChlorineKey : admitted.LocalizedRerootCumulativeRule45Key :=
  localizedCumulativeRule45TerminalKey admitted .rule4a rootChlorineCursor none

private abbrev inwardHydrogenKey : admitted.LocalizedRerootCumulativeRule45Key :=
  localizedCumulativeRule45TerminalKey admitted .rule4a rootHydrogenCursor none

private abbrev outwardFluorineKey : admitted.LocalizedRerootCumulativeRule45Key :=
  localizedCumulativeRule45TerminalKey admitted .rule4a outFluorineCursor none

private abbrev outwardChlorineKey : admitted.LocalizedRerootCumulativeRule45Key :=
  localizedCumulativeRule45TerminalKey admitted .rule4a outChlorineCursor none

private abbrev outwardHydrogenKey : admitted.LocalizedRerootCumulativeRule45Key :=
  localizedCumulativeRule45TerminalKey admitted .rule4a outHydrogenCursor none

private theorem terminal_rule1a
    (cursor : admitted.LocalizedRerootCursor carrierFuel) (node : OfficialCIPNode admitted.Atom)
    (z : Nat)
    (nodeEq : cursor.occurrence.1.node = node)
    (fact : (admitted.moleculeGraph.officialRuleMajorRootKey node true).rule1a = [[([], z)]]) :
    (localizedCumulativeRule45TerminalKey admitted .rule4a cursor none).constitutional.rule1a =
      [[([], z)]] := by
  simpa [localizedCumulativeRule45TerminalKey, nodeEq] using fact

private theorem inward_chlorine_senior :
    retainedCmp inwardChlorineKey inwardFluorineKey = .gt ∧
      retainedCmp inwardChlorineKey inwardHydrogenKey = .gt ∧
      retainedCmp inwardFluorineKey inwardHydrogenKey = .gt := by
  have chlorine := terminal_rule1a rootChlorineCursor retainedRootChlorine 17
    (by simp [rootChlorineCursor, rootChlorineOccurrence, legitimateOccurrenceCarrier_node])
    rootChlorine_rule1a
  have fluorine := terminal_rule1a rootFluorineCursor retainedRootFluorine 9
    (by simp [rootFluorineCursor, rootFluorineOccurrence, legitimateOccurrenceCarrier_node])
    rootFluorine_rule1a
  have hydrogen := terminal_rule1a rootHydrogenCursor retainedRootHydrogen 1
    (by simp [rootHydrogenCursor, rootHydrogenOccurrence, legitimateOccurrenceCarrier_node])
    rootHydrogen_rule1a
  refine ⟨cumulative_gt ?_, cumulative_gt ?_, cumulative_gt ?_⟩
  · exact constitutional_gt_of_heads _ _ (head_of_rule1a chlorine) (head_of_rule1a fluorine)
      (by decide)
  · exact constitutional_gt_of_heads _ _ (head_of_rule1a chlorine) (head_of_rule1a hydrogen)
      (by decide)
  · exact constitutional_gt_of_heads _ _ (head_of_rule1a fluorine) (head_of_rule1a hydrogen)
      (by decide)

private theorem outward_chlorine_senior :
    retainedCmp outwardChlorineKey outwardFluorineKey = .gt ∧
      retainedCmp outwardChlorineKey outwardHydrogenKey = .gt ∧
      retainedCmp outwardFluorineKey outwardHydrogenKey = .gt := by
  have chlorine := terminal_rule1a outChlorineCursor retainedOutChlorine 17
    (by simp [outChlorineCursor, outChlorineOccurrence, legitimateOccurrenceCarrier_node])
    outChlorine_rule1a
  have fluorine := terminal_rule1a outFluorineCursor retainedOutFluorine 9
    (by simp [outFluorineCursor, outFluorineOccurrence, legitimateOccurrenceCarrier_node])
    outFluorine_rule1a
  have hydrogen := terminal_rule1a outHydrogenCursor retainedOutHydrogen 1
    (by simp [outHydrogenCursor, outHydrogenOccurrence, legitimateOccurrenceCarrier_node])
    outHydrogen_rule1a
  refine ⟨cumulative_gt ?_, cumulative_gt ?_, cumulative_gt ?_⟩
  · exact constitutional_gt_of_heads _ _ (head_of_rule1a chlorine) (head_of_rule1a fluorine)
      (by decide)
  · exact constitutional_gt_of_heads _ _ (head_of_rule1a chlorine) (head_of_rule1a hydrogen)
      (by decide)
  · exact constitutional_gt_of_heads _ _ (head_of_rule1a fluorine) (head_of_rule1a hydrogen)
      (by decide)

private theorem inward_fuel2 :
    admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 2 inwardCursor =
      some (localizedCumulativeRule45StepKey admitted .rule4a inwardCursor none
        [inwardChlorineKey, inwardFluorineKey, inwardHydrogenKey]) := by
  have fCl : rootFluorineCursor ≠ rootChlorineCursor := cursor_ne_of_address (by
    simp [rootFluorineCursor, rootChlorineCursor, rootFluorineAddress, rootChlorineAddress])
  have fH : rootFluorineCursor ≠ rootHydrogenCursor := cursor_ne_of_address (by
    simp [rootFluorineCursor, rootHydrogenCursor, rootFluorineAddress, rootHydrogenAddress])
  have clH : rootChlorineCursor ≠ rootHydrogenCursor := cursor_ne_of_address (by
    simp [rootChlorineCursor, rootHydrogenCursor, rootChlorineAddress, rootHydrogenAddress])
  exact fuel2_sorted inwardCursor rootFluorineCursor rootChlorineCursor rootHydrogenCursor
    inwardFluorineKey inwardChlorineKey inwardHydrogenKey rootFluorine_terminal
    rootChlorine_terminal rootHydrogen_terminal fCl fH clH inward_exec_perm
    inward_chlorine_senior.1 inward_chlorine_senior.2.1 inward_chlorine_senior.2.2

private theorem outward_fuel2 :
    admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 2 outwardCursor =
      some (localizedCumulativeRule45StepKey admitted .rule4a outwardCursor none
        [outwardChlorineKey, outwardFluorineKey, outwardHydrogenKey]) := by
  have fCl : outFluorineCursor ≠ outChlorineCursor := cursor_ne_of_address (by
    simp [outFluorineCursor, outChlorineCursor, outFluorineAddress, outChlorineAddress])
  have fH : outFluorineCursor ≠ outHydrogenCursor := cursor_ne_of_address (by
    simp [outFluorineCursor, outHydrogenCursor, outFluorineAddress, outHydrogenAddress])
  have clH : outChlorineCursor ≠ outHydrogenCursor := cursor_ne_of_address (by
    simp [outChlorineCursor, outHydrogenCursor, outChlorineAddress, outHydrogenAddress])
  exact fuel2_sorted outwardCursor outFluorineCursor outChlorineCursor outHydrogenCursor
    outwardFluorineKey outwardChlorineKey outwardHydrogenKey outFluorine_terminal
    outChlorine_terminal outHydrogen_terminal fCl fH clH outward_exec_perm
    outward_chlorine_senior.1 outward_chlorine_senior.2.1 outward_chlorine_senior.2.2

private theorem merge_monovalent {z0 z1 z2 : Nat}
    {k0 k1 k2 : OfficialRuleMajorKey admitted.Atom}
    (h0 : k0.rule1a = [[([], z0)]]) (h1 : k1.rule1a = [[([], z1)]])
    (h2 : k2.rule1a = [[([], z2)]]) :
    OfficialRuleMajorKey.mergeChildren [k0, k1, k2] OfficialRuleMajorKey.rule1a =
      [[([0], z0), ([1], z1), ([2], z2)]] := by
  have count : OfficialRuleMajorKey.childLayerCount [k0, k1, k2] OfficialRuleMajorKey.rule1a = 1 := by
    simp [OfficialRuleMajorKey.childLayerCount, h0, h1, h2]
  simp [OfficialRuleMajorKey.mergeChildren, OfficialRuleMajorKey.prefixLayer, count, h0, h1, h2,
    List.range_succ, List.range_zero, List.zipIdx_cons, List.getD]

private theorem inward_node :
    inwardCursor.occurrence.1.node = originalRoot := by
  simp [inwardCursor, rootOccurrence, legitimateOccurrenceCarrier_node]

private theorem outward_node :
    outwardCursor.occurrence.1.node = originalOut := by
  simp [outwardCursor, outOccurrence, legitimateOccurrenceCarrier_node]

private theorem inward_assembled_rule1a :
    (localizedCumulativeRule45StepKey admitted .rule4a inwardCursor none
      [inwardChlorineKey, inwardFluorineKey, inwardHydrogenKey]).constitutional.rule1a =
      [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]] := by
  have chlorine := terminal_rule1a rootChlorineCursor retainedRootChlorine 17
    (by simp [rootChlorineCursor, rootChlorineOccurrence, legitimateOccurrenceCarrier_node])
    rootChlorine_rule1a
  have fluorine := terminal_rule1a rootFluorineCursor retainedRootFluorine 9
    (by simp [rootFluorineCursor, rootFluorineOccurrence, legitimateOccurrenceCarrier_node])
    rootFluorine_rule1a
  have hydrogen := terminal_rule1a rootHydrogenCursor retainedRootHydrogen 1
    (by simp [rootHydrogenCursor, rootHydrogenOccurrence, legitimateOccurrenceCarrier_node])
    rootHydrogen_rule1a
  have merged := merge_monovalent chlorine fluorine hydrogen
  simp only [inwardChlorineKey, inwardFluorineKey, inwardHydrogenKey, List.map_cons, List.map_nil]
  rw [OfficialRuleMajorKey.assemble, inward_node, root_rule1a false, merged]
  rfl

private theorem outward_assembled_rule1a :
    (localizedCumulativeRule45StepKey admitted .rule4a outwardCursor none
      [outwardChlorineKey, outwardFluorineKey, outwardHydrogenKey]).constitutional.rule1a =
      [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]] := by
  have chlorine := terminal_rule1a outChlorineCursor retainedOutChlorine 17
    (by simp [outChlorineCursor, outChlorineOccurrence, legitimateOccurrenceCarrier_node])
    outChlorine_rule1a
  have fluorine := terminal_rule1a outFluorineCursor retainedOutFluorine 9
    (by simp [outFluorineCursor, outFluorineOccurrence, legitimateOccurrenceCarrier_node])
    outFluorine_rule1a
  have hydrogen := terminal_rule1a outHydrogenCursor retainedOutHydrogen 1
    (by simp [outHydrogenCursor, outHydrogenOccurrence, legitimateOccurrenceCarrier_node])
    outHydrogen_rule1a
  have merged := merge_monovalent chlorine fluorine hydrogen
  simp only [outwardChlorineKey, outwardFluorineKey, outwardHydrogenKey, List.map_cons,
    List.map_nil]
  rw [OfficialRuleMajorKey.assemble, outward_node, out_rule1a false, merged]
  rfl

private theorem step_rule1b
    (cursor : admitted.LocalizedRerootCursor carrierFuel) (node : OfficialCIPNode admitted.Atom)
    (distance : Nat) (sorted : List admitted.LocalizedRerootCumulativeRule45Key)
    (nodeEq : cursor.occurrence.1.node = node)
    (distanceEq : node.rule1bRootDistance = distance) :
    (localizedCumulativeRule45StepKey admitted .rule4a cursor none sorted).constitutional.rule1b =
      [[([], distance)]] ++ OfficialRuleMajorKey.mergeChildren
        (sorted.map fun child => child.constitutional) OfficialRuleMajorKey.rule1b := by
  simp [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKey, nodeEq,
    distanceEq]

private theorem inward_rule1b_split :
    (localizedCumulativeRule45StepKey admitted .rule4a inwardCursor none
      [inwardChlorineKey, inwardFluorineKey, inwardHydrogenKey]).constitutional.rule1b =
      [[([], 0)]] ++ OfficialRuleMajorKey.mergeChildren
        ([inwardChlorineKey, inwardFluorineKey, inwardHydrogenKey].map
          fun child => child.constitutional) OfficialRuleMajorKey.rule1b :=
  step_rule1b inwardCursor originalRoot 0 _ inward_node original_occurrence_depths.1

private theorem outward_rule1b_split :
    (localizedCumulativeRule45StepKey admitted .rule4a outwardCursor none
      [outwardChlorineKey, outwardFluorineKey, outwardHydrogenKey]).constitutional.rule1b =
      [[([], 2)]] ++ OfficialRuleMajorKey.mergeChildren
        ([outwardChlorineKey, outwardFluorineKey, outwardHydrogenKey].map
          fun child => child.constitutional) OfficialRuleMajorKey.rule1b :=
  step_rule1b outwardCursor originalOut 2 _ outward_node original_occurrence_depths.2.1

private theorem rule1b_prefix_gt (left right : List (List (OfficialSparseEntry Nat))) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
      ([[([], 0)]] ++ left) ([[([], 2)]] ++ right) = .gt := by
  have head : OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareRule1b
      [([], 0)] [([], 2)] = .gt := by
    decide +kernel
  rw [OfficialRuleMajorKey.compareSparseLayers, List.singleton_append, List.singleton_append]
  simp [List.compareLex, head]

private theorem concrete_rule1a_tie :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]]
      [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]] = .eq := by
  decide +kernel

private theorem compare_after_rule1a_tie {V : Type} (left right : OfficialRuleMajorKey V)
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a = .eq)
    (senior : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
      left.rule1b right.rule1b = .gt) :
    OfficialRuleMajorKey.compare left right = .gt := by
  simp [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey, tie, senior]

private theorem reference_rule1a_tie :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (localizedCumulativeRule45StepKey admitted .rule4a inwardCursor none
        [inwardChlorineKey, inwardFluorineKey, inwardHydrogenKey]).constitutional.rule1a
      (localizedCumulativeRule45StepKey admitted .rule4a outwardCursor none
        [outwardChlorineKey, outwardFluorineKey, outwardHydrogenKey]).constitutional.rule1a =
      .eq := by
  rw [inward_assembled_rule1a, outward_assembled_rule1a]
  exact concrete_rule1a_tie

private theorem reference_rule1b_gt :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
      (localizedCumulativeRule45StepKey admitted .rule4a inwardCursor none
        [inwardChlorineKey, inwardFluorineKey, inwardHydrogenKey]).constitutional.rule1b
      (localizedCumulativeRule45StepKey admitted .rule4a outwardCursor none
        [outwardChlorineKey, outwardFluorineKey, outwardHydrogenKey]).constitutional.rule1b =
      .gt := by
  rw [inward_rule1b_split, outward_rule1b_split]
  exact rule1b_prefix_gt _ _

private theorem reference_compare_gt :
    OfficialRuleMajorKey.compare
      (localizedCumulativeRule45StepKey admitted .rule4a inwardCursor none
        [inwardChlorineKey, inwardFluorineKey, inwardHydrogenKey]).constitutional
      (localizedCumulativeRule45StepKey admitted .rule4a outwardCursor none
        [outwardChlorineKey, outwardFluorineKey, outwardHydrogenKey]).constitutional = .gt :=
  compare_after_rule1a_tie _ _ reference_rule1a_tie reference_rule1b_gt

private theorem rule1b_take_one (distance : Nat)
    (rest : List (List (OfficialSparseEntry Nat))) :
    ([[([], distance)]] ++ rest).take 1 = [[([], distance)]] := by
  rw [List.singleton_append]
  simp [List.take_succ_cons]

private theorem aux_unit_atom :
    (admitted.molecularFrameUnit auxOccurrence.1).atom = auxA := by
  simp [CertifiedLocalizedCIPInput.molecularFrameUnit, OccurrenceUnit.atom, auxOccurrence,
    legitimateOccurrenceCarrier_root, legitimateOccurrenceCarrier_node, originalAux, originalRoot,
    OfficialCIPNode.extend, OfficialCIPNode.root]

private def auxDetected : DetectedOccurrence admitted.moleculeGraph :=
  ⟨admitted.molecularFrameUnit auxOccurrence.1, by
    rw [aux_unit_atom]
    exact four_ligand_centers.2.1⟩

private theorem inward_depth : inwardCursor.occurrence.1.node.depth = 0 := by
  simp [inwardCursor, rootOccurrence, legitimateOccurrenceCarrier_node, originalRoot,
    OfficialCIPNode.root, OfficialCIPNode.depth]

private theorem outward_depth : outwardCursor.occurrence.1.node.depth = 2 := by
  simp [outwardCursor, outOccurrence, legitimateOccurrenceCarrier_node, originalOut, originalAux,
    originalRoot, OfficialCIPNode.extend, OfficialCIPNode.root, OfficialCIPNode.depth]

private theorem inward_real :
    inwardCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  simp [inwardCursor, rootOccurrence, legitimateOccurrenceCarrier_node, originalRoot,
    OfficialCIPNode.root]

private theorem outward_real :
    outwardCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  simp [outwardCursor, outOccurrence, legitimateOccurrenceCarrier_node, originalOut, originalAux,
    originalRoot, OfficialCIPNode.extend, OfficialCIPNode.root, OfficialCIPNode.childProvenance]
  decide +kernel

private theorem arm_sphere {d : Nat} (cursor : admitted.LocalizedRerootCursor carrierFuel)
    (key : admitted.LocalizedRerootCumulativeRule45Key)
    (built : admitted.buildRuleMajorCumulativeWithRead? .rule4a noneRead 2 cursor = some key)
    (member : cursor ∈ admitted.executableLocalizedRerootChildren auxiliaryOpenCursor)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (depthEq : cursor.occurrence.1.node.depth = d) :
    ∃ tree : LocalizedCumulativeDecoratedTree admitted carrierFuel,
      tree.source = cursor ∧
        retainedContextRuleValue admitted.moleculeGraph (ruleMajorTreeGraph tree) auxDetected
          .rule1bDuplicateNodeProximity (ruleMajorTreeGraph tree).root = d := by
  obtain ⟨tree, sourceEq, trace⟩ := exists_ruleMajorTrace_of_buildWithRead admitted .rule4a
    noneRead 2 cursor key built
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have rootAddr : (ruleMajorTreeGraph tree).root.1 = [] := rfl
  have lookup := subtreeAt?_nil tree
  rw [← rootAddr] at lookup
  have realNode : tree.source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
    rw [sourceEq]
    exact real
  have value := retainedRealNode_eq_outerDigraphSphere admitted simple_bonded auxiliaryOpenCursor
    auxDetected rfl tree realizes (by simpa [sourceEq] using member) (ruleMajorTreeGraph tree).root
    tree lookup realNode
  refine ⟨tree, sourceEq, ?_⟩
  rw [value.1, sourceEq, depthEq]

theorem retained_reference_builds :
    ∃ inwardKey outwardKey : admitted.LocalizedRerootCumulativeRule45Key,
      admitted.buildRuleMajorCumulativeWithRead? .rule4a (fun _ => none) 2 inwardCursor =
          some inwardKey ∧
        admitted.buildRuleMajorCumulativeWithRead? .rule4a (fun _ => none) 2 outwardCursor =
          some outwardKey ∧
        inwardKey.constitutional.rule1a =
          [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]] ∧
        outwardKey.constitutional.rule1a =
          [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]] ∧
        inwardKey.constitutional.rule1b.take 1 = [[([], 0)]] ∧
        outwardKey.constitutional.rule1b.take 1 = [[([], 2)]] ∧
        OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          inwardKey.constitutional.rule1a outwardKey.constitutional.rule1a = .eq ∧
        OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
          inwardKey.constitutional.rule1b outwardKey.constitutional.rule1b = .gt ∧
        OfficialRuleMajorKey.compare inwardKey.constitutional outwardKey.constitutional = .gt := by
  refine ⟨_, _, inward_fuel2, outward_fuel2, inward_assembled_rule1a, outward_assembled_rule1a,
    ?_, ?_, reference_rule1a_tie, reference_rule1b_gt, reference_compare_gt⟩
  · rw [inward_rule1b_split]
    exact rule1b_take_one 0 _
  · rw [outward_rule1b_split]
    exact rule1b_take_one 2 _

theorem retained_constitutional_decision
    {fuelL fuelR : Nat} (stageL stageR : LocalizedCumulativeRule45Stage)
    (readL readR : admitted.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    {keyL keyR : admitted.LocalizedRerootCumulativeRule45Key}
    (builtL : admitted.buildRuleMajorCumulativeWithRead? stageL readL fuelL inwardCursor =
      some keyL)
    (builtR : admitted.buildRuleMajorCumulativeWithRead? stageR readR fuelR outwardCursor =
      some keyR) :
    keyL.constitutional.rule1a = keyR.constitutional.rule1a ∧
      keyL.constitutional.rule1b.take 1 = [[([], 0)]] ∧
      keyR.constitutional.rule1b.take 1 = [[([], 2)]] ∧
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        keyL.constitutional.rule1a keyR.constitutional.rule1a = .eq ∧
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        keyL.constitutional.rule1b keyR.constitutional.rule1b = .gt ∧
      OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional = .gt := by
  have inwardTables := ruleMajorBuild_constitutionalTables_eq stageL .rule4a readL
    (fun _ => none) inwardCursor builtL inward_fuel2
  have outwardTables := ruleMajorBuild_constitutionalTables_eq stageR .rule4a readR
    (fun _ => none) outwardCursor builtR outward_fuel2
  have compared := ruleMajorBuild_constitutional_compare_congr stageL stageR .rule4a .rule4a
    readL readR (fun _ => none) (fun _ => none) inwardCursor outwardCursor builtL builtR
    inward_fuel2 outward_fuel2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [inwardTables.1, outwardTables.1]
    exact inward_assembled_rule1a.trans outward_assembled_rule1a.symm
  · rw [inwardTables.2.1, inward_rule1b_split]
    exact rule1b_take_one 0 _
  · rw [outwardTables.2.1, outward_rule1b_split]
    exact rule1b_take_one 2 _
  · rw [inwardTables.1, outwardTables.1]
    exact reference_rule1a_tie
  · rw [inwardTables.2.1, outwardTables.2.1]
    exact reference_rule1b_gt
  · rw [compared]
    exact reference_compare_gt

theorem retained_arm_spheres :
    ∃ inTree outTree : LocalizedCumulativeDecoratedTree admitted carrierFuel,
      inTree.source = inwardCursor ∧
        outTree.source = outwardCursor ∧
        retainedContextRuleValue admitted.moleculeGraph (ruleMajorTreeGraph inTree) auxDetected
          .rule1bDuplicateNodeProximity (ruleMajorTreeGraph inTree).root = 0 ∧
        retainedContextRuleValue admitted.moleculeGraph (ruleMajorTreeGraph outTree) auxDetected
          .rule1bDuplicateNodeProximity (ruleMajorTreeGraph outTree).root = 2 := by
  obtain ⟨inTree, inSource, inValue⟩ := arm_sphere inwardCursor _ inward_fuel2
    retained_executable_cursors.1 inward_real inward_depth
  obtain ⟨outTree, outSource, outValue⟩ := arm_sphere outwardCursor _ outward_fuel2
    retained_executable_cursors.2.1 outward_real outward_depth
  exact ⟨inTree, outTree, inSource, outSource, inValue, outValue⟩

end TetraStereo.OneCenter.ActualRealRule1bNoninterference

assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.physical_domain
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.four_ligand_centers
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.auxiliary_neighbor_frame
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.root_neighbor_frame
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.outward_neighbor_frame
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.auxiliary_children
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.inward_branch_children
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.outward_branch_children
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.compared_nodes_are_real
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.inward_simple_occurrence
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.outward_simple_occurrence
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.original_outward_occurrence
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.auxiliary_sphere_depths
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.original_occurrence_depths
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.originalRootDepth_on_compared_nodes
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.auxiliary_sphere_and_constant_tie
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.original_root_depth_decides_after_rule1a_tie
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.cyclic_fixture_root_neighbors
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.abstract_key_witness_breaks_neutral_tie
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.simple_bonded
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.retained_executable_cursors
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.auxiliary_occurrence_four_ligand_frame
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.retained_reference_builds
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.retained_constitutional_decision
assert_kernel_only
  TetraStereo.OneCenter.ActualRealRule1bNoninterference.retained_arm_spheres
