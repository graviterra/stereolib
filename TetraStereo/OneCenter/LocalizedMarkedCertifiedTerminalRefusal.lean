import TetraStereo.OneCenter.LocalizedMarkedTerminalOutward
import TetraStereo.OneCenter.LocalizedPhysicalCalibratedRootReader

set_option autoImplicit false

/-!
# Certified physical terminal twins refuse in inherited promotion contexts

The independent physical terminal-twin predicate supplies the molecular leaves and their
labels. Source-intake agreement transports these to the raw evaluator. The actual occurrence
paths then construct real outward cursors, so no such cursor witnesses or comparison properties
remain in the final theorem. Actual root/source/target frame equations and the selected carried
reference identify the invocation; local-reference fallback remains a separate case.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal

open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedTerminalReferenceScope LocalizedMarkedUncappedOperations
open LocalizedMarkedTerminalOutward LocalizedMarkedTerminalCarriedRefusal
open AuthoritativeCIPMoleculeCursorRanking
open LocalizedMarkedUncappedEvaluator (operations)
open LocalizedMarkedOperationEvaluator (descriptor?)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms?)
open CertifiedLocalizedCIPInput

abbrev Node := RawMolecule.CanonicalBranchNode

theorem raw_atom_bound (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input) (atom : input.Atom) :
    atom.val < mol.atomCount := by
  have count := mol.toSemanticMolecule?_atomCount input.certified.input.molecule agreement.1
  rw [← count]
  exact atom.isLt

theorem raw_atom_data (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input) (atom : input.Atom) :
    input.moleculeGraph.atomZ atom = mol.atomZAt atom.val ∧
      input.moleculeGraph.atomMass atom = mol.atomMassAt atom.val := by
  let index : Fin mol.atomCount := ⟨atom.val, raw_atom_bound mol input agreement atom⟩
  have indexEq : localizedIndexOf mol input agreement index = atom := Fin.ext rfl
  have data := intakeAtomDataCorresponds mol input agreement index
  rw [indexEq] at data
  have lookup : mol.atomAt? index.val =
      some (mol.atoms.get ⟨index.val, index.isLt⟩) := by
    simpa [RawMolecule.atomAt?] using
      listGet?_eq_some_get mol.atoms ⟨index.val, index.isLt⟩
  constructor
  · change input.moleculeGraph.atomZ atom = mol.atomZAt index.val
    rw [RawMolecule.atomZAt, lookup]
    exact data.1
  · exact data.2

theorem raw_single (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded) : SingleBonded mol := by
  intro a b
  by_cases zero : mol.bondOrder a b = 0
  · simp [zero]
  · have positive := Nat.pos_of_ne_zero zero
    have bounds := mol.bondOrder_pos_endpoint_lt wellFormed positive
    let left := localizedIndexOf mol input agreement ⟨a, bounds.1⟩
    let right := localizedIndexOf mol input agreement ⟨b, bounds.2⟩
    have bond := moleculeGraph_bond_eq_rawBondOrder mol input agreement wellFormed unique supported
      left right
    have adj : input.moleculeGraph.Adj left right := by
      change 0 < input.moleculeGraph.bond left right
      rw [bond]
      exact positive
    have one := single left right adj
    rw [bond] at one
    exact Nat.le_of_eq one

theorem raw_terminal (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (center leaf : input.Atom)
    (neighbors : input.moleculeGraph.neighborFinset leaf = {center}) :
    TerminalNeighbor mol center.val leaf.val := by
  have centerMem : center ∈ input.moleculeGraph.neighborFinset leaf := by simp [neighbors]
  have adjacent := (MoleculeGraph.mem_neighborFinset input.moleculeGraph leaf center).mp centerMem
  have bond := moleculeGraph_bond_eq_rawBondOrder mol input agreement wellFormed unique supported
    leaf center
  refine ⟨?_, ?_⟩
  · change 0 < input.moleculeGraph.bond leaf center at adjacent
    rw [bond, RawMolecule.bondOrder_symm] at adjacent
    exact adjacent
  · intro other positive
    have valid := (mol.bondOrder_pos_endpoint_lt wellFormed positive).2
    let target := localizedIndexOf mol input agreement ⟨other, valid⟩
    have otherBond := moleculeGraph_bond_eq_rawBondOrder mol input agreement wellFormed unique
      supported leaf target
    have adj : input.moleculeGraph.Adj leaf target := by
      change 0 < input.moleculeGraph.bond leaf target
      rw [otherBond]
      exact positive
    have member := (MoleculeGraph.mem_neighborFinset input.moleculeGraph leaf target).mpr adj
    rw [neighbors] at member
    exact congrArg Fin.val (Finset.mem_singleton.mp member)

/-- Physical terminality excludes the root atom whenever the actual root has a frame. -/
theorem root_ne_terminal_of_frame (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (root : Nat) (valid : root < mol.atomCount) (atoms : List Nat)
    (frame : frameAtoms? mol (canonicalCenterRoot root) = some atoms)
    (center leaf : Nat) (terminal : TerminalNeighbor mol center leaf) : root ≠ leaf := by
  intro equal
  have absent := terminal_no_frame mol wellFormed single unique (canonicalCenterRoot root)
    (reached_root mol root valid) center (by simpa [canonicalCenterRoot, equal] using terminal)
  rw [frame] at absent
  contradiction

/-- The certified physical terminal-twin predicate now suffices at the descendant center:
all real outward occurrence, depth, reader-silence and comparator-refusal facts are derived.
The carried reference must be accepted by the target frame; its local fallback is not covered. -/
theorem physical_terminal_carried_descriptor_none (mol : RawMolecule)
    (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (root center : input.detectedMultiCenterMolecule.Center)
    (twin : ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule center)
    (rootAtoms : List Nat) (rootFrame : frameAtoms? mol (canonicalCenterRoot root.1.val) = some rootAtoms)
    (source target : Node) (sourcePath : ReachedFrom mol root.1.val source)
    (path : StrictDescendant mol source target) (current : target.atom = center.1.val)
    (sourceAtoms : List Nat) (sourceFrame : frameAtoms? mol source = some sourceAtoms)
    (targetAtoms : List Nat) (targetFrame : frameAtoms? mol target = some targetAtoms)
    (mark : Nat) (sourceSelected : mark ∈ sourceAtoms) (targetSelected : mark ∈ targetAtoms)
    (depth : Nat) (geom : Geometry) :
    descriptor? mol (operations mol) depth geom [] (some mark) target = none := by
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have rootValid := raw_atom_bound mol input agreement root.1
  have sourceReached : Reached mol source := ⟨root.1.val, rootValid, sourcePath⟩
  have targetPath : ReachedFrom mol root.1.val target := by
    obtain ⟨child, edge, rest⟩ := path
    exact (sourcePath.tail edge).trans rest
  have generated := generated_of_reachedFrom mol root.1.val target targetPath
  have real : target.provenance = .realAtom := by
    have notLeaf : target.forcedLeaf = false := by
      cases leaf : target.forcedLeaf with
      | false => rfl
      | true => rw [LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol target leaf]
          at targetFrame; contradiction
    cases provenance : target.provenance <;>
      simp [RawMolecule.CanonicalBranchNode.forcedLeaf, provenance] at notLeaf
    rfl
  obtain ⟨a, b, twins⟩ := twin
  have terminalA : TerminalNeighbor mol target.atom a.val := by
    rw [current]
    exact raw_terminal mol input agreement wellFormed unique supported center.1 a twins.neighbor_a
  have terminalB : TerminalNeighbor mol target.atom b.val := by
    rw [current]
    exact raw_terminal mol input agreement wellFormed unique supported center.1 b twins.neighbor_b
  have rootNeA := root_ne_terminal_of_frame mol wellFormed rawSingle unique root.1.val rootValid
    rootAtoms rootFrame target.atom a.val terminalA
  have rootNeB := root_ne_terminal_of_frame mol wellFormed rawSingle unique root.1.val rootValid
    rootAtoms rootFrame target.atom b.val terminalB
  obtain ⟨left, leftSlot, leftChild, leftAtom, leftReal, _⟩ := exists_outward_terminal_cursor
    mol wellFormed rawSingle unique root.1.val target generated real a.val terminalA rootNeA
  obtain ⟨right, rightSlot, rightChild, rightAtom, rightReal, _⟩ := exists_outward_terminal_cursor
    mol wellFormed rawSingle unique root.1.val target generated real b.val terminalB rootNeB
  have distinct : left ≠ right := by
    intro equal
    have values : a.val = b.val := leftAtom.symm.trans ((congrArg (fun c => c.node.atom) equal).trans rightAtom)
    exact twins.ne (Fin.ext values)
  have aData := raw_atom_data mol input agreement a
  have bData := raw_atom_data mol input agreement b
  apply carried_outward_descriptor_none mol wellFormed rawSingle unique depth geom source target
    sourceReached path sourceAtoms sourceFrame mark sourceSelected targetAtoms targetFrame
    targetSelected left right leftSlot rightSlot distinct leftChild rightChild
    (by simpa [leftAtom] using terminalA) (by simpa [rightAtom] using terminalB) leftReal rightReal
  · rw [leftAtom, rightAtom, ← aData.1, ← bData.1]
    exact twins.z_eq
  · rw [leftAtom, rightAtom, ← aData.2, ← bData.2]
    exact twins.mass_eq

end TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal.raw_atom_bound
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal.raw_atom_data
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal.raw_single
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal.raw_terminal
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal.root_ne_terminal_of_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal.physical_terminal_carried_descriptor_none
