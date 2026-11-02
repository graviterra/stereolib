import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section
open scoped Classical
open RootedDigraph

universe u

/-- At a rooted graph's root, the atom-bearing ancestor path contains the root atom itself. -/
theorem ancestorAtoms_root_of_realAtomLabel {Atom : Type u}
    (graph : RootedDigraph Atom) (leaf : Atom)
    (rootLabel : graph.label graph.root = ⟨some leaf, .realAtom⟩) :
    ancestorAtoms graph graph.root = some [leaf] := by
  have hpath : AncestorPath graph graph.root [some leaf] := by
    simpa [rootLabel] using (AncestorPath.root (graph := graph))
  have hrootNoParent : ∀ parent, ¬ graph.child parent graph.root := by
    intro parent hedge
    have hdepth := graph.child_depth hedge
    rw [graph.root_depth] at hdepth
    omega
  have hunique : ∀ other, AncestorPath graph graph.root other → other = [some leaf] := by
    intro other hother
    cases hother with
    | root => simp [rootLabel]
    | @step parent node path hedge _ => exact (hrootNoParent parent hedge).elim
  unfold ancestorAtoms
  rw [ancestorPath_eq_some hpath hunique]
  rfl

/-- A single root step either walks back to the ranked occurrence's parent (and is not strictly
deeper), or ends at the degree-one atom itself (which is outside the detected tetrahedral
inventory). -/
theorem contextOccurrence_rootLeaf_eq_none {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (unit : DetectedOccurrence molecule) (leaf : Atom)
    (degree : (molecule.neighborFinset leaf).card ≤ 1) :
    contextOccurrence molecule unit [leaf] = none := by
  by_cases hback : incomingAtom? unit.1.root unit.1.path = some leaf
  · simp [contextOccurrence, rerootWalk, rerootStep, hback]
  · have hnotDetected : ¬ IsDetectedCenter molecule leaf := by
      unfold IsDetectedCenter
      omega
    simp [contextOccurrence, rerootWalk, rerootStep, hback, hnotDetected,
      OccurrenceUnit.atom]

/-- Any real leaf at the root of a ligand graph is read as outside the molecular tetrahedral
inventory, for every ranked occurrence and every descriptor map.  No premise is made about the
descriptor map's value at the leaf. -/
theorem occurrenceReading_root_outsideInventory_of_leaf
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom) (leaf : Atom)
    (rootLabel : graph.label graph.root = ⟨some leaf, .realAtom⟩)
    (degree : (molecule.neighborFinset leaf).card ≤ 1) :
    occurrenceReading molecule descriptorMap unit graph graph.root = .outsideInventory := by
  have hreal : (graph.label graph.root).provenance = .realAtom := by
    simp [rootLabel]
  have hsteps : ancestorAtoms graph graph.root = some [leaf] :=
    ancestorAtoms_root_of_realAtomLabel graph leaf rootLabel
  rw [occurrenceReading_eq_readContext molecule descriptorMap unit graph hreal hsteps]
  rw [readContext, contextOccurrence_rootLeaf_eq_none molecule unit leaf degree]

/-- Under the molecular single-bond hypothesis, no node label can carry Rule-3 multiple-bond
evidence. -/
theorem noMultipleBond_of_simpleBonded {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (simpleBonded : molecule.SimpleBonded) (label : NodeLabel Atom) :
    ¬ HasMultipleBond molecule label := by
  rintro ⟨atom, other, _, hbond⟩
  have hadj : molecule.Adj atom other := by
    unfold MoleculeGraph.Adj
    exact lt_of_lt_of_le (by decide : 0 < 2) hbond
  have hsingle := simpleBonded atom other hadj
  rw [hsingle] at hbond
  exact Nat.not_succ_le_self 1 hbond

end

end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ancestorAtoms_root_of_realAtomLabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextOccurrence_rootLeaf_eq_none
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.occurrenceReading_root_outsideInventory_of_leaf
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.noMultipleBond_of_simpleBonded
