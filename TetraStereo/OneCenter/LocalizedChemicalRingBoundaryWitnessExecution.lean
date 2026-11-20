import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch
import TetraStereo.OneCenter.LocalizedChemicalRingWitnessPhysicalExecution
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
Optional matched boundary-witness facts and one successful observation supply two actual
executions, under the original and pulled-back geometries. The step is a parameter with
its covariance law; the operations are the actual sparse retained operations. The query
keeps its original root, parent and entire prefixed history.

No successful execution, frame correspondence or reader equality is assumed. The optional
fact match is the output of the boundary witness readback theorem. A successful observation
is still necessary; this module makes no conclusion about absent labels or physical signs.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessExecution

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingWitnessExecution LocalizedChemicalRingWitnessPhysicalExecution
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingSemanticSymmetry (actual_covariant structuralSymmetry_of_aut)
open LocalizedChemicalRingCompletenessPermutationTransport (descriptorWith_map)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedOperationEvaluator (underWith)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedGenericMarkedRecalculation (Geometry)

/-- Actual child facts supplied to promotion, with empty initial state and a parameterized
one-occurrence step. The molecular comparison operations are unchanged. -/
def snapshotWith (step : Step) (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (source : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    OccurrenceAuxState :=
  underWith mol (sparseOperations input mol) geom [] source
    (factsWith step mol (sparseOperations input mol) depth) mark

theorem root_fixed_of_boundary {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (single : input.moleculeGraph.SimpleBonded) (target : input.LocalizedCIPOccurrence carrierFuel)
    (π : Equiv.Perm input.Atom)
    (fixed : ∀ atom ∈ target.1.node.history.reverse, π atom = atom) : π target.1.root = target.1.root := by
  have head : target.1.node.history.reverse.head? = some target.1.root := by
    rw [List.head?_reverse]
    exact input.carrierOccurrence_history_getLast_eq_root single target
  exact fixed target.1.root (List.mem_of_head? head)

/-- Boundary fixation transports the exact full raw node, including its incoming parent. -/
theorem boundary_node_map {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (single : input.moleculeGraph.SimpleBonded) (target : input.LocalizedCIPOccurrence carrierFuel)
    (π : Equiv.Perm input.Atom)
    (fixed : ∀ atom ∈ target.1.node.history.reverse, π atom = atom) (p : List input.Atom) :
    mapNode (relabelOf input π) (rawPathNode target.1.root (boundaryPath target p)) =
      rawPathNode target.1.root (boundaryPath target (p.map π)) := by
  rw [rawPathNode_map, root_fixed_of_boundary single target π fixed, boundaryPath_map target π fixed p]

/-- The execution budget counts the target prefix as well as the residual witness. -/
theorem remaining_eq {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (single : input.moleculeGraph.SimpleBonded) (target : input.LocalizedCIPOccurrence carrierFuel)
    (p : List input.Atom) (depth : Nat) (source : RawMolecule.CanonicalBranchNode) :
    depth + source.history.length - ((boundaryPath target p).length + 1) =
      depth + source.history.length - (target.1.node.history.length + p.length) := by
  rw [boundaryPath_length single target p]

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (e : input.detectedMultiCenterMolecule.Aut)

include agreement admissible supported single in
/-- The boundary theorem's optional fact match plus one observed generated label derives
both actual descriptor executions at the same exact remaining budget. The second successful
observation and reachability of both queries are conclusions of the generated-fact bridge. -/
theorem snapshot_boundary_matched_pullback (step : Step)
    (stepMap : StepMap step mol (sparseOperations input mol)
      (relabelOf input (e : Equiv.Perm input.Atom)))
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (reference : input.Atom)
    (fixedBoundary : ∀ atom ∈ target.1.node.history.reverse, (e : Equiv.Perm input.Atom) atom = atom)
    (fixedReference : (e : Equiv.Perm input.Atom) reference = reference)
    (p : List input.Atom) (depth : Nat) (geom : Geometry)
    (source : RawMolecule.CanonicalBranchNode) (sourceReached : Reached mol source)
    (matched : ((snapshotWith step input mol depth geom source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target p))).map factLabel =
      ((snapshotWith step input mol depth geom source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target (p.map (e : Equiv.Perm input.Atom))))).map factLabel)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((snapshotWith step input mol depth geom source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target p))).map factLabel = some label) :
    let remaining := depth + source.history.length - ((boundaryPath target p).length + 1)
    descriptorWith step mol (sparseOperations input mol) remaining geom [] (some reference.val)
        (rawPathNode target.1.root (boundaryPath target p)) = some label ∧
      descriptorWith step mol (sparseOperations input mol) remaining
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) geom) [] (some reference.val)
        (rawPathNode target.1.root (boundaryPath target p)) = some label := by
  have matchedFull : ((snapshotWith step input mol depth geom source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target p))).map factLabel =
      ((snapshotWith step input mol depth geom source reference.val).factAt?
        (rawPathNode target.1.root ((boundaryPath target p).map (e : Equiv.Perm input.Atom)))).map factLabel := by
    rw [boundaryPath_map target (e : Equiv.Perm input.Atom) fixedBoundary p]
    exact matched
  obtain ⟨original, image⟩ := matched_paths_execute target.1.root (boundaryPath target p)
    ((boundaryPath target p).map (e : Equiv.Perm input.Atom)) (by simp)
    step mol (sparseOperations input mol) depth geom [] source sourceReached reference.val
    matchedFull label observed
  refine ⟨original, ?_⟩
  have reached := snapshot_path_reached target.1.root (boundaryPath target p) step mol
    (sparseOperations input mol) depth geom [] source sourceReached reference.val label observed
  have fixedRoot := root_fixed_of_boundary single target (e : Equiv.Perm input.Atom) fixedBoundary
  have nodeMap : mapNode (relabelOf input (e : Equiv.Perm input.Atom))
      (rawPathNode target.1.root (boundaryPath target p)) =
      rawPathNode target.1.root ((boundaryPath target p).map (e : Equiv.Perm input.Atom)) := by
    simpa only [fixedRoot] using rawPathNode_map input (e : Equiv.Perm input.Atom)
      target.1.root (boundaryPath target p)
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e
  have cov := actual_covariant input mol agreement admissible supported single e
  have rawSingle := raw_single mol input agreement admissible.1.1 admissible.1.2 supported single
  have transport := descriptorWith_map sym admissible.1.1 admissible.1.2 rawSingle cov step stepMap
    (depth + source.history.length - ((boundaryPath target p).length + 1)) geom (some reference.val)
    (rawPathNode target.1.root (boundaryPath target p)) reached
  simp only [Option.map_some, relabelOf_val, fixedReference, nodeMap] at transport
  exact transport.symm.trans image

end TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessExecution.snapshotWith
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessExecution.root_fixed_of_boundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessExecution.boundary_node_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessExecution.remaining_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessExecution.snapshot_boundary_matched_pullback
