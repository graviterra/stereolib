import TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Relabeling of the actual prepared joint evaluator

The operations contract is discharged by the actual joint comparator. These endpoints therefore
have no callback-covariance or generated-state-agreement premise. They cover all accumulated
reference lists and every recursion depth, including refusal. The source geometry is the
pullback of the image geometry; physical invariance under calibrated proper symmetries is a
separate obligation. This module does not change the production evaluator.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransportExecution

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingJointMarkerOperations
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingJointPreparedCovariance
open LocalizedChemicalRingJointOperationTransport
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms?)

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
  (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))

include agreement admissible supported single sym

/-- Generated facts, at the actual empty incoming state, transport without a supplied-label
or supplied-covariance hypothesis. -/
theorem actual_preparedFacts_map (depth : Nat) (geom : Geometry) (M : List Nat)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node) :
    StateRel (relabelOf input (e : Equiv.Perm input.Atom))
      (preparedFacts mol (jointOperations input mol) depth geom []
        (M.map (relabelOf input (e : Equiv.Perm input.Atom)))
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node))
      (preparedFacts mol (jointOperations input mol) depth
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) geom) [] M node) :=
  preparedFacts_map_empty (jointOperations input mol) sym admissible.1.1 admissible.1.2
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    (jointOperations_preparedCovariant input mol agreement admissible supported single e sym)
    depth geom M node reached

/-- All canonical children are generated and transported at the same accumulated context. -/
theorem actual_preparedChildren_map (depth : Nat) (geom : Geometry) (M : List Nat)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node) :
    StateRel (relabelOf input (e : Equiv.Perm input.Atom))
      (childrenUnder mol (preparedFacts mol (jointOperations input mol) depth) geom []
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node)
        (M.map (relabelOf input (e : Equiv.Perm input.Atom))))
      (childrenUnder mol (preparedFacts mol (jointOperations input mol) depth)
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) geom) [] node M) :=
  preparedChildrenUnder_map (jointOperations input mol) sym admissible.1.1 admissible.1.2
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    (jointOperations_preparedCovariant input mol agreement admissible supported single e sym)
    depth geom M node reached

/-- Actual descriptor transport keeps the two mirror computations separate and derives their
auxiliary states; success is not assumed. -/
theorem actual_preparedDescriptor_map (depth : Nat) (geom : Geometry) (M : List Nat)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node) :
    preparedDescriptor? mol (jointOperations input mol) depth geom []
        (M.map (relabelOf input (e : Equiv.Perm input.Atom)))
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
      preparedDescriptor? mol (jointOperations input mol) depth
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) geom) [] M node :=
  preparedDescriptor_map_empty (jointOperations input mol) sym admissible.1.1 admissible.1.2
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    (jointOperations_preparedCovariant input mol agreement admissible supported single e sym)
    depth geom M node reached

/-- Each actual fallback uses its own generated extended-context state. The required state
permutation is derived from the recursive evaluator, rather than supplied by the caller. -/
theorem actual_evaluateFallback_map (depth : Nat) (geom : Geometry) (M : List Nat)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms atoms' : List Nat) (frame : frameAtoms? mol node = some atoms)
    (frame' : frameAtoms? mol
      (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) = some atoms') (mark : Nat) :
    evaluateFallback? mol (jointOperations input mol) geom []
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node)
        (M.map (relabelOf input (e : Equiv.Perm input.Atom)))
        (childrenUnder mol (preparedFacts mol (jointOperations input mol) depth) geom []
          (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node))
        (relabelOf input (e : Equiv.Perm input.Atom) mark) =
      evaluateFallback? mol (jointOperations input mol)
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) geom) [] node M
        (childrenUnder mol (preparedFacts mol (jointOperations input mol) depth)
          (pullback (relabelOf input (e : Equiv.Perm input.Atom)) geom) [] node) mark :=
  evaluateFallback?_map (jointOperations input mol) sym
    (jointOperations_preparedCovariant input mol agreement admissible supported single e sym)
    node reached atoms atoms' frame frame' M [] [] (List.Perm.refl _) List.nodup_nil _ _
    (fun L => actual_preparedChildren_map input mol agreement admissible supported single e sym
      depth geom L node reached) mark geom

/-- Center assignment at its structural depth transports under atom relabeling, using the
actual operations and generated states. -/
theorem actual_preparedAssignCenter_map (geom : Geometry) (center : Nat)
    (valid : center < mol.atomCount) :
    preparedAssignCenter? mol (jointOperations input mol) geom
        (relabelOf input (e : Equiv.Perm input.Atom) center) =
      preparedAssignCenter? mol (jointOperations input mol)
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) geom) center :=
  preparedAssignCenter?_map (jointOperations input mol) sym admissible.1.1 admissible.1.2
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    (jointOperations_preparedCovariant input mol agreement admissible supported single e sym)
    geom center valid

end TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransportExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransportExecution.actual_preparedFacts_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransportExecution.actual_preparedChildren_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransportExecution.actual_preparedDescriptor_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransportExecution.actual_evaluateFallback_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransportExecution.actual_preparedAssignCenter_map
