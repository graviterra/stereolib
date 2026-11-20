import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport
import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Executable sparse expansion of the prepared joint-context evaluator. The operations are defined
outside classical/noncomputable sections, and joint columns never materialize dense zero padding.
Its report is proved equal to the report used by
the independent source-model theorem, including refusals and every detected candidate.
This is the explicit accumulated-reference development policy, not a default-policy change. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedOrdinaryRanking (rawStateBefore sortBy? adjacentBy)
open LocalizedMarkedRetainedOperations (positions? ordinary)
open LocalizedMarkedRetainedStateReader (rawStateView)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedPromotedOperations (adjacentPromotionCount?)
open LocalizedMarkedCarrierLookup (lookup?)
open LocalizedGenericMarkedRecalculation (frameAtoms? strict)
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations)
open LocalizedChemicalRingPreparedContextRecursion (preparedAssignCenter?)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

variable (input : CertifiedLocalizedCIPInput)

def compareAt? {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor carrierFuel) : Option Ordering :=
  LocalizedChemicalRingJointMarkerSparse.sparseCompareAt? input target view references W D left right

theorem compareAt?_eq {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor carrierFuel) :
    compareAt? input target view references W D left right =
      LocalizedChemicalRingJointMarkerKey.compareJointAt? input target view references W D left right :=
  LocalizedChemicalRingJointMarkerSparse.sparseCompareAt?_eq input target view references W D left right

def before (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (references : List input.Atom) (W D : Nat) (left right : Fin 4) : Option Ordering :=
  (rawStateBefore input state target frame left right).bind fun prior =>
    if prior = Ordering.eq then
      compareAt? input target (rawStateView input state target) references W D
        (frame.cursorAt left) (frame.cursorAt right)
    else some prior

theorem before_eq (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (references : List input.Atom) (W D : Nat) :
    before input state target frame references W D =
      LocalizedChemicalRingJointMarkerOperations.jointBefore input state target frame references W D := by
  funext left right
  simp only [before, LocalizedChemicalRingJointMarkerOperations.jointBefore, compareAt?_eq]

def partition? (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (references : List input.Atom) (W D : Nat) :
    Option (List Nat × List (Option Ordering) × Nat) := do
  let target ← lookup? input node
  let atoms ← frameAtoms? mol node
  let frame ← input.localizedNoDoubleFourLigandFrameExec? target
  let sorted ← sortBy? (before input state target frame references W D) (List.finRange 4)
  let count ← adjacentPromotionCount? (rawStateBefore input state target frame)
    (before input state target frame references W D) sorted
  let positions ← positions? input atoms frame sorted
  some (positions, adjacentBy (before input state target frame references W D) sorted, count)

theorem partition?_eq (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (references : List input.Atom) (W D : Nat) :
    partition? input mol state node references W D =
      LocalizedChemicalRingJointMarkerOperations.jointPartition? input mol state node references W D := by
  simp only [partition?, before_eq, LocalizedChemicalRingJointMarkerOperations.jointPartition?,
    LocalizedChemicalRingJointMarkerOperations.jointFrame?,
    LocalizedChemicalRingJointMarkerOperations.partitionBy?]
  simp only [Option.bind_eq_bind, Option.bind_assoc, Option.bind_some]

def references? (M : List Nat) : Option (List input.Atom) :=
  M.mapM fun mark =>
    if bound : mark < input.certified.input.molecule.atomCount then some ⟨mark, bound⟩ else none

def contextOrder? (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (M : List Nat) :
    Option (List Nat × List (Option Ordering)) := do
  let references ← references? input M
  let (positions, adjacent, _) ← partition? input mol state node references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
  some (positions, adjacent)

def markedJoint? (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (L : List Nat) (_mark : Nat) :
    Option Rule6TrackedRanking := do
  let references ← references? input L
  let (positions, adjacent, count) ← partition? input mol state node references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
  some { positions := positions, unique := strict adjacent, pseudoComparisons := count }

def operations (mol : RawMolecule) : MultiOperations where
  ordinary := ordinary input mol
  contextOrder := contextOrder? input mol
  markedJoint := markedJoint? input mol

theorem operations_eq (mol : RawMolecule) : operations input mol =
    LocalizedChemicalRingJointMarkerOperations.jointOperations input mol := by
  have context : contextOrder? input mol =
      LocalizedChemicalRingJointMarkerOperations.contextOrder? input mol := by
    funext state node M
    simp only [contextOrder?, LocalizedChemicalRingJointMarkerOperations.contextOrder?, partition?_eq]
    rfl
  have marked : markedJoint? input mol =
      LocalizedChemicalRingJointMarkerOperations.markedJoint? input mol := by
    funext state node L mark
    simp only [markedJoint?, LocalizedChemicalRingJointMarkerOperations.markedJoint?, partition?_eq]
    rfl
  unfold operations LocalizedChemicalRingJointMarkerOperations.jointOperations
  rw [context, marked]

def analyze (mol : RawMolecule) : LocalizedChemicalRingJointPreparedReport.Report :=
  input.canonicalTetrahedralCenters.map fun center =>
    (center.1.val, preparedAssignCenter? mol (operations input mol) (inputGeometry input) center.1.val)

theorem analyze_eq (mol : RawMolecule) : analyze input mol =
    LocalizedChemicalRingJointPreparedReport.analyze input mol := by
  simp only [analyze, LocalizedChemicalRingJointPreparedReport.analyze, operations_eq]

end TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.compareAt?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.compareAt?_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.before
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.before_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.partition?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.partition?_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.references?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.contextOrder?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.markedJoint?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.operations
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.operations_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.analyze
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable.analyze_eq
