import TetraStereo.OneCenter.LocalizedChemicalRingJointExecutable
import TetraStereo.OneCenter.LocalizedChemicalRingJointCachedSparse
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Share one materialized carrier across the complete public joint-context report. Each center
captures an exact selected-root reader; ordinary, joint-reference and frame expansions all use
that reader. Every context and geometry still generates its own auxiliary facts. The exact
operations/report equalities include every refusal and impose no molecular or output premises. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedOrdinaryRanking (sortBy? adjacentBy)
open LocalizedMarkedRetainedOperations (positions?)
open LocalizedMarkedRetainedStateReader (rawStateView)
open LocalizedMarkedRetainedPromotedOperations (adjacentPromotionCount?)
open LocalizedMarkedCarrierLookup (lookup?)
open LocalizedGenericMarkedRecalculation (frameAtoms? strict)
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations)
open LocalizedChemicalRingPreparedContextRecursion (preparedAssignCenter?)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

variable (input : CertifiedLocalizedCIPInput)
  (cache : input.LocalizedRerootChildReader (retainedCarrierFuel input))

def before (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (references : List input.Atom) (W D : Nat) (left right : Fin 4) : Option Ordering :=
  (LocalizedChemicalRingCachedOperations.before input cache state target frame left right).bind fun prior =>
    if prior = Ordering.eq then
      LocalizedChemicalRingJointCachedSparse.compareAt? input cache target
        (rawStateView input state target) references W D (frame.cursorAt left) (frame.cursorAt right)
    else some prior

theorem before_eq (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (references : List input.Atom) (W D : Nat) :
    before input cache state target frame references W D =
      LocalizedChemicalRingJointExecutable.before input state target frame references W D := by
  funext left right
  simp only [before, LocalizedChemicalRingJointExecutable.before,
    LocalizedChemicalRingCachedOperations.before_eq,
    LocalizedChemicalRingJointCachedSparse.compareAt?_eq,
    LocalizedChemicalRingJointExecutable.compareAt?]

def partition? (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (references : List input.Atom) (W D : Nat) :
    Option (List Nat × List (Option Ordering) × Nat) := do
  let target ← lookup? input node
  let atoms ← frameAtoms? mol node
  let frame ← LocalizedChemicalRingCachedOperations.frame input cache target
  let sorted ← sortBy? (before input cache state target frame references W D) (List.finRange 4)
  let count ← adjacentPromotionCount?
    (LocalizedChemicalRingCachedOperations.before input cache state target frame)
    (before input cache state target frame references W D) sorted
  let positions ← positions? input atoms frame sorted
  some (positions, adjacentBy (before input cache state target frame references W D) sorted, count)

theorem partition?_eq (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (references : List input.Atom) (W D : Nat) :
    partition? input cache mol state node references W D =
      LocalizedChemicalRingJointExecutable.partition? input mol state node references W D := by
  simp only [partition?, LocalizedChemicalRingJointExecutable.partition?, before_eq,
    LocalizedChemicalRingCachedOperations.frame_eq, LocalizedChemicalRingCachedOperations.before_eq]

def contextOrder? (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (M : List Nat) :
    Option (List Nat × List (Option Ordering)) := do
  let references ← LocalizedChemicalRingJointExecutable.references? input M
  let (positions, adjacent, _) ← partition? input cache mol state node references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
  some (positions, adjacent)

def markedJoint? (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (L : List Nat) (_mark : Nat) :
    Option Rule6TrackedRanking := do
  let references ← LocalizedChemicalRingJointExecutable.references? input L
  let (positions, adjacent, count) ← partition? input cache mol state node references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
  some { positions := positions, unique := strict adjacent, pseudoComparisons := count }

def operations (mol : RawMolecule) : MultiOperations where
  ordinary := LocalizedChemicalRingCachedOperations.ordinary input cache mol
  contextOrder := contextOrder? input cache mol
  markedJoint := markedJoint? input cache mol

theorem operations_eq (mol : RawMolecule) : operations input cache mol =
    LocalizedChemicalRingJointExecutable.operations input mol := by
  have ordinary : LocalizedChemicalRingCachedOperations.ordinary input cache mol =
      LocalizedMarkedRetainedOperations.ordinary input mol := by
    funext state node
    exact LocalizedChemicalRingCachedOperations.ordinary_eq input cache mol state node
  have context : contextOrder? input cache mol =
      LocalizedChemicalRingJointExecutable.contextOrder? input mol := by
    funext state node M
    simp only [contextOrder?, LocalizedChemicalRingJointExecutable.contextOrder?, partition?_eq]
  have marked : markedJoint? input cache mol =
      LocalizedChemicalRingJointExecutable.markedJoint? input mol := by
    funext state node L mark
    simp only [markedJoint?, LocalizedChemicalRingJointExecutable.markedJoint?, partition?_eq]
  unfold operations LocalizedChemicalRingJointExecutable.operations
  rw [ordinary, context, marked]

/-- The full carrier is constructed once before mapping centers. Every center then retains one
root slice and shares it across all recursive contexts, geometry sides and comparison stages. -/
def analyze (mol : RawMolecule) : LocalizedChemicalRingJointPreparedReport.Report :=
  let full := input.localizedRerootCarrierCache (retainedCarrierFuel input)
  input.canonicalTetrahedralCenters.map fun center =>
    let slice := localizedRerootRootSliceCache full center.1
    (center.1.val, preparedAssignCenter? mol (operations input slice.reader mol)
      (inputGeometry input) center.1.val)

theorem analyze_eq (mol : RawMolecule) : analyze input mol =
    LocalizedChemicalRingJointPreparedReport.analyze input mol := by
  unfold analyze
  simp only [operations_eq]
  exact LocalizedChemicalRingJointExecutable.analyze_eq input mol

end TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable.before
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable.before_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable.partition?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable.partition?_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable.contextOrder?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable.markedJoint?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable.operations
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable.operations_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable.analyze
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable.analyze_eq
