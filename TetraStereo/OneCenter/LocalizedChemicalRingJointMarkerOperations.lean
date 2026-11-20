import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey
import TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion
import TetraStereo.OneCenter.LocalizedMarkedRetainedOperations
import TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking
import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedOperations
import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking
import TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations
import TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader
import TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularSelection
import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation
import TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Concrete joint-marker comparison callbacks

The two context callbacks share one actual frame/cursor partition. A joint decision refines
only an ordinary tie; a successful joint tie supplies the successful built keys required by
joint-marker reconstruction. The auxiliary state remains an explicit argument.

This is an experimental operations instance, not a default evaluator change. It does not prove
coverage of ordinary-tied traversal, stability when the generated state changes, universal
sorting success, chemical meaning of accumulated marks, or physical orientation preservation.
The unverified traversal lemmas in the external draft are deliberately not imported here.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations

open CertifiedLocalizedCIPInput DeclarativeCIP DeclarativeCIP.PromotedCanonical
open LocalizedChemicalRingJointMarkerKey
open LocalizedMarkedRetainedCanonicalMarker LocalizedCumulativeDecoratedTree
open LocalizedMarkedRetainedPromotedKey Rule4aTableBridge
open LocalizedGenericMarkedRecalculation
open LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedOperations
open LocalizedMarkedCarrierLookup
open LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedPromotedOperations (adjacentPromotionCount? adjacentPromotionCount?_exists)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

/-! ### Reference membership for the accumulated context -/

/-- The reference atoms named by an accumulated mark context.

Marks are atom indices of the certified molecule read by this input. A mark outside the molecule
is refused, so a bogus context cannot silently become a reference column; this mirrors
`LocalizedMarkedRetainedPromotedOperations.markedWithLayout?`. -/
def referenceAtoms? (M : List Nat) : Option (List input.Atom) :=
  M.mapM fun mark =>
    if bound : mark < input.certified.input.molecule.atomCount then some ⟨mark, bound⟩ else none

/-- One reference column entry per accumulated mark, at a given slot. Inherited reference bits
are exactly `JointMarkerKey.referenceBit`, so the reference vector of the joint marker below is
the accepted one. -/
def referenceBits (references : List input.Atom)
    (cursor : input.LocalizedRerootCursor (retainedCarrierFuel input)) : List Nat :=
  references.map fun reference => referenceBit input reference cursor

/-! ### The single comparator -/

/-- Position of the atom currently occupying a frame slot, as a position in the node's atom list. -/
def slotPosition (atoms : List Nat)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (slot : Fin 4) : Option Nat :=
  (frame.cursorAt slot).occurrence.1.node.current?.bind
    fun atom => atoms.findIdx? (· == atom.val)

/-- **The single joint comparator.**

The certified retained Rules-1--5 raw-state comparison at the actual frame cursors, refined on an
ordinary tie by the actual joint-marker comparison `compareJointAt?` of `LocalizedChemicalRingJointMarkerKey`
at the accumulated references. No agreement between the two is assumed: on a strict ordinary
decision the ordinary value is returned unchanged, so a joint tie is always an ordinary tie. -/
def jointBefore (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (references : List input.Atom) (W D : Nat) (left right : Fin 4) : Option Ordering :=
  (rawStateBefore input state target frame left right).bind fun prior =>
    if prior = Ordering.eq then
      compareJointAt? input target (rawStateView input state target) references W D
        (frame.cursorAt left) (frame.cursorAt right)
    else some prior

/-- One sort pass, the adjacent decisions of the *same* comparator, and the accepted strict
post-tie promotion count. Everything the marked interface reports comes from this one pass. -/
def partitionBy? {α : Type} (ordinary promoted : α → α → Option Ordering) (slots : List α) :
    Option (List α × List (Option Ordering) × Nat) := do
  let sorted ← sortBy? promoted slots
  let count ← adjacentPromotionCount? ordinary promoted sorted
  some (sorted, adjacentBy promoted sorted, count)

/-- The actual frame expansion at a canonical branch node: the certified occurrence, the node's
atom list and the executable four-ligand frame. -/
def jointFrame? (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode) :
    Option (input.LocalizedCIPOccurrence (retainedCarrierFuel input) × List Nat ×
      input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input)) := do
  let target ← lookup? input node
  let atoms ← frameAtoms? mol node
  let frame ← input.localizedNoDoubleFourLigandFrameExec? target
  some (target, atoms, frame)

/-- The joint partition at a node for an accumulated reference context: actual cursors, actual
frame, one comparator pass, actual positions. -/
def jointPartition? (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (references : List input.Atom) (W D : Nat) :
    Option (List Nat × List (Option Ordering) × Nat) := do
  let (target, atoms, frame) ← jointFrame? input mol node
  let (sorted, adjacent, count) ← partitionBy? (rawStateBefore input state target frame)
    (jointBefore input state target frame references W D) (List.finRange 4)
  let positions ← positions? input atoms frame sorted
  some (positions, adjacent, count)

/-! ### The concrete `MultiOperations` -/

/-- The current-context partial ordering: the joint partition at the accumulated references. -/
def contextOrder? (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (M : List Nat) :
    Option (List Nat × List (Option Ordering)) := do
  let references ← referenceAtoms? input M
  let (positions, adjacent, _) ← jointPartition? input mol state node references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
  some (positions, adjacent)

/-- The extended-context ranked reading: the same joint partition at the accumulated references,
reported as a tracked ranking (marked positions, uniqueness of the joint order, and the accepted
strict post-tie count). The inherited marks are read at the joint cursors, so the ranking is the
tracked form of the same comparator used by `contextOrder?`. -/
def markedJoint? (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (L : List Nat) (_mark : Nat) :
    Option Rule6TrackedRanking := do
  let references ← referenceAtoms? input L
  let (positions, adjacent, count) ← jointPartition? input mol state node references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
  some { positions := positions, unique := strict adjacent, pseudoComparisons := count }

/-- The concrete operations record. `ordinary` is the accepted certified ordinary callback
unchanged; the two context callbacks are the actual frame/cursor expansion above. -/
def jointOperations (mol : RawMolecule) :
    LocalizedChemicalRingMultiMarkRecursion.MultiOperations where
  ordinary := ordinary input mol
  contextOrder := contextOrder? input mol
  markedJoint := markedJoint? input mol

/-! ### Unconditional facts about the single comparator -/

/-- **The refinement direction the evaluator needs, unconditionally.**

A joint tie is an ordinary tie: `jointBefore` only consults `compareJointAt?` when the ordinary
comparison already returned `eq`. No agreement of `compareJointAt?` with `rawStateBefore` is used
or claimed; the joint value is only *narrowing* the ordinary tie. -/
theorem jointBefore_eq_some_eq (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (references : List input.Atom) (W D : Nat) (left right : Fin 4)
    (tie : jointBefore input state target frame references W D left right = some Ordering.eq) :
    rawStateBefore input state target frame left right = some Ordering.eq := by
  unfold jointBefore at tie
  cases h : rawStateBefore input state target frame left right with
  | none => simp [h] at tie
  | some prior =>
      by_cases hp : prior = Ordering.eq
      · exact congrArg some hp
      · simp [h, hp] at tie

/-- On a strict ordinary decision the joint comparator returns exactly that decision, so the
joint order refines rather than replaces the ordinary order. -/
theorem jointBefore_of_ordinary_ne (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (references : List input.Atom) (W D : Nat) (left right : Fin 4) (order : Ordering)
    (ordinary : rawStateBefore input state target frame left right = some order)
    (ne : order ≠ Ordering.eq) :
    jointBefore input state target frame references W D left right = some order := by
  unfold jointBefore
  rw [ordinary]
  simp [ne]

/-- Pointwise totality of the joint comparator implies pointwise ordinary totality. -/
theorem rawStateBefore_total_of_jointBefore_total (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (references : List input.Atom) (W D : Nat)
    (total : ∀ left right, ∃ order,
      jointBefore input state target frame references W D left right = some order) :
    ∀ left right, ∃ order, rawStateBefore input state target frame left right = some order := by
  intro left right
  obtain ⟨order, ho⟩ := total left right
  cases h : rawStateBefore input state target frame left right with
  | none => simp [jointBefore, h] at ho
  | some prior => exact ⟨prior, rfl⟩

/-! ### The two callbacks are one pass of one comparator -/

/-- Both callbacks are the *same* `jointPartition?` pass at the same accumulated references: same
frame cursors, same comparator, same sorted slots, same adjacent decisions, same tie class. This
is an equality of values, not an assumed agreement. -/
theorem contextOrder?_eq_marked_partition (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (L : List Nat) (mark : Nat)
    (references : List input.Atom) (positions : List Nat) (adjacent : List (Option Ordering))
    (count : Nat)
    (hrefs : referenceAtoms? input L = some references)
    (hpart : jointPartition? input mol state node references
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) =
        some (positions, adjacent, count)) :
    contextOrder? input mol state node L = some (positions, adjacent) ∧
      markedJoint? input mol state node L mark =
        some { positions := positions, unique := strict adjacent
               pseudoComparisons := count } := by
  constructor
  · simp [contextOrder?, hrefs, hpart]
  · simp [markedJoint?, hrefs, hpart]


/-- An actual frame-level tie exposes both successful joint builds and their tie. These are
exactly the build/tie inputs consumed by joint hierarchy reconstruction. -/
theorem jointBefore_tie_built (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (references : List input.Atom) (W D : Nat) (left right : Fin 4)
    (tie : jointBefore input state target frame references W D left right = some Ordering.eq) :
    ∃ l r : JointPromotedKey input,
      buildJoint? input target (rawStateView input state target) references W D
        (2 * (retainedCarrierFuel input + 1)) (frame.cursorAt left) = some l ∧
      buildJoint? input target (rawStateView input state target) references W D
        (2 * (retainedCarrierFuel input + 1)) (frame.cursorAt right) = some r ∧
      compareJointKeys input l r = Ordering.eq := by
  have ordinaryTie := jointBefore_eq_some_eq input state target frame references W D left right tie
  simp only [jointBefore, ordinaryTie, Option.bind_some] at tie
  unfold compareJointAt? at tie
  cases hl : buildJoint? input target (rawStateView input state target) references W D
      (2 * (retainedCarrierFuel input + 1)) (frame.cursorAt left) with
  | none => simp [hl] at tie
  | some l =>
      cases hr : buildJoint? input target (rawStateView input state target) references W D
          (2 * (retainedCarrierFuel input + 1)) (frame.cursorAt right) with
      | none => simp [hl, hr] at tie
      | some r =>
          exact ⟨l, r, rfl, rfl, by simpa [hl, hr] using tie⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations.referenceAtoms?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations.jointBefore
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations.jointOperations
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations.jointBefore_eq_some_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations.jointBefore_of_ordinary_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations.rawStateBefore_total_of_jointBefore_total
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations.contextOrder?_eq_marked_partition
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations.jointBefore_tie_built
