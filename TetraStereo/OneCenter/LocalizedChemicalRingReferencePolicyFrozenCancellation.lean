import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation
import TetraStereo.OneCenter.Rule6Proposed2018PromotionFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Independent frozen auxiliary generation with cancellation and a single current reference.
The profile's outer Option records operational failure. Completed nonuniqueness contributes no
auxiliary fact. Promotion references affect the actual scalar ranker only; no inherited marker
list enters a descendant query. This is a neutral explicit policy, not normative attribution. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation

open DeclarativeCIP.ProductionOccurrenceRules456
open LocalizedGenericMarkedRecalculation

/-- Sequence successful subtree profiles, retaining operational failure. -/
def collect {α : Type} (profile : α → Option OccurrenceAuxState) :
    List α → Option OccurrenceAuxState
  | [] => some []
  | head :: tail => do
      let first ← profile head
      let rest ← collect profile tail
      pure (first ++ rest)

theorem collect_empty {α : Type} (profile : α → Option OccurrenceAuxState) (nodes : List α)
    (empty : ∀ node ∈ nodes, profile node = some []) : collect profile nodes = some [] := by
  induction nodes with
  | nil => rfl
  | cons head tail ih =>
    rw [collect, empty head (by simp), ih (fun node member => empty node (by simp [member]))]
    rfl

/-- The scalar current-reference ranker is executed separately for each selected reference. -/
def promotionOutcome (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (reference : Nat) : PromotionOutcome :=
  match marked? mol fuel state node reference with
  | none => .operationalFailure
  | some ranking =>
      if ranking.unique then
        match markedReadback? mol fuel geom state node reference with
        | none => .operationalFailure
        | some raw => .descriptor raw
      else .unresolved

theorem promotionOutcome_unresolved (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) (reference : Nat)
    (nonunique : (marked? mol fuel state node reference).map (·.unique) = some false) :
    promotionOutcome mol fuel geom state node reference = .unresolved := by
  cases rank : marked? mol fuel state node reference with
  | none => simp [rank] at nonunique
  | some ranking =>
    have unique : ranking.unique = false := by simpa [rank] using nonunique
    simp [promotionOutcome, rank, unique]

theorem promotionOutcome_descriptor (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (reference : Nat) (raw : RS)
    (reading : markedReadback? mol fuel geom state node reference = some raw) :
    promotionOutcome mol fuel geom state node reference = .descriptor raw := by
  cases frame : frameAtoms? mol node with
  | none => simp [markedReadback?, frame] at reading
  | some atoms =>
    cases rank : marked? mol fuel state node reference with
    | none => simp [markedReadback?, frame, rank] at reading
    | some ranking =>
      cases unique : ranking.unique with
      | false => simp [markedReadback?, frame, rank, rankedAtoms?, unique] at reading
      | true => simp [promotionOutcome, rank, unique, reading]

/-- Generate the pre-promotion descendant map once, then cancel all selected scalar-reference
outcomes. No-frame is structural absence; missing partition or readback is operational failure. -/
def rawWith (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (sub : Geometry → OccurrenceAuxState → RawMolecule.CanonicalBranchNode →
      Option OccurrenceAuxState) : Option (Option RS) :=
  match frameAtoms? mol node with
  | none => some none
  | some atoms => do
      let (sorted, adjacent) ← ordinary? mol fuel state node
      if ¬ atoms.Nodup ∨ consistent adjacent = false then none
      else if strict adjacent then do
        let ranked ← atomsAt? atoms sorted
        let raw ← readback? geom ranked
        pure (some raw)
      else do
        let below ← collect (sub geom state) (tiedChildren mol fuel state node)
        let temporary ← appendFacts? state below
        promotionAggregate ((eligibleOf atoms sorted adjacent).map
          (promotionOutcome mol fuel geom temporary node))

def descriptorWith (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (sub : Geometry → OccurrenceAuxState → RawMolecule.CanonicalBranchNode →
      Option OccurrenceAuxState) : Option (Option LocalizedTetrahedralRSPseudoDescriptor) := do
  let first ← rawWith mol fuel geom state node sub
  let second ← rawWith mol fuel (mirror geom) state node sub
  pure (caseFromMirror? first second)

/-- Independent terminating cancellation profile. Descendant queries retain no reference;
the single current reference exists only within a promotion's scalar comparison call. -/
def facts (mol : RawMolecule) (fuel : Nat) : Nat → Geometry → OccurrenceAuxState →
    RawMolecule.CanonicalBranchNode → Option OccurrenceAuxState
  | 0, _, _, _ => some []
  | depth + 1, geom, state, node => do
      let outcome ← descriptorWith mol fuel geom state node (facts mol fuel depth)
      let descendants ← collect (facts mol fuel depth geom state) (mol.canonicalChildren node)
      pure (outcome.toList.map (factOf node) ++ descendants)

def raw (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) : Option (Option RS) :=
  rawWith mol fuel geom state node (facts mol fuel depth)

def descriptor (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    Option (Option LocalizedTetrahedralRSPseudoDescriptor) :=
  descriptorWith mol fuel geom state node (facts mol fuel depth)

def assignCenter (mol : RawMolecule) (fuel : Nat) (geom : Geometry) (center : Nat) :
    Option (Option LocalizedTetrahedralRSPseudoDescriptor) :=
  descriptor mol fuel (structuralDepth mol (canonicalCenterRoot center)) geom []
    (canonicalCenterRoot center)

theorem descriptorWith_noFrame (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (sub : Geometry → OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxState)
    (frame : frameAtoms? mol node = none) :
    descriptorWith mol fuel geom state node sub = some none := by
  simp [descriptorWith, rawWith, frame, caseFromMirror?]

theorem facts_noFrame (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (frame : frameAtoms? mol node = none) :
    facts mol fuel (depth + 1) geom state node =
      collect (facts mol fuel depth geom state) (mol.canonicalChildren node) := by
  rw [facts, descriptorWith_noFrame mol fuel geom state node _ frame]
  simp

theorem facts_forcedLeaf (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (leaf : node.forcedLeaf = true) : facts mol fuel depth geom state node = some [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [facts_noFrame mol fuel depth geom state node (frameAtoms?_forcedLeaf mol node leaf),
      canonicalChildren_forcedLeaf mol node leaf]
    rfl

theorem facts_shallowNoFrame (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (frame : frameAtoms? mol node = none)
    (leaves : ∀ child ∈ mol.canonicalChildren node, child.forcedLeaf = true) :
    facts mol fuel depth geom state node = some [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [facts_noFrame mol fuel depth geom state node frame]
    exact collect_empty _ _ (fun child member =>
      facts_forcedLeaf mol fuel depth geom state child (leaves child member))

/-- Actual partition reduction, keeping every promotion outcome available for cancellation. -/
theorem rawWith_partition (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (sub : Geometry → OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxState)
    (atoms sorted : List Nat) (adjacent : List (Option Ordering))
    (frame : frameAtoms? mol node = some atoms)
    (order : ordinary? mol fuel state node = some (sorted, adjacent))
    (nodup : atoms.Nodup) (consistent : consistent adjacent = true)
    (tied : strict adjacent = false)
    (empty : collect (sub geom state) (tiedChildren mol fuel state node) = some []) :
    rawWith mol fuel geom state node sub =
      promotionAggregate ((eligibleOf atoms sorted adjacent).map
        (promotionOutcome mol fuel geom state node)) := by
  simp [rawWith, frame, order, nodup, consistent, tied, empty, appendFacts?_nil]

end TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.collect
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.collect_empty
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.promotionOutcome
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.promotionOutcome_unresolved
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.promotionOutcome_descriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.rawWith
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.descriptorWith
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.facts
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.raw
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.descriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.assignCenter
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.descriptorWith_noFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.facts_noFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.facts_forcedLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.facts_shallowNoFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellation.rawWith_partition
