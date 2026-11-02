import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking
import TetraStereo.OneCenter.LocalizedMarkedDetectedOrdinaryExecution
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Experimental marked operations with the full retained ordinary prefix

Both callbacks now use the retained Rules-1–5 path. The marked callback uses full compound
priority at every recursive child, followed by the reference-marker column. The old raw
whole-frontier selector is not called by this operations record.

`adjacentPromotionCount?` counts final adjacent decisions whose ordinary comparison ties and
whose promoted comparison is strict. Its compatibility projection into `pseudoComparisons`
is NOT the historical insertion-time count and has no asserted physical pseudoasymmetry
meaning. The operation evaluator's geometric readback ignores that field; uniqueness is
computed from the final adjacent decisions.

This is an explicit experimental operations value, not a public runtime/default change.
Independent canonical marker agreement, complete layout bounds, generated-label meaning and
inherited-reference policy remain separate obligations. The operation evaluator still has
its existing immediate-frame inherited-reference policy.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedOperations

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedOperations
open LocalizedMarkedCarrierLookup LocalizedMarkedFramePositionBridge
open LocalizedMarkedDetectedOrdinaryExecution
open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedCertifiedTerminalRefusal
open LocalizedGenericMarkedRecalculation (frameAtoms? strict)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- Counts only actual strict promotions after an ordinary tie. Missing decisions fail closed. -/
def adjacentPromotionCount? {α : Type} (ordinary promoted : α → α → Option Ordering) :
    List α → Option Nat
  | [] | [_] => some 0
  | first :: second :: rest => do
      let prior ← ordinary first second
      let after ← promoted first second
      let count ← adjacentPromotionCount? ordinary promoted (second :: rest)
      some (count + if prior = .eq ∧ after ≠ .eq then 1 else 0)

theorem adjacentPromotionCount?_exists {α : Type}
    (ordinary promoted : α → α → Option Ordering)
    (ordinaryTotal : ∀ a b, ∃ order, ordinary a b = some order)
    (promotedTotal : ∀ a b, ∃ order, promoted a b = some order) :
    ∀ xs : List α, ∃ count, adjacentPromotionCount? ordinary promoted xs = some count
  | [] => ⟨0, rfl⟩
  | [_] => ⟨0, rfl⟩
  | first :: second :: rest => by
      obtain ⟨prior, hp⟩ := ordinaryTotal first second
      obtain ⟨after, ha⟩ := promotedTotal first second
      obtain ⟨count, hc⟩ := adjacentPromotionCount?_exists ordinary promoted ordinaryTotal
        promotedTotal (second :: rest)
      exact ⟨count + if prior = .eq ∧ after ≠ .eq then 1 else 0,
        by simp [adjacentPromotionCount?, hp, ha, hc]⟩

variable (input : CertifiedLocalizedCIPInput)

/-- Explicit-layout candidate. Any in-range reference atom is supported by the marker builder;
selection and inherited-reference policy belong to the calling evaluator. -/
def markedWithLayout? (mol : RawMolecule) (W D : Nat) (state : OccurrenceAuxState)
    (node : Node) (mark : Nat) : Option Rule6TrackedRanking := do
  if bound : mark < input.certified.input.molecule.atomCount then
    let reference : input.Atom := ⟨mark, bound⟩
    let target ← lookup? input node
    let atoms ← frameAtoms? mol node
    let frame ← input.localizedNoDoubleFourLigandFrameExec? target
    let partition ← LocalizedMarkedRetainedPromotedRanking.partition? input state target reference W D
    let positions ← positions? input atoms frame partition.1
    let count ← adjacentPromotionCount?
      (rawStateBefore input state target frame)
      (LocalizedMarkedRetainedPromotedRanking.before input state target reference W D frame)
      partition.1
    some { positions := positions, unique := strict partition.2, pseudoComparisons := count }
  else none

/-- Candidate finite marker window. Completeness of this layout is not claimed here. -/
def marked? (mol : RawMolecule) (state : OccurrenceAuxState) (node : Node) (mark : Nat) :
    Option Rule6TrackedRanking :=
  markedWithLayout? input mol (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
    state node mark

/-- Both callbacks use retained priority; no legacy marked callback is included. -/
def operations (mol : RawMolecule) : LocalizedMarkedOperationEvaluator.Operations where
  ordinary := ordinary input mol
  marked := marked? input mol

/-- Missing/out-of-range reference atoms are refused rather than coerced into the molecule. -/
theorem markedWithLayout?_invalid (mol : RawMolecule) (W D : Nat) (state : OccurrenceAuxState)
    (node : Node) (mark : Nat) (outside : input.certified.input.molecule.atomCount ≤ mark) :
    markedWithLayout? input mol W D state node mark = none := by
  simp [markedWithLayout?, Nat.not_lt.mpr outside]

/-- At a physically detected reached real occurrence, all lookup, frame, sorting and position
steps succeed. The returned positions are an actual four-slot permutation. No ordering success,
compound builds or desired descriptors are premises. -/
theorem markedWithLayout?_exists_of_physical_detected_reached
    (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (root : Nat) (valid : root < mol.atomCount)
    (center : input.detectedMultiCenterMolecule.Center) (node : Node)
    (reached : ReachedFrom mol root node)
    (rawReal : node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (current : node.atom = center.1.val)
    (reference : input.Atom) (W D : Nat) :
    ∃ ranking, markedWithLayout? input mol W D state node reference.val = some ranking ∧
      ranking.positions.Perm [0, 1, 2, 3] := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  obtain ⟨target, found, _, corresponds⟩ := lookup?_exists_of_reachedFrom mol input agreement
    wellFormed unique supported rawSingle root valid node reached
  have real := lookup?_real input node target found rawReal
  have detected := lookup_detected_of_physical_center mol input agreement admissible supported
    single center node current target found
  let unit : DetectedOccurrence input.moleculeGraph := ⟨input.molecularFrameUnit target.1, detected⟩
  let frames := rawStateFrames input single state target real unit rfl
  obtain ⟨atoms, length, reindex, rawFrame, nodup, readback⟩ :=
    exists_frame_position_permutation mol input agreement admissible supported single
      (rawStateDescriptorMap input state) target frames node ⟨root, valid, reached⟩ corresponds
  let key := LocalizedMarkedRetainedPromotedRanking.refinedKey input single state target real
    unit rfl reference W D
  let sorted := keyOrder key (List.finRange 4)
  let adjacent := adjacentBy (fun left right => some (compare (key left) (key right))) sorted
  have partition : LocalizedMarkedRetainedPromotedRanking.partition? input state target reference W D =
      some (sorted, adjacent) :=
    LocalizedMarkedRetainedPromotedRanking.partition?_eq input single state target real unit rfl
      reference W D
  have positions := positions?_eq_inverse_reindex input atoms length nodup frames.frame reindex
    readback sorted
  have oldTotal : ∀ a b, ∃ order, rawStateBefore input state target frames.frame a b = some order := by
    intro a b
    exact ⟨_, rawStateBefore_eq_keys input single state target real unit rfl a b⟩
  have newTotal : ∀ a b, ∃ order,
      LocalizedMarkedRetainedPromotedRanking.before input state target reference W D frames.frame
        a b = some order := by
    intro a b
    exact ⟨_, LocalizedMarkedRetainedPromotedRanking.before_eq_refined input single state target
      real unit rfl reference W D a b⟩
  obtain ⟨count, counted⟩ := adjacentPromotionCount?_exists
    (rawStateBefore input state target frames.frame)
    (LocalizedMarkedRetainedPromotedRanking.before input state target reference W D frames.frame)
    oldTotal newTotal sorted
  refine ⟨⟨sorted.map (fun slot => (reindex.symm slot).val), strict adjacent, count⟩, ?_, ?_⟩
  · simp only [markedWithLayout?, dif_pos reference.isLt, found, rawFrame,
      frames.frameComputed, partition, positions, counted, Option.bind_eq_bind, Option.bind_some]
  · exact inverse_reindex_perm reindex sorted (keyOrder_perm key _)

end TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedOperations

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedOperations.adjacentPromotionCount?_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedOperations.markedWithLayout?_invalid
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedOperations.markedWithLayout?_exists_of_physical_detected_reached
