import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey
import TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Actual promoted frame sorting refines the independent ordinary order

The executable comparator builds full ordinary-plus-marker keys under the original raw-state
view. At every real detected carrier target of a single-bond input, the four keys exist, the
frame sort succeeds, and its result is a descending permutation. The earlier component of the
sort key is the independent retained Rules-1–5 signature; the later component is the actual
computed marker. Thus every strict independent ordinary decision survives promotion.

The marker is not here identified with an independent canonical marker. This is a frame-level
execution and earlier-rule refinement theorem, not yet chemical Rule-6 correctness or a proof
of the recursively generated descriptor state's meaning. Rings and reference ties are allowed.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking

open CertifiedLocalizedCIPInput DeclarativeCIP DeclarativeCIP.PromotedCanonical Rule4aTableBridge
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedKey

abbrev RefinedKey := Lex (CompleteLigandRule5Key × MarkerKey)

private theorem natList_compare_lt_iff (left right : List Nat) :
    compare left right = .lt ↔ left < right :=
  compareLex_eq_lt_iff_of compare (fun _ _ => compare_lt_iff_lt)
    (fun _ _ => compare_eq_iff_eq) left right

private theorem natList_compare_eq_iff (left right : List Nat) :
    compare left right = .eq ↔ left = right :=
  compareLex_eq_eq_iff_of compare (fun _ _ => compare_eq_iff_eq) left right

private theorem marker_compare_lt_iff (left right : MarkerKey) :
    compare left right = .lt ↔ left < right :=
  compareLex_eq_lt_iff_of compare natList_compare_lt_iff natList_compare_eq_iff left right

private theorem marker_compare_eq_iff (left right : MarkerKey) :
    compare left right = .eq ↔ left = right :=
  compareLex_eq_eq_iff_of compare natList_compare_eq_iff left right

theorem refined_compare_lt_iff (left right : RefinedKey) :
    compare left right = .lt ↔ left < right :=
  then_eq_lt_iff_lex compare compare completeLigandRule5Key_compare_lt_iff
    completeLigandRule5Key_compare_eq_iff marker_compare_lt_iff
    (ofLex left).1 (ofLex right).1 (ofLex left).2 (ofLex right).2

theorem refined_compare_eq_iff (left right : RefinedKey) :
    compare left right = .eq ↔ left = right :=
  then_eq_eq_iff_lex compare compare completeLigandRule5Key_compare_eq_iff marker_compare_eq_iff
    (ofLex left).1 (ofLex right).1 (ofLex left).2 (ofLex right).2

variable (input : CertifiedLocalizedCIPInput)

def before (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (reference : input.Atom) (W D : Nat)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (left right : Fin 4) : Option Ordering :=
  compareAt? input target (rawStateView input state target) reference W D
    (frame.cursorAt left) (frame.cursorAt right)

/-- Ties remain visible; this partition does not invent a strict ranking. -/
def partition? (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (reference : input.Atom) (W D : Nat) :
    Option (List (Fin 4) × List (Option Ordering)) := do
  let frame ← input.localizedNoDoubleFourLigandFrameExec? target
  let sorted ← sortBy? (before input state target reference W D frame) (List.finRange 4)
  some (sorted, adjacentBy (before input state target reference W D frame) sorted)

noncomputable section

variable (single : input.moleculeGraph.SimpleBonded) (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (reference : input.Atom) (W D : Nat)

abbrev frames := rawStateFrames input single state target real unit targetUnit

theorem slot_valid (slot : Fin 4) :
    input.LocalizedRerootCursorValid
      ((frames input single state target real unit targetUnit).frame.cursorAt slot) :=
  input.localizedRerootChild_valid ⟨target, none⟩ _ _
    (input.executableLocalizedRerootChildren_declarative ⟨target, none⟩)
    ((frames input single state target real unit targetUnit).childAt slot)

/-- Proof-only names for the actual successfully computed keys. -/
def compiled (slot : Fin 4) : PromotedKey input :=
  Classical.choose (build?_exists input target (rawStateView input state target) reference W D
    ((frames input single state target real unit targetUnit).frame.cursorAt slot)
    (slot_valid input single state target real unit targetUnit slot))

theorem compiled_built (slot : Fin 4) :
    build? input target (rawStateView input state target) reference W D
        (2 * (retainedCarrierFuel input + 1))
        ((frames input single state target real unit targetUnit).frame.cursorAt slot) =
      some (compiled input single state target real unit targetUnit reference W D slot) :=
  Classical.choose_spec (build?_exists input target (rawStateView input state target) reference W D
    ((frames input single state target real unit targetUnit).frame.cursorAt slot)
    (slot_valid input single state target real unit targetUnit slot))

theorem compiled_prior (slot : Fin 4) :
    (compiled input single state target real unit targetUnit reference W D slot).prior =
      (frames input single state target real unit targetUnit).compounds slot := by
  have actual := build?_prior input target (rawStateView input state target) reference W D _ _ _
    (compiled_built input single state target real unit targetUnit reference W D slot)
  unfold ordinaryKey? at actual
  rw [rawStateView_eq_molecularView,
    (frames input single state target real unit targetUnit).compoundBuilt slot] at actual
  exact (Option.some.inj actual).symm

/-- Independent ordinary signature followed by the actual marker column. -/
def refinedKey (slot : Fin 4) : RefinedKey :=
  toLex (rawStateKeys input single state target real unit targetUnit slot,
    (compiled input single state target real unit targetUnit reference W D slot).marker)

theorem before_eq_refined (left right : Fin 4) :
    before input state target reference W D
        (frames input single state target real unit targetUnit).frame left right =
      some (compare (refinedKey input single state target real unit targetUnit reference W D left)
        (refinedKey input single state target real unit targetUnit reference W D right)) := by
  simp only [before, compareAt?,
    compiled_built input single state target real unit targetUnit reference W D,
    Option.bind_eq_bind, Option.bind_some]
  unfold compareKeys
  rw [compiled_prior input single state target real unit targetUnit reference W D left,
    compiled_prior input single state target real unit targetUnit reference W D right,
    (frames input single state target real unit targetUnit).fullOrdering
      (rawStateDescriptorMap_tetrahedral input state) single unit targetUnit left right]
  rfl

/-- The actual promoted sort succeeds and equals the descending order of the refined keys. -/
theorem partition?_eq :
    partition? input state target reference W D =
      some (keyOrder (refinedKey input single state target real unit targetUnit reference W D)
          (List.finRange 4),
        adjacentBy (fun left right => some
          (compare (refinedKey input single state target real unit targetUnit reference W D left)
            (refinedKey input single state target real unit targetUnit reference W D right)))
          (keyOrder (refinedKey input single state target real unit targetUnit reference W D)
            (List.finRange 4))) := by
  have callback := funext fun left => funext fun right =>
    before_eq_refined input single state target real unit targetUnit reference W D left right
  unfold partition?
  rw [(frames input single state target real unit targetUnit).frameComputed]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [callback, sortBy?_key compare refined_compare_lt_iff]
  rfl

include single real unit targetUnit in
/-- All four slots are returned, and none of the adjacent comparisons is inverted or absent. -/
theorem partition?_permutation_consistent :
    ∃ sorted adjacent, partition? input state target reference W D = some (sorted, adjacent) ∧
      sorted.Perm (List.finRange 4) ∧
      ∀ decision ∈ adjacent, decision = some Ordering.gt ∨ decision = some Ordering.eq := by
  exact ⟨_, _, partition?_eq input single state target real unit targetUnit reference W D,
    keyOrder_perm _ _, adjacentBy_key_consistent compare refined_compare_lt_iff
      refined_compare_eq_iff _ _ (keyOrder_pairwise _ _)⟩

/-- A strict independent ordinary decision is preserved, with no desired-sort/build premise. -/
theorem before_eq_ordinary_of_strict (left right : Fin 4)
    (strict : compare (rawStateKeys input single state target real unit targetUnit left)
        (rawStateKeys input single state target real unit targetUnit right) ≠ .eq) :
    before input state target reference W D
        (frames input single state target real unit targetUnit).frame left right =
      some (compare (rawStateKeys input single state target real unit targetUnit left)
        (rawStateKeys input single state target real unit targetUnit right)) := by
  rw [before_eq_refined input single state target real unit targetUnit reference W D]
  change some ((compare (rawStateKeys input single state target real unit targetUnit left)
      (rawStateKeys input single state target real unit targetUnit right)).then _) = _
  cases h : compare (rawStateKeys input single state target real unit targetUnit left)
      (rawStateKeys input single state target real unit targetUnit right) <;> simp_all

end
end TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking.refined_compare_lt_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking.refined_compare_eq_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking.compiled_built
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking.compiled_prior
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking.before_eq_refined
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking.partition?_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking.partition?_permutation_consistent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking.before_eq_ordinary_of_strict
