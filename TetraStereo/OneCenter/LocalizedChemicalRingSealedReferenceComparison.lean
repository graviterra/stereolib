import TetraStereo.OneCenter.LocalizedChemicalRingAbsentReferenceKey
import TetraStereo.OneCenter.LocalizedChemicalRingSealedCursorReference
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
Local graph sealing is sufficient to remove an inherited reference from an actual sparse
comparison anywhere below an incoming cursor. Both ordinary builds and promoted comparison
success are derived. No marker equality, comparison outcome or generated-label agreement is
assumed. The dependency view remains arbitrary: this lemma does not establish its meaning.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSealedReferenceComparison

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree (LocalizedRerootCursorIncomingParent)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedPromotedKey LocalizedMarkedRetainedSparsePromotedKey
open LocalizedChemicalRingSealedCursorReference LocalizedChemicalRingAbsentReferenceKey

variable (input : CertifiedLocalizedCIPInput)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (view : input.LocalizedDependencyView target) (reference atom : input.Atom)
  (W D : Nat)
  (source left right : input.LocalizedRerootCursor (retainedCarrierFuel input))
  (incoming : LocalizedRerootCursorIncomingParent input source)
  (sourceReal : source.occurrence.1.node.provenance = .realAtom)
  (current : source.occurrence.1.node.current? = some atom) (different : atom ≠ reference)
  (sealed : ∀ neighbor, input.moleculeGraph.Adj neighbor reference →
    neighbor ∈ source.occurrence.1.node.history)
  (notAdjacent : ¬ input.moleculeGraph.Adj atom reference)
  (leftPath : Relation.ReflTransGen (E input) source left)
  (rightPath : Relation.ReflTransGen (E input) source right)
  (leftValid : input.LocalizedRerootCursorValid left)
  (rightValid : input.LocalizedRerootCursorValid right)

include incoming sourceReal current different sealed notAdjacent leftPath rightPath leftValid rightValid

/-- The actual ordinary keys exist and their full comparison is preserved by promotion
under the local molecular sealing conditions. In particular, promotion succeeds. -/
theorem actual_comparison_preserved :
    ∃ priorL priorR,
      ordinaryKey? input target view left = some priorL ∧
      ordinaryKey? input target view right = some priorR ∧
      sparseCompareAt? input target view reference W D left right =
        some (input.compareLocalizedRerootCompoundThroughRule5 priorL priorR).ordering := by
  obtain ⟨priorL, leftBuilt⟩ := ordinaryKey?_exists input target view left leftValid
  obtain ⟨priorR, rightBuilt⟩ := ordinaryKey?_exists input target view right rightValid
  refine ⟨priorL, priorR, leftBuilt, rightBuilt, ?_⟩
  apply sparseCompareAt_eq_prior_of_absent input target view reference W D left right
    leftValid rightValid _ _ priorL priorR leftBuilt rightBuilt
  · intro descendant path
    exact cursor_reference_absent_of_not_adjacent input source descendant incoming reference atom
      sourceReal current different sealed notAdjacent (leftPath.trans path)
  · intro descendant path
    exact cursor_reference_absent_of_not_adjacent input source descendant incoming reference atom
      sourceReal current different sealed notAdjacent (rightPath.trans path)

/-- An actual ordinary tie survives the inherited-reference promotion. The premise is an
ordinary comparison, while success and the vanishing promotion are conclusions. -/
theorem actual_tie_preserved
    (priorL priorR : input.LocalizedRerootCompoundRule45Key)
    (leftBuilt : ordinaryKey? input target view left = some priorL)
    (rightBuilt : ordinaryKey? input target view right = some priorR)
    (tie : (input.compareLocalizedRerootCompoundThroughRule5 priorL priorR).ordering = .eq) :
    sparseCompareAt? input target view reference W D left right = some .eq := by
  obtain ⟨l, r, hl, hr, comparison⟩ := actual_comparison_preserved input target view reference atom
    W D source left right incoming sourceReal current different sealed notAdjacent
    leftPath rightPath leftValid rightValid
  have lEq : l = priorL := Option.some.inj (hl.symm.trans leftBuilt)
  have rEq : r = priorR := Option.some.inj (hr.symm.trans rightBuilt)
  simpa only [lEq, rEq, tie] using comparison

end TetraStereo.OneCenter.LocalizedChemicalRingSealedReferenceComparison

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSealedReferenceComparison.actual_comparison_preserved
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSealedReferenceComparison.actual_tie_preserved
