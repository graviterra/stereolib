import TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedKey
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
Actual reference absence makes the sparse promotion column identically zero. Absence is
quantified over the reflexive-transitive closure of the shipped executable child reader;
it includes the initial cursor and every duplicate leaf, without a provenance restriction.
The builder proof derives the marker from successful recursion and sparse assembly.

At valid cursors, existing budget completeness derives the two actual builds. Their sparse
comparison then equals the existing full ordinary-key comparison. This does not replace
reference absence by history membership, or assume that earlier ordinary keys tie.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingAbsentReferenceKey

open CertifiedLocalizedCIPInput LocalizedMarkedRetainedPromotedKey
open LocalizedMarkedRetainedSparsePromotedKey LocalizedPhysicalMarkedSparseMarker

private theorem empty_getD (n index : Nat) :
    (List.replicate n ([] : Row)).getD index [] = [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq]

private theorem pack_empty (width n : Nat) : packRows width (List.replicate n []) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, packRows, ih]

/-- Zero observations remain zero under the exact sparse positional assembly, including
out-of-range child and row padding. -/
theorem assemble_zero (W D : Nat) (children : List SparseMarker)
    (zero : ∀ marker ∈ children, marker = List.replicate (D + 1) []) :
    assemble W D 0 children = List.replicate (D + 1) [] := by
  have atSlot (slot level : Nat) : (children.getD slot []).getD level [] = [] := by
    by_cases present : slot < children.length
    · rw [List.getD_eq_get children [] ⟨slot, present⟩,
        zero _ (List.get_mem children ⟨slot, present⟩)]
      exact empty_getD _ _
    · rw [List.getD_eq_default children [] (Nat.le_of_not_gt present)]
      rfl
  simp only [assemble, ite_true, atSlot, List.map_const', List.length_range,
    pack_empty, List.replicate_succ]

private theorem mapM_mem {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys →
      ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], ys, h => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      simp
  | x :: xs, ys, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨y, hy, rest, hrest, rfl⟩ := h
      intro z member
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨x, List.mem_cons_self, hy⟩
      · obtain ⟨w, wMem, hw⟩ := mapM_mem f xs rest hrest z tail
        exact ⟨w, List.mem_cons_of_mem _ wMem, hw⟩

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
  (target : input.LocalizedCIPOccurrence carrierFuel)
  (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D : Nat)

/-- Every successful actual sparse build with zero reference observations throughout its
actual cursor subtree has the same empty sparse marker, for arbitrary fuel and layout. -/
theorem sparseBuild_marker_zero : ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : SparseKey input),
    (∀ descendant, Relation.ReflTransGen (E input) cursor descendant →
      referenceBit input reference descendant = 0) →
    sparseBuild? input target view reference W D fuel cursor = some key →
      key.marker = List.replicate (D + 1) []
  | 0, cursor, key, absent, built => by
      simp only [sparseBuild?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
      obtain ⟨prior, _, children, _, rest⟩ := built
      split at rest
      · cases Option.some.inj rest
        rw [absent cursor .refl]
        exact assemble_zero W D [] (by simp)
      · cases rest
  | fuel + 1, cursor, key, absent, built => by
      simp only [sparseBuild?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
      obtain ⟨prior, _, children, childrenEq, keys, keysEq, same⟩ := built
      cases Option.some.inj same
      rw [absent cursor .refl]
      apply assemble_zero
      intro marker member
      obtain ⟨sortedKey, sortedMember, rfl⟩ := List.mem_map.mp member
      have original : sortedKey ∈ keys :=
        (List.perm_insertionSort _ keys).mem_iff.mp sortedMember
      obtain ⟨child, childMember, childBuilt⟩ := mapM_mem _ children keys keysEq sortedKey original
      apply sparseBuild_marker_zero fuel child sortedKey _ childBuilt
      intro descendant path
      apply absent descendant
      have edge : E input cursor child := by
        have sameChildren := Option.some.inj
          (childrenEq.symm.trans (input.executableLocalizedRerootChildren?_eq_some cursor))
        change child ∈ input.executableLocalizedRerootChildren cursor
        rw [← sameChildren]
        exact childMember
      exact (Relation.ReflTransGen.single edge).trans path

/-- Atom absence, including duplicate occurrences, discharges the bit condition used by
the actual sparse-builder induction. -/
theorem sparseBuild_marker_zero_of_absent (fuel : Nat)
    (cursor : input.LocalizedRerootCursor carrierFuel) (key : SparseKey input)
    (absent : ∀ descendant, Relation.ReflTransGen (E input) cursor descendant →
      descendant.occurrence.1.node.current? ≠ some reference)
    (built : sparseBuild? input target view reference W D fuel cursor = some key) :
    key.marker = List.replicate (D + 1) [] :=
  sparseBuild_marker_zero input target view reference W D fuel cursor key
    (fun descendant path => by simp only [referenceBit, if_neg (absent descendant path)]) built

private theorem compare_empty (n : Nat) :
    compareMarker (List.replicate n []) (List.replicate n []) = .eq := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change compareMarker (List.replicate n []) (List.replicate n []) = .eq
      exact ih

/-- With absence on both actual subtrees, sparse promotion cannot change any ordinary
comparison result. The two successful keys are produced by the actual builders. -/
theorem compareSparse_eq_prior_of_absent (left right : input.LocalizedRerootCursor carrierFuel)
    (fuelL fuelR : Nat) (l r : SparseKey input)
    (leftAbsent : ∀ descendant, Relation.ReflTransGen (E input) left descendant →
      descendant.occurrence.1.node.current? ≠ some reference)
    (rightAbsent : ∀ descendant, Relation.ReflTransGen (E input) right descendant →
      descendant.occurrence.1.node.current? ≠ some reference)
    (leftBuilt : sparseBuild? input target view reference W D fuelL left = some l)
    (rightBuilt : sparseBuild? input target view reference W D fuelR right = some r) :
    compareSparse input l r =
      (input.compareLocalizedRerootCompoundThroughRule5 l.prior r.prior).ordering := by
  unfold compareSparse
  rw [sparseBuild_marker_zero_of_absent input target view reference W D fuelL left l leftAbsent leftBuilt,
    sparseBuild_marker_zero_of_absent input target view reference W D fuelR right r rightAbsent rightBuilt,
    compare_empty]
  cases (input.compareLocalizedRerootCompoundThroughRule5 l.prior r.prior).ordering <;> rfl

/-- At valid cursors, the shipped marker budget derives runtime success and the actual
sparse comparison is exactly the comparison of the actual ordinary keys. -/
theorem sparseCompareAt_eq_prior_of_absent
    (left right : input.LocalizedRerootCursor carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid left)
    (rightValid : input.LocalizedRerootCursorValid right)
    (leftAbsent : ∀ descendant, Relation.ReflTransGen (E input) left descendant →
      descendant.occurrence.1.node.current? ≠ some reference)
    (rightAbsent : ∀ descendant, Relation.ReflTransGen (E input) right descendant →
      descendant.occurrence.1.node.current? ≠ some reference)
    (priorL priorR : input.LocalizedRerootCompoundRule45Key)
    (leftPrior : ordinaryKey? input target view left = some priorL)
    (rightPrior : ordinaryKey? input target view right = some priorR) :
    sparseCompareAt? input target view reference W D left right =
      some (input.compareLocalizedRerootCompoundThroughRule5 priorL priorR).ordering := by
  obtain ⟨l, leftBuilt⟩ := build?_exists input target view reference W D left leftValid
  obtain ⟨r, rightBuilt⟩ := build?_exists input target view reference W D right rightValid
  have leftSparse : sparseBuild? input target view reference W D (2 * (carrierFuel + 1)) left =
      some (toSparse input l) := by rw [sparseBuild?_eq, leftBuilt]; rfl
  have rightSparse : sparseBuild? input target view reference W D (2 * (carrierFuel + 1)) right =
      some (toSparse input r) := by rw [sparseBuild?_eq, rightBuilt]; rfl
  have leftEq : l.prior = priorL := Option.some.inj
    ((build?_prior input target view reference W D _ left l leftBuilt).symm.trans leftPrior)
  have rightEq : r.prior = priorR := Option.some.inj
    ((build?_prior input target view reference W D _ right r rightBuilt).symm.trans rightPrior)
  unfold sparseCompareAt?
  rw [leftSparse, rightSparse]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [compareSparse_eq_prior_of_absent input target view reference W D left right _ _
    (toSparse input l) (toSparse input r) leftAbsent rightAbsent leftSparse rightSparse]
  change some (input.compareLocalizedRerootCompoundThroughRule5 l.prior r.prior).ordering = _
  rw [leftEq, rightEq]

/-- An actual ordinary tie survives promotion when neither entire cursor subtree carries
the reference. Success follows from cursor validity, not an assumed promoted build. -/
theorem sparseCompareAt_tie_of_absent
    (left right : input.LocalizedRerootCursor carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid left)
    (rightValid : input.LocalizedRerootCursorValid right)
    (leftAbsent : ∀ descendant, Relation.ReflTransGen (E input) left descendant →
      descendant.occurrence.1.node.current? ≠ some reference)
    (rightAbsent : ∀ descendant, Relation.ReflTransGen (E input) right descendant →
      descendant.occurrence.1.node.current? ≠ some reference)
    (priorL priorR : input.LocalizedRerootCompoundRule45Key)
    (leftPrior : ordinaryKey? input target view left = some priorL)
    (rightPrior : ordinaryKey? input target view right = some priorR)
    (tie : (input.compareLocalizedRerootCompoundThroughRule5 priorL priorR).ordering = .eq) :
    sparseCompareAt? input target view reference W D left right = some .eq := by
  rw [sparseCompareAt_eq_prior_of_absent input target view reference W D left right leftValid rightValid
    leftAbsent rightAbsent priorL priorR leftPrior rightPrior, tie]

end TetraStereo.OneCenter.LocalizedChemicalRingAbsentReferenceKey

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAbsentReferenceKey.assemble_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAbsentReferenceKey.sparseBuild_marker_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAbsentReferenceKey.sparseBuild_marker_zero_of_absent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAbsentReferenceKey.compareSparse_eq_prior_of_absent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAbsentReferenceKey.sparseCompareAt_eq_prior_of_absent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAbsentReferenceKey.sparseCompareAt_tie_of_absent
