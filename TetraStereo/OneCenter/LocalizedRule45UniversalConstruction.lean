import TetraStereo.OneCenter.LocalizedOccurrenceRule45Descriptor
import TetraStereo.OneCenter.LocalizedOccurrenceRule45Exact
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Executable

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Universal Rule-4a--5 compound-key construction at the occurrence evaluation fuel

`LocalizedRerootFuelCompleteness` proves that every path-valid reroot cursor admits a complete
Rules-4a--5 compound key once the evaluation fuel is twice the carrier depth.  The occurrence
evaluator is parameterized by the *named* fuel
`localizedOccurrenceRerootEvaluationFuel carrierFuel`
(`LocalizedOccurrenceRule45Descriptor`), which is that same quantity by definition.

This module

* bridges the two fuels and states universal key existence directly at the named fuel;
* attaches the canonical meaning of the returned key for an arbitrary dependency view;
* transfers existence and meaning to the executable compiler
  `buildLocalizedRerootCompoundRule45KeyExec?`, whose six wrappers are computationally transparent
  (`LocalizedRerootCompoundRule45Executable`);
* lifts existence/meaning to a list of valid cursors and to every indexed cursor of a
  declaratively valid four-ligand occurrence frame.

Nothing here assumes any property of the dependency view: the view is an arbitrary parameter.  The
only structural hypothesis is `LocalizedRerootCursorValid`, i.e. that the cursor's incoming
coordinate is absent or is a tree neighbor of the occurrence from which it was reached.

The results concern **key construction only**.  They do not assert that two ligands are
distinguished: `compareLocalizedRerootCompoundThroughRule5` may still return `Ordering.eq`, and a
descriptor additionally needs the strict all-pairs order and rational geometry.  See the final
section for the exact boundary.
-/

namespace CertifiedLocalizedCIPInput

/-! ## Key existence at the named occurrence evaluation fuel -/

/-- Every path-valid reroot cursor admits a complete Rules-4a--5 compound key at the fuel actually
used by the occurrence evaluator.  This is the named-fuel form of
`exists_buildLocalizedRerootCompoundRule45Key?_at_twice`; the two fuels are definitionally
equal.  No chemical-label or dependency-view hypothesis is used. -/
theorem exists_buildLocalizedRerootCompoundRule45Key?_at_evaluationFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor = some key := by
  simpa only [localizedOccurrenceRerootEvaluationFuel] using
    input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice target view cursor valid

/-- Fuel is never the reason the occurrence compound compiler fails on a valid cursor. -/
theorem buildLocalizedRerootCompoundRule45Key?_ne_none_at_evaluationFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor ≠ none := by
  obtain ⟨key, computed⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45Key?_at_evaluationFuel
      target view cursor valid
  rw [computed]
  exact Option.some_ne_none key

/-- The key whose existence is guaranteed at the evaluation fuel carries the full canonical
Rules-4a--5 meaning: the compound Rules-4b/4c key is canonical (exact Rule-4a cumulative key, exact
P-92 reference selection, exact reference-count priority, and the pointwise canonical
no/one/`[R,S]` alternatives) and both common-reference Rule-5 reading lists are canonical. -/
theorem exists_canonical_buildLocalizedRerootCompoundRule45Key?_at_evaluationFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key,
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor = some key ∧
        input.CanonicalLocalizedRerootCompoundRule45Key target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor key := by
  obtain ⟨key, computed⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45Key?_at_evaluationFuel
      target view cursor valid
  exact ⟨key, computed,
    (input.buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor key).mp
      computed⟩

/-! ## Transfer to the executable compiler -/

/-- The executable compound Rules-4a--5 compiler also succeeds at the named evaluation fuel on
every valid cursor. -/
theorem exists_buildLocalizedRerootCompoundRule45KeyExec?_at_evaluationFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootCompoundRule45KeyExec? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor = some key := by
  obtain ⟨key, computed⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45Key?_at_evaluationFuel
      target view cursor valid
  exact ⟨key, by
    rw [← input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]
    exact computed⟩

/-- The executable compiler never fails at the named evaluation fuel on a valid cursor. -/
theorem buildLocalizedRerootCompoundRule45KeyExec?_ne_none_at_evaluationFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    input.buildLocalizedRerootCompoundRule45KeyExec? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor ≠ none := by
  obtain ⟨key, computed⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45KeyExec?_at_evaluationFuel
      target view cursor valid
  rw [computed]
  exact Option.some_ne_none key

/-- Every key the executable compiler returns at the evaluation fuel is canonical.  The executable
wrappers return exactly the noncomputable keys, so their meaning is inherited without any extra
assumption. -/
theorem exists_canonical_buildLocalizedRerootCompoundRule45KeyExec?_at_evaluationFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key,
      input.buildLocalizedRerootCompoundRule45KeyExec? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor = some key ∧
        input.CanonicalLocalizedRerootCompoundRule45Key target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor key := by
  obtain ⟨key, computed⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45KeyExec?_at_evaluationFuel
      target view cursor valid
  refine ⟨key, computed, ?_⟩
  exact (input.buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
    target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor key).mp (by
      rw [input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]
      exact computed)

/-- A whole list of valid cursors is compiled executably at the evaluation fuel, with the exact
list length preserved.  This is the reusable form of the map over a four-ligand frame. -/
theorem exists_mapM_buildLocalizedRerootCompoundRule45KeyExec?_of_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, input.LocalizedRerootCursorValid cursor) →
      ∃ keys,
        cursors.mapM (input.buildLocalizedRerootCompoundRule45KeyExec? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)) = some keys ∧
        keys.length = cursors.length
  | [], _ => ⟨[], rfl, rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, keyComputed⟩ :=
        input.exists_buildLocalizedRerootCompoundRule45KeyExec?_at_evaluationFuel
          target view cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed, keysLength⟩ :=
        input.exists_mapM_buildLocalizedRerootCompoundRule45KeyExec?_of_valid
          target view cursors (fun child present => valid child (by simp [present]))
      refine ⟨key :: keys, ?_, by simp [keysLength]⟩
      simp [List.mapM_cons, keyComputed, keysComputed]

/-! ## Integration with the four-ligand occurrence frame -/

/-- Every indexed cursor of a declaratively valid four-ligand frame has an executable canonical
compound key at the evaluation fuel.  The frame's declarative meaning supplies the parent step,
hence structural cursor validity, for each child. -/
theorem exists_buildLocalizedRerootCompoundRule45KeyExec?_cursorAt_at_evaluationFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (index : Fin 4) :
    ∃ key,
      input.buildLocalizedRerootCompoundRule45KeyExec? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)
          (frame.cursorAt index) = some key ∧
        input.CanonicalLocalizedRerootCompoundRule45Key target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)
          (frame.cursorAt index) key := by
  exact input.exists_canonical_buildLocalizedRerootCompoundRule45KeyExec?_at_evaluationFuel
    target view (frame.cursorAt index)
    (LocalizedOccurrenceFourLigandFrame.cursorAt_valid input target frame derived index)

/-- For any ordered pair of frame ligands, the executable compiler produces two canonical
compound keys and the tracked Rule-5 comparison record of those keys.  The record is produced by
the pure comparator; whether it is `eq` (a genuine tie) is a separate question. -/
theorem exists_executableComparison_of_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (left right : Fin 4) :
    ∃ leftKey rightKey result,
      input.buildLocalizedRerootCompoundRule45KeyExec? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)
          (frame.cursorAt left) = some leftKey ∧
        input.buildLocalizedRerootCompoundRule45KeyExec? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)
          (frame.cursorAt right) = some rightKey ∧
        input.CanonicalLocalizedRerootCompoundRule45Key target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)
          (frame.cursorAt left) leftKey ∧
        input.CanonicalLocalizedRerootCompoundRule45Key target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)
          (frame.cursorAt right) rightKey ∧
        result = localizedOccurrenceRule45ComparisonRecord
          (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey) := by
  obtain ⟨leftKey, leftComputed, leftCanonical⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45KeyExec?_cursorAt_at_evaluationFuel
      target view frame derived left
  obtain ⟨rightKey, rightComputed, rightCanonical⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45KeyExec?_cursorAt_at_evaluationFuel
      target view frame derived right
  exact ⟨leftKey, rightKey,
    localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey),
    leftComputed, rightComputed, leftCanonical, rightCanonical, rfl⟩

/-- The noncomputable occurrence pair evaluator cannot refuse for lack of reroot fuel once the
four-ligand frame is declared.  This restates
`exists_compareLocalizedOccurrenceThroughRule5At?_of_frame` in no-failure form; refusal can only
come from a genuine tie/cycle or from a later geometry/applicability gate. -/
theorem compareLocalizedOccurrenceThroughRule5At?_ne_none_of_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (left right : Fin 4) :
    input.compareLocalizedOccurrenceThroughRule5At?
      target view frame left right ≠ none := by
  obtain ⟨result, computed⟩ :=
    input.exists_compareLocalizedOccurrenceThroughRule5At?_of_frame
      target view frame derived left right
  rw [computed]
  exact Option.some_ne_none result

/-! ## Does key existence imply ligand distinction?

No.  The statements above construct keys and comparison records; they say nothing about the
`ordering` field.  A tie `Ordering.eq` is compatible with every theorem in this module, because
the comparator is a function of the two keys and no hypothesis here separates them.  Ligand
distinction requires additional, independent structure:

* the strict all-pairs witness of `CanonicalSafeLocalizedOccurrenceRule45TrackedOrder`, whose
  `Pairwise` component demands `Ordering.gt` for every earlier/later pair; and
* for an actual descriptor, the rational tetrahedral geometry
  `RationalTetrahedralDescriptor` of the emitted points.

Those are exactly the layers that `LocalizedOccurrenceRule45Exact` characterizes (including the
`none`-iff-no-canonical directions).  In particular, no declaration in this module asserts
`compareLocalizedRerootCompoundThroughRule5 left right ≠ Ordering.eq` or
`localizedOccurrenceRule45Descriptor? = some _`; doing so from cursor validity alone would be
unsound.
-/

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
