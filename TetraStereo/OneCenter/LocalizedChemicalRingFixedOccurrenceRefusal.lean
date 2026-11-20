import TetraStereo.OneCenter.LocalizedChemicalRingWitnessPhysicalExecution
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! A fixed reference can fail at an auxiliary occurrence even when the stabilizer is
even. These lemmas use actual callback covariance at arbitrary reached histories, rather
than limiting the refusal argument to original roots. Concrete stabilizers must still be
constructed; no implication from arbitrary refusal to an odd gauge is asserted. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingFixedOccurrenceRefusal

open LocalizedChemicalRingRelabel LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingCompletenessStrict (map_eq_self_fixes)
open LocalizedMarkedOperationEvaluator (Operations markedReading?)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? rankedAtoms? atomsAt? readback?)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedConfigurationTransport (frame_length)
open LocalizedMarkedCyclicDiscardedReference (readback_length rankedAtoms_subset)
open LocalizedChemicalRingOrientationInduction (StepNoFrame descriptorWith_none_of_frame)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)

/-- A successful four-atom geometric reading cannot use an invariant ordered list if
the relabelling moves any of the four frame atoms. -/
theorem readback_none_of_fixed_list (σ : Nat → Nat) (geom : Geometry) (atoms : List Nat)
    (four : atoms.length = 4) (moved : ∃ atom ∈ atoms, σ atom ≠ atom)
    (order : Option (List Nat)) (fixed : order = order.map (List.map σ))
    (subset : ∀ ranked, order = some ranked → ∀ atom ∈ ranked, atom ∈ atoms) :
    order.bind (readback? geom) = none := by
  cases found : order with
  | none => rfl
  | some ranked =>
      rw [found, Option.map_some, Option.some.injEq] at fixed
      cases reading : readback? geom ranked with
      | none => exact reading
      | some value =>
          have length := readback_length geom ranked value reading
          have nodup := readback_nodup' geom ranked value reading
          have perm := (nodup.subperm (subset ranked found)).perm_of_length_le (by omega)
          obtain ⟨atom, member, different⟩ := moved
          exact False.elim (different (map_eq_self_fixes σ ranked fixed.symm atom (perm.mem_iff.mpr member)))

/-- Fixed occurrence, fixed reference and invariant actual auxiliary facts force marked
refusal whenever the symmetry moves a frame atom. The symmetry need not be odd. -/
theorem markedReading_none_of_fixed (mol : RawMolecule) (ops : Operations) (σ : Nat → Nat)
    (cov : Covariant mol ops σ) (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (fixedNode : mapNode σ node = node) (mark : Nat) (fixedMark : σ mark = mark)
    (state : OccurrenceAuxState) (invariant : state.Perm (state.map (mapFact σ)))
    (unique : (state.map (·.key)).Nodup) (moved : ∃ atom ∈ atoms, σ atom ≠ atom)
    (geom : Geometry) : markedReading? mol ops geom state node mark = none := by
  have fixed := cov.marked node reached atoms atoms frame (by rw [fixedNode]; exact frame)
    state state invariant unique mark
  rw [fixedNode, fixedMark] at fixed
  have refused := readback_none_of_fixed_list σ geom atoms (frame_length mol node atoms frame)
    moved ((ops.marked state node mark).bind (rankedAtoms? atoms)) fixed (by
      intro ranked success atom member
      obtain ⟨ranking, _, rankedEq⟩ := Option.bind_eq_some_iff.mp success
      exact rankedAtoms_subset atoms ranking ranked rankedEq atom member)
  simpa only [markedReading?, frame, Option.bind_some, Option.bind_assoc] using refused

/-- A child-closed region without actual frames emits no auxiliary facts, at any depth
or inherited reference. This is shared by both actual recursive evaluators. -/
theorem factsWith_nil_of_no_frames (mol : RawMolecule) (ops : Operations) (step : Step)
    (noFrame : StepNoFrame mol ops step) (P : RawMolecule.CanonicalBranchNode → Prop)
    (closed : ∀ parent child, P parent → child ∈ mol.canonicalChildren parent → P child)
    (absent : ∀ node, P node → frameAtoms? mol node = none) :
    ∀ depth geom state ctx node, P node → factsWith step mol ops depth geom state ctx node = [] := by
  intro depth
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro geom state ctx node member
      rw [factsWith_succ, descriptorWith_none_of_frame mol ops step noFrame depth geom state ctx node (absent node member)]
      simp only [Option.toList_none, List.map_nil, List.nil_append]
      rw [LocalizedGenericMarkedRecalculation.flatMap_congr_mem _ _ (fun _ => [])
        (fun child edge => ih geom state ctx child (closed node child member edge))]
      simp

theorem underWith_nil_of_no_frames (mol : RawMolecule) (ops : Operations) (step : Step)
    (noFrame : StepNoFrame mol ops step) (source : RawMolecule.CanonicalBranchNode)
    (absent : ∀ node, StrictDescendant mol source node → frameAtoms? mol node = none)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (mark : Nat) :
    LocalizedMarkedOperationEvaluator.underWith mol ops geom state source
      (factsWith step mol ops depth) mark = [] := by
  have closed : ∀ parent child, StrictDescendant mol source parent →
      child ∈ mol.canonicalChildren parent → StrictDescendant mol source child := by
    rintro parent child ⟨first, edge, rest⟩ next
    exact ⟨first, edge, rest.tail next⟩
  unfold LocalizedMarkedOperationEvaluator.underWith
  rw [LocalizedGenericMarkedRecalculation.flatMap_congr_mem _ _ (fun _ => [])
    (fun child selected => factsWith_nil_of_no_frames mol ops step noFrame
      (StrictDescendant mol source) closed absent depth geom state (some mark) child
      ⟨child, LocalizedMarkedOperationEvaluator.mem_tiedChildren_actual mol ops state source child selected, .refl⟩)]
  simp

/-- A local inherited reference fixed by a nontrivial frame symmetry refuses. The actual
distant-reference policy does not consult its fallback when that reference is in the frame. -/
theorem distantStep_none_of_fixed (mol : RawMolecule) (ops : Operations) (σ : Nat → Nat)
    (cov : Covariant mol ops σ) (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (fixedNode : mapNode σ node = node) (mark : Nat) (fixedMark : σ mark = mark)
    (present : mark ∈ atoms) (moved : ∃ atom ∈ atoms, σ atom ≠ atom) (geom : Geometry) :
    LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom [] (some mark) node (fun _ => []) = none := by
  simp only [LocalizedPhysicalMarkedDistantReference.rawStep?, frame, Option.bind_eq_bind, Option.bind_some]
  cases ordered : ops.ordinary [] node with
  | none => rfl
  | some result =>
      obtain ⟨sorted, adjacent⟩ := result
      simp only [Option.bind_some]
      split_ifs with bad strict
      · rfl
      · have covariance := cov.ordinary node reached atoms atoms frame (by rw [fixedNode]; exact frame)
        rw [fixedNode, ordered, ordinaryRel_some_some] at covariance
        exact readback_none_of_fixed_list σ geom atoms (frame_length mol node atoms frame) moved
          (atomsAt? atoms sorted) (covariance.2.2.1 strict)
          (fun ranked success => atomsAt_subset atoms sorted ranked success)
      · rw [LocalizedPhysicalMarkedDistantReference.chooseInherited_local _ _ _ _ present]
        simpa only [LocalizedPhysicalMarkedDistantReference.inheritedRead?,
          LocalizedGenericMarkedRecalculation.appendFacts?, Option.bind_some] using
          markedReading_none_of_fixed mol ops σ cov node reached atoms frame fixedNode mark
            fixedMark [] (by simp) (by simp) moved geom

end TetraStereo.OneCenter.LocalizedChemicalRingFixedOccurrenceRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFixedOccurrenceRefusal.readback_none_of_fixed_list
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFixedOccurrenceRefusal.markedReading_none_of_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFixedOccurrenceRefusal.factsWith_nil_of_no_frames
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFixedOccurrenceRefusal.underWith_nil_of_no_frames
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFixedOccurrenceRefusal.distantStep_none_of_fixed
