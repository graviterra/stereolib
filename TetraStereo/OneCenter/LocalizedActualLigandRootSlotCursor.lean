import TetraStereo.OneCenter.LocalizedActualPhysicalReferenceObservationClosure
import TetraStereo.OneCenter.LocalizedTetrahedralRootDoubleBondBound
import TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The frame slots of the final occurrence are the ligand-root cursors

The production path evaluates the four ligands of a detected centre at the cursors of the actual
four-ligand frame (`LocalizedOccurrenceFourLigandFrame.cursorAt`), while the original-root arm
package (`OriginalRootArm`) is built at `localizedLigandRootCursor center index`.  This module
identifies the two:

* `fourLigandFrame_cursors_eq` — the frame's cursor list is the executable child list of the root
  cursor of the final occurrence;
* `exists_cursorAt_eq_localizedLigandRootCursor` — for every ligand index there is a frame slot
  whose cursor is literally the ligand-root cursor (same occurrence, same incoming parent);
* `localizedLigandRootCursor_injective` — distinct indices give distinct cursors, so the
  index-to-slot assignment is a bijection of the four slots.

Nothing about labels, stages, references or readers occurs here.
-/

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

/-- The successful four-ligand frame lists exactly the executable children of the root cursor. -/
theorem fourLigandFrame_cursors_eq {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    frame.cursors =
      input.executableLocalizedRerootChildren
        ({ occurrence := target, previous? := none } : input.LocalizedRerootCursor carrierFuel) := by
  have decl := input.localizedOccurrenceFourLigandFrame?_sound target frame computed
  have h := (input.localizedOccurrenceLigandFrame?_eq_some_iff target frame.cursors).2 decl.1
  rw [localizedOccurrenceLigandFrame?, localizedRerootChildren?_eq_some_executable] at h
  exact (Option.some.inj h).symm

/-- The ligand-root cursors of distinct indices are distinct (their nodes carry distinct
canonical ligand atoms). -/
theorem localizedLigandRootCursor_injective (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) :
    Function.Injective (input.localizedLigandRootCursor center) := by
  intro i j h
  have hnode := congrArg (fun cursor : input.LocalizedRerootCursor _ =>
    cursor.occurrence.1.node.current?) h
  simp only [localizedLigandRootCursor_node, localizedLigandRootNode,
    OfficialCIPNode.extend, Option.some.injEq] at hnode
  exact input.canonicalLigandAtom_injective center hnode

section Physical

variable (input : LocalizedUniversalReference.Input)
  (c : input.certified.detectedMultiCenterMolecule.Center)

/-- The final occurrence of the detected centre is the atom-root occurrence of the centre atom. -/
theorem topTarget_eq_localizedAtomRootOccurrence
    (center : input.certified.TetrahedralCenter) (hcenter : center.1 = c.1) :
    ActualReaderPhysicalBranchInverse.topTarget input c =
      input.certified.localizedAtomRootOccurrence
        (input.certified.certified.input.molecule.atomCount + 1) center.1 := by
  apply Subtype.ext
  apply LocalizedCIPOccurrenceFrame.ext
  · rw [ActualReaderPhysicalBranchInverse.topTarget_root, localizedAtomRootOccurrence_root]
    exact hcenter.symm
  · rw [ActualReaderPhysicalBranchInverse.topTarget_address]; rfl
  · show (input.certified.localizedFinalOccurrence _ ⟨c.1, c.2⟩).1.node = OfficialCIPNode.root center.1
    rw [AuxiliaryContextIntegrity.localizedFinalOccurrence_node, hcenter]
  · show (input.certified.localizedFinalOccurrence _ ⟨c.1, c.2⟩).1.remaining = _
    rw [AuxiliaryContextIntegrity.localizedFinalOccurrence_remaining]
    rfl

/-- **Every ligand-root cursor is a frame slot.**  For each ligand index there is a slot of the
actual four-ligand frame whose cursor is the ligand-root cursor of that index. -/
theorem exists_cursorAt_eq_localizedLigandRootCursor
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (center : input.certified.TetrahedralCenter) (hcenter : center.1 = c.1) (index : Fin 4) :
    ∃ slot : Fin 4,
      frame.cursorAt slot = input.certified.localizedLigandRootCursor center index := by
  set target := ActualReaderPhysicalBranchInverse.topTarget input c with htarget
  set ligand := input.certified.localizedLigandRootCursor center index with hligand
  have memOutward : ligand.occurrence.1 ∈
      input.certified.localizedCarrierOutwardChildFrames
        (fuel := LocalizedUniversalReference.carrierFuel input) target.1 := by
    rw [localizedCarrierOutwardChildFrames, List.mem_filter]
    refine ⟨ligand.occurrence.2, ?_⟩
    rw [htarget, ActualReaderPhysicalBranchInverse.topTarget_root,
      ActualReaderPhysicalBranchInverse.topTarget_address, hligand,
      localizedLigandRootCursor_root, localizedLigandRootCursor_address, hcenter]
    simp
  have memIntended : ligand.occurrence.1 ∈
      input.certified.intendedLocalizedRerootChildFrames
        ({ occurrence := target, previous? := none } :
          input.certified.LocalizedRerootCursor (LocalizedUniversalReference.carrierFuel input)) := by
    rw [intendedLocalizedRerootChildFrames_eq_outwardChildFrames_of_address_nil input.certified
      target (ActualReaderPhysicalBranchInverse.topTarget_address input c)]
    exact memOutward
  have cursorsEq := fourLigandFrame_cursors_eq target frame frameComputed
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.1 memIntended
  have lengthEq : (input.certified.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } :
        input.certified.LocalizedRerootCursor (LocalizedUniversalReference.carrierFuel input))).length =
      (input.certified.intendedLocalizedRerootChildFrames
        ({ occurrence := target, previous? := none } :
          input.certified.LocalizedRerootCursor (LocalizedUniversalReference.carrierFuel input))).length := by
    rw [executableLocalizedRerootChildren, List.length_map, List.length_attach]
  have hk4 : k < 4 := by
    have := frame.length_eq
    rw [cursorsEq, lengthEq] at this
    omega
  refine ⟨⟨k, hk4⟩, ?_⟩
  have prevEq := topTarget_eq_localizedAtomRootOccurrence input c center hcenter
  have cursorEq : (input.certified.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } :
        input.certified.LocalizedRerootCursor (LocalizedUniversalReference.carrierFuel input)))[k]'(by
          rw [lengthEq]; exact hk) = ligand := by
    simp only [executableLocalizedRerootChildren, List.getElem_map, List.getElem_attach]
    apply LocalizedRerootCursor.ext
    · exact Subtype.ext hget
    · show some target = ligand.previous?
      rw [hligand, localizedLigandRootCursor_previous, htarget, prevEq]
  show frame.cursors.get _ = ligand
  rw [List.get_eq_getElem]
  simp only [Fin.val_cast]
  rw [List.getElem_of_eq cursorsEq]
  exact cursorEq

/-- The slot assigned to an index, chosen from `exists_cursorAt_eq_localizedLigandRootCursor`. -/
noncomputable def ligandSlot (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (center : input.certified.TetrahedralCenter) (hcenter : center.1 = c.1)
    (index : Fin 4) : Fin 4 :=
  Classical.choose
    (exists_cursorAt_eq_localizedLigandRootCursor input c frame frameComputed center hcenter index)

theorem cursorAt_ligandSlot (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (center : input.certified.TetrahedralCenter) (hcenter : center.1 = c.1)
    (index : Fin 4) :
    frame.cursorAt (ligandSlot input c frame frameComputed center hcenter index) =
      input.certified.localizedLigandRootCursor center index :=
  Classical.choose_spec
    (exists_cursorAt_eq_localizedLigandRootCursor input c frame frameComputed center hcenter index)

/-- The index-to-slot assignment is injective, hence a bijection of `Fin 4`. -/
theorem ligandSlot_injective (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (center : input.certified.TetrahedralCenter)
    (hcenter : center.1 = c.1) :
    Function.Injective (ligandSlot input c frame frameComputed center hcenter) := by
  intro i j h
  apply localizedLigandRootCursor_injective input.certified center
  rw [← cursorAt_ligandSlot input c frame frameComputed center hcenter i,
    ← cursorAt_ligandSlot input c frame frameComputed center hcenter j, h]

theorem ligandSlot_bijective (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (center : input.certified.TetrahedralCenter)
    (hcenter : center.1 = c.1) :
    Function.Bijective (ligandSlot input c frame frameComputed center hcenter) :=
  Finite.injective_iff_bijective.1 (ligandSlot_injective input c frame frameComputed center hcenter)

end Physical

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.fourLigandFrame_cursors_eq
assert_kernel_only TetraStereo.OneCenter.localizedLigandRootCursor_injective
assert_kernel_only TetraStereo.OneCenter.topTarget_eq_localizedAtomRootOccurrence
assert_kernel_only TetraStereo.OneCenter.exists_cursorAt_eq_localizedLigandRootCursor
assert_kernel_only TetraStereo.OneCenter.cursorAt_ligandSlot
assert_kernel_only TetraStereo.OneCenter.ligandSlot_bijective
