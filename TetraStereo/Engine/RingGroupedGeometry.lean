import TetraStereo.Engine.RingGroupedPublication
import TetraStereo.OneCenter.LocalizedSimpleBondFourLigandFrames

set_option autoImplicit false

namespace TetraStereo.Engine.RingGroupedGeometry
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame)
open RingActivePairReport (Slot)
open LocalizedChemicalRingPhysicalSense (inputGeometry inputGeometry_val)

private theorem four_eta {α : Type} (xs : List α) {n} (size : xs.length = n) :
    (List.finRange n).map (fun k => xs.get (Fin.cast size.symm k)) = xs := by
  subst n
  exact List.map_get_finRange xs

/-- Even when this is a rerooted occurrence in a ring, the retained frame
contains exactly the four distinct canonical coordinate carriers. -/
theorem frame_exists {i : Input} {q : Site i} {c : i.certified.TetrahedralCenter}
    (recognized : i.certified.localizedOccurrenceDescriptorCenter? q = some c) :
    ∃ fr, RingNestedActivePair.frame? i q = some fr := by
  obtain ⟨frame,alpha,hf,atSlot⟩ := i.certified.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_ligandPermutation_of_recognition
    i.single (Nat.le_succ _) q c recognized
  have same : frame.cursors = RingRetainedAuxiliary.frame i.certified q :=
    i.certified.localizedOccurrenceFourLigandFrame_cursors_eq_executable q frame hf
  have four := (congrArg List.length same).symm.trans frame.length_eq
  let sigma : Equiv.Perm Slot := alpha.trans (i.certified.canonicalLigandReindex c)
  let atom (k : Slot) := (i.certified.canonicalLigandAtom c k).val
  have physical (k : Slot) : (frame.cursorAt k).occurrence.val.node.current?.map Fin.val = some (atom (sigma k)) := by
    rw [atSlot k,i.certified.canonicalLigandReindex_spec]; rfl
  let ids := (List.finRange 4).map fun k => atom (sigma k)
  have read : (RingRetainedAuxiliary.frame i.certified q).mapM (fun t => t.occurrence.val.node.current?.map Fin.val) = some ids := by
    have eta : (List.finRange 4).map frame.cursorAt = frame.cursors := four_eta _ frame.length_eq
    rw [← same,← eta,List.mapM_map]
    change (List.finRange 4).mapM (fun k => (frame.cursorAt k).occurrence.val.node.current?.map Fin.val) = some ids
    simp only [physical]; rfl
  have perm : ids.Perm (RingRetainedAuxiliary.canonical i.certified c) := by
    simpa only [List.map_map,Function.comp_def] using (sigma.map_finRange_perm.map atom)
  let fr : Frame i q := ⟨c,recognized,four,ids,read,perm⟩
  exact ⟨fr,by simp [RingNestedActivePair.frame?,Option.attach_eq_some _ ⟨c,recognized⟩,four,
    Option.attach_eq_some _ ⟨ids,read⟩,perm,fr]⟩

theorem calibrated {i : Input} (coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true) {q : Site i}
    (fr : Frame i q) : RingGroupedTrials.Calibrated fr := by
  let c := fr.center
  let atom (k : Slot) := (i.certified.canonicalLigandAtom c k).val
  obtain ⟨points,observed,nonzero,_⟩ := LocalizedChemicalRingPhysicalAdmission.canonical_all_calibrated i.certified coordinates c
  have point (k : Slot) : inputGeometry i.certified (atom k) = some (points k) := (inputGeometry_val i.certified _).trans (observed k)
  have original : (readback? (inputGeometry i.certified) (RingRetainedAuxiliary.canonical i.certified c)).isSome = true := by
    change (readback? _ [atom 0,atom 1,atom 2,atom 3]).isSome = true
    rcases lt_or_gt_of_ne nonzero with neg | pos
    · simp [readback?,point,descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,neg]
    · simp [readback?,point,descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,pos,not_lt.mpr pos.le]
  have nd : (RingRetainedAuxiliary.canonical i.certified c).Nodup :=
    (List.nodup_finRange 4).map (Fin.val_injective.comp (i.certified.canonicalLigandAtom_injective c))
  intro ss hs
  apply RingChemicalPriority.ReferenceFrame.readback_all_permutations nd (by simp [RingRetainedAuxiliary.canonical]) original
  have same : (fr.atoms (List.finRange 4)) = fr.ids := four_eta _ (by simpa [RingRetainedAuxiliary.canonical] using fr.physical.length_eq)
  exact ((hs.map _).trans (List.Perm.of_eq same)).trans fr.physical

theorem physical {i : Input} (coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingGroupedPublication.Physical i := by
  intro q c recog
  obtain ⟨fr,ok⟩ := frame_exists recog
  exact ⟨fr,ok,calibrated coordinates fr⟩

end TetraStereo.Engine.RingGroupedGeometry
assert_kernel_only TetraStereo.Engine.RingGroupedGeometry.physical
