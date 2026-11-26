import TetraStereo.Engine.RingConstitutionalHand
import TetraStereo.Engine.RingPyramidalConstitution

/-! Atomic-number priority at every real tetrahedral occurrence. -/
set_option autoImplicit false
noncomputable section
namespace TetraStereo.Engine.RingAtomicFramePriority
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot)
open RingPyramidalConstitution (key_atomic word_lt_of_Z)
attribute [local instance] lexOrd

/-- Physical coordinate ID of the actual retained slot, including the incoming arm. -/
def slotId {i : Input} {q : Site i} (fr : Frame i q) (k : Slot) := (fr.atoms [k]).head!

private theorem slot_mem {i : Input} {q : Site i} (fr : Frame i q) (k : Slot) :
    slotId fr k ∈ RingRetainedAuxiliary.canonical i.certified fr.center := by
  apply fr.physical.mem_iff.mp
  exact List.get_mem _ _

private theorem slot_canonical {i : Input} {q : Site i} (fr : Frame i q) (k : Slot) :
    ∃ t : Slot, slotId fr k = (i.certified.canonicalLigandAtom fr.center t).val := by
  obtain ⟨t,_,eqn⟩ := List.mem_map.mp (slot_mem fr k)
  exact ⟨t,eqn.symm⟩

def slotNeighbor {i : Input} {q : Site i} (fr : Frame i q) (k : Slot) :
    i.certified.moleculeGraph.Neighbor fr.center.val :=
  i.certified.canonicalLigandNeighbor fr.center (Classical.choose (slot_canonical fr k))

theorem slotNeighbor_val {i : Input} {q : Site i} (fr : Frame i q) (k : Slot) :
    (slotNeighbor fr k).val.val = slotId fr k :=
  (Classical.choose_spec (slot_canonical fr k)).symm

theorem slot_current {i : Input} {q : Site i} (fr : Frame i q) (k : Slot) :
    (fr.arm k).occurrence.val.node.current? = some (slotNeighbor fr k).val := by
  obtain ⟨a,ha,value⟩ := Option.map_eq_some_iff.mp (fr.point_at k)
  have same : a = (slotNeighbor fr k).val := Fin.ext (value.trans (slotNeighbor_val fr k).symm)
  exact ha.trans (congrArg some same)

private theorem slot_injective {i : Input} {q : Site i} (fr : Frame i q) :
    Function.Injective (slotNeighbor fr) := by
  intro j k eqn
  have values := congrArg (fun n : i.certified.moleculeGraph.Neighbor fr.center.val => n.val.val) eqn
  dsimp only at values
  rw [slotNeighbor_val,slotNeighbor_val] at values
  have nd : fr.ids.Nodup := fr.physical.nodup_iff.mpr
    ((List.nodup_finRange 4).map (Fin.val_injective.comp (i.certified.canonicalLigandAtom_injective fr.center)))
  have same := nd.get_inj_iff.mp values
  exact Fin.ext (congrArg (fun t : Fin fr.ids.length => t.val) same)

private def slotPermutation {i : Input} {q : Site i} (fr : Frame i q)
    (enum : Slot ≃ i.certified.moleculeGraph.Neighbor fr.center.val) : Equiv.Perm Slot :=
  let f := fun k => enum.symm (slotNeighbor fr k)
  let inj := enum.symm.injective.comp (slot_injective fr)
  Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩

/-- The actual native center reading follows a physical enumeration strictly
ordered by atomic number; all subsequent recursive key components are irrelevant. -/
theorem centre_strict_atomic {i : Input}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} (fr : Frame i q) {r : Reader i} (ready : RingGroupedStereo.Ready q r)
    (enum : Slot ≃ i.certified.moleculeGraph.Neighbor fr.center.val)
    (records : Slot → AtomSpec)
    (written : ∀ k, i.molecule.atoms[(enum k).val.val]? = some (records k))
    (descending : StrictAnti (fun k => (records k).element.atomicNumber)) :
    RingFullPathPublication.centre? fr r = some
      ((readback? (inputGeometry i.certified)
        [(enum 0).val.val,(enum 1).val.val,(enum 2).val.val,(enum 3).val.val]).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  let e := slotPermutation fr enum
  have atom (k : Slot) : (slotNeighbor fr k).val = (enum (e k)).val := by
    change (slotNeighbor fr k).val = (enum (enum.symm (slotNeighbor fr k))).val
    rw [enum.apply_symm_apply]
  let cs (k : Slot) := RingRetainedChemicalPreorder.keyFor (fr.direction k)
  have native (k : Slot) := RingRetainedChemicalPreorder.read_key (fr.direction k)
  have formed (k : Slot) := (RingRetainedChemicalTrace.key_source (native k)).formed
  have z (k : Slot) : (cs k).root.atomic = (records (e k)).element.atomicNumber := by
    apply key_atomic (q := RingGroupedCentre.cursor fr k) (a := (slotNeighbor fr k).val)
    · exact slot_current fr k
    · rw [atom]; exact written (e k)
    · exact native k
  have lower {j k : Slot} (lt : e j < e k) :
      RingFullPathConstitution.word fr k < RingFullPathConstitution.word fr j :=
    word_lt_of_Z (formed k) (formed j) (by
      change (cs k).root.atomic < (cs j).root.atomic
      rw [z,z]
      exact descending lt)
  have inj : Function.Injective (RingFullPathConstitution.word fr) := by
    intro j k eqn
    by_contra ne
    rcases lt_or_gt_of_ne (e.injective.ne ne) with lt | lt
    · exact (ne_of_lt (lower lt)) eqn.symm
    · exact (ne_of_lt (lower lt)) eqn
  let row := (List.finRange 4).map e.symm
  have legal : RingStereoSiblingPass.Legal (RingFullPathConstitution.word fr) (List.finRange 4) row := by
    refine ⟨Equiv.Perm.map_finRange_perm e.symm,?_⟩
    rw [List.map_map]
    apply List.pairwise_map.mpr
    exact (List.pairwise_lt_finRange 4).imp fun {j k} h => le_of_lt (lower (by simpa using h))
  have ids : fr.atoms row = [(enum 0).val.val,(enum 1).val.val,(enum 2).val.val,(enum 3).val.val] := by
    have each (k : Slot) : slotId fr (e.symm k) = (enum k).val.val := by
      rw [←slotNeighbor_val,atom,e.apply_symm_apply]
    change [slotId fr (e.symm 0),slotId fr (e.symm 1),slotId fr (e.symm 2),slotId fr (e.symm 3)] = _
    simp only [each]
  exact RingConstitutionalHand.centre_read geom
    (RingConstitutionalHand.DescendingFrame.ranked ⟨row,inj,legal,ids⟩) ready

/-- Four physical neighbors with strictly descending written atomic numbers
determine the actual native state at roots and auxiliary real occurrences. -/
theorem state_strict_atomic {i : Input}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (a : i.certified.Atom)
    (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a)
    (enum : Slot ≃ i.certified.moleculeGraph.Neighbor a)
    (records : Slot → AtomSpec)
    (written : ∀ k, i.molecule.atoms[(enum k).val.val]? = some (records k))
    (descending : StrictAnti (fun k => (records k).element.atomicNumber)) :
    RingChemicalGraphProof.state i q = some
      ((readback? (inputGeometry i.certified)
        [(enum 0).val.val,(enum 1).val.val,(enum 2).val.val,(enum 3).val.val]).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 :=
    (Fintype.card_congr enum).symm.trans (Fintype.card_fin 4)
  let c : i.certified.TetrahedralCenter :=
    ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet a).mpr degree⟩
  have recognized : i.certified.localizedOccurrenceDescriptorCenter? q = some c :=
    (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mpr ⟨real,current⟩
  obtain ⟨fr,framed⟩ := RingGroupedGeometry.frame_exists recognized
  have center : fr.center = c := Option.some.inj (fr.recognized.symm.trans recognized)
  let changeCenter : i.certified.moleculeGraph.Neighbor a ≃
      i.certified.moleculeGraph.Neighbor fr.center.val := {
    toFun := fun n => ⟨n.val,by simpa only [center] using n.property⟩
    invFun := fun n => ⟨n.val,by simpa only [center] using n.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let enum' := enum.trans changeCenter
  have written' : ∀ k, i.molecule.atoms[(enum' k).val.val]? = some (records k) := written
  have noP : RingPyramidalPublication.focusP i q = none := by
    have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) a degree
    simp [RingPyramidalPublication.focusP,real,current,off]
  have result := centre_strict_atomic geom fr (RingChemicalGraphProof.ready geom q) enum' records written' descending
  rw [RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,noP,
    RingFullPathConstitution.fast_local geom (RingChemicalGraphProof.ready geom q),
    RingFullPathPublication.publish?,framed]
  exact result

end TetraStereo.Engine.RingAtomicFramePriority

assert_kernel_only TetraStereo.Engine.RingAtomicFramePriority.slot_current
assert_kernel_only TetraStereo.Engine.RingAtomicFramePriority.centre_strict_atomic
assert_kernel_only TetraStereo.Engine.RingAtomicFramePriority.state_strict_atomic
