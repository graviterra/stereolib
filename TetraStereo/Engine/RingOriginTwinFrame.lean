import TetraStereo.Engine.RingOriginTwinLeaves

/-! Graph witnesses for terminal twin directions in actual tetrahedral frames. -/
set_option autoImplicit false
noncomputable section
namespace TetraStereo.Engine.RingOriginTwinFrame
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Frame Reader)
open RingHydrogenSpelling (TwinPair path_avoids_terminal_leaf)
open RingHydrogenLeafGeometry (SupportedLeaf)
open RingGroupedCentre (cursor)
open private word from TetraStereo.Engine.RingOriginPriorityStore
open private slot_injective from TetraStereo.Engine.RingAtomicFramePriority

/-- Every physical neighbor is represented by one actual frame slot. -/
theorem slot_exists {i : Input} {f : Site i} (fr : Frame i f)
    (a : i.certified.Atom) (adj : i.certified.moleculeGraph.Adj fr.center.val a) :
    ∃ k : Fin 4, (fr.arm k).occurrence.val.node.current? = some a := by
  have bij : Function.Bijective (RingAtomicFramePriority.slotNeighbor fr) := by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    exact ⟨slot_injective fr,Fintype.card_congr
      (Equiv.ofBijective (i.certified.canonicalLigandNeighbor fr.center)
        (i.certified.canonicalLigandNeighbor_bijective fr.center))⟩
  obtain ⟨k,hk⟩ := bij.2 ⟨a,adj⟩
  exact ⟨k,(RingAtomicFramePriority.slot_current fr k).trans
    (congrArg some (congrArg Subtype.val hk))⟩

/-- At a physical terminal neighbor away from the root the actual slot is real,
and removing its incoming coordinate leaves no child. -/
theorem terminal_slot {i : Input} {f : Site i} (fr : Frame i f)
    (leaf : i.certified.Atom) (support : SupportedLeaf i leaf fr.center.val)
    (off : f.val.root ≠ leaf) (k : Fin 4)
    (current : (fr.arm k).occurrence.val.node.current? = some leaf) :
    (cursor fr k).occurrence.val.node.provenance = .realAtom ∧
    i.certified.executableLocalizedRerootChildren (cursor fr k) = [] := by
  obtain ⟨real,atCenter⟩ := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff f fr.center).mp fr.recognized
  obtain ⟨a,atA,path⟩ := RingGraphPaths.site_path f real
  have eqn : a = fr.center.val := Option.some.inj (atA.symm.trans atCenter)
  subst a
  have different : fr.center.val ≠ leaf := by
    intro same
    have edge := (support fr.center.val).mpr rfl
    rw [←same] at edge
    simp [MoleculeGraph.Adj,i.certified.moleculeGraph.bond_self] at edge
  have fresh := path_avoids_terminal_leaf support path off different
  have member : fr.arm k ∈ RingRetainedAuxiliary.frame i.certified f := List.get_mem ..
  have childReal := (RingPyramidalPathProvenance.arm_endpoint f fr.center.val leaf real atCenter
    (fr.arm k) member current).1.mpr (Or.inr fresh)
  have neighbor : (cursor fr k).occurrence.val ∈ i.certified.localizedRerootNeighborFrames
      (fuel := i.certified.certified.input.molecule.atomCount + 1) f.val := RingGroupedCentre.valid fr k
  have reverse := i.certified.mem_localizedRerootNeighborFrames_symm f _ neighbor
  have guard := RingSecondShellIncidence.realGuard i i.single (cursor fr k) f rfl reverse
    fr.center.val leaf childReal current atCenter
  have empty : (i.certified.moleculeGraph.neighborFinset leaf).erase fr.center.val = ∅ := by
    ext a
    simp only [Finset.mem_erase,Finset.notMem_empty,iff_false,not_and]
    intro ne adj
    exact ne ((support a).mp ((MoleculeGraph.mem_neighborFinset _ _ _).mp adj))
  have length := guard.physical.length_eq
  simp only [empty,Finset.toList_empty,List.length_nil,List.length_map] at length
  exact ⟨childReal,List.eq_nil_of_length_eq_zero length⟩

/-- A ready frozen reader supplies successful known absences at these actual
terminal directions; their entire active keys therefore coincide. -/
theorem twin_keys {i : Input} (p : TwinPair i) {f : Site i} (fr : Frame i f)
    (center : fr.center = p.c) (offU : f.val.root ≠ p.u) (offV : f.val.root ≠ p.v)
    (read : Reader i) (ready : RingGroupedStereo.Ready f read) (rev : Bool)
    (u v : Fin 4)
    (atU : (fr.arm u).occurrence.val.node.current? = some p.u)
    (atV : (fr.arm v).occurrence.val.node.current? = some p.v) :
    RingSingleCycleComparison.rebuilt i f (cursor fr u) =
      RingSingleCycleComparison.rebuilt i f (cursor fr v) ∧
    RingOriginFullKeys.active i f read rev (cursor fr u) =
      RingOriginFullKeys.active i f read rev (cursor fr v) := by
  have su : SupportedLeaf i p.u fr.center.val := center.symm ▸ p.supportU
  have sv : SupportedLeaf i p.v fr.center.val := center.symm ▸ p.supportV
  obtain ⟨ru,lu⟩ := terminal_slot fr p.u su offU u atU
  obtain ⟨rv,lv⟩ := terminal_slot fr p.v sv offV v atV
  have reads (k : Fin 4) (empty : i.certified.executableLocalizedRerootChildren (cursor fr k) = []) :
      read (cursor fr k).occurrence = some none := by
    obtain ⟨labels,seen,_,terminal⟩ := ready (cursor fr k) (fr.direction k).property.1
    exact seen.trans (congrArg some (terminal empty))
  exact ⟨RingOriginTwinLeaves.twin_rebuilt_eq p f _ _ lu lv atU atV ru rv,
    RingOriginTwinLeaves.twin_active_eq p f read rev _ _ lu lv (reads u lu) (reads v lv) atU atV ru rv⟩

/-- Actual frozen coordinate states read every terminal atom as a completed
absence, even when its address lies in a deeper visible batch. -/
theorem frozen_terminal {i : Input} (stateGeometry : LocalizedGenericMarkedRecalculation.Geometry)
    (f t : Site i) (sameRoot : t.val.root = f.val.root)
    (a : i.certified.Atom) (atA : t.val.node.current? = some a)
    (degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 1) :
    RingActiveDistanceSchedule.frozen (RingFrameTransport.stateG i stateGeometry) f t = some none := by
  have no : ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) t := by
    rintro ⟨_,b,atB,eligible⟩
    have eqn : b = a := Option.some.inj (atB.symm.trans atA)
    subst b
    rw [LeafAllRequests.terminal_ineligible i a degree] at eligible
    contradiction
  have empty := (RingFrameTransport.stateG_eq i stateGeometry t).trans
    (RingFrameTransport.skipsG i stateGeometry t _ no)
  simp [RingActiveDistanceSchedule.frozen,sameRoot,empty]

/-- Full active key equality on the evaluator's actual frozen state. -/
theorem frozen_twin_keys {i : Input} (p : TwinPair i) {f : Site i} (fr : Frame i f)
    (center : fr.center = p.c) (offU : f.val.root ≠ p.u) (offV : f.val.root ≠ p.v)
    (g : LocalizedGenericMarkedRecalculation.Geometry) (rev : Bool) (u v : Fin 4)
    (atU : (fr.arm u).occurrence.val.node.current? = some p.u)
    (atV : (fr.arm v).occurrence.val.node.current? = some p.v) :
    RingOriginFullKeys.active i f (RingActiveDistanceSchedule.frozen (RingFrameTransport.stateG i g) f)
      rev (cursor fr u) =
    RingOriginFullKeys.active i f (RingActiveDistanceSchedule.frozen (RingFrameTransport.stateG i g) f)
      rev (cursor fr v) := by
  obtain ⟨ru,lu⟩ := terminal_slot fr p.u (center.symm ▸ p.supportU) offU u atU
  obtain ⟨rv,lv⟩ := terminal_slot fr p.v (center.symm ▸ p.supportV) offV v atV
  apply RingOriginTwinLeaves.twin_active_eq p f _ rev _ _ lu lv
    (frozen_terminal g f _ (fr.direction u).property.1 p.u atU p.supportU.degree_one)
    (frozen_terminal g f _ (fr.direction v).property.1 p.v atV p.supportV.degree_one) atU atV ru rv

/-- Twin graph witnesses select distinct actual slots whose constitutional and
complete active priorities tie, for every ready frozen reader. -/
theorem twin_slots {i : Input} (p : TwinPair i) {f : Site i} (fr : Frame i f)
    (center : fr.center = p.c) (offU : f.val.root ≠ p.u) (offV : f.val.root ≠ p.v)
    (read : Reader i) (ready : RingGroupedStereo.Ready f read) (rev : Bool) :
    ∃ u v : Fin 4, u ≠ v ∧
      RingSingleCycleComparison.rebuilt i f (cursor fr u) =
        RingSingleCycleComparison.rebuilt i f (cursor fr v) ∧
      RingOriginFullKeys.active i f read rev (cursor fr u) =
        RingOriginFullKeys.active i f read rev (cursor fr v) := by
  have au : i.certified.moleculeGraph.Adj fr.center.val p.u := by
    rw [center]
    exact i.certified.moleculeGraph.adj_symm.mpr ((p.supportU p.c.val).mpr rfl)
  have av : i.certified.moleculeGraph.Adj fr.center.val p.v := by
    rw [center]
    exact i.certified.moleculeGraph.adj_symm.mpr ((p.supportV p.c.val).mpr rfl)
  obtain ⟨u,hu⟩ := slot_exists fr p.u au
  obtain ⟨v,hv⟩ := slot_exists fr p.v av
  refine ⟨u,v,?_,twin_keys p fr center offU offV read ready rev u v hu hv⟩
  intro same
  subst v
  exact p.distinct (Option.some.inj (hu.symm.trans hv))

/-- The actual frozen evaluator has two distinct tied full-key slots. -/
theorem frozen_twin_slots {i : Input} (p : TwinPair i) {f : Site i} (fr : Frame i f)
    (center : fr.center = p.c) (offU : f.val.root ≠ p.u) (offV : f.val.root ≠ p.v)
    (g : LocalizedGenericMarkedRecalculation.Geometry) (rev : Bool) :
    ∃ u v : Fin 4, u ≠ v ∧
      RingOriginFullKeys.active i f (RingActiveDistanceSchedule.frozen (RingFrameTransport.stateG i g) f)
        rev (cursor fr u) =
      RingOriginFullKeys.active i f (RingActiveDistanceSchedule.frozen (RingFrameTransport.stateG i g) f)
        rev (cursor fr v) := by
  have au : i.certified.moleculeGraph.Adj fr.center.val p.u := by
    rw [center]
    exact i.certified.moleculeGraph.adj_symm.mpr ((p.supportU p.c.val).mpr rfl)
  have av : i.certified.moleculeGraph.Adj fr.center.val p.v := by
    rw [center]
    exact i.certified.moleculeGraph.adj_symm.mpr ((p.supportV p.c.val).mpr rfl)
  obtain ⟨u,hu⟩ := slot_exists fr p.u au
  obtain ⟨v,hv⟩ := slot_exists fr p.v av
  refine ⟨u,v,?_,frozen_twin_keys p fr center offU offV g rev u v hu hv⟩
  intro same
  subst v
  exact p.distinct (Option.some.inj (hu.symm.trans hv))

/-- The constitutional early exit cannot publish a hand at an actual twin
parent whose original root avoids both leaves. -/
theorem early_none {i : Input} (p : TwinPair i) (f : Site i)
    (real : f.val.node.provenance = .realAtom)
    (current : f.val.node.current? = some p.c.val)
    (offU : f.val.root ≠ p.u) (offV : f.val.root ≠ p.v) :
    RingOriginPriorityStore.early? i f = none := by
  have recognized := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff f p.c).mpr ⟨real,current⟩
  obtain ⟨fr,found⟩ := RingGroupedGeometry.frame_exists recognized
  have center : fr.center = p.c := Option.some.inj (fr.recognized.symm.trans recognized)
  have au : i.certified.moleculeGraph.Adj fr.center.val p.u := by
    rw [center]
    exact i.certified.moleculeGraph.adj_symm.mpr ((p.supportU p.c.val).mpr rfl)
  have av : i.certified.moleculeGraph.Adj fr.center.val p.v := by
    rw [center]
    exact i.certified.moleculeGraph.adj_symm.mpr ((p.supportV p.c.val).mpr rfl)
  obtain ⟨u,hu⟩ := slot_exists fr p.u au
  obtain ⟨v,hv⟩ := slot_exists fr p.v av
  obtain ⟨ru,lu⟩ := terminal_slot fr p.u (center.symm ▸ p.supportU) offU u hu
  obtain ⟨rv,lv⟩ := terminal_slot fr p.v (center.symm ▸ p.supportV) offV v hv
  have keys := RingOriginTwinLeaves.twin_rebuilt_eq p f _ _ lu lv hu hv ru rv
  have same : word (fr.direction u) = word (fr.direction v) := by
    change ((RingSingleCycleComparison.rebuilt i f (cursor fr u)).map _).getD [] =
      ((RingSingleCycleComparison.rebuilt i f (cursor fr v)).map _).getD []
    rw [keys]
  have zero : RingOrientation.orientation (fun k => word (fr.direction k)) = 0 := by
    apply (RingOrientation.orientation_zero _).mpr
    intro injective
    have slots := injective same
    subst v
    exact p.distinct (Option.some.inj (hu.symm.trans hv))
  simp [RingOriginPriorityStore.early?,found,zero]

end TetraStereo.Engine.RingOriginTwinFrame
assert_kernel_only TetraStereo.Engine.RingOriginTwinFrame.terminal_slot
assert_kernel_only TetraStereo.Engine.RingOriginTwinFrame.twin_keys
assert_kernel_only TetraStereo.Engine.RingOriginTwinFrame.twin_slots
assert_kernel_only TetraStereo.Engine.RingOriginTwinFrame.frozen_twin_keys
assert_kernel_only TetraStereo.Engine.RingOriginTwinFrame.early_none
assert_kernel_only TetraStereo.Engine.RingOriginTwinFrame.frozen_twin_slots
