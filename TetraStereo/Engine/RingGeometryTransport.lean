import TetraStereo.Engine.RingFrameRelabeling
import TetraStereo.Engine.RingGeometryAutomorphism

set_option autoImplicit false

namespace TetraStereo.Engine.RingGeometryTransport
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader)
open RingGroupedCentre (Arms cursor)
open RingGroupedOrders (marks wins)
open RingGeometryExchange (Carrier Frozen Marked)
open RingActivePairReport (Slot)
open RingActiveDistanceSchedule (View Visible distance frozen)
open RingFrameRelabeling (sign)
open RingGeometryCriterion (Signature)
attribute [local instance] lexOrd

/-- Raw data for two presentations of a tetrahedral site. The volume is read
once in the same physical order. Atom identities can change throughout. -/
structure FrameMap {i j f g} (x : Frame i f) (y : Frame j g) where
  slots : Equiv.Perm Slot
  carrier : Carrier i j
  covers : ∀ s, carrier.domain (cursor x s)
  incident : ∀ s, carrier.image (cursor x s) = cursor y (slots s)
  atom : ∀ s, Marked carrier (RingGroupedTrials.atom x s) (RingGroupedTrials.atom y (slots s))
  geometry : readback? (inputGeometry i.certified) (x.atoms (List.finRange 4)) =
    readback? (inputGeometry j.certified) (y.atoms ((List.finRange 4).map slots))

theorem FrameMap.baseline {i j f g x y} (p : @FrameMap i j f g x y) :
    RingOrientation.baseline x = sign p.slots * RingOrientation.baseline y := by
  have mapped := RingOrientation.frame_read y (inputGeometry j.certified)
    ⟨(List.finRange 4).map p.slots,p.slots.map_finRange_perm⟩
  unfold RingOrientation.baseline
  rw [p.geometry,mapped]
  unfold sign RingJointObservations.parity
  simp only [List.map_map,Function.comp_def]
  cases RawMolecule.permutationIsEven ((List.finRange 4).map (fun k => (p.slots k).val)) <;>
    cases readback? (inputGeometry j.certified) (y.atoms (List.finRange 4)) with
    | none => rfl
    | some h => cases h <;> rfl

theorem FrameMap.key {i j f g x y l r} (p : @FrameMap i j f g x y) (frozenLabels : Frozen p.carrier l r)
    (a : Arms x l) (b : Arms y r) (rev : Bool) (s : Slot) : a.key rev s = b.key rev (p.slots s) := by
  cases rev
  · exact p.carrier.priority frozenLabels (p.covers s) (a.source s) ((p.incident s).symm ▸ b.source _)
  · exact p.carrier.priority frozenLabels (p.covers s) (a.source s).reflect ((p.incident s).symm ▸ (b.source _).reflect)

theorem FrameMap.word {i j f g x y l r} (p : @FrameMap i j f g x y) (labs : Frozen p.carrier l r)
    (ready : RingGroupedStereo.Ready f l) (ready' : RingGroupedStereo.Ready g r) (s k : Slot) :
    RingOrientation.markedWord x l s k = RingOrientation.markedWord y r (p.slots s) (p.slots k) := by
  obtain ⟨u,hu⟩ := RingGroupedMark.arm_ready ready (RingGroupedTrials.atom x s) (cursor x k)
    (RingGroupedCentre.valid x k) (x.direction k).property.1
  obtain ⟨v,hv⟩ := RingGroupedMark.arm_ready ready' (RingGroupedTrials.atom y (p.slots s)) (cursor y (p.slots k))
    (RingGroupedCentre.valid y _) (y.direction _).property.1
  have eqn := p.carrier.mark labs (p.atom s) (p.covers k) (RingGroupedMark.arm_source hu).2
    ((p.incident k).symm ▸ (RingGroupedMark.arm_source hv).2)
  simp [RingOrientation.markedWord,hu,hv,eqn]

theorem FrameMap.markPermutation {i j f g x y l r} (p : @FrameMap i j f g x y) (labs : Frozen p.carrier l r)
    (a : Arms x l) (b : Arms y r) : ((marks a).map p.slots).Perm (marks b) := by
  have nd {i f fr read} (u : @Arms i f fr read) : (marks u).Nodup := (List.nodup_finRange 4).filter _
  apply (List.perm_ext_iff_of_nodup ((nd a).map p.slots.injective) (nd b)).mpr
  intro t
  obtain ⟨s,rfl⟩ := p.slots.surjective t
  simp only [List.mem_map]
  constructor
  · rintro ⟨u,hu,id⟩
    obtain rfl := p.slots.injective id
    obtain ⟨v,ne,tied⟩ := (RingGroupedOrders.marked_iff a u false).mp hu
    exact (RingGroupedOrders.marked_iff b _ false).mpr
      ⟨p.slots v,p.slots.injective.ne ne,(p.key labs a b false u).symm.trans (tied.trans (p.key labs a b false v))⟩
  · intro ht
    obtain ⟨v,ne,tied⟩ := (RingGroupedOrders.marked_iff b _ false).mp ht
    obtain ⟨u,rfl⟩ := p.slots.surjective v
    exact ⟨s,(RingGroupedOrders.marked_iff a _ false).mpr
      ⟨u,fun h => ne (congrArg p.slots h),(p.key labs a b false s).trans (tied.trans (p.key labs a b false u).symm)⟩,rfl⟩

theorem FrameMap.index {i j f g x y l r} (p : @FrameMap i j f g x y) (labs : Frozen p.carrier l r)
    (a : Arms x l) (b : Arms y r) (ready : RingGroupedStereo.Ready f l) (ready' : RingGroupedStereo.Ready g r) :
    RingOrientation.index a = sign p.slots * RingOrientation.index b := by
  have all := p.markPermutation labs a b
  have length : (marks a).length = (marks b).length := by simpa using all.length_eq
  unfold RingOrientation.index
  rw [length]
  split
  · rw [funext (p.key labs a b false),RingFrameRelabeling.alternating]
  · let vote (t : Slot) := RingOrientation.orientation (wins b false (RingOrientation.markedWord y r t))
    have each (s : Slot) : RingOrientation.orientation (wins a false (RingOrientation.markedWord x l s)) =
        sign p.slots * vote (p.slots s) := by
      have h (k : Slot) : wins a false (RingOrientation.markedWord x l s) k =
          wins b false (RingOrientation.markedWord y r (p.slots s)) (p.slots k) :=
        Prod.ext (p.key labs a b false k) (p.word labs ready ready' s k)
      rw [funext h,RingFrameRelabeling.alternating]
    have rearranged := (all.map vote).sum_eq
    simp only [List.map_map,Function.comp_def] at rearranged
    simp only [each,List.sum_map_mul_left,rearranged,vote]

private def changed {i f fr read} (a : @Arms i f fr read) (j k : Slot) :=
  compare (a.key false j) (a.key false k) != compare (a.key true j) (a.key true k)

private theorem changed_count {i f fr read} (a : @Arms i f fr read) :
    LocalizedChemicalRing.ConstitutionalPartition.pairs.countP (fun z => changed a z.1 z.2) = RingGeometryCriterion.reversals a := by
  apply (List.Perm.refl _).countP_congr
  intro p _
  obtain ⟨z,allowed,_,order⟩ := a.represented p.1 p.2
  change (_ != _) = ((_ == Ordering.gt) != (_ == Ordering.gt))
  rw [← order false,← order true]
  simp only [RingActivePairs.molecularValues,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with h | h | h | h | h <;> rw [h] <;> decide

theorem FrameMap.reversals {i j f g x y l r} (p : @FrameMap i j f g x y) (labs : Frozen p.carrier l r)
    (a : Arms x l) (b : Arms y r) : RingGeometryCriterion.reversals a = RingGeometryCriterion.reversals b := by
  rw [← changed_count,← changed_count]
  have eqn (j k : Slot) : changed a j k = changed b (p.slots j) (p.slots k) := by simp only [changed,p.key labs a b]
  simp_rw [eqn]
  apply RingFrameRelabeling.pairs_unchanged p.slots (fun z => changed b z.1 z.2)
  intro j k
  unfold changed
  rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := b.key false j) (b := b.key false k),
    Std.OrientedCmp.eq_swap (cmp := compare) (a := b.key true j) (b := b.key true k)]
  cases compare (b.key false k) (b.key false j) <;> cases compare (b.key true k) (b.key true j) <;> rfl

/-- A presentation relates original occurrences and visible dependencies.
Its data specify frame geometry and decorated carriers before any label exists. -/
inductive SiteMap {i j : Input} (site : Site i → Site j) (q : Site i) : Type where
  | absent (source : i.certified.localizedOccurrenceDescriptorCenter? q = none)
      (target : j.certified.localizedOccurrenceDescriptorCenter? (site q) = none)
  | centre {x : Frame i q} {y : Frame j (site q)} (left : RingNestedActivePair.frame? i q = some x)
      (right : RingNestedActivePair.frame? j (site q) = some y) (transport : FrameMap x y)
      (occurrence : ∀ u, transport.carrier.domain u → (transport.carrier.image u).occurrence = site u.occurrence)

structure Presentation (i j : Input) where
  site : Site i → Site j
  root : ∀ q t, (site t).val.root = (site q).val.root ↔ t.val.root = q.val.root
  visible : ∀ q t, Visible (site q) (site t) ↔ Visible q t
  localFrame : ∀ q, Nonempty (SiteMap site q)

private theorem frozen_eq {i j} (p : Presentation i j) (s : View i) (t : View j) (q u : Site i)
    (earlier : ∀ v, Visible q v → s v = t (p.site v)) : frozen s q u = frozen t (p.site q) (p.site u) := by
  by_cases on : u.val.root = q.val.root
  · have mapped := (p.root q u).mpr on
    by_cases allowed : Visible q u
    · have m := (p.visible q u).mpr allowed
      simp only [frozen,if_neg (not_not_intro on),if_neg (not_not_intro mapped),if_pos allowed.2,if_pos m.2,earlier u allowed]
    · have off : ¬(distance q < distance u ∧ u.val.node.current? ≠ some q.val.root) := fun h => allowed ⟨on,h⟩
      have off' : ¬(distance (p.site q) < distance (p.site u) ∧
          (p.site u).val.node.current? ≠ some (p.site q).val.root) := fun h => allowed ((p.visible q u).mp ⟨mapped,h⟩)
      simp only [frozen,if_neg (not_not_intro on),if_neg (not_not_intro mapped),if_neg off,if_neg off']
  · simp only [frozen,if_pos on,if_pos (mt (p.root q u).mp on)]

private theorem state_rule {i : Input} (coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i) :
    RingGroupedPublication.state i q = RingGeometryCriterion.rule i q (frozen (RingGroupedPublication.state i) q) := by
  have eqn := RingActiveDistanceSchedule.evaluate_eq (RingGeometryCriterion.rule i) q
  have same : RingActiveDistanceSchedule.evaluate (RingGeometryCriterion.rule i) = RingGroupedPublication.state i :=
    (RingActiveDistanceSchedule.snapshot_table ..).symm.trans (RingGeometryCriterion.state_eq coordinates)
  rwa [same] at eqn

/-- Simultaneous transport of every frozen publication, all Rule 6 marks and
both letters. The induction begins with physical input data on both molecules. -/
theorem Presentation.publications {i j} (p : Presentation i j)
    (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) (coords' : LocalizedChemicalRing.coordinatesAdmitted j = true)
    (q : Site i) : RingGroupedPublication.state i q = RingGroupedPublication.state j (p.site q) := by
  let s := RingGroupedPublication.state i
  let t := RingGroupedPublication.state j
  suffices ∀ n (u : Site i), RingActiveDistanceSchedule.height i - distance u = n → s u = t (p.site u) from this _ q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u depth
    have earlier (v : Site i) (vis : Visible u v) : s v = t (p.site v) := by
      have bound := RingActiveDistanceSchedule.distance_bound v
      have down := vis.2.1
      exact ih _ (by omega) v rfl
    change RingGroupedPublication.state i u = RingGroupedPublication.state j (p.site u)
    rw [state_rule coords u,state_rule coords' (p.site u)]
    obtain ⟨localData⟩ := p.localFrame u
    cases localData with
    | absent left right => simp [RingGeometryCriterion.rule,left,right]
    | @centre x y left right tr occurrence =>
      have ready := RingGroupedPublication.ready (RingGroupedGeometry.physical coords) u
      have ready' := RingGroupedPublication.ready (RingGroupedGeometry.physical coords') (p.site u)
      obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (RingGroupedCentre.arms_ready x ready)
      obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp (RingGroupedCentre.arms_ready y ready')
      have labs : Frozen tr.carrier (frozen s u) (frozen t (p.site u)) := by
        intro v on
        rw [occurrence v on]
        exact frozen_eq p s t u v.occurrence earlier
      have balance := tr.index labs a b ready ready'
      have equal : RingOrientation.baseline x * RingOrientation.index a = RingOrientation.baseline y * RingOrientation.index b := by
        rw [balance,tr.baseline]
        calc _ = (sign tr.slots * sign tr.slots) * (RingOrientation.baseline y * RingOrientation.index b) := by ring
             _ = _ := by rw [RingFrameRelabeling.sign_squared,one_mul]
      simp [RingGeometryCriterion.rule,RingGeometryCriterion.signature?,x.recognized,y.recognized,left,right,ha,hb,equal,tr.reversals labs a b]

section Automorphism
variable {i : Input} (e : i.certified.moleculeGraph.Aut)

/-- Preservation of handedness in the raw coordinate data. It can be checked
on the four neighbors in each order without reading any ligand priorities. -/
def Configured := ∀ (c : i.certified.TetrahedralCenter) (v : Slot ≃ i.certified.moleculeGraph.Neighbor c.val),
  let g := inputGeometry i.certified
  readback? g ((List.finRange 4).map (fun k => (v k).val.val)) =
    readback? g ((List.finRange 4).map (fun k => ((e : Equiv.Perm i.certified.Atom) (v k).val).val))

private theorem cursor_slot {q : Site i} (x : Frame i q)
    {frame : i.certified.LocalizedOccurrenceFourLigandFrame (i.certified.certified.input.molecule.atomCount+1)}
    (found : i.certified.localizedOccurrenceFourLigandFrame? q = some frame) (k : Slot) :
    cursor x k = frame.cursorAt k := by
  have parent := i.certified.executableLocalizedRerootChildren_previous (⟨q,none⟩ : RingActivePairs.Arm i)
    (x.arm k) (show x.arm k ∈ RingRetainedAuxiliary.frame i.certified q from List.get_mem ..)
  have h : cursor x k = x.arm k := by
    cases arm : x.arm k with
    | mk occ prev =>
      change (⟨(x.arm k).occurrence,some q⟩ : RingActivePairs.Arm i) = _
      rw [arm] at parent ⊢
      cases parent
      rfl
  rw [h]
  have lists := i.certified.localizedOccurrenceFourLigandFrame_cursors_eq_executable q frame found
  unfold RingNestedActivePair.Frame.arm LocalizedOccurrenceFourLigandFrame.cursorAt
  apply List.getElem_of_eq
  exact lists.symm

private theorem carriers {q : Site i} (x : Frame i q) {c : i.certified.TetrahedralCenter}
    {v : Slot ≃ i.certified.moleculeGraph.Neighbor c.val}
    (current : ∀ k, (cursor x k).occurrence.val.node.current? = some (v k).val) :
    ∀ k, RingGroupedTrials.atom x k = (v k).val.val := by
  intro k
  have point := x.point_at k
  change (cursor x k).occurrence.val.node.current?.map Fin.val = some (RingGroupedTrials.atom x k) at point
  rw [current k] at point
  exact (Option.some.inj point).symm

/-- A graph automorphism preserving raw atom records and the handedness of
the neighbor coordinates carries the complete report. Only the two physical
input conditions are required of the automorphism. -/
theorem automorphism_publications (records : RingGeometryAutomorphism.Records e) (configured : Configured e)
    (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i) :
    RingGroupedPublication.state i q = RingGroupedPublication.state i (RingGeometryAutomorphism.site e q) := by
  let site := RingGeometryAutomorphism.site e
  have forward {f : Site i} {c} (recognized : i.certified.localizedOccurrenceDescriptorCenter? f = some c) :
      i.certified.localizedOccurrenceDescriptorCenter? (site f) = some (i.certified.transportTetrahedralCenter e c) :=
    (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mpr
      (i.certified.realTetrahedralCenterNode_transport i.single e f c
        ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp recognized))
  refine Presentation.publications (j := i) ⟨site,?_,RingGeometryAutomorphism.visible e,?_⟩ coords coords q
  · intro x y
    exact (e : Equiv.Perm i.certified.Atom).injective.eq_iff
  · intro f
    cases recog : i.certified.localizedOccurrenceDescriptorCenter? f with
    | none =>
      refine ⟨.absent recog ?_⟩
      cases img : i.certified.localizedOccurrenceDescriptorCenter? (site f) with
      | none => rfl
      | some c =>
        have back := i.certified.realTetrahedralCenterNode_transport i.single (e⁻¹) (site f) c
          ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp img)
        change i.certified.RealTetrahedralCenterNode
          (i.certified.transportOccurrence i.single (e⁻¹) (i.certified.transportOccurrence i.single e f)).val.node _ at back
        rw [i.certified.transportOccurrence_inv_apply] at back
        exact nomatch recog.symm.trans ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mpr back)
    | some c =>
      obtain ⟨x,hx⟩ := RingGroupedGeometry.frame_exists recog
      obtain ⟨y,hy⟩ := RingGroupedGeometry.frame_exists (forward recog)
      let t := i.certified.actualFrameSlotTransport i.single e (Nat.le_succ _) f c
        ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp recog)
      have source := cursor_slot x t.sourceComputed
      have target := cursor_slot y t.imageComputed
      have left := carriers x (fun k => (congrArg (fun u : RingActivePairs.Arm i => u.occurrence.val.node.current?) (source k)).trans (t.source_current k))
      have right := carriers y (fun k => (congrArg (fun u : RingActivePairs.Arm i => u.occurrence.val.node.current?) (target k)).trans (t.image_current k))
      have renumber (k : Slot) : (t.imageLigand (t.slotPerm k)).val = (e : Equiv.Perm i.certified.Atom) (t.sourceLigand k).val :=
        congrArg Subtype.val (t.neighbor_eq k)
      refine ⟨.centre hx hy ⟨t.slotPerm,RingGeometryAutomorphism.carrier e records,?_,?_,?_,?_⟩ (fun _ _ => rfl)⟩
      · intro k previous hp
        change some f = some previous at hp
        obtain rfl := Option.some.inj hp
        exact (x.direction k).property.1.symm
      · intro k
        change i.certified.transportCursor i.single e (cursor x k) = cursor y (t.slotPerm k)
        rw [source,target,t.cursorAt_eq]
      · intro k
        rw [left,right,renumber]
        exact RingGeometryAutomorphism.mark e records (t.sourceLigand k).val
      · change readback? _ ((List.finRange 4).map (RingGroupedTrials.atom x)) =
          readback? _ (((List.finRange 4).map t.slotPerm).map (RingGroupedTrials.atom y))
        rw [funext left]
        simp only [List.map_map,Function.comp_def,right,renumber]
        exact configured c t.sourceLigand

end Automorphism

end TetraStereo.Engine.RingGeometryTransport
assert_kernel_only TetraStereo.Engine.RingGeometryTransport.Presentation.publications
assert_kernel_only TetraStereo.Engine.RingGeometryTransport.automorphism_publications
