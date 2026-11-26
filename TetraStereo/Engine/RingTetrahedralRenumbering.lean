import TetraStereo.Engine.RingChemicalRenumberingBase

set_option autoImplicit false
namespace TetraStereo.Engine.RingTetrahedralRenumbering
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings
open RingGeometryTransport (FrameMap)
open RingGeometryExchange (Frozen)

/-- The nomination list commutes with arbitrary slot bijections. -/
theorem tiedSlots_perm (σ : Equiv.Perm Slot) (x y : Slot → Key)
    (keys : ∀ k, x k = y (σ k)) :
    ((RingFullPathEligibility.tiedSlots x).map σ).Perm (RingFullPathEligibility.tiedSlots y) := by
  have nd (z : Slot → Key) : (RingFullPathEligibility.tiedSlots z).Nodup :=
    (List.nodup_finRange 4).filter _
  apply (List.perm_ext_iff_of_nodup ((nd x).map σ.injective) (nd y)).mpr
  intro t
  obtain ⟨s,rfl⟩ := σ.surjective t
  simp only [List.mem_map]
  constructor
  · rintro ⟨u,hu,eq⟩
    obtain rfl := σ.injective eq
    obtain ⟨k,ne,tie⟩ := (RingFullPathEligibility.mem_tied x u).mp hu
    exact (RingFullPathEligibility.mem_tied y _).mpr
      ⟨σ k,σ.injective.ne ne,(keys u).symm.trans (tie.trans (keys k))⟩
  · intro hu
    obtain ⟨v,ne,tie⟩ := (RingFullPathEligibility.mem_tied y _).mp hu
    obtain ⟨k,rfl⟩ := σ.surjective v
    exact ⟨s,(RingFullPathEligibility.mem_tied x s).mpr
      ⟨k,fun e => ne (congrArg σ e),(keys s).trans (tie.trans (keys k).symm)⟩,rfl⟩

theorem candidates_perm (σ : Equiv.Perm Slot) (x y : Slot → Key)
    (keys : ∀ k, x k = y (σ k)) :
    ((RingFullPathEligibility.candidates x).map σ).Perm (RingFullPathEligibility.candidates y) := by
  have p := tiedSlots_perm σ x y keys
  have len : (RingFullPathEligibility.tiedSlots x).length =
      (RingFullPathEligibility.tiedSlots y).length := by simpa using p.length_eq
  simp only [RingFullPathEligibility.candidates,len]
  split
  · exact p
  · exact List.Perm.nil

theorem trials_perm (σ : Equiv.Perm Slot) (x y : Slot → Key)
    (keys : ∀ k, x k = y (σ k)) :
    ((trials x).map (Option.map σ)).Perm (trials y) := by
  have p := candidates_perm σ x y keys
  unfold trials
  cases hx : RingFullPathEligibility.candidates x with
  | nil =>
    have hy : RingFullPathEligibility.candidates y = [] := by
      simp only [hx,List.map_nil] at p
      exact p.symm.eq_nil
    simp [hy]
  | cons a as =>
    cases hy : RingFullPathEligibility.candidates y with
    | nil => simp [hx,hy] at p
    | cons b bs => simpa [hx,hy,List.map_map,Function.comp_def] using p.map some

private theorem select_atoms (a : Slot → Nat) (row : List Slot) :
    atomsAt? [a 0,a 1,a 2,a 3] (row.map Fin.val) = some (row.map a) := by
  have lookup (k : Slot) : [a 0,a 1,a 2,a 3][k.val]? = some (a k) := by fin_cases k <;> rfl
  induction row with
  | nil => rfl
  | cons k row ih =>
    unfold atomsAt? at ih ⊢
    simp only [List.map_cons,List.mapM_cons,lookup,ih]
    rfl

/-- The baseline geometry clause transports every physical ordering, including
orders different from the two native written-neighbor orders. -/
theorem frame_hand {i j f g x y} (p : @FrameMap i j f g x y) (rev : Bool)
    (row : List Slot) (perm : row.Perm (List.finRange 4)) :
    hand? x rev row = hand? y rev (row.map p.slots) := by
  have before := LocalizedMarkedConfigurationTransport.reordered_readback_partial
    (inputGeometry i.certified) (RingGroupedTrials.atom x) (row.map Fin.val) (perm.map Fin.val)
  have after := LocalizedMarkedConfigurationTransport.reordered_readback_partial
    (inputGeometry j.certified) (fun k => RingGroupedTrials.atom y (p.slots k))
    (row.map Fin.val) (perm.map Fin.val)
  rw [select_atoms] at before
  rw [select_atoms (fun k => RingGroupedTrials.atom y (p.slots k)) row] at after
  have baseline : readback? (inputGeometry i.certified)
      [RingGroupedTrials.atom x 0,RingGroupedTrials.atom x 1,RingGroupedTrials.atom x 2,RingGroupedTrials.atom x 3] =
      readback? (inputGeometry j.certified)
      [RingGroupedTrials.atom y (p.slots 0),RingGroupedTrials.atom y (p.slots 1),
       RingGroupedTrials.atom y (p.slots 2),RingGroupedTrials.atom y (p.slots 3)] := p.geometry
  simp only [Option.bind_some,baseline] at before after
  have raw : readback? (inputGeometry i.certified) (x.atoms row) =
      readback? (inputGeometry j.certified) (y.atoms (row.map p.slots)) := by
    simpa [RingGroupedTrials.atom,Frame.atoms,List.map_map,Function.comp_def] using before.trans after.symm
  cases rev <;> simp only [hand?,Bool.false_eq_true,if_false,if_true,readback_mirror,raw]
theorem outcome_transport {i j f g x y} (p : @FrameMap i j f g x y)
    (rev : Bool) (w w' : Slot → List (List RingRetainedChemicalTrace.Word))
    (keys : ∀ k, w k = w' (p.slots k)) {h : Option RS} (seen : Outcome x rev w h) :
    Outcome y rev w' h := by
  cases seen with
  | tie ne eq =>
    exact .tie (p.slots.injective.ne ne) ((keys _).symm.trans (eq.trans (keys _)))
  | @hand row h inj legal observed =>
    have inj' : Function.Injective w' := by
      intro a b eq
      obtain ⟨a,rfl⟩ := p.slots.surjective a
      obtain ⟨b,rfl⟩ := p.slots.surjective b
      exact congrArg p.slots (inj ((keys a).trans (eq.trans (keys b).symm)))
    have perm : (row.map p.slots).Perm (List.finRange 4) :=
      (legal.perm.map p.slots).trans p.slots.map_finRange_perm
    have descending : ((row.map p.slots).map w').Pairwise (· ≥ ·) := by
      simpa only [List.map_map,Function.comp_def,← keys] using legal.descending
    exact .hand inj' ⟨perm,descending⟩ ((frame_hand p rev row legal.perm).symm.trans observed)

theorem readTrial_transport {i j f g x y} (p : @FrameMap i j f g x y)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (geom' : LocalizedChemicalRing.coordinatesAdmitted j = true)
    (rev : Bool) (w w' : Slot → List (List RingRetainedChemicalTrace.Word))
    (keys : ∀ k, w k = w' (p.slots k)) :
    readTrial x rev w = readTrial y rev w' := by
  exact (read_exact geom' y rev w' _).mp
    (outcome_transport p rev w w' keys ((read_exact geom x rev w _).mpr rfl))

private theorem mark_value {i f} (fr : @Frame i f) (r : Reader i)
    (ready : RingGroupedStereo.Ready f r) (s : Slot) (ws : Slot → RingRetainedChemicalTrace.Word)
    (found : markWords? fr r (some s) = some ws) (k : Slot) :
    ws k = RingOrientation.markedWord fr r s k := by
  obtain ⟨w,hw,only⟩ := mark_exact fr ready false (some s)
  have ww : w = ws := Option.some.inj (hw.symm.trans found)
  subst w
  obtain ⟨b,hb,hk⟩ := (only ws).mpr rfl k
  obtain ⟨e,he⟩ := RingGroupedMark.arm_ready ready (RingGroupedTrials.atom fr s)
    (RingGroupedCentre.cursor fr k) (RingGroupedCentre.valid fr k) (fr.direction k).property.1
  have eq := hb.unique (RingGroupedMark.arm_source he).2
  simp only [RingOrientation.markedWord,he,Option.map_some,Option.getD_some]
  exact hk.trans (congrArg RingStereoSiblingPass.Branch.word eq)

/-- Actual mark readers commute slotwise, for baseline and nominated trials. -/
theorem markWords_transport {i j f g x y l r} (p : @FrameMap i j f g x y)
    (labs : Frozen p.carrier l r) (ready : RingGroupedStereo.Ready f l)
    (ready' : RingGroupedStereo.Ready g r) (s : Option Slot) :
    ∃ ws ws', markWords? x l s = some ws ∧
      markWords? y r (s.map p.slots) = some ws' ∧ ∀ k, ws k = ws' (p.slots k) := by
  obtain ⟨ws,hw,_⟩ := mark_exact x ready false s
  obtain ⟨ws',hw',_⟩ := mark_exact y ready' false (s.map p.slots)
  refine ⟨ws,ws',hw,hw',?_⟩
  cases s with
  | none =>
    have eq : ws = fun _ => [] := (Option.some.inj hw).symm
    have eq' : ws' = fun _ => [] := (Option.some.inj hw').symm
    simp [eq,eq']
  | some s =>
    intro k
    exact (mark_value x l ready s ws hw k).trans
      ((p.word labs ready ready' s k).trans (mark_value y r ready' _ ws' hw' _).symm)
private theorem reads_transport {i j f g x y l r} (p : @FrameMap i j f g x y)
    (ready : RingGroupedStereo.Ready f l) (ready' : RingGroupedStereo.Ready g r)
    (keys : ∀ rev k, RingFullPathEligibility.key? i l rev (RingGroupedCentre.cursor x k) =
      RingFullPathEligibility.key? j r rev (RingGroupedCentre.cursor y (p.slots k)))
    (rev : Bool) (k : Slot) (key : Key)
    (read : RingFullPathEligibility.Reads i l rev (RingGroupedCentre.cursor x k) key) :
    RingFullPathEligibility.Reads j r rev (RingGroupedCentre.cursor y (p.slots k)) key := by
  obtain ⟨a,ha,ua⟩ := RingFullPathEligibility.key_exact ready rev (RingGroupedCentre.cursor x k)
    (RingGroupedCentre.valid x k) (x.direction k).property.1
  obtain ⟨b,hb,ub⟩ := RingFullPathEligibility.key_exact ready' rev (RingGroupedCentre.cursor y (p.slots k))
    (RingGroupedCentre.valid y _) (y.direction _).property.1
  have ab : a = b := Option.some.inj (ha.symm.trans ((keys rev k).trans hb))
  exact (ub key).mpr (((ua key).mp read).trans ab)

/-- Transport source ballots while retaining their multiset of actual hands.
Only ordinary executable key agreement is assumed; mark and trial agreement
are derived from the physical frame map and the ready frozen readers. -/
theorem ballots_transport {i j f g x y l r} (p : @FrameMap i j f g x y)
    (labs : Frozen p.carrier l r) (ready : RingGroupedStereo.Ready f l)
    (ready' : RingGroupedStereo.Ready g r)
    (keys : ∀ rev k, RingFullPathEligibility.key? i l rev (RingGroupedCentre.cursor x k) =
      RingFullPathEligibility.key? j r rev (RingGroupedCentre.cursor y (p.slots k)))
    (rev : Bool) (ks : Slot → Key) (hands : List (Option RS))
    (ballot : RingFullPathPublication.Ballots x l rev ks hands) :
    ∃ hands', hands'.Perm hands ∧ RingFullPathPublication.Ballots y r rev
      (fun t => ks (p.slots.symm t)) hands' := by
  let ks' : Slot → Key := fun t => ks (p.slots.symm t)
  have keymap (k : Slot) : ks k = ks' (p.slots k) := by simp [ks']
  have actual : ∀ t, RingFullPathEligibility.Reads j r rev (RingGroupedCentre.cursor y t) (ks' t) := by
    intro t
    obtain ⟨k,rfl⟩ := p.slots.surjective t
    simpa [ks'] using reads_transport p ready ready' keys rev k (ks k) (ballot.1 k)
  let P := fun s v => ∃ ws, MarkWords y r rev s ws ∧
    Outcome y rev (fun k => trialKey (ks' k) (ws k)) v
  have each (s : Option Slot) (v : Option RS)
      (h : ∃ ws, MarkWords x l rev s ws ∧ Outcome x rev (fun k => trialKey (ks k) (ws k)) v) :
      P (s.map p.slots) v := by
    obtain ⟨w,hw,out⟩ := h
    obtain ⟨ws,hws,only⟩ := mark_exact x ready rev s
    have ww : w = ws := (only w).mp hw
    subst w
    obtain ⟨a,b,ha,hb,eq⟩ := markWords_transport p labs ready ready' s
    have wa : ws = a := Option.some.inj (hws.symm.trans ha)
    subst a
    obtain ⟨ws',hws',only'⟩ := mark_exact y ready' rev (s.map p.slots)
    have wb : b = ws' := Option.some.inj (hb.symm.trans hws')
    subst b
    refine ⟨ws',(only' ws').mpr rfl,?_⟩
    exact outcome_transport p rev _ _ (fun k => by rw [keymap k,eq k]) out
  have related : List.Forall₂ P ((trials ks).map (Option.map p.slots)) hands := by
    have all := ballot.2
    clear ballot
    generalize trials ks = ss at all ⊢
    induction all with
    | nil => exact .nil
    | cons h tail ih => exact .cons (each _ _ h) ih
  obtain ⟨hands',all,perm⟩ := List.perm_comp_forall₂ (trials_perm p.slots ks ks' keymap).symm related
  exact ⟨hands',perm,actual,all⟩

private theorem frame_unique {i f} (x y : @Frame i f) : x = y := by
  obtain ⟨c,hc,_,ids,read,_⟩ := x
  obtain ⟨d,hd,_,ids',read',_⟩ := y
  obtain rfl := Option.some.inj (hc.symm.trans hd)
  obtain rfl := Option.some.inj (read.symm.trans read')
  rfl

private theorem crossed_perm {a b c d : List (Option RS)} (ha : a.Perm b) (hc : c.Perm d) :
    RingFullPathPublication.crossed a c = RingFullPathPublication.crossed b d := by
  unfold RingFullPathPublication.crossed
  rw [LocalizedChemicalRingPromotionAggregation.readingBalance_perm ha,
    LocalizedChemicalRingPromotionAggregation.readingBalance_perm hc]
/-- Tetrahedral publication is invariant under the physical slot presentation.
The only new chemical comparison premise is agreement of ordinary full-path
keys on corresponding slots of the two actual ready frozen readers.

The existing two-geometry source theorem supplies the six-pair reversal law;
ballot transport preserves each independently cancelled signed majority. -/
theorem centre_transport {i j f g x y} (p : @FrameMap i j f g x y)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (geom' : LocalizedChemicalRing.coordinatesAdmitted j = true)
    (view : RingActiveDistanceSchedule.View i) (view' : RingActiveDistanceSchedule.View j)
    (ready : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f))
    (ready' : RingGroupedStereo.Ready g (RingActiveDistanceSchedule.frozen view' g))
    (labs : Frozen p.carrier (RingActiveDistanceSchedule.frozen view f)
      (RingActiveDistanceSchedule.frozen view' g))
    (left : RingNestedActivePair.frame? i f = some x)
    (right : RingNestedActivePair.frame? j g = some y)
    (keys : ∀ rev k,
      RingFullPathEligibility.key? i (RingActiveDistanceSchedule.frozen view f) rev
        (RingGroupedCentre.cursor x k) =
      RingFullPathEligibility.key? j (RingActiveDistanceSchedule.frozen view' g) rev
        (RingGroupedCentre.cursor y (p.slots k))) :
    RingFullPathPublication.centre? x (RingActiveDistanceSchedule.frozen view f) =
      RingFullPathPublication.centre? y (RingActiveDistanceSchedule.frozen view' g) := by
  obtain ⟨v,hv,_⟩ := RingFullPathPublication.source_exact geom ready
  have source := (RingFullPathPublication.two_geometry_iff geom f view ready v).mp hv
  cases source with
  | absent no => exact nomatch no.symm.trans x.recognized
  | @centre fr ks ms hs ts actual reflected =>
    obtain rfl := frame_unique x fr
    obtain ⟨hs',hperm,a⟩ := ballots_transport p labs ready ready' keys false ks hs actual
    obtain ⟨ts',tperm,b⟩ := ballots_transport p labs ready ready' keys true ms ts reflected
    have target := RingFullPathPublication.TwoGeometry.centre a b
    have eq := crossed_perm hperm tperm
    rw [eq] at target
    have got := (RingFullPathPublication.two_geometry_iff geom' g view' ready' _).mpr target
    simp only [RingFullPathPublication.publish?,left] at hv
    simp only [RingFullPathPublication.publish?,right] at got
    exact hv.trans got.symm
end TetraStereo.Engine.RingTetrahedralRenumbering

assert_kernel_only TetraStereo.Engine.RingTetrahedralRenumbering.centre_transport

namespace TetraStereo.Engine.RingReportRenumber
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingRawRenumbering (AtomMap)
open RingRawRenumbering.AtomMap (arm site)
open RingActiveDistanceSchedule (View Visible frozen)
open RingPyramidalPublication (focusP publish)
open RingNestedActivePair (Frame)
open RingActivePairReport (Slot)
open RingGroupedCentre (cursor)
variable {i j : Input}

private theorem cursor_mem {q : Site i} (x : Frame i q) (k : Slot) :
    cursor x k ∈ RingRetainedAuxiliary.frame i.certified q := by
  have mem : x.arm k ∈ RingRetainedAuxiliary.frame i.certified q := List.get_mem ..
  have hp := i.certified.executableLocalizedRerootChildren_previous (⟨q,none⟩ : Arm i) (x.arm k) mem
  have eq : cursor x k = x.arm k := by
    change (⟨(x.arm k).occurrence,some q⟩ : Arm i) = x.arm k
    cases h : x.arm k with
    | mk occ prev => rw [h] at hp; cases hp; rfl
  rw [eq]
  exact mem

/-- At a nonphosphorus focus the native fast publisher agrees after atom
renumbering once ordinary full-path keys agree on the actual incident arms.
All frozen labels needed by marked trials follow from earlier publications. -/
theorem publish_tetra_rename (r : AtomMap i j)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i)
    (focus : focusP i q = none)
    (earlier : ∀ v, Visible q v → RingChemicalGraphProof.state i v =
      RingChemicalGraphProof.state j (site r v))
    (keys : ∀ rev t, t ∈ RingRetainedAuxiliary.frame i.certified q →
      RingFullPathEligibility.key? j (frozen (RingChemicalGraphProof.state j) (site r q)) rev (arm r t) =
      RingFullPathEligibility.key? i (frozen (RingChemicalGraphProof.state i) q) rev t) :
    publish j (site r q) (frozen (RingChemicalGraphProof.state j) (site r q)) =
      publish i q (frozen (RingChemicalGraphProof.state i) q) := by
  have geom' := RingRawRenumbering.AtomMap.coordinates r geom
  have ready := RingChemicalGraphProof.ready geom q
  have ready' := RingChemicalGraphProof.ready geom' (site r q)
  have focus' : focusP j (site r q) = none := by rw [focus_atom,focus]; rfl
  simp only [publish,focus,focus']
  rw [RingFullPathConstitution.fast_local geom ready,RingFullPathConstitution.fast_local geom' ready']
  obtain localFrame := Classical.choice ((RingRawRenumbering.AtomMap.presentation r).localFrame q)
  cases localFrame with
  | absent no no' =>
    change j.certified.localizedOccurrenceDescriptorCenter? (site r q) = none at no'
    have off {k : Input} {u : Site k} (h : k.certified.localizedOccurrenceDescriptorCenter? u = none) :
        RingNestedActivePair.frame? k u = none := by
      cases hf : RingNestedActivePair.frame? k u with
      | none => rfl
      | some fr => exact nomatch h.symm.trans fr.recognized
    simp only [RingFullPathPublication.publish?,off no,off no']
  | @centre x y hx hy p occ =>
    change RingNestedActivePair.frame? j (site r q) = some y at hy
    have labels : RingGeometryExchange.Frozen p.carrier
        (frozen (RingChemicalGraphProof.state i) q)
        (frozen (RingChemicalGraphProof.state j) (site r q)) := by
      intro u on
      rw [occ u on]
      exact frozen_site r q _ _ earlier u.occurrence
    have comparison (rev : Bool) (k : Slot) :
        RingFullPathEligibility.key? i (frozen (RingChemicalGraphProof.state i) q) rev (cursor x k) =
        RingFullPathEligibility.key? j (frozen (RingChemicalGraphProof.state j) (site r q)) rev
          (cursor y (p.slots k)) := by
      rw [← frame_incident r p occ k]
      exact (keys rev _ (cursor_mem x k)).symm
    have eq := RingTetrahedralRenumbering.centre_transport p geom geom'
      (RingChemicalGraphProof.state i) (RingChemicalGraphProof.state j)
      ready ready' labels hx hy comparison
    simpa only [RingFullPathPublication.publish?,hx,hy] using eq.symm
end TetraStereo.Engine.RingReportRenumber
assert_kernel_only TetraStereo.Engine.RingReportRenumber.publish_tetra_rename

namespace TetraStereo.Engine.RingReportRenumber
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame)
open RingActivePairReport (Slot)
open RingRawRenumbering (AtomMap)
open RingRawRenumbering.AtomMap (site)
attribute [local instance] lexOrd
variable {i j : Input}

def constitutionalWord {i : Input} {f : Site i} (x : Frame i f) (k : Slot) :=
  RingRetainedChemicalPreorder.orderWord (RingRetainedChemicalPreorder.keyFor (x.direction k))

theorem frame_constitutional_word {f : Site i} {g : Site j} {x : Frame i f} {y : Frame j g}
    (p : RingGeometryTransport.FrameMap x y) (k : Slot) :
    constitutionalWord x k = constitutionalWord y (p.slots k) := by
  apply congrArg RingRetainedChemicalPreorder.orderWord
  apply p.carrier.constitution (p.covers k)
    (RingRetainedChemicalTrace.key_source (RingRetainedChemicalPreorder.read_key (x.direction k)))
  rw [p.incident k]
  exact RingRetainedChemicalTrace.key_source (RingRetainedChemicalPreorder.read_key (y.direction (p.slots k)))

theorem frame_constitutional_zero {f : Site i} {g : Site j} {x : Frame i f} {y : Frame j g}
    (p : RingGeometryTransport.FrameMap x y) :
    RingOrientation.orientation (constitutionalWord x) = 0 ↔
      RingOrientation.orientation (constitutionalWord y) = 0 := by
  rw [RingOrientation.orientation_zero,RingOrientation.orientation_zero]
  suffices eq : Function.Injective (constitutionalWord x) ↔ Function.Injective (constitutionalWord y) from not_congr eq
  constructor
  · intro h a b eqn
    obtain ⟨a,rfl⟩ := p.slots.surjective a
    obtain ⟨b,rfl⟩ := p.slots.surjective b
    exact congrArg p.slots (h (by simpa only [frame_constitutional_word p] using eqn))
  · intro h a b eqn
    apply p.slots.injective
    exact h (by simpa only [frame_constitutional_word p] using eqn)

/-- The actual zero-mass early-exit gate chooses the same path under atom renumbering.
This is independent of admitted geometry and of every stereo reader. -/
theorem zeroEarly_isSome (r : AtomMap i j) (q : Site i) :
    (RingZeroMassReport.zeroEarly? j (site r q)).isSome =
      (RingZeroMassReport.zeroEarly? i q).isSome := by
  rw [RingZeroMassReport.zero_early_exact,RingZeroMassReport.zero_early_exact]
  obtain localFrame := Classical.choice ((RingRawRenumbering.AtomMap.presentation r).localFrame q)
  cases localFrame with
  | absent no no' =>
    change j.certified.localizedOccurrenceDescriptorCenter? (site r q) = none at no'
    have off {k : Input} {u : Site k} (h : k.certified.localizedOccurrenceDescriptorCenter? u = none) :
        RingNestedActivePair.frame? k u = none := by
      cases hf : RingNestedActivePair.frame? k u with
      | none => rfl
      | some fr => exact nomatch h.symm.trans fr.recognized
    simp [RingSphereQueue.early?,off no,off no']
  | @centre x y hx hy p occ =>
    change RingNestedActivePair.frame? j (site r q) = some y at hy
    unfold RingSphereQueue.early?
    rw [hx,hy]
    change (if RingOrientation.orientation (constitutionalWord y) = 0 then none else
      some (⟨RingOrientation.baseline y * RingOrientation.orientation (constitutionalWord y),0⟩ : RingGeometryCriterion.Signature)).isSome =
      (if RingOrientation.orientation (constitutionalWord x) = 0 then none else
      some (⟨RingOrientation.baseline x * RingOrientation.orientation (constitutionalWord x),0⟩ : RingGeometryCriterion.Signature)).isSome
    by_cases zero : RingOrientation.orientation (constitutionalWord x) = 0
    · rw [if_pos zero,if_pos ((frame_constitutional_zero p).mp zero)]
    · rw [if_neg zero,if_neg (fun h => zero ((frame_constitutional_zero p).mpr h))]
      rfl

/-- The branch condition of `RingChemicalGraphProof.fastRoot`: phosphorus and
occurrences without a strict early result enter the distance schedule. -/
def fastRootUsesQueue (i : Input) (a : i.certified.Atom) : Bool :=
  let q := RingGroupedReport.origin i a
  (RingPyramidalPublication.focusP i q).isSome || !(RingZeroMassReport.zeroEarly? i q).isSome

theorem fastRoot_by_queue_flag (i : Input) (a : i.certified.Atom) :
    RingChemicalGraphProof.fastRoot i a =
      if fastRootUsesQueue i a then
        RingEligibleGraph.root i (RingPyramidalPublication.eligible i) (RingPyramidalPublication.publish i) a
      else (RingZeroMassReport.zeroEarly? i (RingGroupedReport.origin i a)).map (fun s => s.letters) := by
  cases hp : RingPyramidalPublication.focusP i (RingGroupedReport.origin i a) <;>
    cases he : RingZeroMassReport.zeroEarly? i (RingGroupedReport.origin i a) <;>
    simp [RingChemicalGraphProof.fastRoot,fastRootUsesQueue,hp,he]

theorem fastRootUsesQueue_rename (r : AtomMap i j) (a : i.certified.Atom) :
    fastRootUsesQueue j (r.atoms a) = fastRootUsesQueue i a := by
  unfold fastRootUsesQueue
  dsimp only
  rw [←site_origin r a,focus_atom,zeroEarly_isSome]
  simp

end TetraStereo.Engine.RingReportRenumber
assert_kernel_only TetraStereo.Engine.RingReportRenumber.zeroEarly_isSome
assert_kernel_only TetraStereo.Engine.RingReportRenumber.fastRootUsesQueue_rename
