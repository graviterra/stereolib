import TetraStereo.Engine.RingRawRenumbering
import TetraStereo.Engine.RingSingleCycleComparison

/-! Transport the actual retained origin metric under molecular atom bijections. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginMetricRenumber
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingRawRenumbering (AtomMap)
open RingSingleCycleOrigin (originPath shared pathDistance)
open RingSingleCycleComparison (native active weight rebuilt)

theorem shared_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (xs ys : List α) : shared (xs.map e) (ys.map e) = shared xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys => by_cases h : x = y <;> simp [shared, h, ih]

theorem pathDistance_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (xs ys : List α) :
    pathDistance (xs.map e) (ys.map e) = pathDistance xs ys := by
  simp [pathDistance, shared_map]

theorem originPath_map {n m : Nat} (e : Fin n ≃ Fin m)
    (v : OfficialCIPNode (Fin n)) (d : Nat) :
    originPath (RingRawRenumbering.nodeMap e v) d = (originPath v d).map e := by
  simp [originPath, RingRawRenumbering.nodeMap, List.map_tail, List.map_reverse,
    List.map_take]

private theorem atomCount {i j : Input} (r : AtomMap i j) :
    j.molecule.atomCount = i.molecule.atomCount := by
  have card : i.certified.certified.input.molecule.atomCount =
      j.certified.certified.input.molecule.atomCount := by
    simpa using Fintype.card_congr r.atoms
  exact (j.molecule.toSemanticMolecule?_atomCount _ j.agreement.1).symm.trans
    (card.symm.trans (i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1))

theorem active_map {i j : Input} (r : AtomMap i j) (focus : List i.certified.Atom)
    (q : Arm i) (aligned : i.certified.cursorPreviousRootAligned q) :
    active j (focus.map r.atoms) (r.arm q) = active i focus q := by
  have obs := (r.carrier.observation q aligned).symm
  change native j (r.arm q) = native i q at obs
  unfold active
  rw [obs]
  have prov : (r.arm q).occurrence.val.node.provenance = q.occurrence.val.node.provenance := rfl
  rw [prov]
  cases q.occurrence.val.node.provenance <;> try rfl
  simp only [RingRawRenumbering.AtomMap.arm, RingRawRenumbering.AtomMap.site]
  simp [weight, originPath_map, pathDistance_map, atomCount r]
private theorem mapM_perm {α β : Type} (f : α → Option β) {xs ys : List α}
    (p : xs.Perm ys) :
    (xs.mapM f = none ∧ ys.mapM f = none) ∨
    ∃ as bs, xs.mapM f = some as ∧ ys.mapM f = some bs ∧ as.Perm bs := by
  induction p with
  | nil => exact Or.inr ⟨[], [], rfl, rfl, .nil⟩
  | @cons x xs ys p ih =>
    cases h : f x with
    | none => exact Or.inl ⟨by simp [h], by simp [h]⟩
    | some b =>
      rcases ih with ⟨ha,hb⟩ | ⟨as,bs,ha,hb,hp⟩
      · exact Or.inl ⟨by simp [h,ha], by simp [h,hb]⟩
      · exact Or.inr ⟨b::as,b::bs,by simp [h,ha],by simp [h,hb],hp.cons b⟩
  | swap x y xs =>
    cases hx : f x <;> cases hy : f y <;> cases hs : xs.mapM f <;>
      simp [List.mapM_cons,hx,hy,hs]
    exact List.Perm.swap ..
  | trans p q ih iq =>
    rcases ih with ⟨ha,hb⟩ | ⟨as,bs,ha,hb,hp⟩ <;>
      rcases iq with ⟨hc,hd⟩ | ⟨cs,ds,hc,hd,hq⟩
    · exact Or.inl ⟨ha,hd⟩
    · simp_all
    · simp_all
    · have eq : bs = cs := Option.some.inj (hb.symm.trans hc)
      subst cs
      exact Or.inr ⟨as,ds,ha,hd,hp.trans hq⟩

open RingRetainedChemicalTrace (Key WellFormed assemble)

theorem framed {α : Type} (read : α → Option RingRetainedChemicalTrace.Observation)
    (children : α → List α) (n : Nat) (q : α) {k : Key}
    (h : RingDuplicateScale.build read children n q = some k) : WellFormed k := by
  induction n generalizing q k with
  | zero => simp [RingDuplicateScale.build] at h
  | succ n ih =>
    cases hr : read q with
    | none => simp [RingDuplicateScale.build,hr] at h
    | some o =>
      cases hs : (children q).mapM (RingDuplicateScale.build read children n) with
      | none => simp [RingDuplicateScale.build,hr,hs] at h
      | some ks =>
        have hk : assemble o ks = k := by simpa [RingDuplicateScale.build,hr,hs] using h
        rw [← hk]
        apply RingRetainedChemicalTrace.assemble_framed
        intro c hc
        obtain ⟨t,_,hit⟩ := RingRetainedUnitPass.forOutput hs hc
        exact ih t hit

theorem build_map {i j : Input} (r : AtomMap i j) (focus : List i.certified.Atom)
    (n : Nat) (q : Arm i) (aligned : i.certified.cursorPreviousRootAligned q) :
    RingDuplicateScale.build (active i focus) i.certified.executableLocalizedRerootChildren n q =
    RingDuplicateScale.build (active j (focus.map r.atoms))
      j.certified.executableLocalizedRerootChildren n (r.arm q) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have kids : ((i.certified.executableLocalizedRerootChildren q).map r.arm).Perm
        (j.certified.executableLocalizedRerootChildren (r.arm q)) := r.carrier.children q aligned
    have each : (i.certified.executableLocalizedRerootChildren q).mapM
        (RingDuplicateScale.build (active i focus) i.certified.executableLocalizedRerootChildren n) =
        ((i.certified.executableLocalizedRerootChildren q).map r.arm).mapM
        (RingDuplicateScale.build (active j (focus.map r.atoms)) j.certified.executableLocalizedRerootChildren n) := by
      rw [List.mapM_map]
      apply RingFrameTransport.mapM_congr_mem
      intro t ht
      exact ih t (r.carrier.below q aligned t ht)
    simp only [RingDuplicateScale.build, active_map r focus q aligned]
    rw [each]
    rcases mapM_perm (RingDuplicateScale.build (active j (focus.map r.atoms))
      j.certified.executableLocalizedRerootChildren n) kids with ⟨ha,hb⟩ | ⟨as,bs,ha,hb,hp⟩
    · rw [ha,hb]
    · rw [ha,hb]
      cases active i focus q with
      | none => rfl
      | some o =>
        change some (assemble o as) = some (assemble o bs)
        congr 1
        apply RingRetainedChemicalTrace.assemble_perm o hp
        intro c hc
        obtain ⟨t,_,hit⟩ := RingRetainedUnitPass.forOutput ha hc
        exact framed _ _ n t hit

theorem rebuilt_map {i j : Input} (r : AtomMap i j) (f : Site i) (q : Arm i)
    (aligned : i.certified.cursorPreviousRootAligned q) :
    rebuilt i f q = rebuilt j (r.site f) (r.arm q) := by
  have card : i.certified.certified.input.molecule.atomCount =
      j.certified.certified.input.molecule.atomCount := by
    simpa using Fintype.card_congr r.atoms
  unfold rebuilt
  simpa only [card, RingRawRenumbering.AtomMap.site, List.map_reverse] using
    build_map r f.val.node.history.reverse _ q aligned

end TetraStereo.Engine.RingOriginMetricRenumber

assert_kernel_only TetraStereo.Engine.RingOriginMetricRenumber.pathDistance_map
assert_kernel_only TetraStereo.Engine.RingOriginMetricRenumber.active_map
assert_kernel_only TetraStereo.Engine.RingOriginMetricRenumber.build_map
assert_kernel_only TetraStereo.Engine.RingOriginMetricRenumber.rebuilt_map
