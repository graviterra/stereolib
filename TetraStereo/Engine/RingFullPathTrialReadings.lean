import TetraStereo.Engine.RingFullPathEligibility

/-! # Coordinate readings for ordinary and marked full-path priorities -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingFullPathTrialReadings
open OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot)
open RingStereoSiblingPass (Legal order legal_order)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key Reads key? candidates)

def bitWord (bs : List Bool) : Word := bs.map fun b => [b.toNat]

/-- Earlier rules compare in sequence. Only an ordinary tie reaches the
last component that gives the marked molecular atom priority. -/
def trialKey (k : Key) (marked : Word) : List (List Word) :=
  [k.throughFourA,[bitWord k.bestFourB],[k.fourC],[bitWord k.fixedR],[marked]]

def trials (ks : Slot → Key) : List (Option Slot) :=
  match candidates ks with
  | [] => [none]
  | s :: ss => (s :: ss).map some

def markWords? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) :
    Option Slot → Option (Slot → Word)
  | none => some (fun _ => [])
  | some s => (RingGroupedTrials.marking? fr r s).map RingGroupedTrials.Marking.word

def MarkWords {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (rev : Bool) :
    Option Slot → (Slot → Word) → Prop
  | none,ws => ∀ k, ws k = []
  | some s,ws => ∀ k, ∃ b, RingGroupedMark.OnGeometry i r rev (RingGroupedTrials.atom fr s)
      (RingGroupedCentre.cursor fr k) b ∧ ws k = b.word

theorem mark_exact {i f r} (fr : @Frame i f) (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (s : Option Slot) :
    ∃ ws, markWords? fr r s = some ws ∧ ∀ other, MarkWords fr r rev s other ↔ other = ws := by
  cases s with
  | none => exact ⟨_,rfl,fun w => ⟨fun h => funext h,fun h _ => congrFun h _⟩⟩
  | some s =>
    obtain ⟨m,hm⟩ := Option.isSome_iff_exists.mp (RingGroupedTrials.marking_ready fr ready s)
    have src (k : Slot) : RingGroupedMark.OnGeometry i r rev (RingGroupedTrials.atom fr s)
        (RingGroupedCentre.cursor fr k) (m.branches k) := by
      cases rev
      · exact m.source k
      · exact (m.source k).reflect
    refine ⟨m.word,by simp [markWords?,hm],fun w => ⟨?_,?_⟩⟩
    · intro h
      funext k
      obtain ⟨b,hb,eqn⟩ := h k
      exact eqn.trans (congrArg RingStereoSiblingPass.Branch.word (hb.unique (src k)))
    · rintro rfl k
      exact ⟨_,src k,rfl⟩

private def strict (w : Slot → List (List Word)) :=
  (List.finRange 4).all fun a => (List.finRange 4).all fun b => a == b || w a != w b

private theorem strict_injective {w : Slot → List (List Word)} : strict w = true ↔ Function.Injective w := by
  simp only [strict,List.all_eq_true,List.mem_finRange,forall_const,Bool.or_eq_true,beq_iff_eq,bne_iff_ne]
  grind [Function.Injective]

def hand? {i f} (fr : @Frame i f) (rev : Bool) (row : List Slot) :=
  let g := inputGeometry i.certified
  readback? (if rev then mirror g else g) (fr.atoms row)

/-- A completed tie yields an absent hand. A strict order reads the four
coordinate carriers in that priority order. -/
def readTrial {i f} (fr : @Frame i f) (rev : Bool) (w : Slot → List (List Word)) : Option RS :=
  if strict w then hand? fr rev (order w (List.finRange 4)) else none

inductive Outcome {i f} (fr : @Frame i f) (rev : Bool) (w : Slot → List (List Word)) :
    Option RS → Prop where
  | tie {j k} (different : j ≠ k) (same : w j = w k) : Outcome fr rev w none
  | hand {row h} (strictOrder : Function.Injective w) (legal : Legal w (List.finRange 4) row)
      (observed : hand? fr rev row = some h) : Outcome fr rev w (some h)

theorem read_exact {i f} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (fr : @Frame i f) (rev : Bool) (w : Slot → List (List Word)) (answer : Option RS) :
    Outcome fr rev w answer ↔ answer = readTrial fr rev w := by
  have canon := legal_order w (List.finRange 4)
  by_cases injective : Function.Injective w
  · have strictRow := strict_injective.mpr injective
    have physical := RingGroupedGeometry.calibrated geom fr _ canon.perm
    obtain ⟨h,hh⟩ := Option.isSome_iff_exists.mp physical
    have found : (hand? fr rev (order w (List.finRange 4))).isSome = true := by
      cases rev <;> simp [hand?,readback_mirror,hh]
    obtain ⟨hand,seen⟩ := Option.isSome_iff_exists.mp found
    rw [readTrial,if_pos strictRow,seen]
    constructor
    · intro o
      cases o with
      | tie ne eqn => exact (ne (injective eqn)).elim
      | hand _ legal observed =>
        have same := List.Perm.eq_of_pairwise
          (fun _ _ _ _ ab ba => injective (le_antisymm ba ab))
          (List.pairwise_map.mp legal.descending) (List.pairwise_map.mp canon.descending)
          (legal.perm.trans canon.perm.symm)
        exact observed.symm.trans (same ▸ seen)
    · rintro rfl
      exact .hand injective canon seen
  · have fail : ¬ strict w = true := fun h => injective (strict_injective.mp h)
    rw [readTrial,if_neg fail]
    constructor
    · rintro (_ | ⟨inj,_,_⟩)
      · rfl
      · exact (injective inj).elim
    · rintro rfl
      unfold Function.Injective at injective
      push_neg at injective
      obtain ⟨j,k,same,ne⟩ := injective
      exact .tie ne same

def readings? {i f} (fr : @Frame i f) (r : Reader i) (rev : Bool) :
    Option (List (Option Slot × Option RS)) := do
  let ks ← RingActivePairReport.four? fun k => key? i r rev (RingGroupedCentre.cursor fr k)
  (trials ks).mapM fun s => do
    let ws ← markWords? fr r s
    return (s,readTrial fr rev (fun k => trialKey (ks k) (ws k)))

/-- All baseline trials start on one ready reader. Every
reported entry agrees with every legal choice of the ordinary priorities,
mark readings and coordinate ranking for its trial. -/
theorem ready_readings {i f r} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (fr : @Frame i f) (ready : RingGroupedStereo.Ready f r) (rev : Bool) :
    ∃ ks out, readings? fr r rev = some out ∧ out.map Prod.fst = trials ks ∧
      (∀ k, Reads i r rev (RingGroupedCentre.cursor fr k) (ks k)) ∧
      ∀ s v, (s,v) ∈ out → ∀ (keys : Slot → Key) (ws : Slot → Word),
        (∀ k, Reads i r rev (RingGroupedCentre.cursor fr k) (keys k)) →
        MarkWords fr r rev s ws → Outcome fr rev (fun k => trialKey (keys k) (ws k)) v := by
  have each (k : Slot) := RingFullPathEligibility.key_exact ready rev (RingGroupedCentre.cursor fr k)
    (RingGroupedCentre.valid fr k) (fr.direction k).property.1
  choose keys got onlyKey using each
  obtain ⟨ks,hks⟩ := Option.isSome_iff_exists.mp (RingActivePairReport.four_full _ fun k =>
    Option.isSome_iff_exists.mpr ⟨keys k,got k⟩)
  have same : ks = keys := funext fun k =>
    Option.some.inj ((RingActivePairReport.four_at hks k).symm.trans (got k))
  subst ks
  choose words hw unique using mark_exact fr ready rev
  let entry := fun s => (s,readTrial fr rev (fun k => trialKey (keys k) (words s k)))
  refine ⟨keys,(trials keys).map entry,?_,?_,fun k => (onlyKey k _).mpr rfl,?_⟩
  · have pureRow (xs : List (Option Slot)) :
        xs.mapM (fun s => some (entry s)) = some (xs.map entry) := by
      induction xs with
      | nil => rfl
      | cons s ss ih => simp [List.mapM_cons,ih]
    simpa [readings?,hks,hw,entry] using pureRow (trials keys)
  · simp [List.map_map,entry,Function.comp_def]
  · intro s v mem other ws hOther hWs
    obtain ⟨u,_,out⟩ := List.mem_map.mp mem
    have mark : u = s := congrArg Prod.fst out
    subst u
    have hand := congrArg Prod.snd out
    obtain rfl := show other = keys from funext fun k => (onlyKey k _).mp (hOther k)
    obtain rfl := (unique s ws).mp hWs
    exact (read_exact geom fr rev _ _).mpr hand.symm

/-- All baseline trials start on the same reachable frozen reader. Every
reported entry agrees with every legal choice of the ordinary priorities,
mark readings and coordinate ranking for its trial. -/
theorem frozen_readings {i f} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (fr : @Frame i f) (rev : Bool) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    ∃ ks out, readings? fr r rev = some out ∧ out.map Prod.fst = trials ks ∧
      (∀ k, Reads i r rev (RingGroupedCentre.cursor fr k) (ks k)) ∧
      ∀ s v, (s,v) ∈ out → ∀ (keys : Slot → Key) (ws : Slot → Word),
        (∀ k, Reads i r rev (RingGroupedCentre.cursor fr k) (keys k)) →
        MarkWords fr r rev s ws → Outcome fr rev (fun k => trialKey (keys k) (ws k)) v :=
  ready_readings geom fr (RingGroupedPublication.ready (RingGroupedGeometry.physical geom) f) rev

end TetraStereo.Engine.RingFullPathTrialReadings
assert_kernel_only TetraStereo.Engine.RingFullPathTrialReadings.read_exact
assert_kernel_only TetraStereo.Engine.RingFullPathTrialReadings.frozen_readings
