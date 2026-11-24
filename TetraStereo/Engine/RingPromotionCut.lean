import TetraStereo.Engine.RingGeometryCertificates
import TetraStereo.Engine.RingMassDifference
import TetraStereo.Engine.RingNeutralPromotion

/-! # Checking when all local ring promotion trials leave a tie -/

set_option autoImplicit false

namespace TetraStereo.Engine.RingPromotionCut
open RingActivePairReport (Slot)

/-- The possible marked arms are the marked slot and, for a root-returning slot,
other slots carrying the root-return flag. The molecular check verifies this bound. -/
abbrev affected (loop : Slot → Bool) (mark arm : Slot) := mark = arm ∨ (loop mark ∧ loop arm)
def eligible (cls : Slot → Slot) := (List.finRange 4).filter fun j =>
  (List.finRange 4).any fun k => j != k && cls j == cls k

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
/-- If ordinary ties preserve the flag and at most two slots carry it, each
eligible promotion leaves two ordinarily tied slots outside its possible support. -/
theorem outside (cls : Slot → Slot) (loop : Slot → Bool)
    (few : ((List.finRange 4).filter loop).length ≤ 2)
    (respect : ∀ j k, cls j = cls k → loop j = loop k)
    (gate : 3 ≤ (eligible cls).length) (s : Slot) (member : s ∈ eligible cls) :
    ∃ j k, j ≠ k ∧ cls j = cls k ∧ ¬affected loop s j ∧ ¬affected loop s k := by
  have finite : ∀ a b c d : Slot, ∀ w x y z : Bool,
      let cls : Slot → Slot := ![a,b,c,d]
      let loop : Slot → Bool := ![w,x,y,z]
      ((List.finRange 4).filter loop).length ≤ 2 →
      (∀ j k, cls j = cls k → loop j = loop k) →
      3 ≤ (eligible cls).length → ∀ s ∈ eligible cls,
      ∃ j k, j ≠ k ∧ cls j = cls k ∧ ¬affected loop s j ∧ ¬affected loop s k := by decide +kernel
  have clsEq : cls = ![cls 0,cls 1,cls 2,cls 3] := by funext j; fin_cases j <;> rfl
  have loopEq : loop = ![loop 0,loop 1,loop 2,loop 3] := by funext j; fin_cases j <;> rfl
  have h := finite (cls 0) (cls 1) (cls 2) (cls 3) (loop 0) (loop 1) (loop 2) (loop 3)
  dsimp only at h
  rw [← clsEq,← loopEq] at h
  exact h few respect gate s member
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Frame Reader)
open RingGroupedCentre (Arms cursor)
open RingRetainedChemicalTrace (Word)
attribute [local instance] lexOrd

/-- Look only at the atom identifier in each molecular occurrence. A zero fuel
matches the empty domain of the corresponding bounded stereo calculation. -/
def sameBits (i : Input) (s t : Nat) : Nat → Arm i → Bool
  | 0,_ => true
  | n+1,q => RingGroupedMark.bit s q == RingGroupedMark.bit t q &&
    (i.certified.executableLocalizedRerootChildren q).all (sameBits i s t n)

private theorem mapM_congr {α β : Type} (xs : List α) (f g : α → Option β)
    (same : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.mapM_cons,List.mapM_cons,same a List.mem_cons_self,
      ih (fun x hx => same x (List.mem_cons_of_mem _ hx))]

theorem bits_preserve {i : Input} (r : Reader i) (s t : Nat) (n : Nat) (q : Arm i)
    (h : sameBits i s t n q = true) :
    let key := RingRetainedChemicalTrace.key? i
    let kids := i.certified.executableLocalizedRerootChildren
    RingGroupedMark.build i r s key kids n q = RingGroupedMark.build i r t key kids n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [sameBits,Bool.and_eq_true,beq_iff_eq,List.all_eq_true] at h
    obtain ⟨here,below⟩ := h
    have kids := mapM_congr (i.certified.executableLocalizedRerootChildren q) _ _
      (fun c hc => ih c (below c hc))
    simp only [RingGroupedMark.build,kids,RingGroupedMark.join,here]

/-- Test for the priority assigned to an origin-zero duplicate in the Rule 1b column.
The shallow and deep row orders may repeat an occurrence. This test uses only presence. -/
def rootFlag {i f fr read} (a : @Arms i f fr read) (j : Slot) : Bool :=
  ((a.key false j).1[1]?).any fun word => word.any fun row => row.contains (i.molecule.atomCount + 1)

theorem rootFlag_constitution {i f fr read} (a : @Arms i f fr read) (j : Slot) :
    rootFlag a j = (RingRetainedChemicalPreorder.keyFor (fr.direction j)).duplicate.word.any
      (fun row => row.contains (i.molecule.atomCount + 1)) := by
  have prior := a.constitution false j
  change (a.profiles j).unit.priorDeep = _ at prior
  change ((a.profiles j).unit.priorDeep[1]?).any _ = _
  rw [prior]
  rfl

open OneCenter RingRetainedChemicalTrace
open LocalizedChemicalRing (Input)
open RingRetainedConstitution (Cursor)

/-- At the molecular recursion bound the executable incidence test checks
exactly the equality of mark bits on every reachable occurrence. -/
theorem sameBits_iff {i : Input} {s t : Nat} {q : Arm i}
    (valid : i.certified.LocalizedRerootCursorValid q) {n : Nat}
    (bound : i.certified.localizedRerootCursorBudget q < n) :
    sameBits i s t n q = true ↔ ∀ c, Reaches i q c →
      RingGroupedMark.bit s c = RingGroupedMark.bit t c := by
  induction n generalizing q with
  | zero => omega
  | succ n ih =>
    simp only [sameBits,Bool.and_eq_true,beq_iff_eq,List.all_eq_true]
    have frame := i.certified.executableLocalizedRerootChildren_declarative q
    have child (c : Arm i) (hc : c ∈ i.certified.executableLocalizedRerootChildren q) :=
      ih (i.certified.localizedRerootChild_valid q c _ frame hc)
        (by have less := i.certified.localizedRerootChild_budget_lt q c _ valid frame hc; omega)
    constructor
    · rintro ⟨here,below⟩ c reach
      cases reach with
      | here => exact here
      | descend hc rest => exact ((child _ hc).mp (below _ hc)) _ rest
    · intro all
      exact ⟨all q .here,fun c hc => (child c hc).mpr fun v hv => all v (.descend hc hv)⟩

/-- The mark has no effect on a valid arm exactly when the marked atom
identifier occurs nowhere in that arm, including its duplicate leaves. -/
theorem sameBits_neutral_iff {i : Input} (s : Nat) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q) :
    sameBits i s i.molecule.atomCount (i.certified.localizedRerootCursorBudget q + 1) q = true ↔
    ∀ c, Reaches i q c → c.occurrence.val.node.current?.map Fin.val ≠ some s := by
  rw [sameBits_iff valid (Nat.lt_succ_self _)]
  apply forall_congr'; intro c
  rw [RingNeutralPromotion.neutralBit]
  by_cases eqn : c.occurrence.val.node.current?.map Fin.val = some s <;> simp [RingGroupedMark.bit,eqn]

private theorem mem_interleave {α : Type} (x : α) (a b : List (List α)) :
    x ∈ (RingChildKeyRecovery.interleave a b).flatten ↔ x ∈ a.flatten ∨ x ∈ b.flatten := by
  induction a generalizing b with
  | nil => simp [RingChildKeyRecovery.interleave]
  | cons _ _ ih => cases b <;> simp [RingChildKeyRecovery.interleave,ih,or_assoc,or_left_comm]

private theorem in_forest (s : Stage) (z : Nat) (cs : List Key) :
    z ∈ (RingMassDifference.forest s cs).flatten.flatten ↔
      ∃ k ∈ cs, z ∈ (k.column s).levels.flatten.flatten := by
  induction cs with
  | nil => simp [RingMassDifference.forest]
  | cons k ks ih =>
    let a := (k.column s).levels
    let b := RingMassDifference.forest s ks
    have merged : z ∈ (RingChildKeyRecovery.interleave a b).flatten.flatten ↔
        z ∈ a.flatten.flatten ∨ z ∈ b.flatten.flatten := by
      constructor
      · rintro hz
        obtain ⟨row,hrow,here⟩ := List.mem_flatten.mp hz
        rcases (mem_interleave row a b).mp hrow with h | h
        · exact Or.inl (List.mem_flatten.mpr ⟨row,h,here⟩)
        · exact Or.inr (List.mem_flatten.mpr ⟨row,h,here⟩)
      · rintro (h | h) <;> obtain ⟨row,hrow,here⟩ := List.mem_flatten.mp h
        · exact List.mem_flatten.mpr ⟨row,(mem_interleave row a b).mpr (Or.inl hrow),here⟩
        · exact List.mem_flatten.mpr ⟨row,(mem_interleave row a b).mpr (Or.inr hrow),here⟩
    change z ∈ (RingChildKeyRecovery.interleave a b).flatten.flatten ↔ _
    rw [merged]
    simp [b,ih,a]

private theorem entry_in_node (s : Stage) (z : Nat) (o : Observation) (cs : List Key)
    (formed : ∀ k ∈ cs, WellFormed k) :
    z ∈ ((assemble o cs).column s).word.flatten ↔ z = o.atStage s ∨ ∃ k ∈ cs, z ∈ (k.column s).word.flatten := by
  have shape := (assemble_framed o cs formed s).2
  rw [shape,RingMassDifference.common_layout s o cs formed]
  let sh := RingMassDifference.rank RingMassDifference.headAt .mass cs
  let de := RingMassDifference.rank RingMassDifference.wordAt .mass cs
  have ps : sh.Perm cs := List.mergeSort_perm ..
  have pd : de.Perm cs := List.mergeSort_perm ..
  change z ∈ ([o.atStage s] :: ([sh.map _,de.map _] :: RingMassDifference.forest s de).flatten).flatten ↔ _
  simp only [List.flatten_cons,List.flatten_append,List.flatten_nil,List.append_nil,List.mem_append,List.mem_map,
    List.mem_singleton,in_forest]
  apply or_congr_right
  constructor
  · rintro ((⟨k,h,rfl⟩ | ⟨k,h,rfl⟩) | ⟨k,h,hz⟩)
    · exact ⟨k,ps.mem_iff.mp h,by rw [(formed k (ps.mem_iff.mp h) s).2]; simp⟩
    · exact ⟨k,pd.mem_iff.mp h,by rw [(formed k (pd.mem_iff.mp h) s).2]; simp⟩
    · exact ⟨k,pd.mem_iff.mp h,by rw [(formed k (pd.mem_iff.mp h) s).2]; simp [hz]⟩
  · rintro ⟨k,h,hz⟩
    rw [(formed k h s).2] at hz
    simp only [List.flatten_cons,List.mem_append,List.mem_singleton] at hz
    rcases hz with rfl | hz
    · exact Or.inl (Or.inr ⟨k,pd.mem_iff.mpr h,rfl⟩)
    · exact Or.inr ⟨k,pd.mem_iff.mpr h,hz⟩

private theorem observed_flag {i : Input} {d : Nat} {q : Cursor i.certified d} {t o}
    (h : observation? i q t = some o) :
    i.molecule.atomCount+1 = o.duplicate ↔ q.occurrence.val.node.provenance = .ringDuplicate 0 := by
  unfold observation? at h
  obtain ⟨a,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨recd,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
  cases prov : q.occurrence.val.node.provenance <;> simp only [prov] at h <;> try contradiction
  case realAtom =>
    obtain ⟨_,_,out⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj out
    simp [duplicateValue]
  case ringDuplicate d =>
    obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_,_,out⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj out
    simp [duplicateValue]
    omega

theorem duplicate_origin_zero {i : Input} {d : Nat} {q : Cursor i.certified d} {k : Key}
    (e : Expansion i q k) :
    i.molecule.atomCount+1 ∈ k.duplicate.word.flatten ↔
      ∃ c, Reaches i q c ∧ c.occurrence.val.node.provenance = .ringDuplicate 0 := by
  induction e with
  | @node q kids o ks frame seen lookup all sub ih =>
    have actual := Option.some.inj (((i.certified.localizedRerootChildren?_eq_some_iff q kids).mpr frame).symm.trans
      (i.certified.localizedRerootChildren?_eq_some_executable q))
    subst kids
    have formed (k) (hk : k ∈ ks) : WellFormed k := by
      obtain ⟨c,hc,get⟩ := RingRetainedUnitPass.forOutput all hk
      exact (sub c hc get).formed
    change _ ∈ ((assemble o ks).column .duplicate).word.flatten ↔ _
    rw [entry_in_node _ _ _ _ formed]
    constructor
    · rintro (here | ⟨k,hk,flag⟩)
      · exact ⟨q,.here,(observed_flag seen).mp here⟩
      · obtain ⟨c,hc,get⟩ := RingRetainedUnitPass.forOutput all hk
        obtain ⟨t,reach,tag⟩ := (ih c hc get).mp flag
        exact ⟨t,.descend hc reach,tag⟩
    · rintro ⟨t,reach,tag⟩
      cases reach with
      | here => exact Or.inl ((observed_flag seen).mpr tag)
      | descend hc further =>
        obtain ⟨k,hk,get⟩ := RingRetainedReferenceGroup.forInput all hc
        exact Or.inr ⟨k,hk,(ih _ hc get).mpr ⟨_,further,tag⟩⟩


/-- For an actual directed ligand the flag is present exactly when its
occurrence tree reaches a duplicate of the original root at depth zero. -/
theorem rootFlag_iff {i f fr read} (a : @Arms i f fr read) (j : Slot) :
    rootFlag a j = true ↔ ∃ c, Reaches i (cursor fr j) c ∧
      c.occurrence.val.node.provenance = .ringDuplicate 0 := by
  rw [rootFlag_constitution]
  simpa only [List.any_eq_true,List.contains_iff_mem,List.mem_flatten] using
    (duplicate_origin_zero (key_source (RingRetainedChemicalPreorder.read_key (fr.direction j))))

def neutralWord {i f} (fr : Frame i f) (r : Reader i) (j : Slot) : Word :=
  ((RingGroupedMark.arm? i r i.molecule.atomCount (cursor fr j)).map (fun e => e.2.word)).getD []

/-- All normally tied arms have the same neutral word because ordinary
ties include equality of the complete through-4c word. -/
theorem neutral_tie {i f fr read} (a : @Arms i f fr read) (ready : RingGroupedStereo.Ready f read)
    {j k : Slot} (tie : a.key false j = a.key false k) : neutralWord fr read j = neutralWord fr read k := by
  have word (j : Slot) : neutralWord fr read j = RingNeutralPromotion.eraseWord (a.profiles j).lower.word := by
    obtain ⟨e,he⟩ := RingGroupedMark.arm_ready ready i.molecule.atomCount (cursor fr j)
      (RingGroupedCentre.valid fr j) (fr.direction j).property.1
    have same := (RingGroupedMark.arm_source he).1.unique (a.source j)
    simp only [neutralWord,he,Option.map_some,Option.getD_some]
    rw [RingNeutralPromotion.neutral_word he,same]
  have same : (a.profiles j).lower.word = (a.profiles k).lower.word :=
    congrArg (fun x => x.2.2.2.1) tie
  rw [word,word,same]

/-- The remaining molecular check walks atom identifiers to bound each mark's support. -/
def Check {i f fr read} (a : @Arms i f fr read) : Prop :=
  3 ≤ (RingGroupedOrders.marks a).length ∧ ((List.finRange 4).filter (rootFlag a)).length ≤ 2 ∧
  ∀ s j : Slot, ¬affected (rootFlag a) s j →
    sameBits i (RingGroupedTrials.atom fr s) i.molecule.atomCount
      (i.certified.localizedRerootCursorBudget (cursor fr j) + 1) (cursor fr j) = true

def check {i f fr read} (a : @Arms i f fr read) : Bool :=
  let slots := List.finRange 4
  let flag := rootFlag a
  decide (3 ≤ (RingGroupedOrders.marks a).length) && decide ((slots.filter flag).length ≤ 2) &&
    slots.all (fun s => slots.all fun j => decide (affected flag s j) ||
      sameBits i (RingGroupedTrials.atom fr s) i.molecule.atomCount
        (i.certified.localizedRerootCursorBudget (cursor fr j)+1) (cursor fr j))

theorem check_iff {i f fr read} (a : @Arms i f fr read) : check a = true ↔ Check a := by
  simp [check,Check,or_iff_not_imp_left,and_assoc]

theorem check_index {i f fr read} {a : @Arms i f fr read} (ready : RingGroupedStereo.Ready f read)
    (h : Check a) : RingOrientation.index a = 0 := by
  obtain ⟨gate,few,bits⟩ := h
  let cls := RingGroupedOrders.representative a
  have ties : eligible cls = RingGroupedOrders.marks a := by
    unfold eligible RingGroupedOrders.marks
    apply List.filter_congr
    intro j _
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,cls,RingGroupedOrders.representative_iff a _ _ false]
  have flag (j k : Slot) (eqn : cls j = cls k) : rootFlag a j = rootFlag a k := by
    unfold rootFlag
    rw [(RingGroupedOrders.representative_iff a j k false).mp eqn]
  have each (s : Slot) (hs : s ∈ RingGroupedOrders.marks a) :
      RingOrientation.orientation (RingGroupedOrders.wins a false (RingOrientation.markedWord fr read s)) = 0 := by
    obtain ⟨j,k,ne,eqn,hj,hk⟩ := outside cls _ few flag (ties ▸ gate) s (ties ▸ hs)
    have ordinary := (RingGroupedOrders.representative_iff a j k false).mp eqn
    have neutral (j : Slot) (off : ¬affected (rootFlag a) s j) :
        RingOrientation.markedWord fr read s j = neutralWord fr read j := by
      unfold RingOrientation.markedWord neutralWord RingGroupedMark.arm?
      rw [bits_preserve read _ _ _ _ (bits s j off)]
    apply (RingOrientation.orientation_zero _).mpr
    intro inj
    exact ne (inj (Prod.ext ordinary ((neutral j hj).trans ((neutral_tie a ready ordinary).trans (neutral k hk).symm))))
  unfold RingOrientation.index
  rw [if_neg (by omega)]
  exact List.sum_eq_zero (fun x hx => by obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx; exact each s hs)

/-- A successful cut certificate yields a completed refusal on both geometries. -/
theorem publication {i : Input} {q : Site i} (c : RingGeometryCertificates.Context i q)
    (h : Check c.arms) : RingGroupedPublication.state i q = some none := by
  obtain ⟨s,hs,pub,_⟩ := RingGeometryCriterion.at_centre c.coordinates q c.fr.recognized
  rw [RingGeometryCriterion.state_eq c.coordinates,← RingGeometryCriterion.rootReader_exact c.coordinates q,← c.geometric] at hs
  simp [RingGeometryCriterion.signature?,c.frame,c.profiles] at hs
  subst s
  rw [pub]
  apply congrArg some
  have ready : RingGroupedStereo.Ready q c.read := by
    rw [c.geometric,RingGeometryCriterion.rootReader_exact c.coordinates]
    exact RingGroupedPublication.ready (RingGroupedGeometry.physical c.coordinates) q
  exact (RingGeometryCriterion.Signature.refusal_iff _).mpr (by simp [check_index ready h])

/-- A graph proof of locality can discharge the last premise without running any mark trial. -/
theorem publication_of_locality {i : Input} {q : Site i} (c : RingGeometryCertificates.Context i q)
    (eligibleMarks : 3 ≤ (RingGroupedOrders.marks c.arms).length)
    (fewReturns : ((List.finRange 4).filter (rootFlag c.arms)).length ≤ 2)
    (locality : ∀ s j : Slot, ¬affected (rootFlag c.arms) s j →
      ∀ v, Reaches i (cursor c.fr j) v →
        v.occurrence.val.node.current?.map Fin.val ≠ some (RingGroupedTrials.atom c.fr s)) :
    RingGroupedPublication.state i q = some none :=
  publication c ⟨eligibleMarks,fewReturns,fun s j off =>
    (sameBits_neutral_iff _ _ (RingGroupedCentre.valid c.fr j)).mpr (locality s j off)⟩

def refusal? {i : Input} {q : Site i} (c : RingGeometryCertificates.Context i q) :
    Option (PLift (RingGroupedPublication.state i q = some none)) :=
  if ok : check c.arms = true then some ⟨publication c ((check_iff _).mp ok)⟩ else none

end TetraStereo.Engine.RingPromotionCut

assert_kernel_only TetraStereo.Engine.RingPromotionCut.rootFlag_iff
assert_kernel_only TetraStereo.Engine.RingPromotionCut.sameBits_neutral_iff
assert_kernel_only TetraStereo.Engine.RingPromotionCut.outside
assert_kernel_only TetraStereo.Engine.RingPromotionCut.publication
assert_kernel_only TetraStereo.Engine.RingPromotionCut.publication_of_locality
