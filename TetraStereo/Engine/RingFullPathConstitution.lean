import TetraStereo.Engine.RingFullPathReport
import TetraStereo.Engine.RingGraphCache

/-! # Constitutional early decisions inside the full-path evaluator

Four pairwise distinct constitutional ligand words decide a centre before any
stereo suffix or promotion mark is read. The through-4a word of every legal
molecular reading extends the constitutional word by one entry, so both
priority rows of the full-path evaluator are fixed by constitution alone on
each geometry. The derivation below is local to the full-path publication:
it reads the evaluator's own keys, its single unmarked trial and its own
reversal count on an arbitrary ready reader. No grouped publication enters. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingFullPathConstitution
open OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingPromotionAggregation (readingScore readingBalance)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader Labels)
open RingActivePairReport (Slot)
open RingActiveDistanceSchedule (Cell View evaluate)
open RingRetainedChemicalTrace (Word)
open RingStereoSiblingPass (Legal)
open RingGroupedCentre (cursor)
open RingGeometryCriterion (Signature)
open RingFullPathEligibility (Key Reads key?)
open RingFullPathTrialReadings (trialKey trials Outcome hand? readings?)
open RingFullPathPublication (publish? centre? keys? letters)
open RingSphereQueue (early? finalCell molecularQueue inventory SkipsNoncentres)
open RingZeroMassReport (zeroEarly?)

/-! ## Constitutional words and the through-4a prefix -/

/-- The constitutional word tested by the early signature at one slot. -/
def word {i : Input} {f : Site i} (fr : Frame i f) (s : Slot) : List Word :=
  RingRetainedChemicalPreorder.orderWord (RingRetainedChemicalPreorder.keyFor (fr.direction s))

private theorem nat_lt (a b : List Nat) : compare a b = .lt ↔ a < b :=
  DeclarativeCIP.compareLex_eq_lt_iff_of compare (fun _ _ => compare_lt_iff_lt)
    (fun _ _ => Std.compare_eq_eq_iff_eq) a b

theorem word_lt (a b : List Word) : compare a b = .lt ↔ a < b :=
  DeclarativeCIP.compareLex_eq_lt_iff_of compare
    (DeclarativeCIP.compareLex_eq_lt_iff_of compare nat_lt (fun _ _ => Std.compare_eq_eq_iff_eq))
    (fun _ _ => Std.compare_eq_eq_iff_eq) a b

/-- Every legal molecular key on either geometry extends the constitutional
word of its slot by exactly one Rule 4a entry. -/
theorem through_extends {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i} {rev : Bool}
    {s : Slot} {k : Key} (legal : Reads i r rev (cursor fr s) k) :
    ∃ u : Word, k.throughFourA = word fr s ++ [u] := by
  obtain ⟨u,_,_,_,_,du,_,_,_,_,rfl⟩ := legal
  have unitRead : RingRetainedUnitPass.Reading i r rev (cursor fr s) u := du
  obtain ⟨c,hc,prior⟩ := unitRead.constitution
  have same := Option.some.inj (hc.symm.trans (RingRetainedChemicalPreorder.read_key (fr.direction s)))
  exact ⟨u.word,congrArg (fun prefix' : List Word => prefix' ++ [u.word])
    (prior.trans (congrArg RingRetainedChemicalPreorder.orderWord same))⟩

private theorem head_order {c d : List Word} (len : c.length = d.length) (ne : c ≠ d)
    (u v : Word) (t w : List (List Word)) :
    (c ++ [u]) :: t < (d ++ [v]) :: w ↔ c < d := by
  rw [List.cons_lt_cons_iff,RingPathRankTransport.snoc_lt len]
  constructor
  · rintro ((h | ⟨h,_⟩) | ⟨h,_⟩)
    · exact h
    · exact (ne h).elim
    · exact (ne (List.append_inj_left h len)).elim
  · exact fun h => Or.inl (Or.inl h)

/-- With distinct constitutional words, every trial comparison is decided
by constitution, whatever the later ordinary components and marks are. -/
private theorem trial_order {a b : Key} {c d : List Word} {u v : Word}
    (ha : a.throughFourA = c ++ [u]) (hb : b.throughFourA = d ++ [v])
    (len : c.length = d.length) (ne : c ≠ d) (m n : Word) :
    trialKey a m < trialKey b n ↔ c < d := by
  unfold trialKey
  rw [ha,hb]
  exact head_order len ne ..

private theorem trial_ne {a b : Key} {c d : List Word} {u v : Word}
    (ha : a.throughFourA = c ++ [u]) (hb : b.throughFourA = d ++ [v])
    (len : c.length = d.length) (ne : c ≠ d) (m n : Word) : trialKey a m ≠ trialKey b n := by
  intro eqn
  have head : a.throughFourA = b.throughFourA := by
    unfold trialKey at eqn
    exact (List.cons.inj eqn).1
  rw [ha,hb] at head
  exact ne (List.append_inj_left head len)

private theorem key_ne {a b : Key} {c d : List Word} {u v : Word}
    (ha : a.throughFourA = c ++ [u]) (hb : b.throughFourA = d ++ [v])
    (len : c.length = d.length) (ne : c ≠ d) : a ≠ b := by
  rintro rfl
  exact ne (List.append_inj_left (ha.symm.trans hb) len)

private theorem word_length {i : Input} {f : Site i} (fr : Frame i f) (j k : Slot) :
    (word fr j).length = (word fr k).length := rfl

/-! ## Both priority rows are fixed before any stereo suffix or mark -/

section Strict
variable {i : Input} {f : Site i} (fr : Frame i f)

/-- Every row of trial keys built from legal readings is strict and carries
the constitutional order, on either geometry and under any mark words. -/
private theorem row_order (strict : Function.Injective (word fr)) {keys : Slot → Key}
    (shape : ∀ s, ∃ u : Word, (keys s).throughFourA = word fr s ++ [u]) (marks : Slot → Word)
    (j k : Slot) (ne : j ≠ k) :
    trialKey (keys j) (marks j) < trialKey (keys k) (marks k) ↔ word fr j < word fr k := by
  obtain ⟨u,hu⟩ := shape j
  obtain ⟨v,hv⟩ := shape k
  exact trial_order hu hv (word_length fr j k) (strict.ne ne) _ _

private theorem row_injective (strict : Function.Injective (word fr)) {keys : Slot → Key}
    (shape : ∀ s, ∃ u : Word, (keys s).throughFourA = word fr s ++ [u]) (marks : Slot → Word) :
    Function.Injective fun s => trialKey (keys s) (marks s) := by
  intro j k eqn
  by_contra ne
  obtain ⟨u,hu⟩ := shape j
  obtain ⟨v,hv⟩ := shape k
  exact trial_ne hu hv (word_length fr j k) (strict.ne ne) _ _ eqn

/-- No ordinary tie survives, so the trial list is the single unmarked trial. -/
private theorem one_trial (strict : Function.Injective (word fr)) {keys : Slot → Key}
    (shape : ∀ s, ∃ u : Word, (keys s).throughFourA = word fr s ++ [u]) : trials keys = [none] := by
  have empty : RingFullPathEligibility.tiedSlots keys = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro s member
    obtain ⟨j,ne,tie⟩ := (RingFullPathEligibility.mem_tied keys s).mp member
    obtain ⟨u,hu⟩ := shape s
    obtain ⟨v,hv⟩ := shape j
    exact key_ne hu hv (word_length fr s j) (strict.ne ne) tie
  simp [trials,RingFullPathEligibility.candidates,empty]

/-- The same constitutional order governs the original and the reflected
row, so no ordinary comparison reverses. -/
private theorem no_reversal (strict : Function.Injective (word fr)) {x y : Slot → Key}
    (actual : ∀ s, ∃ u : Word, (x s).throughFourA = word fr s ++ [u])
    (reflected : ∀ s, ∃ u : Word, (y s).throughFourA = word fr s ++ [u]) :
    RingFullPathPublication.reversals x y = 0 := by
  change RingFullPathTrialParity.reversals x y = 0
  unfold RingFullPathTrialParity.reversals
  apply List.countP_eq_zero.mpr
  intro p hp
  have ne : p.2 ≠ p.1 :=
    (ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp hp)).symm
  have same : trialKey (x p.2) [] < trialKey (x p.1) [] ↔ trialKey (y p.2) [] < trialKey (y p.1) [] :=
    (row_order fr strict actual (fun _ => []) p.2 p.1 ne).trans
      (row_order fr strict reflected (fun _ => []) p.2 p.1 ne).symm
  simp [same]

end Strict

/-! ## The coordinate reading of a strict row -/

/-- In a descending strict row, an earlier position is a greater key. -/
private theorem position_order {κ : Type} [LinearOrder κ] {w : Slot → κ} (inj : Function.Injective w)
    {row : List Slot} (legal : Legal w (List.finRange 4) row) {j k : Slot} (ne : j ≠ k) :
    row.idxOf k < row.idxOf j ↔ w j < w k := by
  have mem (s : Slot) : s ∈ row := legal.perm.mem_iff.mpr (List.mem_finRange s)
  have descending := List.pairwise_map.mp legal.descending
  have before {a b : Slot} (lt : row.idxOf a < row.idxOf b) : w b ≤ w a := by
    have h := List.pairwise_iff_getElem.mp descending _ _ (List.idxOf_lt_length_of_mem (mem a))
      (List.idxOf_lt_length_of_mem (mem b)) lt
    simpa only [List.getElem_idxOf] using h
  have distinct : row.idxOf j ≠ row.idxOf k := fun h => ne ((List.idxOf_inj (mem j)).mp h)
  constructor
  · intro lt
    exact lt_of_le_of_ne (before lt) (fun h => ne (inj h))
  · intro lt
    by_contra no
    have other : row.idxOf j < row.idxOf k := by omega
    exact absurd (before other) (not_le.mpr lt)

/-- Parity of the sorting permutation from the six comparisons of the keys. -/
theorem sorted_parity {κ : Type} [LinearOrder κ] {w : Slot → κ} (inj : Function.Injective w)
    {row : List Slot} (legal : Legal w (List.finRange 4) row)
    (test : Slot → Slot → Bool) (law : ∀ j k, j ≠ k → (w j < w k ↔ test j k = true)) :
    RingJointObservations.parity ⟨row,legal.perm⟩ =
      decide (LocalizedChemicalRing.ConstitutionalPartition.pairs.countP
        (fun p => test p.1 p.2) % 2 = 0) := by
  have parity : ∀ ss ∈ (List.finRange 4).permutations',
      decide (LocalizedChemicalRing.ConstitutionalPartition.pairs.countP
        (fun p => decide (ss.idxOf p.2 < ss.idxOf p.1)) % 2 = 0) =
      RawMolecule.permutationIsEven (ss.map Fin.val) := by decide +kernel
  have count := (List.Perm.refl LocalizedChemicalRing.ConstitutionalPartition.pairs).countP_congr
    (p := fun p => decide (row.idxOf p.2 < row.idxOf p.1))
    (p' := fun p => test p.1 p.2)
    (fun p hp => Bool.eq_iff_iff.mpr (by
      have ne := ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp hp)
      simpa only [decide_eq_true_eq] using (position_order inj legal ne).trans (law _ _ ne)))
  change RawMolecule.permutationIsEven (row.map Fin.val) = _
  rw [← parity row (List.mem_permutations'.mpr legal.perm),count]

theorem strict_orientation {α : Type} [Ord α] [Std.LawfulEqOrd α] (key : Slot → α)
    (inj : Function.Injective key) :
    RingOrientation.orientation key =
      if LocalizedChemicalRing.ConstitutionalPartition.pairs.countP
        (fun p => compare (key p.1) (key p.2) == .lt) % 2 = 0 then 1 else -1 := by
  have no : ¬ LocalizedChemicalRing.ConstitutionalPartition.pairs.any
      (fun p => compare (key p.1) (key p.2) == .eq) = true := by
    intro h
    obtain ⟨p,hp,v⟩ := List.any_eq_true.mp h
    exact (ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp hp))
      (inj (Std.compare_eq_eq_iff_eq.mp (beq_iff_eq.mp v)))
  unfold RingOrientation.orientation
  dsimp only
  rw [if_neg no]

/-- The physical hand of any legal row carrying the constitutional order is
the written-frame sign times the constitutional orientation. -/
private theorem strict_score {i : Input} {f : Site i} (fr : Frame i f)
    (strict : Function.Injective (word fr)) {w : Slot → List (List Word)}
    (inj : Function.Injective w) (order : ∀ j k, j ≠ k → (w j < w k ↔ word fr j < word fr k))
    {row : List Slot} {h : RS} (legal : Legal w (List.finRange 4) row)
    (observed : hand? fr false row = some h) :
    readingScore (some h) = RingOrientation.baseline fr * RingOrientation.orientation (word fr) := by
  have parity := sorted_parity inj legal (fun j k => compare (word fr j) (word fr k) == .lt)
    (fun j k ne => by simpa only [beq_iff_eq,word_lt] using order j k ne)
  have seen : readback? (inputGeometry i.certified) (fr.atoms row) = some h := by
    simpa only [hand?,Bool.false_eq_true,if_false] using observed
  rw [RingOrientation.frame_read fr _ ⟨row,legal.perm⟩,parity] at seen
  rw [strict_orientation (word fr) strict]
  unfold RingOrientation.baseline
  generalize readback? (inputGeometry i.certified) (fr.atoms (List.finRange 4)) = base at seen ⊢
  by_cases even : LocalizedChemicalRing.ConstitutionalPartition.pairs.countP
      (fun p => compare (word fr p.1) (word fr p.2) == .lt) % 2 = 0
  · rcases base with _ | (_ | _) <;> cases h <;> simp_all [readingScore]
  · rcases base with _ | (_ | _) <;> cases h <;> simp_all [readingScore,RS.swap]

/-! ## The local early-exit theorem -/

private theorem keys_some {i : Input} {f : Site i} {r : Reader i} (fr : Frame i f)
    (ready : RingGroupedStereo.Ready f r) (rev : Bool) :
    ∃ ks, keys? fr r rev = some ks ∧ ∀ s, Reads i r rev (cursor fr s) (ks s) := by
  have each (s : Slot) := RingFullPathEligibility.key_exact ready rev (cursor fr s)
    (RingGroupedCentre.valid fr s) (fr.direction s).property.1
  choose ks computed exactKey using each
  obtain ⟨keys,row⟩ := Option.isSome_iff_exists.mp
    (RingActivePairReport.four_full _ (fun s => Option.isSome_iff_exists.mpr ⟨ks s,computed s⟩))
  have same : keys = ks := funext fun s => Option.some.inj
    ((RingActivePairReport.four_at row s).symm.trans (computed s))
  subst keys
  exact ⟨ks,row,fun s => (exactKey s _).mpr rfl⟩

/-- Core statement on a recognized frame. The full-path centre rule reads
its own two key rows and its own single trial on an arbitrary ready reader.
With four distinct constitutional words it issues the constitutional
signature: the written-frame sign times the constitutional orientation,
with no reversing pair. -/
theorem strict_centre {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (fr : Frame i f) (strict : Function.Injective (word fr))
    {r : Reader i} (ready : RingGroupedStereo.Ready f r) :
    centre? fr r = some (Signature.letters
      ⟨RingOrientation.baseline fr * RingOrientation.orientation (word fr),0⟩) := by
  obtain ⟨ks,hk,actual⟩ := keys_some fr ready false
  obtain ⟨ms,hm,reflected⟩ := keys_some fr ready true
  obtain ⟨ks',out,hout,slots,reads',sound⟩ := RingFullPathTrialReadings.ready_readings geom fr ready false
  have shapeK (s : Slot) := through_extends fr (actual s)
  have shapeM (s : Slot) := through_extends fr (reflected s)
  have shapeK' (s : Slot) := through_extends fr (reads' s)
  rw [one_trial fr strict shapeK'] at slots
  obtain ⟨v,rfl⟩ : ∃ v, out = [(none,v)] := by
    rcases out with _ | ⟨⟨s,v⟩,tail⟩
    · simp at slots
    · simp only [List.map_cons,List.cons.injEq] at slots
      obtain ⟨rfl,nil⟩ := slots
      obtain rfl := List.map_eq_nil_iff.mp nil
      exact ⟨v,rfl⟩
  have outcome : Outcome fr false (fun s => trialKey (ks s) []) v :=
    sound none v (List.mem_cons.mpr (Or.inl rfl)) ks (fun _ => []) actual (fun _ => rfl)
  have inj := row_injective fr strict shapeK (fun _ => [])
  have rev0 := no_reversal fr strict shapeK shapeM
  have issued : centre? fr r = some (letters ks ms [v]) := by
    simp only [centre?,hk,hm,hout,Option.bind_some,Option.map_some,List.map_cons,List.map_nil]
  rw [issued]
  cases outcome with
  | tie different same => exact (different (inj same)).elim
  | @hand row h _ legal observed =>
    have score := strict_score fr strict inj
      (fun j k ne => row_order fr strict shapeK (fun _ => []) j k ne) legal observed
    have balance : readingBalance [some h] =
        RingOrientation.baseline fr * RingOrientation.orientation (word fr) := by
      simpa [readingBalance] using score
    simp only [letters,Signature.letters,balance,rev0]

/-- A strict constitutional early decision is exactly the full-path local
publication at that focus on every ready reader. -/
theorem early_publish {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {sig : Signature} (hit : early? i q = some sig)
    {r : Reader i} (ready : RingGroupedStereo.Ready q r) :
    publish? i q r = some sig.letters := by
  unfold early? at hit
  obtain ⟨fr,hf,tail⟩ := Option.bind_eq_some_iff.mp hit
  dsimp only at tail
  split at tail
  · contradiction
  rename_i nonzero
  obtain rfl := Option.some.inj tail
  have moving : RingOrientation.orientation (word fr) ≠ 0 := nonzero
  have strict : Function.Injective (word fr) := by
    by_contra h
    exact moving ((RingOrientation.orientation_zero _).mpr h)
  have local' : publish? i q r = centre? fr r := by simp [publish?,hf]
  rw [local']
  exact strict_centre geom fr strict ready

/-- The zero-mass form of the same decision. -/
theorem zero_early_publish {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {sig : Signature} (hit : zeroEarly? i q = some sig)
    {r : Reader i} (ready : RingGroupedStereo.Ready q r) :
    publish? i q r = some sig.letters :=
  early_publish geom ((RingZeroMassReport.zero_early_exact i q).symm.trans hit) ready

/-! ## Fast local rule, including auxiliary sites -/

/-- Decide a constitutionally strict occurrence without reading the store.
A tied occurrence uses the full-path rule on its frozen store. -/
def fastPublish (i : Input) (q : Site i) (r : View i) : Cell :=
  match zeroEarly? i q with
  | some s => some s.letters
  | none => publish? i q r

/-- On every ready reader the fast rule is the full-path rule. -/
theorem fast_local {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready q r) :
    fastPublish i q r = publish? i q r := by
  unfold fastPublish
  cases found : zeroEarly? i q with
  | some s => exact (zero_early_publish geom found ready).symm
  | none => rfl

/-- The distance-recursive state of the fast rule is the full-path state. -/
theorem fast_state (i : Input) (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    evaluate (fastPublish i) = RingFullPathPublication.state i := by
  symm
  apply RingActiveDistanceSchedule.unique
  intro q
  exact (RingFullPathPublication.state_eq i q).trans
    (fast_local geom (RingFullPathPublication.ready geom q)).symm

theorem fast_skips (i : Input) : SkipsNoncentres (fastPublish i) := by
  intro q r no
  have absent : RingNestedActivePair.frame? i q = none := by simp [RingNestedActivePair.frame?,no]
  simp [fastPublish,zeroEarly?,absent,RingFullPathReport.skips i q r no]

/-- Use the early exit at the requested root and at every queued auxiliary.
The original-root inventory is run only on a root tie. -/
def fastRoot (i : Input) (root : i.certified.Atom) : Cell :=
  match zeroEarly? i (RingGroupedReport.origin i root) with
  | some s => some s.letters
  | none => finalCell (fastPublish i) root (RingGraphCache.queue i root)

theorem fast_root_exact (i : Input) (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) : fastRoot i root = RingFullPathReport.rootCell i root := by
  have full : RingFullPathReport.rootCell i root =
      RingFullPathPublication.state i (RingGroupedReport.origin i root) :=
    RingSphereQueue.final_exact (RingFullPathReport.skips i) (inventory i root)
  rw [full]
  unfold fastRoot
  cases found : zeroEarly? i (RingGroupedReport.origin i root) with
  | some s =>
    exact ((RingFullPathPublication.state_eq i _).trans
      (zero_early_publish geom found (RingFullPathPublication.ready geom _))).symm
  | none =>
    exact (RingSphereQueue.final_exact (fast_skips i) (RingGraphCache.inventory i root)).trans
      (congrFun (fast_state i geom) _)

def fastReport (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun a => (fastRoot i a).map fun v => (a.val,v)

/-- The queued fast report is the full-path report for every requested list. -/
theorem fast_report_exact (i : Input) (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) : fastReport i atoms = RingFullPathReport.forAtoms? i atoms := by
  unfold fastReport
  simp only [fast_root_exact i geom]
  rfl

/-- The fast report satisfies the independent molecular specification. -/
theorem fast_report_iff (i : Input) (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) (report : RingGroupedReport.Report) :
    fastReport i atoms = some report ↔ RingFullPathReport.Correct i atoms report := by
  rw [fast_report_exact i geom]
  exact RingFullPathReport.report_iff i geom atoms report

end TetraStereo.Engine.RingFullPathConstitution
assert_kernel_only TetraStereo.Engine.RingFullPathConstitution.through_extends
assert_kernel_only TetraStereo.Engine.RingFullPathConstitution.strict_centre
assert_kernel_only TetraStereo.Engine.RingFullPathConstitution.early_publish
assert_kernel_only TetraStereo.Engine.RingFullPathConstitution.fast_state
assert_kernel_only TetraStereo.Engine.RingFullPathConstitution.fast_report_exact

assert_kernel_only TetraStereo.Engine.RingFullPathConstitution.sorted_parity
assert_kernel_only TetraStereo.Engine.RingFullPathConstitution.strict_orientation
