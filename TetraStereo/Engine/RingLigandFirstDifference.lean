import TetraStereo.Engine.RingFullPathTrialReadings

/-! Exact all-ligand first-difference reduction of the native full-path trial key. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingLigandFirstDifference
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey bitWord)
attribute [local instance] lexOrd

/-- The exact native precedence, with the active promotion word last. -/
inductive Stage where
  | rule1a | rule1b | rule2 | rule4a | rule4b | rule4c | rule5 | activeMark
  deriving DecidableEq, Repr

def stages : List Stage := [.rule1a,.rule1b,.rule2,.rule4a,.rule4b,.rule4c,.rule5,.activeMark]

def Stage.rank : Stage → Fin 8
  | .rule1a => 0 | .rule1b => 1 | .rule2 => 2 | .rule4a => 3
  | .rule4b => 4 | .rule4c => 5 | .rule5 => 6 | .activeMark => 7

theorem stages_complete (s : Stage) : s ∈ stages := by cases s <;> simp [stages]
theorem stages_nodup : stages.Nodup := by decide
theorem stages_ordered : stages.Pairwise (fun a b => a.rank < b.rank) := by decide

structure Words where
  atomic : Word
  duplicate : Word
  mass : Word
  unit : Word
  fourB : Word
  fourC : Word
  five : Word
  marked : Word

def Words.at (w : Words) : Stage → Word
  | .rule1a => w.atomic | .rule1b => w.duplicate | .rule2 => w.mass
  | .rule4a => w.unit | .rule4b => w.fourB | .rule4c => w.fourC
  | .rule5 => w.five | .activeMark => w.marked

/-- Exact field decomposition, rather than an assumption about a final comparison. -/
structure Decomposes (key : Key) (mark : Word) (w : Words) : Prop where
  through : key.throughFourA = [w.atomic,w.duplicate,w.mass,w.unit]
  fourB : bitWord key.bestFourB = w.fourB
  fourC : key.fourC = w.fourC
  five : bitWord key.fixedR = w.five
  marked : mark = w.marked

/-- Accepted molecular readings expose the three constitutional subwords and
Rule 4a unit word, together with the precise remaining native fields. -/
theorem extract {i : Input} {r : Reader i} {rev : Bool} {arm : Arm i} {key : Key}
    (accepted : Reads i r rev arm key) (mark : Word) :
    ∃ c : RingRetainedChemicalTrace.Key, ∃ w : Words,
      RingRetainedChemicalTrace.key? i arm = some c ∧ Decomposes key mark w ∧
      w.atomic = c.atomic.word ∧ w.duplicate = c.duplicate.word ∧ w.mass = c.mass.word := by
  obtain ⟨u,l,ar,as',fr,du,_,_,_,_,rfl⟩ := accepted
  have reading : RingRetainedUnitPass.Reading i r rev arm u := du
  obtain ⟨c,native,prior⟩ := reading.constitution
  refine ⟨c,⟨c.atomic.word,c.duplicate.word,c.mass.word,u.word,
    bitWord (max ar as'),l.word,bitWord fr,mark⟩,native,?_,rfl,rfl,rfl⟩
  refine ⟨?_,rfl,rfl,rfl,rfl⟩
  change u.priorDeep ++ [u.word] = _
  rw [prior]
  rfl

/-- Independent left-to-right scan of the typed stage directions. -/
def scan (directions : Stage → Ordering) : List Stage → Ordering
  | [] => .eq
  | s::ss => (directions s).then (scan directions ss)

def directions (a b : Words) (s : Stage) : Ordering := compare (a.at s) (b.at s)

/-- Equality of Ordering preserves lt, eq, and gt without a strictness premise. -/
theorem compare_trial_eq_scan {a b : Key} {m n : Word} {x y : Words}
    (hx : Decomposes a m x) (hy : Decomposes b n y) :
    compare (trialKey a m) (trialKey b n) = scan (directions x y) stages := by
  simp only [trialKey,hx.through,hy.through,hx.fourB,hy.fourB,hx.fourC,hy.fourC,
    hx.five,hy.five,hx.marked,hy.marked,stages,scan,directions,Words.at,List.compare_cons_cons]
  simp [Ordering.then_assoc]

/-- An actual first deciding stage, all earlier stages having tied. -/
inductive First (directions : Stage → Ordering) : List Stage → Stage → Ordering → Prop where
  | here {s ss} (nonzero : directions s ≠ .eq) : First directions (s::ss) s (directions s)
  | later {s ss t o} (tie : directions s = .eq) (rest : First directions ss t o) :
      First directions (s::ss) t o

theorem First.nonzero {d ss s o} (h : First d ss s o) : o ≠ .eq := by
  induction h with
  | here ne => exact ne
  | later _ _ ih => exact ih

theorem First.value {d ss s o} (h : First d ss s o) : d s = o := by
  induction h with
  | here => rfl
  | later _ _ ih => exact ih

theorem First.scan_value {d ss s o} (h : First d ss s o) : scan d ss = o := by
  induction h with
  | here ne => cases eqn : d _ <;> simp_all [scan]
  | later tie _ ih => simp [scan,tie,ih]

theorem First.unique {d ss s t o p} (a : First d ss s o) (b : First d ss t p) : s = t ∧ o = p := by
  induction a with
  | here ne => cases b with
    | here => exact ⟨rfl,rfl⟩
    | later tie rest => exact (ne tie).elim
  | later tie rest ih => cases b with
    | here ne => exact (ne tie).elim
    | later _ other => exact ih other

theorem scan_tie_iff (d : Stage → Ordering) (ss : List Stage) :
    scan d ss = .eq ↔ ∀ s ∈ ss, d s = .eq := by
  induction ss with
  | nil => simp [scan]
  | cons s ss ih => cases h : d s <;> simp [scan,h,ih]

theorem scan_decides (d : Stage → Ordering) (ss : List Stage) (nonzero : scan d ss ≠ .eq) :
    ∃! s, First d ss s (scan d ss) := by
  have witness : ∃ s o, First d ss s o := by
    induction ss with
    | nil => exact (nonzero rfl).elim
    | cons s ss ih =>
      by_cases tie : d s = .eq
      · have tail : scan d ss ≠ .eq := by simpa [scan,tie] using nonzero
        obtain ⟨t,o,h⟩ := ih tail
        exact ⟨t,o,First.later tie h⟩
      · exact ⟨s,d s,First.here tie⟩
  obtain ⟨s,o,h⟩ := witness
  refine ⟨s,h.scan_value.symm ▸ h,?_⟩
  intro t other
  exact (other.unique (h.scan_value.symm ▸ h)).1

theorem full_tie_iff {a b : Key} {m n : Word} {x y : Words}
    (hx : Decomposes a m x) (hy : Decomposes b n y) :
    compare (trialKey a m) (trialKey b n) = .eq ↔ ∀ s ∈ stages, x.at s = y.at s := by
  rw [compare_trial_eq_scan hx hy,scan_tie_iff]
  simp only [directions,Std.compare_eq_eq_iff_eq]

theorem full_tie_iff_all {a b : Key} {m n : Word} {x y : Words}
    (hx : Decomposes a m x) (hy : Decomposes b n y) :
    compare (trialKey a m) (trialKey b n) = .eq ↔ ∀ s, x.at s = y.at s := by
  rw [full_tie_iff hx hy]
  exact ⟨fun h s => h s (stages_complete s),fun h s _ => h s⟩

theorem unique_deciding_stage {a b : Key} {m n : Word} {x y : Words}
    (hx : Decomposes a m x) (hy : Decomposes b n y)
    (nonzero : compare (trialKey a m) (trialKey b n) ≠ .eq) :
    ∃! s, First (directions x y) stages s (compare (trialKey a m) (trialKey b n)) := by
  rw [compare_trial_eq_scan hx hy] at nonzero ⊢
  exact scan_decides _ _ nonzero

/-- Every pair of valid rooted arms on either geometry has an exact stage scan;
no constitutional distinctness, successful hand or final rank is assumed. -/
theorem all_arms {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (rev : Bool) (a b : Arm i)
    (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (ra : a.occurrence.val.root = f.val.root) (rb : b.occurrence.val.root = f.val.root)
    (m n : Word) :
    ∃ ka kb : Key, ∃ x y : Words,
      RingFullPathEligibility.key? i r rev a = some ka ∧
      RingFullPathEligibility.key? i r rev b = some kb ∧
      Decomposes ka m x ∧ Decomposes kb n y ∧
      compare (trialKey ka m) (trialKey kb n) = scan (directions x y) stages := by
  obtain ⟨ka,ha,onlyA⟩ := RingFullPathEligibility.key_exact ready rev a va ra
  obtain ⟨kb,hb,onlyB⟩ := RingFullPathEligibility.key_exact ready rev b vb rb
  obtain ⟨_,x,_,dx,_,_,_⟩ := extract ((onlyA ka).mpr rfl) m
  obtain ⟨_,y,_,dy,_,_,_⟩ := extract ((onlyB kb).mpr rfl) n
  exact ⟨ka,kb,x,y,ha,hb,dx,dy,compare_trial_eq_scan dx dy⟩

/-- The executable optional active marking used by native trials. -/
def markWord? {i : Input} (r : Reader i) (active : Option Nat) (a : Arm i) : Option Word :=
  match active with
  | none => some []
  | some id => (RingGroupedMark.arm? i r id a).map (fun b => b.2.word)

theorem mark_total {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (active : Option Nat) (a : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid a) (root : a.occurrence.val.root = f.val.root) :
    ∃ m, markWord? r active a = some m := by
  cases active with
  | none => exact ⟨[],rfl⟩
  | some id =>
    obtain ⟨b,hit⟩ := RingGroupedMark.arm_ready ready id a valid root
    exact ⟨b.2.word,by simp [markWord?,hit]⟩

/-- The active word is the actual marked pass on either geometry, rather than
an arbitrary supplied preference. The unmarked trial has the empty word. -/
theorem mark_source {i : Input} {r : Reader i} {a : Arm i} {active : Option Nat} {m : Word}
    (hit : markWord? r active a = some m) (rev : Bool) :
    match active with
    | none => m = []
    | some id => ∃ b, RingGroupedMark.OnGeometry i r rev id a b ∧ m = b.word := by
  cases active with
  | none => exact (Option.some.inj hit).symm
  | some id =>
    obtain ⟨b,read,value⟩ := Option.map_eq_some_iff.mp hit
    have source := (RingGroupedMark.arm_source read).2
    cases rev
    · exact ⟨b.2,source,value.symm⟩
    · exact ⟨b.2,source.reflect,value.symm⟩

/-- Full reduction for every valid rooted pair, with the native optional
active marking computed as well as the accepted ordinary keys. -/
theorem all_active_arms {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (rev : Bool) (a b : Arm i)
    (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (ra : a.occurrence.val.root = f.val.root) (rb : b.occurrence.val.root = f.val.root)
    (active : Option Nat) :
    ∃ ka kb : Key, ∃ m n : Word, ∃ x y : Words,
      RingFullPathEligibility.key? i r rev a = some ka ∧
      RingFullPathEligibility.key? i r rev b = some kb ∧
      markWord? r active a = some m ∧ markWord? r active b = some n ∧
      Decomposes ka m x ∧ Decomposes kb n y ∧
      compare (trialKey ka m) (trialKey kb n) = scan (directions x y) stages := by
  obtain ⟨m,hm⟩ := mark_total ready active a va ra
  obtain ⟨n,hn⟩ := mark_total ready active b vb rb
  obtain ⟨ka,kb,x,y,ha,hb,dx,dy,eqn⟩ := all_arms ready rev a b va vb ra rb m n
  exact ⟨ka,kb,m,n,x,y,ha,hb,hm,hn,dx,dy,eqn⟩

theorem First.prefix_rows {d ss s o} (h : First d ss s o) :
    ∃ before after, ss = before ++ s::after ∧ (∀ t ∈ before, d t = .eq) ∧ d s = o := by
  induction h with
  | here => exact ⟨[],_,rfl,by simp,rfl⟩
  | @later head tail s o tie rest ih =>
    obtain ⟨before,after,row,prior,value⟩ := ih
    exact ⟨head::before,after,by simp [row],by simpa using And.intro tie prior,value⟩

private theorem scan_congr {a b : Stage → Ordering} {ss : List Stage}
    (same : ∀ s ∈ ss, a s = b s) : scan a ss = scan b ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [scan,same s (by simp),ih (fun t h => same t (by simp [h]))]

/-- If an independent chemical stage sequence disagrees with the native
comparison, some first direction differs, and every prior direction agrees.
The independent sequence need not be strict and may itself contain ties. -/
theorem independent_disagreement {a b : Key} {m n : Word} {x y : Words}
    (hx : Decomposes a m x) (hy : Decomposes b n y) (independent : Stage → Ordering)
    (different : compare (trialKey a m) (trialKey b n) ≠ scan independent stages) :
    ∃ s before after, stages = before ++ s::after ∧
      (∀ t ∈ before, directions x y t = independent t) ∧ directions x y s ≠ independent s := by
  let delta (s : Stage) := if directions x y s = independent s then Ordering.eq else .gt
  have nonzero : scan delta stages ≠ .eq := by
    intro tied
    apply different
    rw [compare_trial_eq_scan hx hy]
    apply scan_congr
    intro s member
    have eqn := (scan_tie_iff delta stages).mp tied s member
    by_contra ne
    simp [delta,ne] at eqn
  obtain ⟨s,first,_⟩ := scan_decides delta stages nonzero
  obtain ⟨before,after,row,prior,value⟩ := first.prefix_rows
  refine ⟨s,before,after,row,?_,?_⟩
  · intro t member
    have eqn := prior t member
    by_contra ne
    simp [delta,ne] at eqn
  · intro same
    apply first.nonzero
    rw [←value]
    simp [delta,same]

end TetraStereo.Engine.RingLigandFirstDifference
assert_kernel_only TetraStereo.Engine.RingLigandFirstDifference.extract
assert_kernel_only TetraStereo.Engine.RingLigandFirstDifference.compare_trial_eq_scan
assert_kernel_only TetraStereo.Engine.RingLigandFirstDifference.scan_tie_iff
assert_kernel_only TetraStereo.Engine.RingLigandFirstDifference.unique_deciding_stage
assert_kernel_only TetraStereo.Engine.RingLigandFirstDifference.full_tie_iff
assert_kernel_only TetraStereo.Engine.RingLigandFirstDifference.all_arms
assert_kernel_only TetraStereo.Engine.RingLigandFirstDifference.mark_source
assert_kernel_only TetraStereo.Engine.RingLigandFirstDifference.all_active_arms
assert_kernel_only TetraStereo.Engine.RingLigandFirstDifference.independent_disagreement
assert_kernel_only TetraStereo.Engine.RingLigandFirstDifference.full_tie_iff_all
