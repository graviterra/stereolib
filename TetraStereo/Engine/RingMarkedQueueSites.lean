import TetraStereo.Engine.RingMarkedTreeOrder
import TetraStereo.Engine.RingMarkedDistanceOrder

/-! Molecular child rows for a paired Rule 6 traversal. Both sorts take their
priorities from the unordered marked trees of actual children. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedQueueSites
open OneCenter RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRule5Shape (Valid On kids)
open RingGroupedMark (Reading bit)

abbrev Slot (i : Input) := Arm i × Branch

def child? (i : Input) (r : Reader i) (atom : Nat) (q : Arm i) : Option (Slot i) := do
  let n := i.certified.localizedRerootCursorBudget q + 1
  let b ← RingMarkedTreeOrder.reconstruct n (RingMarkedTreeFold.view i r atom n q)
  return (q,b)

private def sorted {α κ : Type} [LinearOrder κ] (key : α → κ) (xs : List α) :=
  xs.insertionSort fun a b => key b ≤ key a

private theorem sorted_legal {i : Input} {κ : Type} [LinearOrder κ]
    (key : Branch → κ) (xs : List (Slot i)) :
    Legal key (xs.map Prod.snd) ((sorted (fun x : Slot i => key x.2) xs).map Prod.snd) := by
  let le (a b : Slot i) := key b.2 ≤ key a.2
  letI : Std.Total le := ⟨fun a b => le_total _ _⟩
  letI : IsTrans (Slot i) le := ⟨fun _ _ _ ab bc => le_trans bc ab⟩
  refine ⟨(List.perm_insertionSort le xs).map Prod.snd,?_⟩
  simpa only [List.pairwise_map,sorted] using List.pairwise_insertionSort le xs

def pop? (i : Input) (r : Reader i) (atom : Nat) (q : Arm i) := do
  let cs ← (kids i q).mapM (child? i r atom)
  return (sorted (fun c : Slot i => c.2.shallow) cs,
    sorted (fun c : Slot i => c.2.deep) cs)

def Good {i : Input} (f : Site i) (r : Reader i) (atom : Nat) (s : Slot i) :=
  Valid s.1 ∧ On f s.1 ∧ Reading i r atom s.1 s.2

private theorem budget_lt {i : Input} {p c : Arm i}
    (v : Valid p) (hc : c ∈ kids i p) :
    i.certified.localizedRerootCursorBudget c < i.certified.localizedRerootCursorBudget p :=
  i.certified.localizedRerootChild_budget_lt p c _ v
    (i.certified.executableLocalizedRerootChildren_declarative p) hc

/-- Both sorted lists are full physical child frames. The parent has exactly
these two value rows, and every enqueued site has a smaller cursor budget. -/
theorem pop_ready {i : Input} {f : Site i} {r : Reader i} {atom : Nat}
    (ready : RingGroupedStereo.Ready f r) {s : Slot i} (good : Good f r atom s) :
    ∃ sh de, pop? i r atom s.1 = some (sh,de) ∧
      (sh.map Prod.fst).Perm (kids i s.1) ∧ (de.map Prod.fst).Perm (kids i s.1) ∧
      s.2.levels = rows (sh.map Prod.snd) (de.map Prod.snd) ∧
      ∀ c ∈ de, Good f r atom c ∧
        i.certified.localizedRerootCursorBudget c.1 < i.certified.localizedRerootCursorBudget s.1 := by
  obtain ⟨q,b⟩ := s
  obtain ⟨valid,on,read⟩ := good
  change Reading i r atom q b at read
  change Valid q at valid
  change On f q at on
  cases read with
  | @node q prior cs oldSh oldDe before lookup all sub shallow deep =>
    have frame := i.certified.executableLocalizedRerootChildren_declarative q
    have props (c : Arm i) (hc : c ∈ kids i q) :
        Valid c ∧ On f c :=
      ⟨i.certified.localizedRerootChild_valid _ _ _ frame hc,
        (i.certified.localizedRerootChildren_root_eq _ _ _ frame hc).trans on⟩
    have pack : ∀ c ∈ kids i q, ∀ t, lookup c = some t →
        child? i r atom c = some (c,t) := by
      intro c hc t ht
      have exactTree := RingMarkedTreeOrder.reconstruct_reading ready _ (props c hc).1
        (props c hc).2 (Nat.lt_succ_self _) (sub c hc ht)
      simp only [child?,exactTree]
      rfl
    have bridge : ∀ (qs : List (Arm i)) (bs : List Branch),
        (∀ c ∈ qs, c ∈ kids i q) → qs.mapM lookup = some bs →
        ∃ es : List (Slot i), qs.mapM (child? i r atom) = some es ∧
          es.map Prod.fst = qs ∧ es.map Prod.snd = bs ∧
          ∀ e ∈ es, e.1 ∈ kids i q ∧ lookup e.1 = some e.2 := by
      intro qs
      induction qs with
      | nil => intro bs _ h; exact ⟨[],rfl,rfl,(Option.some.inj h),by simp⟩
      | cons c qs ih =>
        intro bs mem h
        rw [List.mapM_cons] at h
        obtain ⟨v,hv,rest⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨vs,hvs,out⟩ := Option.bind_eq_some_iff.mp rest
        cases Option.some.inj out
        obtain ⟨es,hes,hq,hb,each⟩ := ih vs (fun t ht => mem t (.tail _ ht)) hvs
        have hc := mem c List.mem_cons_self
        exact ⟨(c,v)::es,by simp [List.mapM_cons,pack c hc v hv,hes],by simp [hq],
          by simp [hb],by simpa only [List.forall_mem_cons] using And.intro (And.intro hc hv) each⟩
    obtain ⟨es,hes,hq,hb,each⟩ := bridge _ _ (fun _ h => h) all
    let sh := sorted (fun e : Slot i => e.2.shallow) es
    let de := sorted (fun e : Slot i => e.2.deep) es
    have ps : sh.Perm es := List.perm_insertionSort _ _
    have pd : de.Perm es := List.perm_insertionSort _ _
    have legS := sorted_legal Branch.shallow es
    have legD := sorted_legal Branch.deep es
    rw [hb] at legS legD
    refine ⟨sh,de,by simp [pop?,hes,sh,de],hq ▸ ps.map Prod.fst,hq ▸ pd.map Prod.fst,?_,?_⟩
    · exact rows_unique shallow deep legS legD (fun t ht => by
        obtain ⟨c,hc,hit⟩ := RingRetainedUnitPass.forOutput all ht
        exact (sub c hc hit).framed)
    · intro e he
      obtain ⟨hc,hit⟩ := each e (pd.mem_iff.mp he)
      exact ⟨⟨(props _ hc).1,(props _ hc).2,sub _ hc hit⟩,budget_lt valid hc⟩

/-- The abstract queue may pop any occurrence with this priority. A witness
must supply the actual sorted lists at that occurrence. -/
def Allowed {i : Input} (f : Site i) (r : Reader i) (atom : Nat)
    (b : Branch) (sh de : List Branch) : Prop :=
  ∃ q ss ds, Good f r atom (q,b) ∧ pop? i r atom q = some (ss,ds) ∧
    ss.map Prod.snd = sh ∧ ds.map Prod.snd = de

theorem allowed_layout {i : Input} {f : Site i} {r : Reader i} {atom : Nat}
    (ready : RingGroupedStereo.Ready f r) {b sh de} (h : Allowed f r atom b sh de) :
    b.levels = rows sh de := by
  obtain ⟨q,ss,ds,good,found,rfl,rfl⟩ := h
  obtain ⟨s,d,got,_,_,layout,_⟩ := pop_ready ready good
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans got))
  exact layout

/-- The finite queue is inhabited for every valid marked ligand, including leaves. -/
theorem visits {i : Input} {f : Site i} {r : Reader i} {atom : Nat}
    (ready : RingGroupedStereo.Ready f r) {q : Arm i} {b : Branch}
    (good : Good f r atom (q,b)) : ∃ out, Visits (Allowed f r atom) [b] [] out := by
  let accepts (s : Slot i) (ss ds : List (Slot i)) :=
    Good f r atom s ∧ pop? i r atom s.1 = some (ss,ds)
  let bound (n : Nat) (s : Slot i) :=
    Good f r atom s ∧ i.certified.localizedRerootCursorBudget s.1 < n
  have existsWalk := visits_exist (allowed := accepts) bound
    (fun _ h => Nat.not_lt_zero _ h.2) (by
      intro n s hs
      obtain ⟨ss,ds,found,_,_,_,next⟩ := pop_ready ready hs.1
      exact ⟨ss,ds,⟨hs.1,found⟩,fun c hc =>
        ⟨(next c hc).1,lt_of_lt_of_le (next c hc).2 (Nat.lt_succ_iff.mp hs.2)⟩⟩)
  obtain ⟨out,walk⟩ := existsWalk (i.certified.localizedRerootCursorBudget q + 1)
    [(q,b)] (fun c hc => by
      obtain rfl := List.mem_singleton.mp hc
      exact ⟨good,Nat.lt_succ_self _⟩)
  exact ⟨out.map Prod.snd,walk.map Prod.snd (fun s ss ds h =>
    ⟨s.1,ss,ds,h.1,h.2,rfl,rfl⟩)⟩

end TetraStereo.Engine.RingMarkedQueueSites
assert_kernel_only TetraStereo.Engine.RingMarkedQueueSites.pop_ready
assert_kernel_only TetraStereo.Engine.RingMarkedQueueSites.allowed_layout
assert_kernel_only TetraStereo.Engine.RingMarkedQueueSites.visits
