import TetraStereo.Engine.RingGroupedMark
import TetraStereo.Engine.RingRule5Shape

set_option autoImplicit false

namespace TetraStereo.Engine.RingMarkedTreeFold
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingRule5Shape (Valid On kids)
open private key_state from TetraStereo.Engine.RingRule5Shape
open private lower_earlier from TetraStereo.Engine.RingRetainedSeedFrames

/-- A bounded, unordered native tree carrying the complete earlier key and mark. -/
def Shape : Nat → Type
  | 0 => Unit
  | n+1 => (List Word × Nat) × Multiset (Shape n)

def view (i : Input) (r : Reader i) (atom : Nat) : (n : Nat) → Arm i → Shape n
  | 0,_ => ()
  | n+1,q => ((RingRule5Shape.key i r false q, RingGroupedMark.bit atom q),
      ((kids i q).map (view i r atom n) : Multiset (Shape n)))

/-- Equal complete bounded native trees give equal marked priorities. The bound
covers both cursor budgets; the selected atoms need not coincide. -/
theorem reading_eq {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (n : Nat)
    {a b : Arm i} {atom other : Nat} {x y : Branch}
    (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (ba : i.certified.localizedRerootCursorBudget a < n)
    (bb : i.certified.localizedRerootCursorBudget b < n)
    (same : view i r atom n a = view i r other n b)
    (left : RingGroupedMark.Reading i r atom a x)
    (right : RingGroupedMark.Reading i r other b y) : x = y := by
  classical
  induction n generalizing a b atom other x y with
  | zero => omega
  | succ n ih =>
    have heads := congrArg (fun t => t.1.1) same
    have marks := congrArg (fun t => t.1.2) same
    have population := congrArg Prod.snd same
    change RingRule5Shape.key i r false a = RingRule5Shape.key i r false b at heads
    change RingGroupedMark.bit atom a = RingGroupedMark.bit other b at marks
    have prior_eq {p t : Branch}
        (hp : RingRetainedStereoRefinement.Derives i r false [.lowercase] a p)
        (ht : RingRetainedStereoRefinement.Derives i r false [.lowercase] b t) : p = t := by
      obtain ⟨sa,ha⟩ := RingOccurrenceStereo.state_at ready false va oa
      obtain ⟨sb,hb⟩ := RingOccurrenceStereo.state_at ready false vb ob
      have ka := key_state ready sa (ha.symm ▸ oa)
      have kb := key_state ready sb (hb.symm ▸ ob)
      rw [ha] at ka
      rw [hb] at kb
      have low := (lower_earlier (a := sa) (b := sb)
        (ka.symm.trans (heads.trans kb))).2
      have pa := RingRetainedStereoRefinement.unique _ _ _ _ hp (ha ▸ sa.source.lower)
      have pb := RingRetainedStereoRefinement.unique _ _ _ _ ht (hb ▸ sb.source.lower)
      exact pa.trans (low.trans pb.symm)
    let Has (s : Shape n) (z : Branch) : Prop :=
      ∃ (q : Arm i) (mark : Nat), Valid q ∧ On f q ∧
        i.certified.localizedRerootCursorBudget q < n ∧
        view i r mark n q = s ∧ RingGroupedMark.Reading i r mark q z
    let out (s : Shape n) : Branch := if h : ∃ z, Has s z then h.choose else x
    have factor (q : Arm i) (mark : Nat) (z : Branch) (vq : Valid q) (oq : On f q)
        (bq : i.certified.localizedRerootCursorBudget q < n)
        (hz : RingGroupedMark.Reading i r mark q z) : z = out (view i r mark n q) := by
      have existsZ : ∃ z, Has (view i r mark n q) z := ⟨z,q,mark,vq,oq,bq,rfl,hz⟩
      dsimp only [out]
      rw [dif_pos existsZ]
      obtain ⟨t,m,vt,ot,bt,st,ht⟩ := existsZ.choose_spec
      exact ih vq vt oq ot bq bt st.symm hz ht
    have child_valid (q : Arm i) (c : Arm i) (hc : c ∈ kids i q) : Valid c :=
      i.certified.localizedRerootChild_valid q c _
        (i.certified.executableLocalizedRerootChildren_declarative q) hc
    have child_on (q : Arm i) (c : Arm i) (hc : c ∈ kids i q) (oq : On f q) : On f c :=
      (i.certified.localizedRerootChildren_root_eq q c _
        (i.certified.executableLocalizedRerootChildren_declarative q) hc).trans oq
    have child_budget (q : Arm i) (c : Arm i) (hc : c ∈ kids i q) (vq : Valid q)
        (bq : i.certified.localizedRerootCursorBudget q < n+1) :
        i.certified.localizedRerootCursorBudget c < n := by
      have := i.certified.localizedRerootChild_budget_lt q c _ vq
        (i.certified.executableLocalizedRerootChildren_declarative q) hc
      omega
    have factor_list (q : Arm i) (mark : Nat) (look : Arm i → Option Branch) (cs : List Branch)
        (all : (kids i q).mapM look = some cs)
        (below : ∀ c ∈ kids i q, ∀ {z}, look c = some z → RingGroupedMark.Reading i r mark c z)
        (vq : Valid q) (oq : On f q) (bq : i.certified.localizedRerootCursorBudget q < n+1) :
        cs = ((kids i q).map (view i r mark n)).map out := by
      have pairs := TerminalTie.mapM_forall₂ _ _ _ all
      have transform : ∀ (xs : List (Arm i)) (zs : List Branch),
          List.Forall₂ (fun c z => look c = some z) xs zs →
          (∀ c ∈ xs, c ∈ kids i q) →
          List.Forall₂ (fun c z => out (view i r mark n c) = z) xs zs := by
        intro xs zs h
        induction h with
        | nil => intro _; exact .nil
        | @cons c z xs zs hz rest ih =>
          intro mem
          have hc := mem c List.mem_cons_self
          exact .cons (factor c mark z (child_valid q c hc) (child_on q c hc oq)
            (child_budget q c hc vq bq) (below c hc hz)).symm
            (ih (fun t ht => mem t (List.mem_cons_of_mem _ ht)))
      have eqs := transform _ _ pairs (fun _ h => h)
      have equal := List.forall₂_map_left_iff.mpr eqs
      rw [List.forall₂_eq_eq_eq] at equal
      simpa only [List.map_map,Function.comp_def] using equal.symm
    cases left with
    | node p look ca sub sa da =>
      cases right with
      | node p' look' cb sub' sb db =>
        have earlier := prior_eq p p'
        have ea := factor_list a atom look _ ca sub va oa ba
        have eb := factor_list b other look' _ cb sub' vb ob bb
        have perm : ((kids i a).map (view i r atom n)).Perm
            ((kids i b).map (view i r other n)) := Quotient.exact population
        have rowsPerm := perm.map out
        rw [← ea,← eb] at rowsPerm
        have rows := rows_unique sa da
          ⟨sb.perm.trans rowsPerm.symm,sb.descending⟩ ⟨db.perm.trans rowsPerm.symm,db.descending⟩
          (fun z hz => by
            obtain ⟨c,hc,get⟩ := RingRetainedUnitPass.forOutput ca hz
            exact (sub c hc get).framed)
        simp only [RingRetainedStereoRefinement.extend,earlier,marks,rows]

/-- Executable marked arms share the same full Branch when their complete
bounded views agree. Frozen earlier profiles remain internal to the evaluator. -/
theorem arm_eq {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (n : Nat)
    {a b : Arm i} {atom other : Nat}
    (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (ba : i.certified.localizedRerootCursorBudget a < n)
    (bb : i.certified.localizedRerootCursorBudget b < n)
    (same : view i r atom n a = view i r other n b) :
    (RingGroupedMark.arm? i r atom a).map Prod.snd =
      (RingGroupedMark.arm? i r other b).map Prod.snd := by
  obtain ⟨x,hx⟩ := RingGroupedMark.arm_ready ready atom a va oa
  obtain ⟨y,hy⟩ := RingGroupedMark.arm_ready ready other b vb ob
  have eqn := reading_eq ready n va vb oa ob ba bb same
    (RingGroupedMark.arm_source hx).2 (RingGroupedMark.arm_source hy).2
  simp only [hx,hy,Option.map_some,eqn]

end TetraStereo.Engine.RingMarkedTreeFold

assert_kernel_only TetraStereo.Engine.RingMarkedTreeFold.reading_eq
assert_kernel_only TetraStereo.Engine.RingMarkedTreeFold.arm_eq
