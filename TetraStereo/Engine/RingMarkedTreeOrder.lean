import TetraStereo.Engine.RingMarkedTreeFold
import TetraStereo.Engine.RingMarkedTypeRecovery

/-! An executable ordered-key decoder for unordered marked native trees. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedTreeOrder
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word Framed)
open RingMarkedTreeFold (Shape view)
open RingRule5Shape (Valid On kids)
open private mapM_perm from TetraStereo.Engine.RingActivePairs
open private prior_read from TetraStereo.Engine.RingMarkedTypeRecovery

/-- Every rule word starts with the singleton observation at its own root. -/
def heads (d : List Word) : List Nat :=
  d.map fun w => (w.head?.bind List.head?).getD 0

private theorem heads_derived {i r rev q b} : ∀ os,
    RingRetainedStereoRefinement.Derives i r rev os q b → heads b.deep = b.shallow
  | [],h => by
    cases h with
    | @node q k labs cs sh de hk seen physical look all sub first second =>
      have formed := (RingRetainedChemicalTrace.key_source hk).formed
      have a := (formed .atomic).2
      have d := (formed .duplicate).2
      have m := (formed .mass).2
      change k.atomic.word = _ at a
      change k.duplicate.word = _ at d
      change k.mass.word = _ at m
      simp [heads,RingRetainedUnitPass.branch,Branch.deep,Branch.shallow,Branch.word,
        RingRetainedChemicalPreorder.orderWord,RingRetainedChemicalTrace.Observation.atStage,a,d,m]
  | o::os,h => by
    cases h with
    | @node q p v cs sh de prior seen look all sub first second =>
      have ih := heads_derived os prior
      change heads (p.deep ++ [[o.value v rev] :: (rows sh de).flatten]) = p.shallow ++ [o.value v rev]
      simpa only [heads,List.map_append,List.map_cons,List.map_nil,List.head?_cons,
        Option.bind_some,Option.getD_some] using congrArg (fun x => x ++ [o.value v rev]) ih

private abbrev FramedBranch := {b : Branch // Framed 2 b.levels}

private def pack (d : List Word) (mark : Nat) (cs : List FramedBranch) : FramedBranch :=
  let bs := cs.map Subtype.val
  ⟨⟨heads d,d,mark,rows (order Branch.shallow bs) (order Branch.deep bs)⟩,
    rows_framed (legal_order Branch.shallow bs).perm (legal_order Branch.deep bs).perm
      (fun b hb => by obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb; exact v.property)⟩

private theorem pack_perm (d : List Word) (mark : Nat) {xs ys : List FramedBranch}
    (p : xs.Perm ys) : pack d mark xs = pack d mark ys := by
  apply Subtype.ext
  have perm := p.map Subtype.val
  have same := rows_unique (legal_order Branch.shallow (xs.map Subtype.val))
    (legal_order Branch.deep (xs.map Subtype.val))
    ⟨(legal_order Branch.shallow (ys.map Subtype.val)).perm.trans perm.symm,
      (legal_order Branch.shallow (ys.map Subtype.val)).descending⟩
    ⟨(legal_order Branch.deep (ys.map Subtype.val)).perm.trans perm.symm,
      (legal_order Branch.deep (ys.map Subtype.val)).descending⟩
    (fun b hb => by obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb; exact v.property)
  simp only [pack,same]

private def collect {α : Type} (d : List Word) (mark : Nat)
    (read : α → Option FramedBranch) (children : Multiset α) : Option FramedBranch :=
  Quotient.liftOn children (fun xs => (xs.mapM read).map (pack d mark)) (by
    intro xs ys p
    change xs.Perm ys at p
    cases hx : xs.mapM read with
    | some ks =>
      obtain ⟨us,hu,perm⟩ := mapM_perm p.symm hx
      simp [hx,hu,pack_perm d mark perm]
    | none =>
      cases hy : ys.mapM read with
      | none => simp [hx,hy]
      | some us =>
        obtain ⟨ks,hk,_⟩ := mapM_perm p hy
        simp [hx] at hk)

private def checked : (n : Nat) → Shape n → Option FramedBranch
  | 0,_ => none
  | n+1,t => collect t.1.1 t.1.2 (checked n) t.2

/-- Reconstruct the complete marked branch using only the finite unordered tree. -/
def reconstruct (n : Nat) (t : Shape n) : Option Branch :=
  (checked n t).map Subtype.val

private theorem map_reads {α : Type} {f : α → Option Branch} {g : α → Option FramedBranch}
    (xs : List α) {bs : List Branch}
    (agree : ∀ x ∈ xs, ∀ b, f x = some b → ∃ v, g x = some v ∧ v.val = b)
    (hit : xs.mapM f = some bs) : ∃ vs, xs.mapM g = some vs ∧ vs.map Subtype.val = bs := by
  induction xs generalizing bs with
  | nil => exact ⟨[],rfl,Option.some.inj hit⟩
  | cons x xs ih =>
    rw [List.mapM_cons] at hit
    obtain ⟨b,hb,more⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨bs,hbs,out⟩ := Option.bind_eq_some_iff.mp more
    cases Option.some.inj out
    obtain ⟨v,hv,rfl⟩ := agree x List.mem_cons_self b hb
    obtain ⟨vs,hs,rfl⟩ := ih (fun c hc => agree c (.tail _ hc)) hbs
    exact ⟨v::vs,by simp [hv,hs],rfl⟩

private theorem checked_reading {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (n : Nat)
    {q : Arm i} {atom : Nat} {b : Branch} (valid : Valid q) (on : On f q)
    (budget : i.certified.localizedRerootCursorBudget q < n)
    (read : RingGroupedMark.Reading i r atom q b) :
    ∃ v, checked n (view i r atom n q) = some v ∧ v.val = b := by
  induction n generalizing q b with
  | zero => omega
  | succ n ih =>
    cases read with
    | @node q p cs sh de prior look all sub first second =>
      have frame := i.certified.executableLocalizedRerootChildren_declarative q
      obtain ⟨vs,hvs,eqn⟩ := map_reads (g := fun c => checked n (view i r atom n c)) (kids i q)
        (fun c hc b hb => ih
          (i.certified.localizedRerootChild_valid _ _ _ frame hc)
          ((i.certified.localizedRerootChildren_root_eq _ _ _ frame hc).trans on)
          (by have := i.certified.localizedRerootChild_budget_lt _ _ _ valid frame hc; omega)
          (sub c hc hb)) all
      refine ⟨pack (RingRule5Shape.key i r false q) (RingGroupedMark.bit atom q) vs,?_,?_⟩
      · change (((kids i q).map (view i r atom n)).mapM (checked n)).map _ = _
        simpa [List.mapM_map,Function.comp_def] using congrArg (Option.map
          (pack (RingRule5Shape.key i r false q) (RingGroupedMark.bit atom q))) hvs
      · have pkey := (prior_read (RingGroupedMark.OnGeometry.node prior look all sub first second)
          ready valid on).1
        change p.deep = RingRule5Shape.key i r false q at pkey
        have shape := rows_unique first second
          (legal_order Branch.shallow _) (legal_order Branch.deep _)
          (fun b hb => by
            obtain ⟨c,hc,hit⟩ := RingRetainedUnitPass.forOutput all hb
            exact (sub c hc hit).framed)
        simp only [pack,eqn,← pkey,heads_derived [.lowercase] prior,
          RingRetainedStereoRefinement.extend,shape]

/-- On any actual ready arm, the bound recovers the full marked Branch. -/
theorem reconstruct_reading {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (n : Nat)
    {q : Arm i} {atom : Nat} {b : Branch} (valid : Valid q) (on : On f q)
    (budget : i.certified.localizedRerootCursorBudget q < n)
    (read : RingGroupedMark.Reading i r atom q b) :
    reconstruct n (view i r atom n q) = some b := by
  obtain ⟨v,hv,eqn⟩ := checked_reading ready n valid on budget read
  simp [reconstruct,hv,eqn]

/-- Executable native evaluation and tree decoding return the same marked branch. -/
theorem reconstruct_arm {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (n : Nat)
    (q : Arm i) (atom : Nat) (valid : Valid q) (on : On f q)
    (budget : i.certified.localizedRerootCursorBudget q < n) :
    reconstruct n (view i r atom n q) = (RingGroupedMark.arm? i r atom q).map Prod.snd := by
  obtain ⟨e,he⟩ := RingGroupedMark.arm_ready ready atom q valid on
  simpa [he] using reconstruct_reading ready n valid on budget (RingGroupedMark.arm_source he).2

/-- Recover the exact public marked word, including both local sorted rows. -/
theorem word_from_tree {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (n : Nat)
    (q : Arm i) (atom : Nat) (valid : Valid q) (on : On f q)
    (budget : i.certified.localizedRerootCursorBudget q < n) :
    (reconstruct n (view i r atom n q)).map Branch.word =
      (RingGroupedMark.arm? i r atom q).map (fun e => e.2.word) := by
  rw [reconstruct_arm ready n q atom valid on budget]
  simp only [Option.map_map,Function.comp_def]

/-- The entire three-way deep comparison, including both strict outcomes, factors
through the two independently materialized unordered marked trees. -/
theorem compare_from_trees {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (n : Nat)
    (a b : Arm i) (atom other : Nat) (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (ba : i.certified.localizedRerootCursorBudget a < n)
    (bb : i.certified.localizedRerootCursorBudget b < n) :
    (do let x ← reconstruct n (view i r atom n a)
        let y ← reconstruct n (view i r other n b)
        pure (compare x.deep y.deep)) =
    (do let x ← RingGroupedMark.arm? i r atom a
        let y ← RingGroupedMark.arm? i r other b
        pure (compare x.2.deep y.2.deep)) := by
  rw [reconstruct_arm ready n a atom va oa ba,reconstruct_arm ready n b other vb ob bb]
  simp [Option.bind_map]
end TetraStereo.Engine.RingMarkedTreeOrder
assert_kernel_only TetraStereo.Engine.RingMarkedTreeOrder.reconstruct_reading
assert_kernel_only TetraStereo.Engine.RingMarkedTreeOrder.reconstruct_arm
assert_kernel_only TetraStereo.Engine.RingMarkedTreeOrder.compare_from_trees
assert_kernel_only TetraStereo.Engine.RingMarkedTreeOrder.word_from_tree
