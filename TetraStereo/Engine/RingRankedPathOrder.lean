import TetraStereo.Engine.RingRule5SeedExchange

/-! Comparison of emitted bits by complete ordered path layers. Stage-specific
data determine which endpoints emit and the erased slots of the next layer. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingRankedPathOrder
open OneCenter RingStereoSiblingPass RingFullPathPairs RingRule5Shape RingRule5SeedExchange
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)

private theorem compare_prefix {α : Type} [Ord α] [Std.ReflOrd α] (p x y : List α) :
    compare (p ++ x) (p ++ y) = compare x y := by
  induction p with
  | nil => rfl
  | cons a p ih => simpa [List.compare_cons_cons] using ih

private theorem same_step (p : Path) (k : List Word) (a b : Bool) :
    compare (p ++ [stepKey k (some a)]) (p ++ [stepKey k (some b)]) = compare a b := by
  rw [compare_prefix]
  simp only [List.compare_cons_cons,stepKey,compare_prefix]
  cases a <;> cases b <;> decide

variable {i : Input} {P : RS → Nat → FullVisit i → Prop} {bit : RS → Arm i → Option Bool}
  {emit : Nat → Path → Bool}

def Endpoint (P : RS → Nat → FullVisit i → Prop) (bit : RS → Arm i → Option Bool)
    (emit : Nat → Path → Bool) : Prop :=
  ∀ s n v, P s n v → ∃ p k, p.length = n ∧
    v.path = p ++ [stepKey k (bit s v.cursor)] ∧ (bit s v.cursor).isSome = emit n (p ++ [k])

private theorem row_compare (shape : Endpoint P bit emit) {s t n}
    {xs ys : List (FullVisit i)} (left : ∀ v ∈ xs, P s n v)
    (right : ∀ v ∈ ys, P t n v)
    (slots : xs.map (fun v => eraseEndpoint v.path) = ys.map (fun v => eraseEndpoint v.path))
    (x y : List Bool) :
    compare (xs.filterMap (fun v => bit s v.cursor) ++ x)
      (ys.filterMap (fun v => bit t v.cursor) ++ y) =
      (compare (xs.map FullVisit.path) (ys.map FullVisit.path)).then (compare x y) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => simp at slots
    | cons b ys =>
      obtain ⟨slot,rest⟩ := List.cons.inj slots
      have ga := left a List.mem_cons_self
      have gb := right b List.mem_cons_self
      obtain ⟨p,k,lp,pa,ea⟩ := shape _ _ _ ga
      obtain ⟨q,l,lq,pb,eb⟩ := shape _ _ _ gb
      change eraseEndpoint a.path = eraseEndpoint b.path at slot
      rw [pa,pb,erase_snoc,erase_snoc] at slot
      obtain ⟨rfl,kl⟩ := List.append_inj slot (lp.trans lq.symm)
      obtain rfl : k = l := List.singleton_inj.mp kl
      have vis := ea.trans eb.symm
      have tail := ih (fun v hv => left v (.tail _ hv)) (fun v hv => right v (.tail _ hv)) rest
      cases ha : bit s a.cursor with
      | none =>
        cases hb : bit t b.cursor with
        | none => simpa only [List.filterMap_cons,ha,hb,List.map_cons,List.compare_cons_cons,
            pa,pb,Std.ReflCmp.compare_self,Ordering.eq_then] using tail
        | some j => simp [ha,hb] at vis
      | some h =>
        cases hb : bit t b.cursor with
        | none => simp [ha,hb] at vis
        | some j =>
          simp only [List.filterMap_cons,ha,hb,List.cons_append,List.map_cons,List.compare_cons_cons,
            pa,pb,same_step]
          cases h <;> cases j <;> first | exact tail | rfl

theorem walk_compare {s t} (o : Oracle i) (shape : Endpoint P bit emit)
    (nextSlots : Nat → Path → List Path)
    (advance : ∀ s n {row blocks next}, (∀ v ∈ row, P s n v) →
      List.Forall₂ (o.Expansion (bit s)) row blocks → Legal FullVisit.path blocks.flatten next →
      (∀ v ∈ next, P s (n+1) v) ∧ next.map (fun v => eraseEndpoint v.path) =
        order id ((row.map FullVisit.path).flatMap (nextSlots n)))
    {xs out rows} (a : Layers FullVisit.path (o.Expansion (bit s)) xs out rows) :
    ∀ {ys out' rows'}, Layers FullVisit.path (o.Expansion (bit t)) ys out' rows' →
    ∀ n, (∀ v ∈ xs, P s n v) → (∀ v ∈ ys, P t n v) →
      xs.map (fun v => eraseEndpoint v.path) = ys.map (fun v => eraseEndpoint v.path) →
      compare (out.filterMap (fun v => bit s v.cursor))
        (out'.filterMap (fun v => bit t v.cursor)) = compare rows rows' := by
  induction a with
  | stop => intro ys out' rows' b n ga gb slots; cases b <;> simp_all
  | @sphere a xs blocks next rest rows grow sort _ ih =>
    intro ys out' rows' b n ga gb slots
    cases b with
    | stop => simp at slots
    | @sphere b ys blocks' next' rest' rows' grow' sort' below =>
      simp only [List.filterMap_append,List.compare_cons_cons]
      rw [row_compare shape ga gb slots]
      by_cases same : (a::xs).map FullVisit.path = (b::ys).map FullVisit.path
      · obtain ⟨gn,hn⟩ := advance s n ga grow sort
        obtain ⟨gn',hn'⟩ := advance t n gb grow' sort'
        rw [same] at hn
        rw [ih below (n+1) gn gn' (hn.trans hn'.symm)]
      · have ne := mt Std.compare_eq_eq_iff_eq.mp same
        cases h : compare ((a::xs).map FullVisit.path) ((b::ys).map FullVisit.path) <;> simp_all

end TetraStereo.Engine.RingRankedPathOrder
assert_kernel_only TetraStereo.Engine.RingRankedPathOrder.walk_compare
