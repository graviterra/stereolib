import TetraStereo.Examples.PairedCyclopropylComparison

/-! Recover the five donor paths from unordered tagged visits. The input rows
may contain any number of neutral visits, including after the last donor. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylCensus
open Engine OneCenter PairedCyclopropylComparison
open RingStereoSphereInventory (SignedPath Inventory)
open RingEqualPathHandCounts (lastHand visible)
private abbrev Tag := Bool × Fin 5

private def expected (s : Bool) : Nat → List Tag
  | 0 => [(s,0)]
  | 1 => [(s,1)]
  | 2 => [(s,2),(s,3)]
  | 3 => [(s,4)]
  | _ => []

private def layer {α : Type} (path : α → SignedPath) (xs : List α) : Multiset SignedPath := ↑(xs.map path)

private def keep {α : Type} (tag : α → Option Tag) (x : α) := (tag x).map (fun t => (t,x))

private theorem filter_paths {α : Type} (tag : α → Option Tag) (path : α → SignedPath)
    (h : Hands) (row : List α)
    (endpoints : ∀ x ∈ row, lastHand (path x) = (tag x).map (fun t => visit h t.2)) :
    ((row.map path).filter (fun p => (lastHand p).isSome)) = (row.filterMap (keep tag)).map (path ∘ Prod.snd) := by
  induction row with
  | nil => rfl
  | cons x xs ih =>
    have tail := ih (fun y hy => endpoints y (by simp [hy]))
    have head := endpoints x (by simp)
    cases eq : tag x <;> simp [keep,eq,head,Function.comp_def] at tail ⊢ <;> exact tail

open private lift_row from TetraStereo.Examples.AntipodalCyclohexaneHands

private theorem select {α : Type} (tag : α → Option Tag) (path : α → SignedPath)
    (h : Hands) (row : List α) (ids : List Tag)
    (pop : (row.filterMap tag).Perm ids)
    (endpoints : ∀ x ∈ row, lastHand (path x) = (tag x).map (fun t => visit h t.2)) :
    ∃ ys : List (Tag × α), ys.map Prod.fst = ids ∧
      (∀ z ∈ ys, z.2 ∈ row ∧ tag z.2 = some z.1) ∧
      visible (layer path row) = ↑(ys.map (path ∘ Prod.snd)) := by
  let pairs := row.filterMap (keep tag)
  have tags : pairs.map Prod.fst = row.filterMap tag := by
    simp only [pairs,List.map_filterMap]
    apply List.filterMap_congr
    intro x _
    cases ht : tag x <;> simp [keep,ht]
  have sorted := lift_row Prod.fst (xs := pairs) (ys := ids) (tags ▸ pop.symm)
  obtain ⟨ys,idEq,perm⟩ := sorted
  refine ⟨ys,idEq.symm,?_,?_⟩
  · intro z mem
    obtain ⟨x,hx,hz⟩ := List.mem_filterMap.mp (perm.mem_iff.mp mem)
    cases eq : tag x with
    | none => simp [keep,eq] at hz
    | some a =>
      have same : (a,x) = z := Option.some.inj (by simpa [keep,eq] using hz)
      subst z
      exact ⟨hx,eq⟩
  · simp only [visible,layer,Multiset.filter_coe,Bool.decide_coe]
    change (↑((row.map path).filter (fun p => (lastHand p).isSome)) : Multiset SignedPath) = _
    rw [filter_paths tag path h row endpoints]
    exact Quot.sound (perm.map _).symm

private theorem extract1 {α : Type} (t : Tag)
    {ys : List (Tag × α)} (eq : ys.map Prod.fst = [t]) : ∃ x, ys = [(t,x)] := by
  rcases ys with _|⟨⟨a,x⟩,ys⟩
  · contradiction
  · obtain ⟨rfl,empty⟩ := List.cons.inj eq
    exact ⟨x,by simp [List.map_eq_nil_iff.mp empty]⟩

/-- The shared sphere is the only one with two emitting paths. The caller
supplies their graph-derived earlier priorities at the diverging edge. -/
theorem assemble {α : Type} (s : Bool) (h : Hands) (rows : List (List α))
    (tag : α → Option Tag) (path : α → SignedPath)
    (counts : ∀ n, ((rows.getD n []).filterMap tag).Perm (expected s n))
    (hands : ∀ n x, x ∈ rows.getD n [] → lastHand (path x) = (tag x).map (fun t => visit h t.2))
    (shared : ∀ x ∈ rows.getD 2 [], ∀ y ∈ rows.getD 2 [], tag x = some (s,2) → tag y = some (s,3) →
      ∃ e a b ta tb, path x = e :: a :: ta ∧ path y = e :: b :: tb ∧
        b.earlier.length = a.earlier.length ∧ b.earlier < a.earlier) :
    Nonempty (Census h (rows.map (layer path))) := by
  have long : 3 < rows.length := by
    by_contra short
    have no := counts 3
    have none : rows[3]? = none := List.getElem?_eq_none (by omega)
    rw [List.getD_eq_getElem?_getD,none] at no
    exact (by simpa [expected] using no.length_eq)
  obtain ⟨r0,r1,r2,r3,tail,rfl⟩ : ∃ a b c d t, rows = a::b::c::d::t := by
    rcases rows with _|⟨a,_|⟨b,_|⟨c,_|⟨d,t⟩⟩⟩⟩ <;> simp_all
  let rows := r0::r1::r2::r3::tail
  have pick (n : Nat) := select tag path h (rows.getD n []) (expected s n) (counts n) (hands n)
  obtain ⟨ys,ysId,mem0,p0⟩ := pick 0
  obtain ⟨x0,rfl⟩ := extract1 (s,0) ysId
  obtain ⟨ys,ysId,mem1,p1⟩ := pick 1
  obtain ⟨x1,rfl⟩ := extract1 (s,1) ysId
  obtain ⟨ys,ysId,mem2,p2⟩ := pick 2
  obtain ⟨x2,x3,rfl⟩ : ∃ x y, ys = [((s,2),x),((s,3),y)] := by
    rcases ys with _|⟨⟨a,x⟩,rest⟩
    · contradiction
    · obtain ⟨rfl,eq⟩ := List.cons.inj ysId
      obtain ⟨y,rfl⟩ := extract1 (s,3) eq
      exact ⟨x,y,rfl⟩
  obtain ⟨ys,ysId,mem3,p3⟩ := pick 3
  obtain ⟨x4,rfl⟩ := extract1 (s,4) ysId
  let paths : Fin 5 → SignedPath := ![path x0,path x1,path x2,path x3,path x4]
  refine ⟨⟨paths,_,_,_,_,tail.map (layer path),rfl,?_,p0,p1,p2,p3,?_,?_⟩⟩
  · intro row mem
    obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp mem
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hx
    have eq' : rows.getD (4+j) [] = xs := by simpa [rows,List.getD_eq_getElem?_getD,Nat.add_comm,List.getElem?_eq_getElem hj] using eq
    obtain ⟨ys,tags,_,visibleEq⟩ := pick (4+j)
    have empty : expected s (4+j) = [] := by rw [Nat.add_comm]; rfl
    rw [empty] at tags
    rw [List.map_eq_nil_iff.mp tags,eq'] at visibleEq
    exact visibleEq
  · have one (n : Nat) (x : α) (v : Fin 5) (fact : x ∈ rows.getD n [] ∧ tag x = some (s,v)) :
        lastHand (path x) = some (visit h v) := by rw [hands _ _ fact.1,fact.2]; rfl
    intro v
    fin_cases v
    · exact one 0 x0 0 (mem0 ((s,0),x0) (by simp))
    · exact one 1 x1 1 (mem1 ((s,1),x1) (by simp))
    · exact one 2 x2 2 (mem2 ((s,2),x2) (by simp))
    · exact one 2 x3 3 (mem2 ((s,3),x3) (by simp))
    · exact one 3 x4 4 (mem3 ((s,4),x4) (by simp))
  · have a := mem2 ((s,2),x2) (by simp)
    have b := mem2 ((s,3),x3) (by simp)
    exact shared x2 a.1 x3 b.1 a.2 b.2

end TetraStereo.Examples.PairedCyclopropylCensus
assert_kernel_only TetraStereo.Examples.PairedCyclopropylCensus.assemble
