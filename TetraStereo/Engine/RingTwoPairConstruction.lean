import TetraStereo.Engine.RingMolecularPromotion

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority
open OneCenter LocalizedGenericMarkedRecalculation Recursive

variable {m : RawMolecule} {p : List Nat} {omitted : List (List Nat)}
    {e : Experiment m p omitted} {mat : Matrix e}

def pairOrder (a b c d : Nat) (first second : Bool) :=
  (if first then [a,b] else [b,a]) ++ (if second then [c,d] else [d,c])

private theorem pair_perm (a b c d : Nat) (x y : Bool) :
    (pairOrder a b c d x y).Perm [a,b,c,d] := by
  have pair (i j : Nat) (f : Bool) : (if f then [i,j] else [j,i]).Perm [i,j] := by
    cases f
    · exact List.Perm.swap _ _ _
    · exact .refl _
  exact (pair a b x).append (pair c d y)

private theorem original_strict {r : Row e} {o : Ordering} (h : r.unmarked = o)
    (strict : o ≠ .eq) (mark : Nat) : r.ordering? mark false = some o := by
  cases branch : r.directed with
  | within tied ts marks => simp [Row.unmarked,branch] at h; exact (strict h.symm).elim
  | cross c => simpa [Row.ordering?,Row.unmarked,branch] using congrArg some h

private theorem actual_entry {i j : Nat} {o : Ordering}
    (h : (mat.row? i j).map Row.unmarked = some o) (strict : o ≠ .eq) (mark : Nat) :
    (mat.row? i j).bind (·.ordering? mark false) = some o := by
  obtain ⟨r,row,unmarked⟩ := Option.map_eq_some_iff.mp h
  simpa [row] using original_strict unmarked strict mark

private theorem cross_strict {a b c d i j : Nat} (partition : mat.partitionOK [a,b,c,d] = true)
    (hi : i ∈ [a,b]) (lo : j ∈ [c,d]) (mark : Nat) : mat.strict mark false i j = true := by
  have allCross := (Bool.and_eq_true_iff.mp partition).2
  have both := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp allCross i hi) j lo)
  simp only [Matrix.strict,actual_entry (eq_of_beq both.1) (by decide) mark,
    actual_entry (eq_of_beq both.2) (by decide) mark,beq_self_eq_true,Bool.and_self]

theorem Row.marked_witness (row : Row e) {k : Nat} (eligible : k ∈ e.arms.map Arm.ligand)
    (tied : row.unmarked = .eq) :
    ∃ w : MarkedOrder e row.left row.right, w.mark = k ∧
      ∀ rev, row.ordering? k rev = some w.ordering := by
  cases basis : row.directed with
  | cross c =>
    cases wins : c.wins <;> simp [Row.unmarked,basis,wins] at tied
  | within _ ts allMarks =>
    rw [← allMarks] at eligible
    obtain ⟨t,member,mark⟩ := List.mem_map.mp eligible
    cases found : ts.find? (fun t => t.mark == k) with
    | none =>
      have impossible := List.find?_eq_none.mp found t member
      simp [mark] at impossible
    | some w =>
      exact ⟨w,eq_of_beq (List.find?_some (p := fun t : MarkedOrder e row.left row.right => t.mark == k) found),fun rev => by simp [Row.ordering?,basis,found]⟩

private theorem reversed_strict_readings {a b : Arm m e.focus omitted}
    (f : MarkedOrder e a b) (r : MarkedOrder e b a) (mark : f.mark = r.mark) :
    (f.ordering = .gt ∧ r.ordering = .lt) ∨ (f.ordering = .lt ∧ r.ordering = .gt) := by
  have lhs := f.leftAt
  have rhs := f.rightAt
  rw [mark,r.rightAt] at lhs
  rw [mark,r.leftAt] at rhs
  have forward := f.all_completions _ _ (List.forall₂_same.mpr (fun _ _ => .refl _)) (List.forall₂_same.mpr (fun _ _ => .refl _))
  have backward := r.all_completions _ _ (List.forall₂_same.mpr (fun _ _ => .refl _)) (List.forall₂_same.mpr (fun _ _ => .refl _))
  rw [← Option.some.inj lhs,← Option.some.inj rhs] at forward
  rcases forward with ⟨h,lt⟩ | ⟨h,lt⟩ <;> rcases backward with ⟨v,other⟩ | ⟨v,other⟩
  · exact (lt_asymm lt other).elim
  · exact .inl ⟨h,v⟩
  · exact .inr ⟨h,v⟩
  · exact (lt_asymm lt other).elim

theorem Matrix.tied_pair_directions {i j k : Nat} (eligible : k ∈ e.arms.map Arm.ligand)
    (forward : (mat.row? i j).map Row.unmarked = some .eq)
    (backward : (mat.row? j i).map Row.unmarked = some .eq) :
    (∀ rev, mat.strict k rev i j = true ∧ mat.strict k rev j i = false) ∨
    (∀ rev, mat.strict k rev i j = false ∧ mat.strict k rev j i = true) := by
  obtain ⟨f,hf,ft⟩ := Option.map_eq_some_iff.mp forward
  obtain ⟨r,hr,rt⟩ := Option.map_eq_some_iff.mp backward
  obtain ⟨u,um,fu⟩ := Row.marked_witness f eligible ft
  obtain ⟨v,vm,rv⟩ := Row.marked_witness r eligible rt
  have fa : f.address = (i,j) := eq_of_beq (List.find?_some (p := fun t : Row e => t.address == (i,j)) hf)
  have ra : r.address = (j,i) := eq_of_beq (List.find?_some (p := fun t : Row e => t.address == (j,i)) hr)
  have left : r.left = f.right := List.inj_on_of_nodup_map e.distinct r.leftMem f.rightMem
    ((congrArg Prod.fst ra).trans (congrArg Prod.snd fa).symm)
  have right : r.right = f.left := List.inj_on_of_nodup_map e.distinct r.rightMem f.leftMem
    ((congrArg Prod.snd ra).trans (congrArg Prod.fst fa).symm)
  have opposite : (u.ordering = .gt ∧ v.ordering = .lt) ∨ (u.ordering = .lt ∧ v.ordering = .gt) := by
    generalize r.left = rl, r.right = rr at v vm left right ⊢
    subst rl
    subst rr
    exact reversed_strict_readings u v (um.trans vm.symm)
  rcases opposite with ab | ba
  · exact Or.inl (fun rev => by simp [Matrix.strict,hf,hr,fu,rv,ab.1,ab.2])
  · exact Or.inr (fun rev => by simp [Matrix.strict,hf,hr,fu,rv,ba.1,ba.2])

private theorem reflected_entry {i j : Nat} {o : Ordering}
    (h : (mat.row? i j).map Row.unmarked = some o) (strict : o ≠ .eq) (mark : Nat) :
    (mat.row? i j).bind (·.ordering? mark true) = some o.swap := by
  obtain ⟨r,row,initial⟩ := Option.map_eq_some_iff.mp h
  cases basis : r.directed with
  | within _ _ _ => simp [Row.unmarked,basis] at initial; exact (strict initial.symm).elim
  | cross c =>
    cases wins : c.wins <;> simp [Row.unmarked,basis,wins] at initial <;>
      simp [row,Row.ordering?,basis,wins,← initial]

private theorem cross_reflected {a b c d i j : Nat} (partition : mat.partitionOK [a,b,c,d] = true)
    (hi : i ∈ [a,b]) (lo : j ∈ [c,d]) (mark : Nat) : mat.strict mark true j i = true := by
  have allCross := (Bool.and_eq_true_iff.mp partition).2
  have both := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp allCross i hi) j lo)
  simp [Matrix.strict,reflected_entry (eq_of_beq both.1) (by decide) mark,
    reflected_entry (eq_of_beq both.2) (by decide) mark]

private theorem singleton_of_ranked {k : Nat} {rev : Bool} {order : List Nat}
    (perm : order.Perm (e.arms.map Arm.ligand))
    (ranked : order.Pairwise (fun i j => mat.strict k rev i j = true)) :
    mat.orders k rev = [order] := by
  have unique := (List.permutations_perm_permutations' _).nodup_iff.mp
    (List.nodup_permutations _ e.distinct)
  have distinct : (mat.orders k rev).Nodup := unique.filter _
  have member : order ∈ mat.orders k rev := List.mem_filter.mpr ⟨List.mem_permutations'.mpr perm,decide_eq_true ranked⟩
  have only (other) (h : other ∈ mat.orders k rev) : other = order := by
    obtain ⟨inPerms,ok⟩ := List.mem_filter.mp h
    apply ((List.mem_permutations'.mp inPerms).trans perm.symm).eq_of_pairwise _ (of_decide_eq_true ok) ranked
    intro i j _ _ ij ji
    have impossible := (eq_of_beq (Bool.and_eq_true_iff.mp ij).1).symm.trans
      (eq_of_beq (Bool.and_eq_true_iff.mp ji).2)
    contradiction
  cases h : mat.orders k rev with
  | nil => simp [h] at member
  | cons x xs =>
    have head := only x (by simp [h])
    subst x
    cases xs with
    | nil => rfl
    | cons y ys =>
      have hy := only y (by simp [h])
      subst y
      simp [h] at distinct

/-- Every eligible mark in a molecular two-pair partition has exactly one
strict order on each geometry. Both orders follow from the independently
checked pair observations, including when the four marks disagree. -/
theorem Partition.orders_from_comparisons (part : Partition mat)
    {a b c d : Nat} (slots : part.order = [a,b,c,d]) (k : Nat) (eligible : k ∈ e.arms.map Arm.ligand) :
    let x := mat.strict k false a b
    let y := mat.strict k false c d
    mat.orders k false = [pairOrder a b c d x y] ∧ mat.orders k true = [pairOrder c d a b y x] := by
  dsimp only
  have ids : [a,b,c,d].Perm (e.arms.map Arm.ligand) := slots ▸ part.incident
  have unique := ids.nodup_iff.mpr e.distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at unique
  have cls : mat.partitionOK [a,b,c,d] = true := slots ▸ part.classes
  have same := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp cls).1
  have pair {i j : Nat} (ne : i ≠ j)
      (checked : (directedPairs [i,j] id).all (fun (s,t) => ((mat.row? s t).map Row.unmarked) == some .eq) = true) :=
    @Matrix.tied_pair_directions _ _ _ _ mat i j k eligible
      (eq_of_beq (List.all_eq_true.mp checked (i,j) (by simp [directedPairs,ne,Ne.symm ne])))
      (eq_of_beq (List.all_eq_true.mp checked (j,i) (by simp [directedPairs,ne,Ne.symm ne])))
  have high := pair unique.1.1 same.1
  have low := pair unique.2.2.1 same.2
  have between (i) (hi : i ∈ [a,b]) (j) (lo : j ∈ [c,d]) :=
    And.intro (cross_strict cls hi lo k) (cross_reflected cls hi lo k)
  have ac := between a (by simp) c (by simp)
  have ad := between a (by simp) d (by simp)
  have bc := between b (by simp) c (by simp)
  have bd := between b (by simp) d (by simp)
  have switched : [c,d,a,b].Perm [a,b,c,d] := List.perm_append_comm (l₁ := [c,d]) (l₂ := [a,b])
  constructor
  · apply singleton_of_ranked ((pair_perm ..).trans ids)
    rcases high with ha | ha <;> rcases low with hb | hb <;>
      simp [pairOrder,(ha false).1,(ha false).2,(hb false).1,(hb false).2,ac.1,ad.1,bc.1,bd.1]
  · apply singleton_of_ranked ((pair_perm ..).trans (switched.trans ids))
    rcases high with ha | ha <;> rcases low with hb | hb <;>
      simp [pairOrder,(ha false).1,(ha true).1,(ha true).2,(hb false).1,(hb true).1,(hb true).2,
        ac.2,ad.2,bc.2,bd.2]

/-- Construct both priority orders using only the two marked intrapair
comparisons. All molecular eligibility and uniqueness checks are retained
in the result. -/
def Partition.trial (part : Partition mat) (k : Nat) (eligible : k ∈ e.arms.map Arm.ligand) :
    Trial mat :=
  let a := part.order[0]?.getD 0
  let b := part.order[1]?.getD 0
  let c := part.order[2]?.getD 0
  let d := part.order[3]?.getD 0
  have slots : part.order = [a,b,c,d] := by
    have shape := part.classes
    unfold Matrix.partitionOK at shape
    split at shape
    · rename_i i j l n eqn
      simp [a,b,c,d,eqn]
    · contradiction
  let x := mat.strict k false a b
  let y := mat.strict k false c d
  let exactOrders := part.orders_from_comparisons slots k eligible
  ⟨k,pairOrder a b c d x y,pairOrder c d a b y x,exactOrders.1,exactOrders.2,
    by cases x <;> cases y <;> rfl⟩

/-- Every eligible ligand occurs once, with its determined trial, before
coordinates, consensus or cancellation enter the calculation. -/
def Partition.trials (part : Partition mat) : List (Trial mat) :=
  (e.arms.map Arm.ligand).attach.map fun k => part.trial k.val k.property

theorem Partition.marks (part : Partition mat) :
    part.trials.map Trial.mark = e.arms.map Arm.ligand := by
  rw [Partition.trials,List.map_map]
  exact List.attach_map_subtype_val _

/-- A strict molecular trial makes both pair preferences decidable. Its full
four-ligand order is uniquely reconstructed from just those two comparisons. -/
theorem Trial.actual_of_pair_preferences (t : Trial mat) (partition : Partition mat)
    {a b c d : Nat} (slots : partition.order = [a,b,c,d]) :
    t.actual = pairOrder a b c d (mat.strict t.mark false a b) (mat.strict t.mark false c d) := by
  have accepted : t.actual ∈ mat.orders t.mark false := by simp [t.actualUnique]
  obtain ⟨permuted,strict⟩ := List.mem_filter.mp accepted
  have basePerm := slots ▸ partition.incident
  have perm := (List.mem_permutations'.mp permuted).trans basePerm.symm
  let R (i j : Nat) := mat.strict t.mark false i j = true
  have pw : t.actual.Pairwise R := of_decide_eq_true strict
  have total : [a,b,c,d].Pairwise (fun i j => R i j ∨ R j i) :=
    (perm.pairwise_iff (fun h => Or.symm h)).mp (pw.imp fun h => Or.inl h)
  have hab := (List.pairwise_cons.mp total).1 b (by simp)
  have hcd := (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp total).2).2).1 d (by simp)
  have partitioned := slots ▸ partition.classes
  have ac := cross_strict partitioned (i := a) (j := c) (by simp) (by simp) t.mark
  have ad := cross_strict partitioned (i := a) (j := d) (by simp) (by simp) t.mark
  have bc := cross_strict partitioned (i := b) (j := c) (by simp) (by simp) t.mark
  have bd := cross_strict partitioned (i := b) (j := d) (by simp) (by simp) t.mark
  let order := pairOrder a b c d (mat.strict t.mark false a b) (mat.strict t.mark false c d)
  have ranked : order.Pairwise R := by
    dsimp only [R] at hab hcd ⊢
    cases x : mat.strict t.mark false a b <;> cases y : mat.strict t.mark false c d <;>
      simp_all [order,pairOrder,List.pairwise_cons]
  have member : order ∈ mat.orders t.mark false := List.mem_filter.mpr
    ⟨List.mem_permutations'.mpr ((pair_perm ..).trans basePerm),decide_eq_true ranked⟩
  exact (List.mem_singleton.mp (t.actualUnique ▸ member)).symm

end TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.Partition.orders_from_comparisons
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.Partition.trial
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.Partition.marks
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.Trial.actual_of_pair_preferences
