import TetraStereo.Engine.RingReferenceFrame
import TetraStereo.Engine.RingDiscoveredCasing

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.ReferenceFrame
open OneCenter LocalizedGenericMarkedRecalculation Recursive
open LocalizedMarkedTerminalGaugeSwap (readback_swap12 readback_swap23 readback_swap34)

/-- Count each unordered pair once, using the direction in which it
occurs in the given list. -/
def pairCount (test : Nat → Nat → Bool) : List Nat → Nat
  | [] => 0
  | a :: xs => xs.countP (test a) + pairCount test xs

private theorem pairCount_congr {v w : Nat → Nat → Bool} {xs : List Nat}
    (ok : xs.Pairwise fun i j => v i j = w i j) : pairCount v xs = pairCount w xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp ok
    exact congrArg₂ (· + ·) (List.Perm.refl xs |>.countP_congr head) (ih tail)

private theorem pairCount_perm {v : Nat → Nat → Bool} {xs ys : List Nat} (perm : xs.Perm ys)
    (symm : ∀ i ∈ xs, ∀ j ∈ xs, v i j = v j i) : pairCount v xs = pairCount v ys := by
  induction perm with
  | nil => rfl
  | cons a perm ih =>
    exact congrArg₂ (· + ·) (perm.countP_eq _) (ih (fun _ hi _ hj =>
      symm _ (List.mem_cons_of_mem _ hi) _ (List.mem_cons_of_mem _ hj)))
  | swap a b xs =>
    have same := symm b (by simp) a (by simp)
    simp only [pairCount,List.countP_cons,same]
    omega
  | trans l r ih jh =>
    exact (ih symm).trans (jh fun _ hi _ hj => symm _ (l.mem_iff.mpr hi) _ (l.mem_iff.mpr hj))

private theorem adjacent (g : Geometry) (pre post : List Nat) (a b : Nat)
    (four : (pre ++ a :: b :: post).length = 4) :
    readback? g (pre ++ b :: a :: post) = (readback? g (pre ++ a :: b :: post)).map RS.swap := by
  cases pre with
  | nil =>
    obtain ⟨c,d,rfl⟩ : ∃ c d, post = [c,d] := by
      cases post with
      | nil => simp at four
      | cons c tail =>
        obtain ⟨d,rfl⟩ := List.length_eq_one_iff.mp (show tail.length = 1 by simpa using four)
        exact ⟨_,_,rfl⟩
    exact readback_swap12 g a b c d
  | cons c rest =>
    cases rest with
    | nil =>
      obtain ⟨d,rfl⟩ := List.length_eq_one_iff.mp (show post.length = 1 by simpa using four)
      exact readback_swap23 g c a b d
    | cons d more =>
      have n : more.length + post.length = 0 := by simp at four; omega
      obtain ⟨rfl,rfl⟩ : more = [] ∧ post = [] := by simpa using n
      exact readback_swap34 g c d a b

private def flip (n : Nat) (x : Option RS) := if n % 2 = 0 then x else x.map RS.swap

private theorem flip_add (a b : Nat) (x : Option RS) : flip (a+b) x = flip a (flip b x) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      cases x with
      | none => simp [flip,Nat.add_mod,ha,hb]
      | some h => cases h <;> simp [flip,Nat.add_mod,ha,hb,RS.swap]

/-- Sorting a tetrahedral order changes the geometric hand once for
every inversion. The assertion also covers missing and coplanar points. -/
private theorem normalized {xs ys : List Nat} (perm : xs.Perm ys) (g : Geometry)
    (v : Nat → Nat → Bool) (pre : List Nat)
    (four : (pre ++ xs).length = 4)
    (opposite : ∀ i ∈ xs, ∀ j ∈ xs, i ≠ j → v i j = !v j i) (nd : xs.Nodup) :
    flip (pairCount v xs) (readback? g (pre ++ xs)) =
      flip (pairCount v ys) (readback? g (pre ++ ys)) := by
  induction perm generalizing pre with
  | nil => rfl
  | cons a perm ih =>
    have eqn := ih (pre ++ [a]) (by simpa using four) (fun _ hi _ hj hn =>
      opposite _ (by simp [hi]) _ (by simp [hj]) hn) (List.nodup_cons.mp nd).2
    simp only [List.append_assoc,List.singleton_append] at eqn
    simp only [pairCount,← perm.countP_eq (v a)]
    rw [flip_add,flip_add,eqn]
  | swap a b xs =>
    have ne : b ≠ a := fun h => (List.nodup_cons.mp nd).1 (by simp [h])
    have diff := opposite b (by simp) a (by simp) ne
    have adj := adjacent g pre xs b a four
    rw [adj]
    simp only [pairCount,List.countP_cons,diff]
    cases v a b <;> simp [flip] <;> (repeat' split) <;>
      first | omega | rfl | simp [Function.comp_def]
  | trans l r ih jh =>
    exact (ih pre four opposite nd).trans (jh pre (by simpa only [List.length_append,← l.length_eq] using four)
      (fun _ hi _ hj => opposite _ (l.mem_iff.mpr hi) _ (l.mem_iff.mpr hj)) (l.nodup_iff.mp nd))

/-- The two geometries rank this pair in different directions. -/
def crossed (t : Table) (i j : Nat) : Bool := orderAt t false i j != orderAt t true i j

private theorem reciprocal {ids t rev i j} (h : coherent ids t rev = true) (hi : i ∈ ids) (hj : j ∈ ids) :
    orderAt t rev j i = (orderAt t rev i j).map Ordering.swap := by
  have both := List.all_eq_true.mp (List.all_eq_true.mp h i hi) j hj
  simp only [Bool.and_eq_true,beq_iff_eq] at both
  exact both.1.2

private theorem crossed_symm {ids t} (h : ∀ rev, coherent ids t rev = true) :
    ∀ i ∈ ids, ∀ j ∈ ids, crossed t i j = crossed t j i := by
  intro i hi j hj
  simp only [crossed,reciprocal (h false) hi hj,reciprocal (h true) hi hj]
  cases orderAt t false i j with
  | none => cases orderAt t true i j <;> rfl
  | some a =>
    cases orderAt t true i j with
    | none => rfl
    | some b => cases a <;> cases b <;> rfl

private theorem basis_cross {m g p i j} (b : Basis m g p i j) {k s} (found : b.promoted? k = some s) :
    (s.1 != s.2) = (b.initial.1 != b.initial.2) := by
  cases b <;> simp only [Basis.promoted?,Basis.initial] at found ⊢
  all_goals first | (obtain rfl := Option.some.inj found; rfl) | skip
  rename_i pair fixed
  cases h : pair.atMark? k with
  | none => simp [h] at found
  | some c => simpa [h] using congrArg (fun x => x.map (fun t => t.1 != t.2)) found.symm

private theorem lookup_cross {m g p} (rs : List (Row m g p)) {t k} (ok : promoted? rs k = some t)
    (key : Nat × Nat) : ((t.lookup key).map (fun s => s.1 != s.2)) =
      (((entries rs).lookup key).map (fun s => s.1 != s.2)) := by
  induction rs generalizing t with
  | nil => simp [promoted?] at ok; subst t; rfl
  | cons x xs ih =>
    cases hx : x.basis.promoted? k with
    | none => simp [promoted?,List.mapM_cons,hx] at ok
    | some s =>
      cases hy : promoted? xs k with
      | none => simp [promoted?,List.mapM_cons,hx,Option.bind_eq_bind] at ok hy; simp_all
      | some rest =>
        have eqn : t = ((x.i,x.j),s) :: rest := by
          unfold promoted? at ok
          simp only [List.mapM_cons, Option.bind_eq_bind,hx,Option.bind_some] at ok
          change ((promoted? xs k).bind (fun ts => some (((x.i,x.j),s) :: ts))) = some t at ok
          simpa [hy] using ok.symm
        subst t
        by_cases same : key = (x.i,x.j)
        · subst key; simpa [entries] using basis_cross x.basis hx
        · have neq : (key == (x.i,x.j)) = false := beq_eq_false_iff_ne.mpr same
          simpa [entries,List.lookup_cons,neq] using ih hy

theorem Trial.crossed_eq {m g p} {f : Frame m g p} (trial : Trial f) (i j : Nat) :
    crossed trial.table i j = crossed (entries f.rows) i j := by
  by_cases eqn : i = j
  · simp [crossed,orderAt,eqn]
  · have h := lookup_cross _ trial.derived (i,j)
    simp only [crossed,orderAt,if_neg eqn,Bool.false_eq_true,if_false,if_true]
    cases h₁ : trial.table.lookup (i,j) <;> cases h₂ : (entries f.rows).lookup (i,j) <;> simp_all
    exact h

private theorem order_spec {ids t rev l} (h : orders ids t rev = [l]) :
    l.Perm ids ∧ l.Pairwise (fun i j => orderAt t rev i j = some .gt) := by
  have mem : l ∈ orders ids t rev := by simp [h]
  obtain ⟨perm,strict⟩ := List.mem_filter.mp mem
  exact ⟨List.mem_permutations'.mp perm,of_decide_eq_true strict⟩

private theorem pairCount_zero {v : Nat → Nat → Bool} {xs : List Nat}
    (ok : xs.Pairwise fun i j => v i j = false) : pairCount v xs = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp ok
    simp only [pairCount,ih tail,Nat.add_zero,List.countP_eq_zero]
    exact fun i hi => by simp [head i hi]

private theorem earlier_in_order {ids table ys i j} (sorted : orders ids table true = [ys])
    (hi : i ∈ ids) (hj : j ∈ ids) (lt : ys.idxOf i < ys.idxOf j) :
    orderAt table true i j = some .gt := by
  obtain ⟨perm,strict⟩ := order_spec sorted
  have a := List.idxOf_lt_length_of_mem (perm.mem_iff.mpr hi)
  have b := List.idxOf_lt_length_of_mem (perm.mem_iff.mpr hj)
  simpa only [List.getElem_idxOf] using (List.pairwise_iff_getElem.mp strict _ _ a b lt)

/-- Number of unordered ligand pairs whose *ordinary* priority reverses on
reflection. It is available before selecting a reference atom. -/
def MolecularFrame.reversals {m g p} (f : MolecularFrame m g p) := pairCount (crossed (entries f.rows)) f.ids

theorem MolecularFrame.reversals_le_six {m g p} (f : MolecularFrame m g p) : f.reversals ≤ 6 := by
  obtain ⟨a,b,c,d,h⟩ := List.length_eq_four.mp f.four
  let v := crossed (entries f.rows)
  have h₃ := List.countP_le_length (p := v a) (l := [b,c,d])
  have h₂ := List.countP_le_length (p := v b) (l := [c,d])
  have h₁ := List.countP_le_length (p := v c) (l := [d])
  change pairCount v f.ids ≤ 6
  rw [h]
  simp only [pairCount,List.countP_nil,Nat.add_zero]
  simp only [List.length_cons,List.length_nil] at h₃ h₂ h₁
  omega

abbrev Frame.reversals {m g p} (f : Frame m g p) := f.toMolecularFrame.reversals

/-- The parity transport applies to any coherent table preserving which
unordered pairs change order on reflection, including the unmarked table. -/
private theorem table_readback {m g p} (f : MolecularFrame m g p) (table : Table) {a b}
    (consistent : ∀ rev, coherent f.ids table rev = true)
    (same : ∀ i j, crossed table i j = crossed (entries f.rows) i j)
    (actual : orders f.ids table false = [a]) (reflected : orders f.ids table true = [b]) :
    readback? g b = flip f.reversals (readback? g a) := by
  obtain ⟨pa,sa⟩ := order_spec actual
  obtain ⟨pb,sb⟩ := order_spec reflected
  let v := fun i j => orderAt table true i j == some .lt
  have pair (i j : Nat) (hi : i ∈ f.ids) (hj : j ∈ f.ids) (hn : i ≠ j) :
      (orderAt table true i j = some .gt ∧ orderAt table true j i = some .lt) ∨
      (orderAt table true i j = some .lt ∧ orderAt table true j i = some .gt) := by
    have ne : b.idxOf i ≠ b.idxOf j := fun h => hn ((List.idxOf_inj (pb.mem_iff.mpr hi)).mp h)
    rcases lt_or_gt_of_ne ne with lt | gt
    · have w := earlier_in_order reflected hi hj lt
      exact Or.inl ⟨w,by rw [reciprocal (consistent true) hi hj,w]; rfl⟩
    · have w := earlier_in_order reflected hj hi gt
      exact Or.inr ⟨by rw [reciprocal (consistent true) hj hi,w]; rfl,w⟩
  have opposite : ∀ i ∈ a, ∀ j ∈ a, i ≠ j → v i j = !v j i := by
    intro i hi j hj hn
    rcases pair i j (pa.mem_iff.mp hi) (pa.mem_iff.mp hj) hn with w | w <;> simp [v,w.1,w.2]
  have hr : pairCount v b = 0 := pairCount_zero (sb.imp fun h => by simp [v,h])
  have count : pairCount v a = f.reversals := by
    unfold MolecularFrame.reversals
    rw [← pairCount_perm pa (v := crossed (entries f.rows)) (fun i hi j hj =>
      crossed_symm f.ordinary i (pa.mem_iff.mp hi) j (pa.mem_iff.mp hj))]
    apply pairCount_congr
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt
    have win := List.pairwise_iff_getElem.mp sa i j hi hj lt
    have ne : a[i] ≠ a[j] := by
      intro eqn
      simp [eqn,orderAt] at win
    rcases pair a[i] a[j] (pa.mem_iff.mp (List.getElem_mem hi)) (pa.mem_iff.mp (List.getElem_mem hj)) ne with w | w <;>
      rw [← same] <;> simp [v,crossed,win,w.1]
  have eqn := normalized (pa.trans pb.symm) g v [] (by simpa using pa.length_eq.trans f.four)
    opposite (pa.nodup_iff.mpr f.distinct)
  simpa [count,hr,flip] using eqn.symm

theorem Trial.order_readback {m g p} {f : Frame m g p} (t : Trial f) {a b}
    (actual : orders f.ids t.table false = [a]) (reflected : orders f.ids t.table true = [b]) :
    readback? g b = flip f.reversals (readback? g a) :=
  table_readback f.toMolecularFrame _ t.consistent t.crossed_eq actual reflected

private theorem letter_of_transport {g : Geometry} {a b : List Nat} {r : Reading} {n : Nat}
    (transport : readback? g b = flip n (readback? g a))
    (observed : geometric g a b = some r) :
    readback? g a = some r.actual ∧ r.label = some (if n % 2 = 0 then
      .chiral r.actual else .pseudoasymmetric (pseudoRSOfRS r.actual)) := by
  unfold geometric at observed
  rw [readback_mirror,transport] at observed
  cases h : readback? g a with
  | none => simp [h,flip] at observed
  | some hand =>
    by_cases even : n % 2 = 0
    · simp [h,flip,even] at observed
      subst r
      exact ⟨rfl,by simpa [Reading.label,even] using caseFromMirror?_eq_swap hand⟩
    · have same : (⟨hand,hand⟩ : Reading) = r := by
        cases hand <;> simpa [h,flip,even,RS.swap] using observed
      subst r
      exact ⟨rfl,by simpa [Reading.label,even] using caseFromMirror?_eq_same hand⟩

/-- The actual ligand order gives the absolute letter. Casing depends on
the parity of the unmarked reversing pairs, for every strict trial. -/
theorem Trial.chemical_letter {m g p} {f : Frame m g p} (t : Trial f) {a b r}
    (actual : orders f.ids t.table false = [a]) (reflected : orders f.ids t.table true = [b])
    (observed : geometric g a b = some r) :
    readback? g a = some r.actual ∧ r.label = some (if f.reversals % 2 = 0 then
      .chiral r.actual else .pseudoasymmetric (pseudoRSOfRS r.actual)) := by
  exact letter_of_transport (t.order_readback actual reflected) observed

theorem MolecularFrame.chemical_letter {m g p} (f : MolecularFrame m g p) {a b r}
    (actual : orders f.ids (entries f.rows) false = [a]) (reflected : orders f.ids (entries f.rows) true = [b])
    (observed : geometric g a b = some r) :
    readback? g a = some r.actual ∧ r.label = some (if f.reversals % 2 = 0 then
      .chiral r.actual else .pseudoasymmetric (pseudoRSOfRS r.actual)) := by
  exact letter_of_transport (table_readback f _ f.ordinary (fun _ _ => rfl) actual reflected) observed

/-- Every eligible mark gives an actual priority order with the same
geometric letter and the casing predicted before any promotion. -/
theorem Population.chemical_letter {m g p} (s : Population m g p) {r}
    (agreed : s.consensus? = some (some r)) (k : Nat) (eligible : k ∈ marks s.frame.ids (entries s.frame.rows)) :
    ∃ (t : Trial s.frame) (a b : List Nat), t ∈ s.trials ∧ t.mark = k ∧
      orders s.frame.ids t.table false = [a] ∧ orders s.frame.ids t.table true = [b] ∧
      readback? g a = some r.actual ∧ r.label = some (if s.frame.reversals % 2 = 0 then
        .chiral r.actual else .pseudoasymmetric (pseudoRSOfRS r.actual)) := by
  rw [← s.complete] at eligible
  obtain ⟨t,ht,hk⟩ := List.mem_map.mp eligible
  have hr := (s.consensus_iff _).mp agreed t ht
  cases outcome : t.outcome with
  | tied => simp [outcome,Outcome.reading?] at hr
  | assigned a b ha hb v hv =>
    obtain rfl : v = r := by simpa [outcome,Outcome.reading?] using hr
    exact ⟨t,a,b,ht,hk,ha,hb,t.chemical_letter ha hb hv⟩

/-- For two constitutionally separated pairs, either pair can reverse
internally. The parity of their two independent molecular comparisons
determines casing even when both are resolved before a promotion. -/
theorem MolecularFrame.separated_pair_count {m g p} (f : MolecularFrame m g p) {a b c d}
    (ids : [a,b,c,d].Perm f.ids)
    (separated : ∀ i ∈ [a,b], ∀ j ∈ [c,d],
      orderAt (entries f.rows) false i j = orderAt (entries f.rows) true i j) :
    f.reversals = (crossed (entries f.rows) a b).toNat + (crossed (entries f.rows) c d).toNat := by
  have count := pairCount_perm ids (fun i hi j hj =>
    crossed_symm f.ordinary i (ids.mem_iff.mp hi) j (ids.mem_iff.mp hj))
  unfold MolecularFrame.reversals
  rw [← count]
  have no (i) (hi : i ∈ [a,b]) (j) (hj : j ∈ [c,d]) : crossed (entries f.rows) i j = false := by
    simp [crossed,separated i hi j hj]
  simp only [pairCount,List.countP_cons,List.countP_nil,no a (by simp) c (by simp),no a (by simp) d (by simp),
    no b (by simp) c (by simp),no b (by simp) d (by simp)]
  cases crossed (entries f.rows) a b <;> cases crossed (entries f.rows) c d <;> decide

/-- Counting reversing unordered pairs is invariant under enumeration of
the four ligands. -/
theorem Frame.reversals_in_order {m g p} (f : Frame m g p) {xs : List Nat} (perm : xs.Perm f.ids) :
    f.reversals = pairCount (crossed (entries f.rows)) xs :=
  (pairCount_perm perm (fun i hi j hj => crossed_symm f.ordinary i (perm.mem_iff.mp hi) j (perm.mem_iff.mp hj))).symm

private theorem initial_equal {m g p} (rows : List (Row m g p)) (i j : Nat) :
    orderAt (entries rows) false i j = some .eq ↔ orderAt (entries rows) true i j = some .eq := by
  by_cases same : i = j
  · simp [orderAt,same]
  simp only [orderAt,if_neg same,Bool.false_eq_true,if_false,if_true]
  induction rows with
  | nil => rfl
  | cons row tail ih =>
    by_cases key : (i,j) = (row.i,row.j)
    · have hk : ((i,j) == (row.i,row.j)) = true := beq_iff_eq.mpr key
      simp only [entries,List.map_cons,List.lookup_cons,hk,Option.map_some,Option.some.injEq]
      cases row.basis with
      | atomic _ _ _ _ _ w _ | fourth _ w _ | stereo _ w _ _ => cases w <;> simp [Basis.initial]
      | constitution => rfl
      | tied => rfl
    · have hk := beq_eq_false_iff_ne.mpr key
      simpa [entries,List.lookup_cons,hk] using ih

/-- Equivalent ligands have the same relation to any third ligand in a
complete coherent comparison table. -/
private theorem substitute_tie {ids t rev x y z} (h : coherent ids t rev = true)
    (hx : x ∈ ids) (hy : y ∈ ids) (hz : z ∈ ids) (tie : orderAt t rev x y = some .eq) :
    orderAt t rev x z = orderAt t rev y z := by
  let ge i j := (orderAt t rev i j).any (· != .lt)
  have trans (i j k) (hi : i ∈ ids) (hj : j ∈ ids) (hk : k ∈ ids) :
      ge i j = true → ge j k = true → ge i k = true := by
    have all := List.all_eq_true.mp (List.all_eq_true.mp h i hi) j hj
    have atK := List.all_eq_true.mp (Bool.and_eq_true_iff.mp all).2 k hk
    change (!(ge i j && ge j k) || ge i k) = true at atK
    intro ij jk
    simpa [ij,jk] using atK
  have total (i j) (hi : i ∈ ids) (hj : j ∈ ids) : (orderAt t rev i j).isSome := by
    have both := List.all_eq_true.mp (List.all_eq_true.mp h i hi) j hj
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp both).1).1
  have revTie : orderAt t rev y x = some .eq := by rw [reciprocal h hx hy,tie]; rfl
  have one : ge x y = true := by simp [ge,tie]
  have two : ge y x = true := by simp [ge,revTie]
  have out := Bool.eq_iff_iff.mpr ⟨trans y x z hy hx hz two,trans x y z hx hy hz one⟩
  have inc := Bool.eq_iff_iff.mpr ⟨fun zx => trans z x y hz hx hy zx one,fun zy => trans z y x hz hy hx zy two⟩
  have tx := total x z hx hz
  have ty := total y z hy hz
  simp only [ge,reciprocal h hx hz,reciprocal h hy hz] at inc
  dsimp [ge] at out
  cases a : orderAt t rev x z with
  | none => simp [a] at tx
  | some first =>
    cases b : orderAt t rev y z with
    | none => simp [b] at ty
    | some second => cases first <;> cases second <;> simp_all

private theorem cross_within {m g p} (f : Frame m g p) {a b}
    (eqn : orderAt (entries f.rows) false a b = some .eq) : crossed (entries f.rows) a b = false := by
  simp [crossed,eqn,(initial_equal _ _ _).mp eqn]

private theorem cross_congr {m g p} (f : Frame m g p) {a b c} (ha : a ∈ f.ids) (hb : b ∈ f.ids)
    (hc : c ∈ f.ids) (eqn : orderAt (entries f.rows) false a b = some .eq) :
    crossed (entries f.rows) a c = crossed (entries f.rows) b c := by
  simp only [crossed,substitute_tie (f.ordinary false) ha hb hc eqn,
    substitute_tie (f.ordinary true) ha hb hc ((initial_equal _ _ _).mp eqn)]

/-- With two equivalent pairs, reflection either exchanges the two whole
classes or preserves them. There are four or zero reversing pairs. -/
theorem Frame.two_pair_reversals {m g p} (f : Frame m g p) {a b c d}
    (ids : [a,b,c,d].Perm f.ids)
    (ab : orderAt (entries f.rows) false a b = some .eq)
    (cd : orderAt (entries f.rows) false c d = some .eq) :
    f.reversals = if crossed (entries f.rows) a c then 4 else 0 := by
  have ha : a ∈ f.ids := ids.mem_iff.mp (by simp)
  have hb : b ∈ f.ids := ids.mem_iff.mp (by simp)
  have hc : c ∈ f.ids := ids.mem_iff.mp (by simp)
  have hd : d ∈ f.ids := ids.mem_iff.mp (by simp)
  have ac := cross_congr f ha hb hc ab
  have ad := cross_congr f ha hb hd ab
  have ca := cross_congr f hc hd ha cd
  rw [crossed_symm f.ordinary c hc a ha,crossed_symm f.ordinary d hd a ha] at ca
  rw [f.reversals_in_order ids]
  simp only [pairCount,List.countP_cons,List.countP_nil,cross_within f ab,cross_within f cd,
    ← ac,← ad,← ca]
  cases crossed (entries f.rows) a c <;> decide

/-- Three equivalent ligands contribute three reversals exactly when
their class changes priority relative to the fourth ligand. -/
theorem Frame.three_tied_reversals {m g p} (f : Frame m g p) {a b c d}
    (ids : [a,b,c,d].Perm f.ids)
    (ab : orderAt (entries f.rows) false a b = some .eq)
    (ac : orderAt (entries f.rows) false a c = some .eq) :
    f.reversals = if crossed (entries f.rows) a d then 3 else 0 := by
  have ha : a ∈ f.ids := ids.mem_iff.mp (by simp)
  have hb : b ∈ f.ids := ids.mem_iff.mp (by simp)
  have hc : c ∈ f.ids := ids.mem_iff.mp (by simp)
  have hd : d ∈ f.ids := ids.mem_iff.mp (by simp)
  have bc := cross_congr f ha hb hc ab
  have bd := cross_congr f ha hb hd ab
  have cd := cross_congr f ha hc hd ac
  rw [f.reversals_in_order ids]
  simp only [pairCount,List.countP_cons,List.countP_nil,← bc,← bd,← cd,cross_within f ab,cross_within f ac]
  cases crossed (entries f.rows) a d <;> decide

/-- No unmarked pair reverses in the four-way tied case. -/
theorem Frame.four_tied_reversals {m g p} (f : Frame m g p) {a b c d}
    (ids : [a,b,c,d].Perm f.ids)
    (ab : orderAt (entries f.rows) false a b = some .eq)
    (ac : orderAt (entries f.rows) false a c = some .eq)
    (ad : orderAt (entries f.rows) false a d = some .eq) : f.reversals = 0 := by
  simp [f.three_tied_reversals ids ab ac,cross_within f ad]

private abbrev Slots := Fin 4
private def slots : List Slots := [0,1,2,3]

private def edges (ab ac ad bc bd cd : Bool) : Slots → Slots → Bool
  | 0,1 | 1,0 => ab
  | 0,2 | 2,0 => ac
  | 0,3 | 3,0 => ad
  | 1,2 | 2,1 => bc
  | 1,3 | 3,1 => bd
  | 2,3 | 3,2 => cd
  | _,_ => false

private def hasPattern (edge : Slots → Slots → Bool) : List Slots → Bool
  | [a,b,c,d] => edge a b && (edge a c || edge c d)
  | _ => false

/-- Exhaust the 64 simple undirected graphs on four slots. Three or
four occupied vertices require two edges sharing one or zero vertices. -/
private theorem edge_shapes : ∀ a b c d e h : Bool,
    let edge := edges a b c d e h
    (slots.filter (fun i => slots.any (edge i))).length ∈ [3,4] →
    slots.permutations'.any (hasPattern edge) = true := by decide +kernel

private theorem shape_of_symmetric (edge : Slots → Slots → Bool)
    (self : ∀ i, edge i i = false) (symm : ∀ i j, edge i j = edge j i)
    (pop : (slots.filter (fun i => slots.any (edge i))).length ∈ [3,4]) :
    slots.permutations'.any (hasPattern edge) = true := by
  have table : edge = edges (edge 0 1) (edge 0 2) (edge 0 3) (edge 1 2) (edge 1 3) (edge 2 3) := by
    funext i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact self _ | exact symm _ _
  simpa only [← table] using (edge_shapes (edge 0 1) (edge 0 2) (edge 0 3)
    (edge 1 2) (edge 1 3) (edge 2 3) (table ▸ pop))

/-- The eligibility test exhausts the physical tie patterns. The four
distinct returned names are a permutation of the actual incident ligands. -/
theorem Frame.tie_shape {m g p} (f : Frame m g p) :
    ∃ a b c d, [a,b,c,d].Perm f.ids ∧ orderAt (entries f.rows) false a b = some .eq ∧
      (orderAt (entries f.rows) false a c = some .eq ∨ orderAt (entries f.rows) false c d = some .eq) := by
  obtain ⟨a,b,c,d,ids⟩ := List.length_eq_four.mp f.four
  let atom : Slots → Nat := ![a,b,c,d]
  have cover : slots.map atom = f.ids := by rw [ids]; rfl
  let t := entries f.rows
  let edge := fun i j : Slots => (atom i != atom j) && (orderAt t false (atom i) (atom j) == some .eq)
  have member (i : Slots) : atom i ∈ f.ids := by
    rw [← cover]
    exact List.mem_map_of_mem (f := atom) (by fin_cases i <;> decide)
  have symm (i j : Slots) : edge i j = edge j i := by
    dsimp only [edge]
    rw [show orderAt t false (atom j) (atom i) = (orderAt t false (atom i) (atom j)).map Ordering.swap from
      reciprocal (f.ordinary false) (member i) (member j),show (atom j != atom i) = (atom i != atom j) from bne_comm]
    cases orderAt t false (atom i) (atom j) with
    | none => rfl
    | some o => cases o <;> rfl
  have pop : (slots.filter (fun i => slots.any (edge i))).length ∈ [3,4] := by
    have h := f.eligible
    simpa only [marks,← cover,List.filter_map,List.any_map,Function.comp_def,List.length_map,edge,t] using h
  obtain ⟨l,inPerm,ok⟩ := List.any_eq_true.mp (shape_of_symmetric edge (by simp [edge]) symm pop)
  have perm := List.mem_permutations'.mp inPerm
  obtain ⟨i,j,k,n,rfl⟩ := List.length_eq_four.mp (perm.length_eq.trans (by rfl))
  change (edge i j && (edge i k || edge k n)) = true at ok
  have lift {u v} (h : edge u v = true) : orderAt t false (atom u) (atom v) = some .eq :=
    eq_of_beq (Bool.and_eq_true_iff.mp h).2
  exact ⟨atom i,atom j,atom k,atom n,cover ▸ perm.map atom,lift (Bool.and_eq_true_iff.mp ok).1,
    (Bool.or_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).2).imp lift lift⟩

/-- Across every eligible four-ligand frame there are exactly zero,
three or four reversing pairs. Only three gives a lowercase assignment. -/
theorem Frame.reversal_count {m g p} (f : Frame m g p) : f.reversals ∈ [0,3,4] := by
  obtain ⟨a,b,c,d,ids,ab,h⟩ := f.tie_shape
  rcases h with ac | cd
  · rw [f.three_tied_reversals ids ab ac]
    split <;> decide
  · rw [f.two_pair_reversals ids ab cd]
    split <;> decide

/-- An assigned promotion has lowercase casing exactly in the
three-reversal case, irrespective of the chosen reference atom. -/
theorem Population.lowercase_iff {m g p} (s : Population m g p) {r}
    (agreed : s.consensus? = some (some r)) :
    r.label = some (.pseudoasymmetric (pseudoRSOfRS r.actual)) ↔ s.frame.reversals = 3 := by
  have nonempty : marks s.frame.ids (entries s.frame.rows) ≠ [] := by
    intro h
    have count := s.frame.eligible
    simp [h] at count
  obtain ⟨k,hk⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨_,_,_,_,_,_,_,_,label⟩ := s.chemical_letter agreed k hk
  have count := s.frame.reversal_count
  simp only [List.mem_cons,List.not_mem_nil,or_false] at count
  rcases count with h | h | h <;> simp [label,h]

end TetraStereo.Engine.RingChemicalPriority.ReferenceFrame

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Trial.crossed_eq
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Trial.chemical_letter
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.chemical_letter
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Frame.two_pair_reversals
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Frame.three_tied_reversals
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Frame.four_tied_reversals
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Frame.reversal_count
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.lowercase_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.MolecularFrame.separated_pair_count
