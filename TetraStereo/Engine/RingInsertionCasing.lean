import TetraStereo.Engine.RingActiveMagnitude

set_option autoImplicit false

namespace TetraStereo.Engine.RingInsertionCasing
open RingActivePairReport (Slot Score Matrix Ranking)

abbrev Edge := Slot × Slot

/-- An insertion scans the reversed sorted prefix from its last element. The trace
includes the comparison which stops the scan as well as every comparison which swaps. -/
def insert (swap : Slot → Slot → Bool) (x : Slot) : List Slot → List Slot × List Edge
  | [] => ([x],[])
  | a :: rest =>
    if swap a x then
      let (tail,trace) := insert swap x rest
      (a :: tail,(a,x) :: trace)
    else (x :: a :: rest,[(a,x)])

/-- Successive insertions retain the pinned sorter's actual directed comparison sequence. -/
def walk (swap : Slot → Slot → Bool) (start : List Slot) : List Slot × List Edge :=
  let (rev,edges) := start.foldl (init := ([],[])) fun acc x =>
    let (next,trace) := insert swap x acc.1
    (next,acc.2 ++ trace)
  (rev.reverse,edges)

structure Outcome where
  order : List Slot
  trace : List Edge
  unique : Bool
  pseudoCount : Nat
  deriving Repr, DecidableEq

def component (s : Score) (rev : Bool) : Int := if rev then s.2 else s.1

/-- Sort.prioritise counts each encountered score of absolute value above one,
and clears uniqueness whenever it encounters zero. -/
def run {reader} (m : Matrix reader) (rev : Bool) (start : List Slot) : Outcome :=
  let score (e : Edge) := component (m.get e.1 e.2) rev
  let (order,trace) := walk (fun a b => decide (a ≠ b ∧ score (a,b) < 0)) start
  ⟨order,trace,trace.all (fun e => score e != 0),trace.countP (fun e => (score e).natAbs > 1)⟩

def Outcome.lowercase (o : Outcome) : Bool := o.pseudoCount == 1

/-- The exact per-order statement includes order and uniqueness, since the configuration
reader applies casing only to a successful ranking. -/
def accepts (o : Outcome) (ranking : List Slot) (lower : Bool) : Bool :=
  o.unique && o.order == ranking && o.lowercase == lower

def starts := (List.finRange 4).permutations'

theorem starts_size : starts.length = 24 := by decide +kernel

/-- The returned list gives both geometries' actual comparison traces, counts and casing
at every possible initial carrier order. -/
def envelope {reader} (m : Matrix reader) : List (List Slot × Outcome × Outcome) :=
  starts.map fun s => (s,run m false s,run m true s)

theorem envelope_exact {reader} (m : Matrix reader) (s : List Slot) (a b : Outcome) :
    (s,a,b) ∈ envelope m ↔ s.Perm (List.finRange 4) ∧ a = run m false s ∧ b = run m true s := by
  constructor
  · rintro h
    obtain ⟨x,mem,eqn⟩ := List.mem_map.mp h
    cases eqn
    exact ⟨List.mem_permutations'.mp mem,rfl,rfl⟩
  · rintro ⟨p,rfl,rfl⟩
    exact List.mem_map.mpr ⟨s,List.mem_permutations'.mpr p,rfl⟩

def agrees {reader} (m : Matrix reader) (actual reflected : List Slot) (lower : Bool) : Bool :=
  starts.all fun s => accepts (run m false s) actual lower && accepts (run m true s) reflected lower

theorem agrees_iff {reader} (m : Matrix reader) (actual reflected : List Slot) (lower : Bool) :
    agrees m actual reflected lower = true ↔ ∀ s, s.Perm (List.finRange 4) →
      ((run m false s).unique = true ∧ (run m false s).order = actual ∧ (run m false s).lowercase = lower) ∧
      ((run m true s).unique = true ∧ (run m true s).order = reflected ∧ (run m true s).lowercase = lower) := by
  simp [agrees,starts,List.all_eq_true,List.mem_permutations',accepts,and_assoc]

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private def precedes (x : List Slot) (a b : Slot) := decide (x.idxOf a < x.idxOf b)

private def changed (x y : List Slot) (p : Edge) := precedes x p.1 p.2 != precedes y p.1 p.2

private def orderingWalk (x start : List Slot) := walk (fun a b => precedes x b a) start

/-- Distinct slots never compare themselves. A reversed direction of a strict pair is
negative exactly when its other slot comes first in the same molecular ranking. -/
private theorem swap_iff {r m rev} (k : @Ranking r m rev) (a b : Slot) :
    (a ≠ b ∧ component (m.get a b) rev < 0) ↔ k.slots.idxOf b < k.slots.idxOf a := by
  by_cases eqv : a = b
  · subst b
    simp
  have present : ∀ t : Slot, t ∈ k.slots := fun t => k.perm.mem_iff.mpr (by simp)
  have diff : k.slots.idxOf a ≠ k.slots.idxOf b := fun h => eqv ((List.idxOf_inj (present a)).mp h)
  rcases lt_or_gt_of_ne diff with h | h
  · have pos := (k.before_iff eqv).mp h
    change 0 < component (m.get a b) rev at pos
    exact ⟨fun bad => False.elim ((Int.lt_asymm pos) bad.2),fun bad => False.elim ((Nat.lt_asymm h) bad)⟩
  · obtain ⟨s,t,hs,ht,_,htneg⟩ := k.source _ _ h
    have eqn := Option.some.inj ((m.found a b eqv).symm.trans ht)
    exact ⟨fun _ => h,fun _ => ⟨eqv,eqn ▸ htneg⟩⟩

private theorem nonzero {r m rev} (k : @Ranking r m rev) {a b : Slot} (ne : a ≠ b) :
    component (m.get a b) rev ≠ 0 := by
  by_cases h : k.slots.idxOf b < k.slots.idxOf a
  · exact Int.ne_of_lt ((swap_iff k a b).mpr h).2
  · have eqv : k.slots.idxOf a ≠ k.slots.idxOf b := fun he =>
      ne ((List.idxOf_inj (k.perm.mem_iff.mpr (by simp : a ∈ List.finRange 4))).mp he)
    have pos := (k.before_iff ne).mp (lt_of_le_of_ne (Nat.le_of_not_gt h) eqv)
    exact Int.ne_of_gt pos

private theorem replay_order (x s : List Slot) (px : x.Perm (List.finRange 4)) (ps : s.Perm (List.finRange 4)) :
    (orderingWalk x s).1 = x ∧ ∀ e ∈ (orderingWalk x s).2, e.1 ≠ e.2 := by
  have all : ∀ x ∈ starts, ∀ s ∈ starts, (orderingWalk x s).1 = x ∧
      ∀ e ∈ (orderingWalk x s).2, e.1 ≠ e.2 := by decide +kernel
  exact all _ (List.mem_permutations'.mpr px) _ (List.mem_permutations'.mpr ps)

/-- All reversed pairs join consecutive ranks. For four ligands this includes a single
adjacent exchange and two independent adjacent exchanges. -/
def adjacentChanges (x y : List Slot) := LocalizedChemicalRing.ConstitutionalPartition.pairs.all fun p =>
  !(changed x y p) || x.idxOf p.1 + 1 == x.idxOf p.2 || x.idxOf p.2 + 1 == x.idxOf p.1

private theorem counted (x y s : List Slot) (px : x.Perm (List.finRange 4)) (py : y.Perm (List.finRange 4))
    (ps : s.Perm (List.finRange 4)) (adjacent : adjacentChanges x y = true) :
    (orderingWalk x s).2.countP (changed x y) = RingActivePairReport.changes x y := by
  have all : ∀ x ∈ starts, ∀ y ∈ starts, adjacentChanges x y = true → ∀ s ∈ starts,
      (orderingWalk x s).2.countP (changed x y) = RingActivePairReport.changes x y := by decide +kernel
  exact all _ (List.mem_permutations'.mpr px) _ (List.mem_permutations'.mpr py) adjacent _ (List.mem_permutations'.mpr ps)

private theorem adjacent_class (x y : List Slot) (px : x.Perm (List.finRange 4)) (py : y.Perm (List.finRange 4)) :
    (RingActivePairReport.changes x y ≤ 1 → adjacentChanges x y = true) ∧
    (adjacentChanges x y = true → adjacentChanges y x = true ∧
      RingActivePairReport.changes x y ≤ 2 ∧ RingActivePairReport.changes x y = RingActivePairReport.changes y x) := by
  have all : ∀ x ∈ starts, ∀ y ∈ starts,
      (RingActivePairReport.changes x y ≤ 1 → adjacentChanges x y = true) ∧
      (adjacentChanges x y = true → adjacentChanges y x = true ∧
        RingActivePairReport.changes x y ≤ 2 ∧ RingActivePairReport.changes x y = RingActivePairReport.changes y x) := by decide +kernel
  exact all _ (List.mem_permutations'.mpr px) _ (List.mem_permutations'.mpr py)

/-- Molecular magnitudes are checked in **both directed orientations**. Every input
permutation may trigger either orientation of an unordered ligand pair. -/
def Magnitudes {r} (m : Matrix r) (rev : Bool) (x y : List Slot) : Prop :=
  ∀ a b, a ≠ b → decide (1 < (component (m.get a b) rev).natAbs) = changed x y (a,b)

theorem adjacent_count {r m rev} (rank : @Ranking r m rev) (y s : List Slot)
    (py : y.Perm (List.finRange 4)) (ps : s.Perm (List.finRange 4))
    (mag : Magnitudes m rev rank.slots y) (adjacent : adjacentChanges rank.slots y = true) :
    (run m rev s).order = rank.slots ∧ (run m rev s).unique = true ∧
      (run m rev s).pseudoCount = RingActivePairReport.changes rank.slots y := by
  have swap : (fun a b => decide (a ≠ b ∧ component (m.get a b) rev < 0)) =
      (fun a b => precedes rank.slots b a) := by
    funext a b
    simp only [precedes,swap_iff rank a b]
  have wh := replay_order _ _ rank.perm ps
  simp only [run,swap]
  change (orderingWalk rank.slots s).1 = _ ∧ _ ∧ _
  refine ⟨wh.1,List.all_eq_true.mpr (fun e mem => bne_iff_ne.mpr (nonzero rank (wh.2 e mem))),?_⟩
  exact (List.Perm.refl _).countP_congr (fun e he => mag e.1 e.2 (wh.2 e he)) |>.trans
    (counted _ _ _ rank.perm py ps adjacent)

/-- Every initial carrier order yields the physical casing on both geometries whenever
the reversed pairs are adjacent and the score magnitudes identify these reversals. -/
theorem agrees_of_adjacent {r m} (a : @Ranking r m false) (b : Ranking m true)
    (actual : Magnitudes m false a.slots b.slots) (mirror : Magnitudes m true b.slots a.slots)
    (adjacent : adjacentChanges a.slots b.slots = true) :
    agrees m a.slots b.slots (decide (RingActivePairReport.reversals m % 2 ≠ 0)) = true := by
  obtain ⟨other,small,counts⟩ := (adjacent_class _ _ a.perm b.perm).2 adjacent
  apply (agrees_iff ..).mpr
  intro s ps
  obtain ⟨ao,au,ac⟩ := adjacent_count a b.slots s b.perm ps actual adjacent
  obtain ⟨bo,bu,bc⟩ := adjacent_count b a.slots s a.perm ps mirror other
  have odd : (RingActivePairReport.changes a.slots b.slots == 1) =
      decide (RingActivePairReport.reversals m % 2 ≠ 0) := by
    rw [← RingActivePairReport.changes_eq a b]
    have : RingActivePairReport.changes a.slots b.slots = 0 ∨
        RingActivePairReport.changes a.slots b.slots = 1 ∨ RingActivePairReport.changes a.slots b.slots = 2 := by omega
    rcases this with h | h | h <;> simp [h]
  exact ⟨⟨au,ao,by simpa only [Outcome.lowercase,ac] using odd⟩,
    ⟨bu,bo,by simpa only [Outcome.lowercase,bc,← counts] using odd⟩⟩

theorem agrees_of_atMostOne {r m} (a : @Ranking r m false) (b : Ranking m true)
    (actual : Magnitudes m false a.slots b.slots) (mirror : Magnitudes m true b.slots a.slots)
    (small : RingActivePairReport.reversals m ≤ 1) :
    agrees m a.slots b.slots (decide (RingActivePairReport.reversals m % 2 ≠ 0)) = true := by
  apply agrees_of_adjacent a b actual mirror
  exact (adjacent_class _ _ a.perm b.perm).1 (by simpa only [RingActivePairReport.changes_eq a b] using small)



/-- The five molecular score pairs establish the needed magnitude facts for the
actual and reflected matrices, including the reverse of every directed input. -/
theorem magnitudes_of_values {r m} (a : @Ranking r m false) (b : Ranking m true)
    (values : ∀ x y, x ≠ y → m.get x y ∈ RingActivePairs.molecularValues) :
    Magnitudes m false a.slots b.slots ∧ Magnitudes m true b.slots a.slots := by
  have both (x y : Slot) (ne : x ≠ y) :
      decide (1 < (m.get x y).1.natAbs) = changed a.slots b.slots (x,y) ∧
      decide (1 < (m.get x y).2.natAbs) = changed b.slots a.slots (x,y) := by
    have af : precedes a.slots x y = decide (0 < (m.get x y).1) := by simp [precedes,a.before_iff ne]; rfl
    have bf : precedes b.slots x y = decide (0 < (m.get x y).2) := by simp [precedes,b.before_iff ne]; rfl
    simp only [changed,af,bf]
    have value := values x y ne
    simp only [RingActivePairs.molecularValues,List.mem_cons,List.not_mem_nil,or_false] at value
    rcases value with h | h | h | h | h <;> simp [h]
  exact ⟨fun x y ne => (both x y ne).1,fun x y ne => (both x y ne).2⟩

def isLower : OneCenter.LocalizedTetrahedralRSPseudoDescriptor → Bool
  | .chiral _ => false
  | .pseudoasymmetric _ => true

/-- On the molecular reader's accepted ranks, disjoint adjacent reversals suffice for
agreement with the physical assignment's actual letter case at *every* initial order. -/
theorem molecular_adjacent {i c} (o : RingActivePairReport.Assignment i c)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (adjacent : adjacentChanges o.actual.slots o.reflected.slots = true) :
    agrees o.matrix o.actual.slots o.reflected.slots (isLower o.label) = true := by
  obtain ⟨a,b⟩ := magnitudes_of_values o.actual o.reflected
    (fun x y ne => RingActivePairs.rootScore_values (o.matrix.found x y ne))
  have agreement := agrees_of_adjacent o.actual o.reflected a b adjacent
  suffices isLower o.label = decide (RingActivePairReport.reversals o.matrix % 2 ≠ 0) by rwa [this]
  rw [o.casing admit]
  split <;> rename_i h <;> simp [isLower,h]

theorem molecular_atMostOne {i c} (o : RingActivePairReport.Assignment i c)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (small : RingActivePairReport.reversals o.matrix ≤ 1) :
    agrees o.matrix o.actual.slots o.reflected.slots (isLower o.label) = true := by
  apply molecular_adjacent o admit
  exact (adjacent_class _ _ o.actual.perm o.reflected.perm).1
    (by simpa only [RingActivePairReport.changes_eq o.actual o.reflected] using small)

end TetraStereo.Engine.RingInsertionCasing

assert_kernel_only TetraStereo.Engine.RingInsertionCasing.starts_size
assert_kernel_only TetraStereo.Engine.RingInsertionCasing.envelope_exact
assert_kernel_only TetraStereo.Engine.RingInsertionCasing.agrees_iff

assert_kernel_only TetraStereo.Engine.RingInsertionCasing.adjacent_count
assert_kernel_only TetraStereo.Engine.RingInsertionCasing.agrees_of_adjacent
assert_kernel_only TetraStereo.Engine.RingInsertionCasing.agrees_of_atMostOne

assert_kernel_only TetraStereo.Engine.RingInsertionCasing.magnitudes_of_values
assert_kernel_only TetraStereo.Engine.RingInsertionCasing.molecular_adjacent
assert_kernel_only TetraStereo.Engine.RingInsertionCasing.molecular_atMostOne
