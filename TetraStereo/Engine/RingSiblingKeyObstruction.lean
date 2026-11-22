import TetraStereo.Engine.RingFrontierProfileShape

set_option autoImplicit false

namespace TetraStereo.Engine.RingSiblingKeyObstruction
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingRetainedChemicalTrace
open RingRetainedSiblingOrder (SameLeaves chemicalChildren?)
open RingRetainedChemicalPreorder (orderWord compare_word)

private abbrev children (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q

/-- The exact molecular obstruction is witnessed by two different child
occurrences with the same full constitutional key and a nonterminal member. -/
def Collision (i : Input) (q : Arm i) : Prop :=
  ∃ a ∈ children i q, ∃ b ∈ children i q, a ≠ b ∧
    ∃ k, key? i a = some k ∧ key? i b = some k ∧
      (children i a ≠ [] ∨ children i b ≠ [])

/-- The atomic fast path and the complete-key comparator use the same
molecular endpoint atomic number, including at ring duplicate leaves. -/
theorem key_number {i : Input} {q : Arm i} {k : Key} (read : key? i q = some k) :
    RingActivePairs.z? i q = some k.root.atomic := by
  obtain ⟨z,hz⟩ := RingAtomicProfileShape.number_total i q
  have src := key_source read
  cases src with
  | node frame obs _ _ _ =>
    unfold observation? at obs
    obtain ⟨a,ha,more⟩ := Option.bind_eq_some_iff.mp obs
    obtain ⟨r,hr,more⟩ := Option.bind_eq_some_iff.mp more
    obtain ⟨_,pos,kind⟩ := Option.bind_eq_some_iff.mp more
    have endpoint : RingActivePairs.endpointZ? i q = some r.element.atomicNumber := by
      simp [RingActivePairs.endpointZ?,ha,hr,pos]
    unfold RingActivePairs.z? at hz ⊢
    cases hp : q.occurrence.val.node.provenance <;> simp only [hp] at hz kind ⊢
    all_goals first | contradiction | skip
    · obtain ⟨_,_,result⟩ := Option.bind_eq_some_iff.mp kind
      obtain rfl := Option.some.inj result
      exact endpoint
    · split at hz <;> try contradiction
      rename_i leaf
      obtain ⟨_,_,further⟩ := Option.bind_eq_some_iff.mp kind
      obtain ⟨_,_,result⟩ := Option.bind_eq_some_iff.mp further
      obtain rfl := Option.some.inj result
      simp [leaf,endpoint,assemble]

private def Compatible (i : Input) (a b : Arm i) : Prop :=
  ∀ k, key? i a = some k → key? i b = some k → children i a = [] ∧ children i b = []

private theorem symmetric (i : Input) : Symmetric (Compatible i) :=
  fun _ _ h k ka kb => (h k kb ka).symm

private theorem no_collision {i : Input} {q : Arm i} {xs : List (Arm i)}
    (perm : xs.Perm (children i q)) (ok : xs.Pairwise (Compatible i)) : ¬ Collision i q := by
  rintro ⟨a,ha,b,hb,ne,k,ka,kb,nonterminal⟩
  have both := ok.forall (symmetric i) (perm.mem_iff.mpr ha) (perm.mem_iff.mpr hb) ne k ka kb
  exact nonterminal.elim (fun h => h both.1) (fun h => h both.2)

private abbrev z (i : Input) (q : Arm i) := (RingActivePairs.z? i q).getD 0

private theorem number_priority {x y : Key} (hx : WellFormed x) (hy : WellFormed y)
    (lower : x.root.atomic < y.root.atomic) : compareKeys x y = .lt := by
  have ax := queue_start .atomic x hx
  have ay := queue_start .atomic y hy
  change x.atomic.word = [x.root.atomic] :: _ at ax
  change y.atomic.word = [y.root.atomic] :: _ at ay
  have atom := Nat.compare_eq_lt.mpr lower
  simp [compareKeys,keyTrace,ax,ay,atom]

private theorem ordered_pairs {i : Input} {q : Arm i}
    {v : {xs : List (Arm i) // RingRetainedSiblingOrder.Order i q xs}} (got : chemicalChildren? i q = some v) :
    v.val.Pairwise (fun a b => Compatible i a b ∧ z i b ≤ z i a) := by
  unfold chemicalChildren? at got
  split at got
  next es h _ =>
    obtain rfl := Option.some.inj got
    have atom := RingActivePairs.children_source h
    apply atom.descending.imp
    intro a b lt
    refine ⟨?_,le_of_lt lt⟩
    intro k ka kb
    rw [key_number ka,key_number kb] at lt
    exact False.elim (Nat.lt_irrefl _ lt)
  next =>
    obtain ⟨_,_,nextStep⟩ := Option.bind_eq_some_iff.mp got
    obtain ⟨⟨rs,_⟩,_,out⟩ := Option.bind_eq_some_iff.mp nextStep
    dsimp only at out
    split at out
    next strict =>
      obtain rfl := Option.some.inj out
      apply List.pairwise_map.mpr
      apply strict.imp
      intro a b ok
      refine ⟨?_,?_⟩
      · intro k ka kb
        have ax := Option.some.inj (a.2.property.symm.trans ka)
        have bx := Option.some.inj (b.2.property.symm.trans kb)
        rcases ok with higher | ⟨_,leaves⟩
        · change compareKeys a.2.val b.2.val = .gt at higher
          rw [ax,bx,compare_word] at higher
          simp at higher
        · exact ⟨leaves.1,leaves.2.1⟩
      · simp only [z,key_number a.2.property,key_number b.2.property,Option.getD_some]
        by_contra! lower
        have loses := number_priority (key_source a.2.property).formed (key_source b.2.property).formed lower
        change compareKeys a.2.val b.2.val = .gt ∨ (compareKeys a.2.val b.2.val = .eq ∧ _) at ok
        rw [loses] at ok
        simp at ok
    next => contradiction

theorem nonincreasing_z {i : Input} {q : Arm i}
    {v : {xs : List (Arm i) // RingRetainedSiblingOrder.Order i q xs}} (got : chemicalChildren? i q = some v) :
    v.val.Pairwise (fun a b => (RingActivePairs.z? i b).getD 0 ≤ (RingActivePairs.z? i a).getD 0) :=
  (ordered_pairs got).imp And.right

private abbrev Row (i : Input) := (a : Arm i) × {k : Key // key? i a = some k}

private def readRow (i : Input) (a : Arm i) : Option (Row i) :=
  (key? i a).attach.map (Sigma.mk a)

private theorem rows (i : Input) (q : Arm i) :
    ∃ rs, (children i q).mapM (readRow i) = some rs ∧ rs.map Sigma.fst = children i q := by
  have valid (a : Arm i) (ha : a ∈ children i q) := i.certified.localizedRerootChild_valid q a _
    (i.certified.executableLocalizedRerootChildren_declarative q) ha
  suffices ∀ (xs : List (Arm i)), (∀ a ∈ xs, a ∈ children i q) →
      ∃ rs, xs.mapM (readRow i) = some rs ∧ rs.map Sigma.fst = xs from this _ (fun _ h => h)
  intro xs
  induction xs with
  | nil => exact fun _ => ⟨[],rfl,rfl⟩
  | cons x xs ih =>
    intro sub
    obtain ⟨k,hk⟩ := RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) x
      (valid x (sub x List.mem_cons_self))
    obtain ⟨rs,hr,orig⟩ := ih (fun a ha => sub a (List.mem_cons_of_mem _ ha))
    have row : readRow i x = some ⟨x,⟨k,hk⟩⟩ := by
      rw [readRow,Option.attach_eq_some _ ⟨k,hk⟩]; rfl
    exact ⟨⟨x,⟨k,hk⟩⟩::rs,by simp [List.mapM_cons,row,hr],by simp [orig]⟩

private def cmp {i : Input} (a b : Row i) := compareKeys a.2.val b.2.val

private def accepted {i : Input} (a b : Row i) :=
  cmp a b = .gt ∨ (cmp a b = .eq ∧ SameLeaves i a.1 b.1)

private theorem sorted_accepts {i : Input} {q : Arm i} {rs : List (Row i)} (orig : rs.map Sigma.fst = children i q)
    (good : ¬ Collision i q) :
    (rs.mergeSort (fun a b => (cmp a b).isGE)).Pairwise accepted := by
  let ordered := rs.mergeSort (fun a b => (cmp a b).isGE)
  have perm : ordered.Perm rs := List.mergeSort_perm ..
  have allArm : (ordered.map Sigma.fst).Perm (children i q) := orig ▸ perm.map _
  have distinct : ordered.Pairwise (fun a b => a.1 ≠ b.1) :=
    List.pairwise_map.mp (allArm.nodup_iff.mpr (i.certified.executableLocalizedRerootChildren_nodup q))
  have ord : ordered.Pairwise (fun a b => (cmp a b).isGE = true) := by
    apply List.pairwise_mergeSort
    · intro a b c
      simp only [cmp,compare_word]
      exact Std.TransCmp.isGE_trans
    · intro a b
      simp only [cmp,compare_word]
      rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := orderWord a.2.val) (b := orderWord b.2.val)]
      cases compare (orderWord b.2.val) (orderWord a.2.val) <;> rfl
  apply (List.pairwise_and_iff.mpr ⟨ord,distinct⟩).imp_of_mem
  intro a b ha hb pair
  have member (r : Row i) (hr : r ∈ ordered) : r.1 ∈ children i q := allArm.mem_iff.mp (List.mem_map_of_mem hr)
  cases h : cmp a b with
  | lt => have ge := pair.1; rw [h] at ge; contradiction
  | gt => exact Or.inl h
  | eq =>
    have eqn := h
    rw [cmp,compare_word] at eqn
    have same := RingPairGateCount.key_eq (key_source a.2.property).formed (key_source b.2.property).formed
      (Std.compare_eq_eq_iff_eq.mp eqn)
    have akey := a.2.property.trans (congrArg some same)
    have empty : children i a.1 = [] ∧ children i b.1 = [] := by
      by_contra! missing
      apply good
      refine ⟨a.1,member a ha,b.1,member b hb,pair.2,b.2.val,akey,b.2.property,?_⟩
      by_cases left : children i a.1 = []
      · exact Or.inr (missing left)
      · exact Or.inl left
    exact Or.inr ⟨h,empty.1,empty.2,(key_number akey).trans (key_number b.2.property).symm⟩

/-- Exact success of both executable branches. Every child key is covered by
molecular admission, including for a parent whose incoming cut is absent. -/
theorem covered_iff (i : Input) (q : Arm i) : (chemicalChildren? i q).isSome = true ↔ ¬ Collision i q := by
  constructor
  · intro hit
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp hit
    exact no_collision v.property.complete ((ordered_pairs hv).imp And.left)
  · intro good
    unfold chemicalChildren?
    split
    · rfl
    · obtain ⟨rs,hr,orig⟩ := rows i q
      have lift := Option.attach_eq_some _ ⟨rs,hr⟩
      have ok := sorted_accepts orig good
      change ((((children i q).mapM (readRow i)).attach >>= _) : Option _).isSome = true
      rw [lift]
      simp only [Option.bind_eq_bind,Option.bind_some]
      split
      · rfl
      · rename_i rejected
        exact (rejected ok).elim

theorem missing_iff (i : Input) (q : Arm i) : chemicalChildren? i q = none ↔ Collision i q := by
  rw [← not_iff_not]
  simpa only [Option.ne_none_iff_isSome] using covered_iff i q

/-- A shallow conflict is a disagreement of the actual two-geometry unit or
lowercase readings at two sibling occurrences with the same atomic number. -/
def ShallowConflict {i : Input} (read : RingNestedActivePair.Reader i) (q : Arm i) : Prop :=
  ∃ a ∈ children i q, ∃ b ∈ children i q,
    z i a = z i b ∧ RingNestedActivePair.shallowReading read a ≠ RingNestedActivePair.shallowReading read b

theorem shallow_iff {i : Input} {q : Arm i} (read : RingNestedActivePair.Reader i)
    {v : {xs : List (Arm i) // RingRetainedSiblingOrder.Order i q xs}} (got : chemicalChildren? i q = some v) :
    RingNestedActivePair.ShallowOrder i read v.val ↔ ¬ ShallowConflict read q := by
  let agrees (a b : Arm i) := z i a = z i b → RingNestedActivePair.shallowReading read a = RingNestedActivePair.shallowReading read b
  have symmetric : Symmetric agrees := fun _ _ h e => (h e.symm).symm
  have perm := v.property.complete
  constructor
  · intro ok conflict
    obtain ⟨a,ha,b,hb,eqn,unequal⟩ := conflict
    have pw : v.val.Pairwise agrees := ok.imp (fun h eqn => h.elim
      (fun lt => False.elim (lt.ne eqn.symm)) And.right)
    have diff : a ≠ b := fun same => unequal (same ▸ rfl)
    exact unequal (pw.forall symmetric (perm.mem_iff.mpr ha) (perm.mem_iff.mpr hb) diff eqn)
  · intro good
    apply (nonincreasing_z got).imp_of_mem
    intro a b ha hb le
    rcases lt_or_eq_of_le le with lt | eqn
    · exact Or.inl lt
    · refine Or.inr ⟨eqn.symm,?_⟩
      by_contra diff
      exact good ⟨a,perm.mem_iff.mp ha,b,perm.mem_iff.mp hb,eqn.symm,diff⟩

/-- No reader or sorter premise remains in the molecular sibling condition:
it is exactly the absence of the two explicit two-occurrence obstructions. -/
theorem ordered_shallow_iff (i : Input) (q : Arm i) (read : RingNestedActivePair.Reader i) :
    (∃ row, chemicalChildren? i q = some row ∧ RingNestedActivePair.ShallowOrder i read row.val) ↔
      ¬ Collision i q ∧ ¬ ShallowConflict read q := by
  constructor
  · rintro ⟨row,found,shallow⟩
    exact ⟨(covered_iff i q).mp (by rw [found]; rfl),(shallow_iff read found).mp shallow⟩
  · rintro ⟨clear,agree⟩
    obtain ⟨row,found⟩ := Option.isSome_iff_exists.mp ((covered_iff i q).mpr clear)
    exact ⟨row,found,(shallow_iff read found).mpr agree⟩

/-- Missing coverage at a real scheduled frontier is witnessed by one of two
pairs of molecular sibling occurrences, using the actual frozen publications. -/
theorem frontier_missing_iff {i : Input} {root : i.certified.Atom} {f : RingActivePairs.Site i}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (q : Arm i) (on : q.occurrence.val.root = f.val.root)
    (valid : i.certified.LocalizedRerootCursorValid q) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    RingNestedActivePair.retainedLevels? i read (2*(i.certified.certified.input.molecule.atomCount+2)+2) [q] = none ↔
      ∃ t, Reaches i q t ∧ (Collision i t ∨ ShallowConflict read t) := by
  dsimp only
  have placed := RingFrontierProfileShape.missing_iff_sibling listed q on valid
  dsimp only at placed
  rw [placed]
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  rw [ordered_shallow_iff]
  tauto

end TetraStereo.Engine.RingSiblingKeyObstruction

assert_kernel_only TetraStereo.Engine.RingSiblingKeyObstruction.key_number
assert_kernel_only TetraStereo.Engine.RingSiblingKeyObstruction.covered_iff
assert_kernel_only TetraStereo.Engine.RingSiblingKeyObstruction.missing_iff
assert_kernel_only TetraStereo.Engine.RingSiblingKeyObstruction.nonincreasing_z
assert_kernel_only TetraStereo.Engine.RingSiblingKeyObstruction.shallow_iff
assert_kernel_only TetraStereo.Engine.RingSiblingKeyObstruction.frontier_missing_iff
assert_kernel_only TetraStereo.Engine.RingSiblingKeyObstruction.ordered_shallow_iff
