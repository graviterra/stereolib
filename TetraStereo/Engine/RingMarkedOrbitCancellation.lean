import TetraStereo.Engine.RingTwoPairOrientation

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.MarkedOrbit
open OneCenter LocalizedGenericMarkedRecalculation Recursive

variable {m : RawMolecule} {p : List Nat} {omitted : List (List Nat)}
    {e : Experiment m p omitted} {q : Classified e} {g : Geometry}
    {a b c d : Nat}

def atomImage (σ : Equiv.Perm (Fin m.atomCount)) (k : Nat) : Nat :=
  if h : k < m.atomCount then (σ ⟨k,h⟩).val else k

/-- A physical relabeling at this exact molecular occurrence. The two naturality
equations concern the actual marked, directed chemical comparisons. Each Arm
also retains its original addressed inventory, with the same readings. -/
structure Relabeling (q : Classified e) (a b c d : Nat) where
  slots : q.partition.order = [a,b,c,d]
  σ : Equiv.Perm (Fin m.atomCount)
  molecular : σ ∈ m.toMoleculeGraph.Aut
  atomData : ∀ x, m.atoms.get (σ x) = m.atoms.get x
  path : p.map (atomImage σ) = p
  omissions : (omitted.map (List.map (atomImage σ))).Perm omitted
  facts : ∀ u ∈ e.arms, ∃ v ∈ e.arms, v.ligand = atomImage σ u.ligand ∧
    (u.facts.map fun f => (f.1.map (atomImage σ),f.2)).Perm v.facts
  first : Bool
  second : Bool
  leftA : atomImage σ a = if first then b else a
  leftB : atomImage σ b = if first then a else b
  rightC : atomImage σ c = if second then d else c
  rightD : atomImage σ d = if second then c else d

/-- The two comparisons are checked separately for all incident marks on both geometries. -/
def Cells (F : Relabeling q a b c d) : Prop :=
  ∀ k ∈ e.arms.map Arm.ligand, ∀ rev,
    q.matrix.strict (atomImage F.σ k) rev (atomImage F.σ a) (atomImage F.σ b) = q.matrix.strict k rev a b ∧
    q.matrix.strict (atomImage F.σ k) rev (atomImage F.σ c) (atomImage F.σ d) = q.matrix.strict k rev c d

def cells (F : Relabeling q a b c d) : Bool :=
  (e.arms.map Arm.ligand).all fun k => [false,true].all fun rev =>
    (q.matrix.strict (atomImage F.σ k) rev (atomImage F.σ a) (atomImage F.σ b) == q.matrix.strict k rev a b) &&
    (q.matrix.strict (atomImage F.σ k) rev (atomImage F.σ c) (atomImage F.σ d) == q.matrix.strict k rev c d)

theorem cells_iff (F : Relabeling q a b c d) : cells F = true ↔ Cells F := by
  simp only [cells,Cells,List.all_eq_true,Bool.and_eq_true,beq_iff_eq]
  constructor
  · intro checked k hk rev
    exact checked k hk rev (by cases rev <;> simp)
  · exact fun law k hk rev _ => law k hk rev

structure Action (q : Classified e) (a b c d : Nat) extends Relabeling q a b c d where
  natural : Cells toRelabeling

def check? (F : Relabeling q a b c d) : Option (Action q a b c d) :=
  if h : cells F then some ⟨F,(cells_iff F).mp h⟩ else none

theorem check_iff (F : Relabeling q a b c d) : (check? F).isSome = true ↔ Cells F := by
  rw [← cells_iff]
  unfold check?
  split <;> simp_all

variable (A : Action q a b c d)

private theorem ids (A : Action q a b c d) : [a,b,c,d].Perm (e.arms.map Arm.ligand) := A.slots ▸ q.partition.incident

theorem Action.eligible {k : Nat} (h : k ∈ e.arms.map Arm.ligand) :
    atomImage A.σ k ∈ e.arms.map Arm.ligand := by
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
  obtain ⟨v,hv,eqn,_⟩ := A.facts u hu
  exact List.mem_map.mpr ⟨v,hv,eqn⟩

private theorem reversePair {i j k : Nat} (hk : k ∈ e.arms.map Arm.ligand) (ne : i ≠ j)
    (checked : (directedPairs [i,j] id).all
      (fun (s,t) => ((q.matrix.row? s t).map Row.unmarked) == some .eq) = true) (rev : Bool) :
    q.matrix.strict k rev j i = !q.matrix.strict k rev i j := by
  have dir := @Matrix.tied_pair_directions _ _ _ _ q.matrix i j k hk
    (eq_of_beq (List.all_eq_true.mp checked (i,j) (by simp [directedPairs,ne,Ne.symm ne])))
    (eq_of_beq (List.all_eq_true.mp checked (j,i) (by simp [directedPairs,ne,Ne.symm ne])))
  rcases dir with h | h <;> simp [(h rev).1,(h rev).2]

/-- The two marked directions on either geometry transform independently. -/
theorem Action.preferences {k : Nat} (hk : k ∈ e.arms.map Arm.ligand) (rev : Bool) :
    q.matrix.strict (atomImage A.σ k) rev a b =
      (if A.first then !q.matrix.strict k rev a b else q.matrix.strict k rev a b) ∧
    q.matrix.strict (atomImage A.σ k) rev c d =
      (if A.second then !q.matrix.strict k rev c d else q.matrix.strict k rev c d) := by
  have unique := (ids A).nodup_iff.mpr e.distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at unique
  have cls : q.matrix.partitionOK [a,b,c,d] = true := A.slots ▸ q.partition.classes
  have pairs := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp cls).1
  have high := reversePair (A.eligible hk) unique.1.1 pairs.1 rev
  have low := reversePair (A.eligible hk) unique.2.2.1 pairs.2 rev
  obtain ⟨h,l⟩ := A.natural k hk rev
  rw [A.leftA,A.leftB] at h
  rw [A.rightC,A.rightD] at l
  constructor
  · cases f : A.first <;> simp_all
  · cases s : A.second <;> simp_all

private theorem mappedOrder {f : Nat → Nat} {i j u v : Nat} {x y : Bool}
    (hi : f i = if x then j else i) (hj : f j = if x then i else j)
    (hu : f u = if y then v else u) (hv : f v = if y then u else v) (s t : Bool) :
    (pairOrder i j u v s t).map f =
      pairOrder i j u v (if x then !s else s) (if y then !t else t) := by
  cases x <;> cases y <;> cases s <;> cases t <;> simp_all [pairOrder]

/-- Both unique, strict molecular orders are transported, including the reflected order. -/
theorem Action.orders {k : Nat} (hk : k ∈ e.arms.map Arm.ligand) (rev : Bool) :
    q.matrix.orders (atomImage A.σ k) rev =
      (q.matrix.orders k rev).map (List.map (atomImage A.σ)) := by
  have src := q.partition.orders_from_comparisons A.slots k hk
  have dst := q.partition.orders_from_comparisons A.slots _ (A.eligible hk)
  have ⟨h,l⟩ := A.preferences hk false
  cases rev
  · rw [src.1,dst.1,h,l]
    exact congrArg (fun x : List Nat => [x])
      (mappedOrder A.leftA A.leftB A.rightC A.rightD _ _).symm
  · rw [src.2,dst.2,h,l]
    exact congrArg (fun x : List Nat => [x])
      (mappedOrder A.rightC A.rightD A.leftA A.leftB _ _).symm

/-- A single pair transposition would reverse the physical readback. -/
theorem Action.parity {k : Nat} (hk : k ∈ e.arms.map Arm.ligand) :
    q.partition.preserves (atomImage A.σ k) =
      if A.first == A.second then q.partition.preserves k else !q.partition.preserves k := by
  have ⟨h,l⟩ := A.preferences hk false
  simp only [Partition.preserves,A.slots,Matrix.aligned,h,l]
  cases A.first <;> cases A.second <;> cases q.matrix.strict k false a b <;>
    cases q.matrix.strict k false c d <;> decide

/-- Single pair flips fix a mark in the other pair. Its completed vote cannot
be its opposite. Only the identity and the simultaneous double flip survive. -/
theorem Action.even : A.first = A.second := by
  have ha := A.parity ((ids A).mem_iff.mp (show a ∈ [a,b,c,d] by simp))
  have hc := A.parity ((ids A).mem_iff.mp (show c ∈ [a,b,c,d] by simp))
  rw [A.leftA] at ha
  rw [A.rightC] at hc
  cases f : A.first <;> cases s : A.second <;> simp_all

theorem Action.sameVote (s : PopulationReading q g) {k : Nat} (h : k ∈ e.arms.map Arm.ligand) :
    s.atMark (atomImage A.σ k) = s.atMark k := by
  simp [PopulationReading.atMark,A.parity h,A.even]

private theorem orbitBits (flip : A.first = true) :
    q.partition.preserves b = q.partition.preserves a ∧
    q.partition.preserves d = q.partition.preserves c := by
  have ha := A.parity ((ids A).mem_iff.mp (show a ∈ [a,b,c,d] by simp))
  have hc := A.parity ((ids A).mem_iff.mp (show c ∈ [a,b,c,d] by simp))
  have second := A.even.symm.trans flip
  simpa [A.leftA,A.rightC,flip,second] using And.intro ha hc

/-- Under the simultaneous physical exchange, opposite representative
readbacks are necessary and sufficient for the completed signed aggregate to cancel. -/
theorem Action.cancellation_iff (flip : A.first = true) (s : PopulationReading q g) :
    s.proposed = some none ↔ (s.atMark a).actual ≠ (s.atMark c).actual := by
  obtain ⟨ab,cd⟩ := orbitBits A flip
  have count (f : Nat → Bool) :
      e.arms.countP (fun u => f u.ligand) = [a,b,c,d].countP f := by
    simpa only [List.countP_map,Function.comp_def] using
      ((ids A).symm.countP_eq f)
  rw [s.proposed_cancels_iff,count q.partition.preserves,count (fun k => !q.partition.preserves k)]
  cases h : q.partition.preserves a <;> cases j : q.partition.preserves c <;>
    cases r : s.reference <;> simp [ab,cd,h,j,PopulationReading.atMark,r,RS.swap]

/-- The ordinary unanimous certificate can be read off the same two
representatives. The marks and the two-geometry reading are retained. -/
theorem Action.certificate_iff (flip : A.first = true) (s : PopulationReading q g) (r : Reading) :
    (q.certificate? g).map Certificate.reading = some r ↔ s.atMark a = r ∧ s.atMark c = r := by
  obtain ⟨ab,cd⟩ := orbitBits A flip
  have h : s.atMark b = s.atMark a := by simp [PopulationReading.atMark,ab]
  have j : s.atMark d = s.atMark c := by simp [PopulationReading.atMark,cd]
  rw [s.certificate_iff]
  constructor
  · intro all
    exact ⟨all a ((ids A).mem_iff.mp (by simp)),all c ((ids A).mem_iff.mp (by simp))⟩
  · intro both k mem
    have slots := (ids A).mem_iff.mpr mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at slots
    rcases slots with rfl | rfl | rfl | rfl
    · exact both.1
    · exact h.trans both.1
    · exact both.2
    · exact j.trans both.2

end TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.MarkedOrbit

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.MarkedOrbit.Action.orders
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.MarkedOrbit.Action.even
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.MarkedOrbit.Action.sameVote
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.MarkedOrbit.Action.cancellation_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.MarkedOrbit.Action.certificate_iff

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.MarkedOrbit.check_iff
