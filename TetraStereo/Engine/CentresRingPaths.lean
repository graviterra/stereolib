import TetraStereo.OneCenter.ChemistrySemantics
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.Engine.CentresRing
open OneCenter

/-- A path is stored from its current atom back to the original focus. -/
def extendPath (adj : Nat → List Nat) : List Nat → List (List Nat)
  | [] => []
  | a :: tail =>
    ((adj a).filter fun b => !(a :: tail).contains b).map (fun b => b :: a :: tail)

def layers (adj : Nat → List Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, _ => []
  | _+1, [] => []
  | n+1, p :: ps => (p :: ps) ++ layers adj n ((p :: ps).flatMap (extendPath adj))

/-- An independent atom-level characterization of a real (nonduplicate) digraph occurrence. -/
inductive RealPath (adj : Nat → List Nat) (root : Nat) : List Nat → Prop where
  | start : RealPath adj root [root]
  | next {a b tail} : RealPath adj root (a :: tail) → b ∈ adj a → b ∉ a :: tail →
      RealPath adj root (b :: a :: tail)

theorem RealPath.nodup {adj root p} (h : RealPath adj root p) : p.Nodup := by
  induction h with
  | start => simp
  | next _ _ fresh ih => exact List.nodup_cons.mpr ⟨fresh,ih⟩

private theorem mem_layers_cons (adj : Nat → List Nat) (n : Nat) (front : List (List Nat)) (p : List Nat) :
    p ∈ layers adj (n+1) front ↔ p ∈ front ∨ p ∈ layers adj n (front.flatMap (extendPath adj)) := by
  cases front with
  | nil => cases n <;> simp [layers]
  | cons a as => simp only [layers,List.mem_append]

private def level (adj : Nat → List Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, front => front
  | n+1, front => level adj n (front.flatMap (extendPath adj))

private theorem level_next (adj : Nat → List Nat) (n : Nat) (front : List (List Nat)) :
    level adj (n+1) front = (level adj n front).flatMap (extendPath adj) := by
  induction n generalizing front with
  | zero => rfl
  | succ n ih => exact ih (front.flatMap (extendPath adj))

private theorem mem_layers (adj : Nat → List Nat) (n : Nat) (front : List (List Nat)) (p : List Nat) :
    p ∈ layers adj n front ↔ ∃ k < n, p ∈ level adj k front := by
  induction n generalizing front with
  | zero => simp [layers]
  | succ n ih =>
    rw [mem_layers_cons,ih]
    constructor
    · rintro (h | ⟨k,hk,mem⟩)
      · exact ⟨0,Nat.zero_lt_succ _,h⟩
      · exact ⟨k+1,Nat.succ_lt_succ hk,mem⟩
    · rintro ⟨k,hk,mem⟩
      cases k with
      | zero => exact Or.inl mem
      | succ k => exact Or.inr ⟨k,Nat.lt_of_succ_lt_succ hk,mem⟩

private theorem level_exact (adj : Nat → List Nat) (root n : Nat) (p : List Nat) :
    p ∈ level adj n [[root]] ↔ RealPath adj root p ∧ p.length = n+1 := by
  induction n generalizing p with
  | zero =>
    simp only [level,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · rintro rfl; exact ⟨.start,rfl⟩
    · rintro ⟨h,len⟩
      cases h with
      | start => rfl
      | next _ _ _ => simp at len
  | succ n ih =>
    rw [level_next,List.mem_flatMap]
    constructor
    · rintro ⟨old,oldmem,mem⟩
      obtain ⟨path,len⟩ := (ih _).mp oldmem
      cases old with
      | nil => simp [extendPath] at mem
      | cons a tail =>
        simp only [extendPath,List.mem_map,List.mem_filter] at mem
        obtain ⟨b,⟨bond,newAtom⟩,rfl⟩ := mem
        exact ⟨.next path bond (by simpa using newAtom), congrArg Nat.succ len⟩
    · rintro ⟨path,len⟩
      cases path with
      | start => simp at len
      | @next a b tail path bond fresh =>
        exact ⟨a :: tail,(ih _).mpr ⟨path,Nat.succ.inj len⟩,by simpa [extendPath,bond] using fresh⟩

theorem layers_exact (adj : Nat → List Nat) (root fuel : Nat) (p : List Nat) :
    p ∈ layers adj fuel [[root]] ↔ RealPath adj root p ∧ p.length ≤ fuel := by
  rw [mem_layers]
  constructor
  · rintro ⟨k,h,mem⟩
    obtain ⟨path,len⟩ := (level_exact adj root k p).mp mem
    exact ⟨path,by omega⟩
  · rintro ⟨path,bound⟩
    have pos : 0 < p.length := by cases path <;> simp
    exact ⟨p.length-1,by omega,(level_exact adj root _ p).mpr ⟨path,by omega⟩⟩

def bondedAtoms (mol : RawMolecule) (i : Nat) : List Nat :=
  mol.bonds.filterMap fun b =>
    if b.source == i then some b.target else if b.target == i then some b.source else none

def molecularPaths (mol : RawMolecule) (focus : Nat) (centers : List Nat) : List (List Nat) :=
  (layers (bondedAtoms mol) mol.atoms.length [[focus]]).filter fun p =>
    (p.head?.any fun a => a != focus && centers.contains a)

private theorem neighbor_bound (mol : RawMolecule) (wf : mol.WellFormed) {i j : Nat}
    (member : j ∈ bondedAtoms mol i) : j < mol.atomCount := by
  obtain ⟨b,hb,found⟩ := List.mem_filterMap.mp member
  have bounds := wf b hb
  split at found
  · cases found; exact bounds.2.1
  · split at found
    · cases found; exact bounds.1
    · contradiction

private theorem RealPath.bounded {mol : RawMolecule} (wf : mol.WellFormed) {focus p}
    (valid : focus < mol.atomCount) (path : RealPath (bondedAtoms mol) focus p) :
    ∀ i ∈ p, i < mol.atomCount := by
  induction path with
  | start => simpa using valid
  | next prev edge fresh ih =>
    intro i mem
    rcases List.mem_cons.mp mem with rfl | h
    · exact neighbor_bound mol wf edge
    · exact ih i h

/-- Every real path ending at another candidate occurs, with no extra cutoff
hypothesis. A simple path fits within the atom count of a well-formed molecule. -/
theorem molecularPaths_exact (mol : RawMolecule) (wf : mol.WellFormed)
    (focus : Nat) (valid : focus < mol.atomCount) (cs : List Nat) (atom : Nat) (tail : List Nat) :
    atom :: tail ∈ molecularPaths mol focus cs ↔
      RealPath (bondedAtoms mol) focus (atom :: tail) ∧ atom ≠ focus ∧ atom ∈ cs := by
  simp only [molecularPaths,List.mem_filter,layers_exact]
  have bound (h : RealPath (bondedAtoms mol) focus (atom :: tail)) :
      (atom :: tail).length ≤ mol.atoms.length := by
    have subset : atom :: tail ⊆ List.range mol.atomCount := fun i hi =>
      List.mem_range.mpr (h.bounded wf valid i hi)
    simpa [RawMolecule.atomCount] using (List.subperm_of_subset h.nodup subset).length_le
  simp [and_assoc]
  exact fun h _ _ => bound h

section
variable {α : Type*} (le : α → α → Bool)

private def mergeFuel : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | n+1, a :: as, b :: bs =>
    if le a b then a :: mergeFuel n as (b :: bs) else b :: mergeFuel n (a :: as) bs

private theorem mergeFuel_eq (n : Nat) (xs ys : List α) (h : xs.length + ys.length ≤ n) :
    mergeFuel le n xs ys = xs.merge ys le := by
  induction n generalizing xs ys with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hx,hy,mergeFuel]
  | succ n ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel,List.merge]
        split <;> congr 1 <;> apply ih <;> simp_all <;> omega

private def sortFuel : Nat → List α → List α
  | 0, xs => xs
  | _+1, [] => []
  | _+1, [a] => [a]
  | n+1, a :: b :: xs =>
    let parts := List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs,rfl⟩
    mergeFuel le (xs.length+2) (sortFuel n parts.1) (sortFuel n parts.2)

private theorem sortFuel_eq (n : Nat) (xs : List α) (h : xs.length ≤ n) :
    sortFuel le n xs = xs.mergeSort le := by
  induction n generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hx,sortFuel]
  | succ n ih =>
    match xs with
    | [] | [_] => simp [sortFuel]
    | a :: b :: rest =>
      let parts := List.MergeSort.Internal.splitInTwo ⟨a :: b :: rest,rfl⟩
      have left := parts.1.2
      have right := parts.2.2
      change parts.1.val.length = (rest.length+2+1)/2 at left
      change parts.2.val.length = (rest.length+2)/2 at right
      change rest.length+2 ≤ n+1 at h
      rw [List.mergeSort]
      change mergeFuel le (rest.length+2) (sortFuel le n parts.1) (sortFuel le n parts.2) =
        (parts.1.val.mergeSort le).merge (parts.2.val.mergeSort le) le
      rw [ih _ (by omega), ih _ (by omega), mergeFuel_eq]
      simp only [List.length_mergeSort]
      omega

/-- The fuel uses the full input length so closed comparison receipts reduce in the kernel.
Compiled evaluation uses the equivalent standard-library merge sort. -/
def replayListSort (xs : List α) : List α := sortFuel le xs.length xs

theorem replayListSort_eq (xs : List α) : replayListSort le xs = xs.mergeSort le :=
  sortFuel_eq le xs.length xs (Nat.le_refl _)

private def fastListSort (xs : List α) := xs.mergeSort le
@[csimp] private theorem compileReplayListSort : @replayListSort = @fastListSort := by
  funext α le xs
  exact replayListSort_eq le xs
end

def scheduled (paths : List (List Nat)) : List (List Nat × Nat) :=
  replayListSort (fun a b => a.1.length ≥ b.1.length) paths.zipIdx

theorem schedule_exactly_once (paths : List (List Nat)) :
    ((scheduled paths).map Prod.snd).Perm (List.range' 0 paths.length) := by
  simpa only [scheduled,replayListSort_eq,List.zipIdx_map_snd] using
    (List.mergeSort_perm paths.zipIdx (fun a b => decide (a.1.length ≥ b.1.length))).map Prod.snd

private abbrev Item := List Nat × Nat
private abbrev farther (a b : Item) : Bool := decide (a.1.length ≥ b.1.length)

private theorem farther_trans (a b c : Item) (ab : farther a b) (bc : farther b c) : farther a c := by
  simpa [farther] using le_trans (of_decide_eq_true bc) (of_decide_eq_true ab)

private theorem farther_total (a b : Item) : farther a b || farther b a := by
  simp [farther,le_total]

theorem schedule_deeper_first (paths : List (List Nat)) :
    (scheduled paths).Pairwise (fun a b => b.1.length ≤ a.1.length) := by
  simpa [scheduled,replayListSort_eq,farther] using
    (List.pairwise_mergeSort (le := farther) farther_trans farther_total paths.zipIdx)

theorem schedule_same_distance (paths : List (List Nat)) (a b : List Nat × Nat)
    (tie : a.1.length = b.1.length) (order : [a,b].Sublist paths.zipIdx) :
    [a,b].Sublist (scheduled paths) :=
  by
    rw [scheduled,replayListSort_eq]
    exact List.pair_sublist_mergeSort (le := farther) farther_trans farther_total (by simp [farther,tie]) order

end TetraStereo.Engine.CentresRing
assert_kernel_only TetraStereo.Engine.CentresRing.layers_exact
assert_kernel_only TetraStereo.Engine.CentresRing.schedule_exactly_once
assert_kernel_only TetraStereo.Engine.CentresRing.molecularPaths_exact
assert_kernel_only TetraStereo.Engine.CentresRing.schedule_deeper_first
assert_kernel_only TetraStereo.Engine.CentresRing.schedule_same_distance
assert_kernel_only TetraStereo.Engine.CentresRing.replayListSort_eq
