import TetraStereo.Engine.RingStereoSphereInventory
import TetraStereo.Engine.RingStereoPriorityBlocks
import Mathlib.Data.Finset.Sort

/-! Enumerate the distinct molecular donor ranks in each sphere. Each group
retains the complete signed parent rank, the terminal earlier-rule priority,
and all three populations sharing that stem. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMolecularDonorClasses
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingRetainedReferenceGroup (Path)
open RingStereoSphereInventory (SignedPath project Inventory)
open RingFullPathPairs (stepKey stripBit bitOf)
open RingStereoPriorityBlocks (Class)
open RingStereoSiblingPass (order)
open private readRow_sorted from TetraStereo.Engine.RingUnorderedSphereReading

/-- Reconstruct the three terminal populations for a projected rank from the
unsorted signed sphere. Only the last hand is varied in the three lookups. -/
def census (m : Multiset Path) (p : Path) : Class :=
  let stem := p.dropLast
  let earlier := stripBit (p.getLast?.getD [])
  let n b := m.count (stem ++ [stepKey earlier b])
  ⟨stem,earlier,n none,n (some true),n (some false)⟩

theorem census_snoc (m : Multiset Path) (p : Path) (d : List RingRetainedChemicalTrace.Word)
    (b : Option Bool) :
    census m (p ++ [stepKey d b]) =
      ⟨p,d,m.count (p ++ [stepKey d none]),m.count (p ++ [stepKey d (some true)]),
        m.count (p ++ [stepKey d (some false)])⟩ := by
  simp [census,RingFullPathPairs.stripBit_step]

structure Group where
  stem : Class
  like : Bool
  deriving DecidableEq, Repr

def Group.word (g : Group) := List.replicate (if g.like then g.stem.like else g.stem.unlike) g.like

/-- Sort each distinct observed rank only once. Adjacent bits with different
parent keys remain distinct classes even if they have the same sign. -/
def groups (seed : RS) (row : Multiset SignedPath) : List Group :=
  let m := row.map (project seed)
  (m.toFinset.sort (· ≥ ·)).filterMap fun p => (bitOf p).map fun b => ⟨census m p,b⟩

/-- Each reported group comes from a molecular path and vice versa. The
terminal mark selects one population of its three-way stem census. -/
theorem mem_groups (seed : RS) (row : Multiset SignedPath) (g : Group) :
    g ∈ groups seed row ↔ ∃ p ∈ row, ∃ b, bitOf (project seed p) = some b ∧
      g = ⟨census (row.map (project seed)) (project seed p),b⟩ := by
  unfold groups
  simp only [List.mem_filterMap,Finset.mem_sort,Multiset.mem_toFinset,Multiset.mem_map,
    Option.map_eq_some_iff]
  constructor
  · rintro ⟨k,⟨p,hp,rfl⟩,b,hb,rfl⟩
    exact ⟨p,hp,b,hb,rfl⟩
  · rintro ⟨p,hp,b,hb,rfl⟩
    exact ⟨_,⟨p,hp,rfl⟩,b,hb,rfl⟩

def word (seed : RS) (row : Multiset SignedPath) := (groups seed row).flatMap Group.word

private theorem class_word (m : Multiset Path) (seed : RS) (p : SignedPath) :
    ((bitOf (project seed p)).map fun b => Group.mk (census m (project seed p)) b).toList.flatMap Group.word =
      ((bitOf (project seed p)).toList.flatMap (List.replicate (m.count (project seed p)))) := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p e _ =>
    let b := e.hand.map (· == seed)
    rw [show project seed (p ++ [e]) = project seed p ++ [stepKey e.earlier b] by simp [project,b]]
    simp only [RingFullPathPairs.bitOf_snoc,census_snoc]
    change ((b.map _).toList.flatMap _) = (b.toList.flatMap _)
    cases b with
    | none => rfl
    | some t => cases t <;> rfl

private theorem expanded_count (m : Multiset Path) (ks : List Path)
    (nd : ks.Nodup) (x : Path) :
    (ks.flatMap fun k => List.replicate (m.count k) k).count x = if x ∈ ks then m.count x else 0 := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    obtain ⟨off,nd'⟩ := List.nodup_cons.mp nd
    by_cases eqn : k = x
    · subst k
      simp [ih nd',off]
    · simp [List.count_replicate,ih nd',eqn,Ne.symm eqn]

private theorem expanded_sorted (m : Multiset Path) (ks : List Path)
    (sorted : ks.Pairwise (· ≥ ·)) :
    (ks.flatMap fun k => List.replicate (m.count k) k).Pairwise (· ≥ ·) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun _ _ => by simp,sorted.imp ?_⟩
  intro a b ab x hx y hy
  obtain ⟨_,rfl⟩ := List.mem_replicate.mp hx
  obtain ⟨_,rfl⟩ := List.mem_replicate.mp hy
  exact ab

theorem word_exact (seed : RS) (row : Multiset SignedPath) :
    word seed row = RingStereoSphereInventory.sphere seed row := by
  induction row using Quotient.inductionOn with
  | _ xs =>
    let m : Multiset Path := ↑(xs.map (project seed))
    let ks := m.toFinset.sort (· ≥ ·)
    let expanded := ks.flatMap fun k => List.replicate (m.count k) k
    have perm : expanded.Perm (xs.map (project seed)) := by
      apply List.perm_iff_count.mpr
      intro x
      rw [show expanded.count x = _ from expanded_count m ks (Finset.sort_nodup ..) x]
      simp only [ks,Finset.mem_sort,Multiset.mem_toFinset]
      by_cases mem : x ∈ m
      · rw [if_pos mem]
        simp only [m,Multiset.coe_count,List.count_eq_countP]
        congr 2
        funext k
        apply Bool.eq_iff_iff.mpr
        simp
      · rw [if_neg mem]
        symm
        apply List.count_eq_zero.mpr
        exact mem
    have sorted := expanded_sorted m ks (Finset.pairwise_sort ..)
    have native := RingUnorderedSphereReading.readRow_perm id bitOf perm
    rw [readRow_sorted id bitOf expanded (by simpa [expanded] using sorted)] at native
    change _ = RingUnorderedSphereReading.readRow (project seed) bitOf xs
    rw [show RingUnorderedSphereReading.readRow (project seed) bitOf xs =
      RingUnorderedSphereReading.readRow id bitOf (xs.map (project seed)) from
      RingUnorderedSphereReading.readRow_map (project seed) id bitOf xs,←native]
    change ((ks.filterMap fun p => (bitOf p).map fun b => Group.mk (census m p) b).flatMap Group.word) =
      expanded.filterMap bitOf
    have one (p : Path) (hp : p ∈ ks) :
        ((bitOf p).map fun b => Group.mk (census m p) b).toList.flatMap Group.word =
        (List.replicate (m.count p) p).filterMap bitOf := by
      have mem : p ∈ xs.map (project seed) := by simpa [ks,m] using hp
      obtain ⟨q,_,rfl⟩ := List.mem_map.mp mem
      rw [class_word]
      generalize m.count (project seed q) = n
      induction n with
      | zero => cases bitOf (project seed q) <;> rfl
      | succ n ih => cases h : bitOf (project seed q) <;> simp_all [List.replicate_succ]
    change _ = (ks.flatMap _).filterMap bitOf
    rw [List.filterMap_flatMap]
    clear perm native sorted
    generalize hk : ks = ranks at one ⊢
    clear hk
    induction ranks with
    | nil => rfl
    | cons k ranks ih =>
      have first := one k (by simp)
      have tail := ih (fun x hx => one x (by simp [hx]))
      cases hit : bitOf k <;> simp_all

def reading (seed : RS) (inv : Inventory) := inv.flatMap (word seed)

theorem molecular_reading (i : Input) (r : Reader i) (rev : Bool)
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) (q : Arm i) :
    (RingStereoSphereInventory.inventory? i r rev os q).map (reading seed) =
      RingFullPathPairs.stageWords i r rev os seed q := by
  have same : reading seed = RingStereoSphereInventory.reading seed := by
    funext inv
    simp only [reading,RingStereoSphereInventory.reading,funext (word_exact seed)]
  rw [same]
  exact RingStereoSphereInventory.reading_exact i r rev os seed q

/-- Ordered donor classes at each molecular depth, including empty spheres. -/
def groups? (i : Input) (r : Reader i) (rev : Bool)
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) (q : Arm i) :=
  (RingStereoSphereInventory.inventory? i r rev os q).map (List.map (groups seed))

theorem groups_exact (i : Input) (r : Reader i) (rev : Bool)
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) (q : Arm i) :
    (groups? i r rev os seed q).map (List.flatMap (List.flatMap Group.word)) =
      RingFullPathPairs.stageWords i r rev os seed q := by
  rw [←molecular_reading]
  simp only [groups?,Option.map_map]
  congr 1
  funext inv
  simp only [Function.comp_apply,reading,List.flatMap_map]
  rfl

end TetraStereo.Engine.RingMolecularDonorClasses
assert_kernel_only TetraStereo.Engine.RingMolecularDonorClasses.census_snoc
assert_kernel_only TetraStereo.Engine.RingMolecularDonorClasses.word_exact
assert_kernel_only TetraStereo.Engine.RingMolecularDonorClasses.molecular_reading
assert_kernel_only TetraStereo.Engine.RingMolecularDonorClasses.mem_groups
assert_kernel_only TetraStereo.Engine.RingMolecularDonorClasses.groups_exact
