import TetraStereo.Engine.RingGroupedStereo

/-! # Pooling equivalent reference occurrences across parent groups -/

set_option autoImplicit false

namespace TetraStereo.Engine.RingReferenceVotes
open OneCenter CertifiedLocalizedCIPInput
open RingRetainedReferenceGroup (Hit Path)

def net (xs : List RS) : Int := (xs.count .R : Int) - xs.count .S

def sign (n : Int) : Int := if 0 < n then 1 else if n < 0 then -1 else 0

/-- When the population is empty there is no reference. A positive population
with net zero supplies both references. -/
def select (occupied : Bool) (n : Int) : List RS :=
  if !occupied then [] else if 0 < n then [.R] else if n < 0 then [.S] else [.R,.S]

theorem select_exact (xs : List RS) :
    select (!xs.isEmpty) (net xs) = localizedRule4bReferencesFromPopulation xs := by
  simp only [localizedRule4bReferencesFromPopulation,select,net,Bool.not_not,
    ← List.count_eq_length_filter]
  split_ifs <;> first | rfl | omega

theorem two_parents (a b : Int) :
    sign (sign a + sign b) ≠ sign (a+b) ↔
      ((0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b)) ∧ a+b ≠ 0 := by
  unfold sign
  split_ifs <;> omega

theorem net_flatten (parents : List (List RS)) :
    net parents.flatten = (parents.map net).sum := by
  induction parents with
  | nil => rfl
  | cons h t ih =>
    simp only [List.flatten_cons,List.map_cons,List.sum_cons,← ih,net,List.count_append,Nat.cast_add]
    omega

theorem pooled (parents : List (List RS)) :
    select (!parents.flatten.isEmpty) (parents.map net).sum =
      localizedRule4bReferencesFromPopulation parents.flatten := by rw [← net_flatten,select_exact]

/-- Identify the closest occupied sphere and its highest eligible path before counting hands. -/
def best? (xs : List Hit) : Option Path := do
  let d ← (xs.map fun h => h.path.length).min?
  ((xs.filter fun h => h.path.length == d).map Hit.path).max?

theorem best_iff {xs : List Hit} {h : Hit} (mem : h ∈ xs) :
    best? xs = some h.path ↔ h ∈ RingRetainedReferenceGroup.group xs := by
  rw [RingRetainedReferenceGroup.mem_group]
  unfold best?
  constructor
  · intro got
    obtain ⟨d,near,top⟩ := Option.bind_eq_some_iff.mp got
    obtain ⟨_,least⟩ := List.min?_eq_some_iff.mp near
    obtain ⟨hit,high⟩ := List.max?_eq_some_iff.mp top
    obtain ⟨w,hw,eqn⟩ := List.mem_map.mp hit
    have depth : h.path.length = d := eqn ▸ beq_iff_eq.mp (List.mem_filter.mp hw).2
    refine ⟨mem,fun t ht => ⟨depth ▸ least _ (List.mem_map_of_mem ht),?_⟩⟩
    intro same
    exact high _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨ht,beq_iff_eq.mpr (same.trans depth)⟩))
  · rintro ⟨_,all⟩
    apply Option.bind_eq_some_iff.mpr
    refine ⟨h.path.length,List.min?_eq_some_iff.mpr ⟨List.mem_map_of_mem mem,?_⟩,
      List.max?_eq_some_iff.mpr ⟨List.mem_map_of_mem (List.mem_filter.mpr ⟨mem,by simp⟩),?_⟩⟩
    · intro v hv
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hv
      exact (all t ht).1
    · intro v hv
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hv
      obtain ⟨m,e⟩ := List.mem_filter.mp ht
      exact (all t m).2 (beq_iff_eq.mp e)

def atBest (key : Option Path) (xs : List Hit) (rev : Bool) : List RS :=
  (xs.filter fun h => key == some h.path).map fun h => if rev then h.hand.swap else h.hand

theorem atBest_exact (xs : List Hit) (rev : Bool) :
    atBest (best? xs) xs rev = RingRetainedReferenceGroup.hands xs rev := by
  unfold atBest RingRetainedReferenceGroup.hands RingRetainedReferenceGroup.group
  congr 1
  apply List.filter_congr
  intro h mem
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq,best_iff mem]
  simp only [RingRetainedReferenceGroup.group,List.mem_filter,mem,true_and]

/-- Group boundaries may be arbitrary, including empty groups. All surviving votes keep their
multiplicities when groups are combined. The minimum depth and rank are global to this ligand. -/
def fromGroups (parents : List (List Hit)) (rev : Bool) : List RS :=
  let key := best? parents.flatten
  let blocks := parents.map fun p => atBest key p rev
  select (!blocks.flatten.isEmpty) (blocks.map net).sum

theorem fromGroups_exact (parents : List (List Hit)) (rev : Bool) :
    fromGroups parents rev = RingRetainedReferenceGroup.references parents.flatten rev := by
  unfold fromGroups
  rw [pooled]
  unfold RingRetainedReferenceGroup.references
  rw [← atBest_exact]
  apply congrArg localizedRule4bReferencesFromPopulation
  generalize best? parents.flatten = key
  induction parents with
  | nil => rfl
  | cons p ps ih => simpa only [List.map_cons,List.flatten_cons,atBest,List.filter_append,List.map_append] using (congrArg (fun t => atBest key p rev ++ t) ih)

open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Labels)
open RingStereoSiblingPass (Branch)
open RingRetainedReferenceGroup (Listing)

/-- Keep the local site and each child's hits as separate blocks. -/
def blocks (v : Option Labels) (parts : List (Branch × List Hit)) : List (List Hit) :=
  ((RingNestedActivePair.upper (v.map Prod.fst)).map (Hit.mk [])).toList ::
    parts.map fun (k,hs) => hs.map fun h => {h with path := k.deep :: h.path}

private theorem blocks_flatten (v : Option Labels) (parts : List (Branch × List Hit)) :
    (blocks v parts).flatten = RingRetainedReferenceGroup.joinHits v parts := by
  simp only [blocks,List.flatten_cons]
  rfl

private def part? (i : Input) (r : Reader i) (c : Arm i) :=
  (RingGroupedStereo.arm? i r c).map fun p => (p.unit,p.hits)

def molecular? (i : Input) (r : Reader i) (q : Arm i) (rev : Bool) : Option (List RS) := do
  let v ← r q.occurrence
  let parts ← (i.certified.executableLocalizedRerootChildren q).mapM (part? i r)
  return fromGroups (blocks v parts) rev

theorem molecular_exact {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) (rev : Bool) :
    ∃ p, RingGroupedStereo.arm? i r q = some p ∧
      molecular? i r q rev = some (RingRetainedReferenceGroup.references p.hits rev) := by
  obtain ⟨p,hp⟩ := RingGroupedStereo.arm_ready ready q valid on
  obtain ⟨v,hv,ok,leaf⟩ := ready q on
  have frame := i.certified.executableLocalizedRerootChildren_declarative q
  obtain ⟨parts,all⟩ := RingRetainedUnitPass.collect (part? i r) (i.certified.executableLocalizedRerootChildren q)
    (fun c hc => by
      obtain ⟨x,hx⟩ := RingGroupedStereo.arm_ready ready c
        (i.certified.localizedRerootChild_valid q c _ frame hc)
        ((i.certified.localizedRerootChildren_root_eq q c _ frame hc).trans on)
      exact ⟨(x.unit,x.hits),by simp [part?,hx]⟩)
  have reads (c : Arm i) (k : Branch) (hs : List Hit) (h : part? i r c = some (k,hs)) :
      RingRetainedUnitPass.Reading i r false c k ∧ Listing i r c hs := by
    unfold part? at h
    obtain ⟨x,hx,e⟩ := Option.map_eq_some_iff.mp h
    cases e
    exact ⟨(RingGroupedStereo.arm_source hx).unit,(RingGroupedStereo.arm_source hx).hits⟩
  have listing : Listing i r q (RingRetainedReferenceGroup.joinHits v parts) :=
    .node hv ⟨ok,leaf⟩ _ all (fun c _ _ _ h => (reads c _ _ h).1) (fun c _ _ _ h => (reads c _ _ h).2)
  refine ⟨p,hp,?_⟩
  simp only [molecular?,hv,all,Option.bind_eq_bind,Option.bind_some,Option.pure_def,
    fromGroups_exact,blocks_flatten,listing.unique (RingGroupedStereo.arm_source hp).hits]

end TetraStereo.Engine.RingReferenceVotes
assert_kernel_only TetraStereo.Engine.RingReferenceVotes.two_parents
assert_kernel_only TetraStereo.Engine.RingReferenceVotes.pooled

assert_kernel_only TetraStereo.Engine.RingReferenceVotes.molecular_exact
