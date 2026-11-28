import TetraStereo.Engine.RingAlkoxyaziridineOrder
import TetraStereo.Engine.RingDiaziridineStore

/-! The nitrogen's two carbon ligands can exchange priority when a ring
closure truncates one of them. Compute the order at each actual occurrence. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingAlkoxyaziridineStore
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (height distance)
open RingAlkoxyaziridineOrder (SiteRoles descending labels)
open RingAtomicNeighborOrder (atomicNumber neighbors)
open RingSecondShellDecision (shell signature)
open RingPyramidalPathRank (atSite realEndpoint)
open private atomic_of_good sorted_desc from TetraStereo.Engine.RingOxaziridineRootOrder
open private carbon_compare from TetraStereo.Engine.RingChloroaziridineOrder
open private counted capped from TetraStereo.Engine.RingAlkoxyaziridineOrder
attribute [local instance] lexOrd

private theorem decision {i : Input} {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingAlkoxyaziridineNitrogen.constrained i a = true) {o g m : Nat}
    (roles : SiteRoles i.molecule a.val o g m) :
    RingPyramidalPathDecision.direct? i q = some (RingPyramidalPathDecision.reading i q a) := by
  have sel : RingPyramidalPublication.focusP i q = some a := by
    simp [RingPyramidalPublication.focusP,real,current,RingAlkoxyaziridineOrder.selected a motif]
  obtain ⟨d⟩ := RingPyramidalSource.selected_framed sel
  exact RingPyramidalPathDecision.direct_of_strict sel d
    (RingDiaziridineStore.separated_of_graph real current sel d
      ((roles.row.map _).nodup_iff.mpr ((descending roles).imp (fun h => ne_of_gt h))))

/-- The rank of an absent continuation compares the original depths of its
duplicated atoms. For unequal carbon types here the live continuation always
wins over the truncated one, and two live continuations favor gem-dimethyl. -/
def gemFirst {i : Input} (q : Site i) (g m : Nat) : Bool :=
  let live := realEndpoint (q.val.node.history.map Fin.val) (q.val.node.parent?.map Fin.val)
  let depthScore (w : Nat) := i.molecule.atomCount + 1 - (q.val.node.history.map Fin.val).reverse.idxOf w
  if live g then true else if live m then false else decide (depthScore m < depthScore g)

private theorem before {i : Input} (q : Site i) (a : i.certified.Atom) {o g m : Nat}
    (roles : SiteRoles i.molecule a.val o g m) :
    (gemFirst q g m = true ↔ atSite i q a m < atSite i q a g) := by
  obtain ⟨x,y,gs⟩ := roles.gemShell
  obtain ⟨z,ms⟩ := roles.monoShell
  have gg := atomic_of_good _ _ _ roles.gemCarbon
  have mm := atomic_of_good _ _ _ roles.monoCarbon
  have gn : shell i.molecule a.val g ≠ [] := by
    intro e
    simpa [e] using counted gs
  have mn : shell i.molecule a.val m ≠ [] := by
    intro e
    simpa [e] using counted ms
  have order : shell i.molecule a.val m < shell i.molecule a.val g :=
    carbon_compare _ _ (sorted_desc _) (capped ms) (by rw [counted gs,counted ms]; exact Nat.lt_succ_self 2)
  have nonempty {xs : List Nat} (h : xs ≠ []) : ([] : List Nat) < xs := by
    cases xs with
    | nil => contradiction
    | cons => exact List.Lex.nil
  let live := realEndpoint (q.val.node.history.map Fin.val) (q.val.node.parent?.map Fin.val)
  cases hg : live g <;> cases hm : live m
  all_goals change realEndpoint _ _ _ = _ at hg hm
  all_goals simp [gemFirst,atSite,RingPyramidalPathRank.rank,hg,hm,gg,mm,gn,mn]
  · simp [List.cons_lt_cons_iff]
  · exact le_of_lt (List.Lex.rel (List.Lex.cons (List.Lex.rel (nonempty mn))))
  · exact List.Lex.rel (List.Lex.cons (List.Lex.rel (nonempty gn)))
  · exact List.Lex.rel (List.Lex.cons (List.Lex.rel order))

def hands (i : Input) (q : Site i) (a : i.certified.Atom) (o g m : Nat) :=
  if gemFirst q g m then labels i.spatial a.val o g m else labels i.spatial a.val o m g

private theorem read_eq {i : Input} {q : Site i} {a : i.certified.Atom} {o g m : Nat}
    (roles : SiteRoles i.molecule a.val o g m)
    (hit : RingPyramidalPathDecision.direct? i q = some (RingPyramidalPathDecision.reading i q a))
    (sel : RingPyramidalPublication.focusP i q = some a) :
    RingPyramidalPathDecision.reading i q a = hands i q a o g m := by
  let f := atSite i q a
  have nd : ((neighbors i.molecule a.val).map f).Nodup := by
    by_contra h
    change ¬ ((neighbors i.molecule a.val).map (atSite i q a)).Nodup at h
    simp [RingPyramidalPathDecision.direct?,sel,guard,h] at hit
  have distinct := (roles.row.map f).nodup_iff.mp nd
  have ne : f g ≠ f m := by simpa using (List.nodup_cons.mp (List.nodup_cons.mp distinct).2).1
  have high (v : Nat) (zv : atomicNumber i.molecule v = 6) : f v < f o :=
    List.Lex.rel (List.Lex.rel (List.Lex.rel (by rw [zv,atomic_of_good _ _ _ roles.oxygen]; decide)))
  have og := high g (atomic_of_good _ _ _ roles.gemCarbon)
  have om := high m (atomic_of_good _ _ _ roles.monoCarbon)
  obtain ⟨p,sorted⟩ := RingStereoSiblingPass.legal_order f (neighbors i.molecule a.val)
  have desc := (sorted.and ((p.map f).nodup_iff.mpr nd)).imp (fun h => lt_of_le_of_ne h.1 h.2.symm)
  have ordered (xs : List Nat) (perm : (neighbors i.molecule a.val).Perm xs)
      (strict : (xs.map f).Pairwise (· > ·)) : RingPyramidalPathDecision.row i q a = xs :=
    List.Perm.eq_of_pairwise (le := fun x y => f y < f x) (fun _ _ _ _ u v => (lt_asymm u v).elim)
      (List.pairwise_map.mp desc) (List.pairwise_map.mp strict) (p.trans perm)
  unfold hands
  split
  next yes =>
    have win := (before q a roles).mp yes
    rw [RingPyramidalPathDecision.reading,ordered _ roles.row (by simpa [f] using And.intro (And.intro og om) win),
      RingWrittenPHReadings.inputGeometry_eq]
    rfl
  next no =>
    have win : f g < f m := lt_of_le_of_ne (le_of_not_gt (fun h => no ((before q a roles).mpr h))) ne
    rw [RingPyramidalPathDecision.reading,ordered _ (roles.row.trans ((List.Perm.swap ..).cons o))
      (by simp [og,om,win]),RingWrittenPHReadings.inputGeometry_eq]
    rfl

/-- No earlier stereo reading enters the outcome at this site. -/
theorem at_reader {i : Input} {q : Site i} {a : i.certified.Atom} {view : RingNestedActivePair.Reader i}
    (ready : RingGroupedStereo.Ready q view) (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a) (motif : RingAlkoxyaziridineNitrogen.constrained i a = true)
    {o g m : Nat} (roles : SiteRoles i.molecule a.val o g m) :
    RingPyramidalPublication.publish i q view = some (hands i q a o g m) := by
  have hit := decision real current motif roles
  rw [RingPyramidalPathDecision.local_exact ready hit,read_eq roles hit]
  simp [RingPyramidalPublication.focusP,real,current,RingAlkoxyaziridineOrder.selected a motif]

theorem state {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {a : i.certified.Atom} (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a) (motif : RingAlkoxyaziridineNitrogen.constrained i a = true)
    {o g m : Nat} (roles : SiteRoles i.molecule a.val o g m) :
    RingChemicalGraphProof.state i q = some (hands i q a o g m) := by
  rw [RingChemicalGraphProof.state_eq]
  exact at_reader (RingChemicalGraphProof.ready geom q) real current motif roles

/-- Exact membership and descriptor of this nitrogen after each completed sphere. -/
theorem row_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1)
    {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingAlkoxyaziridineNitrogen.constrained i a = true)
    {o g m : Nat} (roles : SiteRoles i.molecule a.val o g m) (v : Option RingNestedActivePair.Labels) :
    (q,some v) ∈ RingSphereStore.rows i root k ↔
      q.val.root = root ∧ a ≠ root ∧ height i < distance q + k ∧ v = hands i q a o g m := by
  rw [RingSphereStore.row_iff_derives geom root k bound q v]
  constructor
  · rintro ⟨h,b,p,rep,other,_,committed,derived⟩
    obtain rfl := Option.some.inj (current.symm.trans rep.2.2.2)
    have len := RingGraphPaths.path_length rep
    have issued := (RingChemicalGraphProof.path_iff geom p v).mpr derived
    rw [RingGraphPaths.unique_site (RingGraphPaths.represents_site p) rep] at issued
    exact ⟨rep.1,other,by omega,Option.some.inj (issued.symm.trans (state geom real current motif roles))⟩
  · rintro ⟨on,other,committed,rfl⟩
    obtain ⟨b,hb,path⟩ := RingGraphPaths.site_path q real
    obtain rfl := Option.some.inj (hb.symm.trans current)
    let p : RingGraphPaths.Path i root q.val.node.history b := on ▸ path
    have rep : RingGraphPaths.Represents q root q.val.node.history b := ⟨on,rfl,real,hb⟩
    have len := RingGraphPaths.path_length rep
    refine ⟨_,b,p,rep,other,?_,by omega,?_⟩
    · simp [RingPyramidalPublication.eligible,RingAlkoxyaziridineOrder.selected b motif]
    · apply (RingChemicalGraphProof.path_iff geom p _).mp
      rw [RingGraphPaths.unique_site (RingGraphPaths.represents_site p) rep]
      exact state geom real hb motif roles

open private raw_adj from TetraStereo.Engine.RingAtomicNeighborOrder
open private mem_adj from TetraStereo.Engine.RingChloroaziridineOrder

/-- From the gem-dimethyl ring carbon, both paths to the very same nitrogen
occur. The two-edge route publishes the reversed carbon order one sphere
before the direct route publishes the root order. Both rows persist. -/
theorem two_paths {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a g m : i.certified.Atom) (o : Nat) (motif : RingAlkoxyaziridineNitrogen.constrained i a = true)
    (roles : SiteRoles i.molecule a.val o g.val m.val) :
    ∃ direct around : Site i, RingGraphPaths.Represents direct g [a,g] a ∧
      RingGraphPaths.Represents around g [a,m,g] a ∧ ∀ k ≤ height i + 1, ∀ v,
      ((direct,some v) ∈ RingSphereStore.rows i g k ↔
        height i < 1+k ∧ v = labels i.spatial a.val o g.val m.val) ∧
      ((around,some v) ∈ RingSphereStore.rows i g k ↔
        height i < 2+k ∧ v = labels i.spatial a.val o m.val g.val) := by
  have adj (w : i.certified.Atom) (member : w.val ∈ [o,g.val,m.val]) : i.certified.moleculeGraph.Adj a w :=
    (raw_adj i a w).mpr (RingAtomicNeighborOrder.mem_neighbors.mp (roles.row.mem_iff.mpr member)).2
  have ag := adj g (by simp)
  have am := adj m (by simp)
  obtain ⟨x,y,shellG⟩ := roles.gemShell
  have outward := (shellG.present m.val (by simp)).1
  simp only [RingSecondShellDecision.adjacent,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq] at outward
  have gm : i.certified.moleculeGraph.Adj g m := (raw_adj i g m).mpr outward.2.2
  have distinct {u v : i.certified.Atom} (edge : i.certified.moleculeGraph.Adj u v) : u ≠ v := by
    rintro rfl
    exact i.certified.moleculeGraph.underlyingSimpleGraph.loopless.irrefl _ edge
  let short : RingGraphPaths.Path i g [a,g] a :=
    .step .origin (i.certified.moleculeGraph.adj_symm.mp ag) (by simpa using distinct ag)
  let long : RingGraphPaths.Path i g [a,m,g] a :=
    .step (.step .origin gm (by simpa using (distinct gm).symm))
      (i.certified.moleculeGraph.adj_symm.mp am) (by simp [distinct am,distinct ag])
  have ds := RingGraphPaths.represents_site short
  have dl := RingGraphPaths.represents_site long
  have one : distance (RingGraphPaths.site short) = 1 := by simpa using (RingGraphPaths.path_length ds).symm
  have two : distance (RingGraphPaths.site long) = 2 := by simpa using (RingGraphPaths.path_length dl).symm
  have ne : m.val ≠ g.val := fun e => distinct gm (Fin.ext e.symm)
  refine ⟨_,_,ds,dl,?_⟩
  intro k bound v
  rw [row_iff geom g k bound ds.2.2.1 ds.2.2.2 motif roles,
    row_iff geom g k bound dl.2.2.1 dl.2.2.2 motif roles,one,two]
  simp [ds.1,dl.1,distinct ag,hands,gemFirst,realEndpoint,OfficialCIPNode.parent?,ds.2.1,dl.2.1,ne]

end TetraStereo.Engine.RingAlkoxyaziridineStore
assert_kernel_only TetraStereo.Engine.RingAlkoxyaziridineStore.at_reader
assert_kernel_only TetraStereo.Engine.RingAlkoxyaziridineStore.row_iff
assert_kernel_only TetraStereo.Engine.RingAlkoxyaziridineStore.two_paths
