import TetraStereo.Engine.RingDiaziridineOrder
import TetraStereo.Engine.RingOxaziridineAuxiliaryReport

/-! Every real occurrence of a recognized dialkyldiaziridine nitrogen has a
graph- and path-determined reading in the public auxiliary store. A closure
truncates its ligand's second shell. Shortest paths recover the root order. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingDiaziridineStore
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (height distance)
open RingPyramidalSource (Directions slots atomId)
open RingPyramidalTwoShell (direction score)
open RingTerminalLigandOrder (rank twoRows bonus)
open RingPyramidalPathDecision (reading)
open RingOxaziridineAuxOrder (score_projected projected)
open RingOxaziridineAuxiliaryReport (Nearest nearest_pyramid)
open RingDiaziridineOrder (roles_of_recognized descending)
open private nodup_injective from TetraStereo.Engine.RingPyramidalSource
attribute [local instance] lexOrd

private theorem focus {i : Input} {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingDialkyldiaziridine.constrained i a = true) :
    RingPyramidalPublication.focusP i q = some a := by
  simp [RingPyramidalPublication.focusP,real,current,RingDiaziridineSelection.selected a motif]

/-- Distinct physical two-shell signatures remain distinguishable on every
rerooted path. If truncation collapses two signatures, the duplicate-origin
comparison distinguishes the two now-empty second rows. -/
theorem separated_of_graph {i : Input} {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (selected : RingPyramidalPublication.focusP i q = some a) (d : Directions i q)
    (raw : ((RingAtomicNeighborOrder.neighbors i.molecule a.val).map
      (RingSecondShellDecision.signature i.molecule a.val)).Nodup) :
    Function.Injective (RingTerminalPyramid.weight d) := by
  let f := RingSecondShellDecision.signature i.molecule a.val
  have p := (RingPyramidalPathRank.neighbors_perm d selected).map f
  have unique := p.nodup_iff.mpr raw
  rw [List.map_map] at unique
  have inj := (nodup_injective _).mp unique
  intro s t equal
  by_contra different
  change rank (direction d s) = rank (direction d t) at equal
  obtain ⟨prefixEq,tail⟩ := List.cons.inj equal
  have b : bonus (direction d s) = bonus (direction d t) := by simpa using tail
  have z : score d s = score d t := prefixEq
  have projectedEq := z
  rw [score_projected current d s,score_projected current d t] at projectedEq
  have nonreal : (d.arm s).occurrence.val.node.provenance ≠ .realAtom ∨
      (d.arm t).occurrence.val.node.provenance ≠ .realAtom := by
    by_contra! both
    apply different
    apply inj
    simpa [Function.comp_def,f,RingSecondShellDecision.signature,projected,both.1,both.2] using projectedEq
  have distinct : d.atom s ≠ d.atom t := by
    intro eq
    apply different
    apply inj
    simp only [Function.comp_def,atomId,eq]
  have es : (twoRows (direction d s))[1]? = some [] := by
    change (score d s)[1]? = some []
    rcases nonreal with off | off
    · simp [score_projected current d s,projected,off]
    · rw [z]
      simp [score_projected current d t,projected,off]
  have et : (twoRows (direction d t))[1]? = some [] := prefixEq ▸ es
  apply RingTerminalLigandOrder.duplicate_ne real current d s t distinct nonreal
  simp only [bonus,es,et,if_true] at b
  exact b

theorem separated {i : Input} {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingDialkyldiaziridine.constrained i a = true) (d : Directions i q) :
    Function.Injective (RingTerminalPyramid.weight d) := by
  obtain ⟨o,c,k,r⟩ := roles_of_recognized motif
  exact separated_of_graph real current (focus real current motif) d
    ((r.row.map _).nodup_iff.mpr ((descending r).imp (fun h => ne_of_gt h)))

/-- The graph/path calculation always issues a decision for this real nitrogen.
Its generated hand may be absent on a degenerate pyramid. -/
theorem decision {i : Input} {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingDialkyldiaziridine.constrained i a = true) :
    RingPyramidalPathDecision.direct? i q = some (reading i q a) := by
  have selected := focus real current motif
  obtain ⟨d⟩ := RingPyramidalSource.selected_framed selected
  exact RingPyramidalPathDecision.direct_of_strict selected d (separated real current motif d)

/-- Every ready local reader issues exactly the same graph/path reading. -/
theorem local_reading {i : Input} {q : Site i} {a : i.certified.Atom}
    {r : RingNestedActivePair.Reader i} (ready : RingGroupedStereo.Ready q r)
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingDialkyldiaziridine.constrained i a = true) :
    RingPyramidalPublication.publish i q r = some (reading i q a) :=
  RingPyramidalPathDecision.local_exact ready (decision real current motif)

theorem state {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingDialkyldiaziridine.constrained i a = true) :
    RingChemicalGraphProof.state i q = some (reading i q a) :=
  RingPyramidalPathDecision.sound geom (decision real current motif)

/-- Precisely which public auxiliary row exists at this address after any
number of complete spheres, and precisely which value the row contains. -/
theorem row_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1)
    {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingDialkyldiaziridine.constrained i a = true) (v : Option RingNestedActivePair.Labels) :
    (q,some v) ∈ RingSphereStore.rows i root k ↔
      q.val.root = root ∧ a ≠ root ∧ height i < distance q + k ∧ v = reading i q a := by
  rw [RingSphereStore.row_iff_derives geom root k bound q v]
  constructor
  · rintro ⟨h,b,p,rep,other,_,committed,derived⟩
    obtain rfl := Option.some.inj (current.symm.trans rep.2.2.2)
    have len := RingGraphPaths.path_length rep
    have issued := (RingChemicalGraphProof.path_iff geom p v).mpr derived
    rw [RingGraphPaths.unique_site (RingGraphPaths.represents_site p) rep] at issued
    exact ⟨rep.1,other,by omega,Option.some.inj (issued.symm.trans (state geom real current motif))⟩
  · rintro ⟨on,other,committed,rfl⟩
    obtain ⟨b,hb,path⟩ := RingGraphPaths.site_path q real
    obtain rfl := Option.some.inj (hb.symm.trans current)
    let p : RingGraphPaths.Path i root q.val.node.history b := on ▸ path
    have rep : RingGraphPaths.Represents q root q.val.node.history b := ⟨on,rfl,real,hb⟩
    have len := RingGraphPaths.path_length rep
    refine ⟨_,b,p,rep,other,?_,by omega,?_⟩
    · simp [RingPyramidalPublication.eligible,RingDiaziridineSelection.selected b motif]
    · apply (RingChemicalGraphProof.path_iff geom p _).mp
      rw [RingGraphPaths.unique_site (RingGraphPaths.represents_site p) rep]
      exact state geom real hb motif

/-- Recognition discharges the entire graph-order premise at every shortest
occurrence of a dialkyldiaziridine nitrogen. -/
theorem nearest_state {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {a : i.certified.Atom} (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a)
    (motif : RingDialkyldiaziridine.constrained i a = true) (nearest : Nearest q a) :
    RingChemicalGraphProof.state i q = RingChemicalGraphProof.root i a := by
  obtain ⟨o,c,k,r⟩ := roles_of_recognized motif
  exact nearest_pyramid geom real current (focus real current motif) nearest [o,c,k] r.row (descending r)

/-- The shortest occurrence publishes the atom's own root descriptor at its
scheduled sphere and retains it at every later cut. -/
theorem nearest_row_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1)
    {q : Site i} {a : i.certified.Atom} (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a) (motif : RingDialkyldiaziridine.constrained i a = true)
    (nearest : Nearest q a) (v : Option RingNestedActivePair.Labels) :
    (q,some v) ∈ RingSphereStore.rows i root k ↔ q.val.root = root ∧ a ≠ root ∧
      height i < distance q + k ∧ RingChemicalGraphProof.root i a = some v := by
  rw [row_iff geom root k bound real current motif, ← nearest_state geom real current motif nearest,
    state geom real current motif]
  simp only [Option.some.injEq, eq_comm (a := v)]

open RingPyramidalPathRank (atSite realEndpoint)
open RingDiaziridineOrder (SiteRoles labels)
open private atomic_of_good from TetraStereo.Engine.RingOxaziridineRootOrder

/-- If the ring carbon closes to an earlier atom but the alkyl carbon has a
continuing second shell, the alkyl carbon outranks the ring carbon. This is
the opposite carbon order from the root. The nitrogen still wins first. -/
theorem closed_ring_state {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingDialkyldiaziridine.constrained i a = true) {o c k : Nat}
    (r : SiteRoles i.molecule a.val o c k)
    (off : realEndpoint (q.val.node.history.map Fin.val) (q.val.node.parent?.map Fin.val) c = false)
    (on : realEndpoint (q.val.node.history.map Fin.val) (q.val.node.parent?.map Fin.val) k = true)
    (continues : RingSecondShellDecision.shell i.molecule a.val k ≠ []) :
    RingChemicalGraphProof.state i q = some (labels i.spatial a.val o k c) := by
  have zo : RingAtomicNeighborOrder.atomicNumber i.molecule o = 7 := atomic_of_good _ _ _ r.nitrogen
  have zc : RingAtomicNeighborOrder.atomicNumber i.molecule c = 6 := atomic_of_good _ _ _ r.ringCarbon
  have zk : RingAtomicNeighborOrder.atomicNumber i.molecule k = 6 := atomic_of_good _ _ _ r.alkylCarbon
  let f := atSite i q a
  have high (v : Nat) (zv : RingAtomicNeighborOrder.atomicNumber i.molecule v = 6) : f v < f o := by
    exact List.Lex.rel (List.Lex.rel (List.Lex.rel (by rw [zv,zo]; decide)))
  have kc : f c < f k := by
    unfold f atSite RingPyramidalPathRank.rank
    simp only [off,on,Bool.false_eq_true,ite_false,ite_true,zc,zk]
    apply List.Lex.rel
    apply List.Lex.cons
    apply List.Lex.rel
    cases h : RingSecondShellDecision.shell i.molecule a.val k with
    | nil => exact (continues h).elim
    | cons _ _ => exact List.Lex.nil
  have strict : ([o,k,c].map f).Pairwise (· > ·) := by simp [high _ zc,high _ zk,kc]
  have perm : (RingAtomicNeighborOrder.neighbors i.molecule a.val).Perm [o,k,c] :=
    r.row.trans ((List.Perm.swap ..).cons o)
  obtain ⟨p,sorted⟩ := RingStereoSiblingPass.legal_order f (RingAtomicNeighborOrder.neighbors i.molecule a.val)
  have nd := ((p.trans perm).map f).nodup_iff.mpr (strict.imp (fun h => ne_of_gt h))
  have desc := (sorted.and nd).imp (fun h => lt_of_le_of_ne h.1 h.2.symm)
  have eq : RingPyramidalPathDecision.row i q a = [o,k,c] :=
    List.Perm.eq_of_pairwise (le := fun x y => f y < f x) (fun _ _ _ _ x y => (lt_asymm x y).elim)
      (List.pairwise_map.mp desc) (List.pairwise_map.mp strict) (p.trans perm)
  rw [state geom real current motif,reading,eq,RingWrittenPHReadings.inputGeometry_eq]
  rfl

open private raw_adj neighbors_nodup from TetraStereo.Engine.RingAtomicNeighborOrder

/-- With the ring carbon as the original root, the two-edge path through the
partner nitrogen really exists. Its root-carbon closure reverses the carbon
order at the second nitrogen, and that exact reading is written at distance two. -/
theorem triangle_store {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a o c k : i.certified.Atom) (motif : RingDialkyldiaziridine.constrained i a = true)
    (r : SiteRoles i.molecule a.val o.val c.val k.val)
    (continues : RingSecondShellDecision.shell i.molecule a.val k.val ≠ []) :
    ∃ q : Site i, RingGraphPaths.Represents q c [a,o,c] a ∧
      ∀ j ≤ height i + 1, ∀ v, (q,some v) ∈ RingSphereStore.rows i c j ↔
        height i < 2 + j ∧ v = labels i.spatial a.val o.val k.val c.val := by
  have adj (v : i.certified.Atom) (mem : v.val ∈ [o.val,c.val,k.val]) :
      i.certified.moleculeGraph.Adj a v :=
    (raw_adj i a v).mpr (RingAtomicNeighborOrder.mem_neighbors.mp (r.row.mem_iff.mpr mem)).2
  have loop {u v : i.certified.Atom} (edge : i.certified.moleculeGraph.Adj u v) : u ≠ v := by
    rintro rfl
    exact i.certified.moleculeGraph.underlyingSimpleGraph.loopless.irrefl _ edge
  have co : i.certified.moleculeGraph.Adj c o := by
    apply (raw_adj i c o).mpr
    have m := r.closes
    simp only [RingSecondShellDecision.adjacent,List.mem_filter,List.mem_range,Bool.and_eq_true,
      bne_iff_ne,decide_eq_true_eq] at m
    exact m.2.2
  have ao := adj o (by simp)
  have ac := loop (adj c (by simp))
  have ak := loop (adj k (by simp))
  have distinct : [o.val,c.val,k.val].Nodup := r.row.nodup_iff.mp (neighbors_nodup _ _)
  simp only [List.nodup_cons,List.mem_cons,not_or,List.nodup_nil,
    List.not_mem_nil,not_false_eq_true,and_true] at distinct
  let p : RingGraphPaths.Path i c [a,o,c] a :=
    .step (.step .origin co (by simpa using (loop co).symm))
      (i.certified.moleculeGraph.adj_symm.mp ao) (by simp [loop ao,ac])
  let q := RingGraphPaths.site p
  have rep : RingGraphPaths.Represents q c [a,o,c] a := RingGraphPaths.represents_site p
  have dp : distance q = 2 := by have l := RingGraphPaths.path_length rep; simpa using l.symm
  have parent : q.val.node.parent? = some o := by simp [OfficialCIPNode.parent?,rep.2.1]
  have off : realEndpoint (q.val.node.history.map Fin.val) (q.val.node.parent?.map Fin.val) c.val = false := by
    simp [realEndpoint,parent,rep.2.1,distinct.1.1]
  have on : realEndpoint (q.val.node.history.map Fin.val) (q.val.node.parent?.map Fin.val) k.val = true := by
    simp [realEndpoint,parent,rep.2.1,Ne.symm distinct.1.2,Ne.symm distinct.2,
      Ne.symm (fun h => ak (Fin.ext h) : a.val ≠ k.val)]
  have assigned := closed_ring_state geom rep.2.2.1 rep.2.2.2 motif r off on continues
  have readEq := Option.some.inj ((state geom rep.2.2.1 rep.2.2.2 motif).symm.trans assigned)
  refine ⟨q,rep,?_⟩
  intro j bound v
  rw [row_iff geom c j bound rep.2.2.1 rep.2.2.2 motif v,dp,readEq]
  simp [rep.1,ac]

open private nonempty from TetraStereo.Engine.RingGraphPaths

private theorem nontrivial_length {i r h a} (p : RingGraphPaths.Path i r h a) (ne : a ≠ r) :
    2 ≤ h.length := by
  cases p with
  | origin => contradiction
  | step prev _ _ =>
    have positive := List.length_pos_iff.mpr (nonempty prev)
    simp only [List.length_cons]
    omega

/-- With the same C3 root as the two-edge path, the direct one-edge path
publishes the original carbon order at distance one. -/
theorem direct_store {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a o c k : i.certified.Atom) (motif : RingDialkyldiaziridine.constrained i a = true)
    (r : SiteRoles i.molecule a.val o.val c.val k.val) :
    ∃ q : Site i, RingGraphPaths.Represents q c [a,c] a ∧
      ∀ j ≤ height i + 1, ∀ v, (q,some v) ∈ RingSphereStore.rows i c j ↔
        height i < 1 + j ∧ v = labels i.spatial a.val o.val c.val k.val := by
  have ac : i.certified.moleculeGraph.Adj a c :=
    (raw_adj i a c).mpr (RingAtomicNeighborOrder.mem_neighbors.mp (r.row.mem_iff.mpr (by simp))).2
  have ne : a ≠ c := by rintro rfl; exact i.certified.moleculeGraph.underlyingSimpleGraph.loopless.irrefl _ ac
  let p : RingGraphPaths.Path i c [a,c] a :=
    .step .origin (i.certified.moleculeGraph.adj_symm.mp ac) (by simpa using ne)
  let q := RingGraphPaths.site p
  have rep : RingGraphPaths.Represents q c [a,c] a := RingGraphPaths.represents_site p
  have dp : distance q = 1 := by have l := RingGraphPaths.path_length rep; simpa using l.symm
  have nearest : Nearest q a := by
    intro t rt
    obtain ⟨b,hb,walk⟩ := RingGraphPaths.site_path t rt.2.2.1
    obtain rfl := Option.some.inj (hb.symm.trans rt.2.2.2)
    have size := nontrivial_length walk (by rwa [rt.1,rep.1])
    have length := RingGraphPaths.path_length rt
    omega
  have actual := RingDiaziridineOrder.root geom a (RingDiaziridineSelection.selected a motif) r
  rw [RingWrittenPHReadings.inputGeometry_eq] at actual
  refine ⟨q,rep,?_⟩
  intro j bound v
  rw [nearest_row_iff geom c j bound rep.2.2.1 rep.2.2.2 motif nearest v,dp,actual]
  simp [rep.1,ne,labels,eq_comm (a := v)]

end TetraStereo.Engine.RingDiaziridineStore
assert_kernel_only TetraStereo.Engine.RingDiaziridineStore.separated_of_graph
assert_kernel_only TetraStereo.Engine.RingDiaziridineStore.row_iff
assert_kernel_only TetraStereo.Engine.RingDiaziridineStore.nearest_row_iff
assert_kernel_only TetraStereo.Engine.RingDiaziridineStore.closed_ring_state
assert_kernel_only TetraStereo.Engine.RingDiaziridineStore.triangle_store
assert_kernel_only TetraStereo.Engine.RingDiaziridineStore.direct_store
