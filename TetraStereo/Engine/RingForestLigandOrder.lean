import TetraStereo.Engine.RingFeedbackRoot
import TetraStereo.Engine.RingSingleCycleComparison

/-! Graph forest and bridge-stem criteria for all-depth ligand comparison. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingForestLigandOrder
open OneCenter CertifiedLocalizedCIPInput SimpleGraph
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingSingleCycleComparison (CommonOrigin rebuilt)
open RingRetainedChemicalTrace (compareKeys)
open RingCycleEntry (FirstEntry)

/-- All cycles may share a root even when their number is unrestricted. -/
theorem common_of_feedback {i : Input} {r : i.certified.Atom}
    (feedback : RingFeedbackRoot.FeedbackRoot i.certified.moleculeGraph.underlyingSimpleGraph r) :
    CommonOrigin i r := by
  intro q p d e qr pr qd pd
  obtain ⟨a,ha⟩ := RingFeedbackRoot.carrier_origin feedback q.occurrence qr qd
  obtain ⟨b,hb⟩ := RingFeedbackRoot.carrier_origin feedback p.occurrence pr pd
  exact ⟨a.trans b.symm,ha.trans hb.symm⟩

theorem of_feedback {i : Input} (f : Site i)
    (feedback : RingFeedbackRoot.FeedbackRoot i.certified.moleculeGraph.underlyingSimpleGraph f.val.root)
    (x y : RingRetainedChemicalPreorder.Direction i f) :
    (do let u ← rebuilt i f ⟨x.val,some f⟩
        let v ← rebuilt i f ⟨y.val,some f⟩
        pure (compareKeys u v)) =
    RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) x y :=
  RingSingleCycleComparison.of_common_origin f (common_of_feedback feedback) x y

/-- Deleting the original root leaves a forest. -/
theorem of_vertex_forest {i : Input} (f : Site i)
    (forest : (i.certified.moleculeGraph.underlyingSimpleGraph.induce
      {a | a ≠ f.val.root}).IsAcyclic)
    (x y : RingRetainedChemicalPreorder.Direction i f) :
    (do let u ← rebuilt i f ⟨x.val,some f⟩
        let v ← rebuilt i f ⟨y.val,some f⟩
        pure (compareKeys u v)) =
    RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) x y :=
  of_feedback f (RingFeedbackRoot.of_induce_acyclic forest) x y

/-- Deleting a single edge leaves a forest; the chosen cycle is explicitly inhabited. -/
theorem of_edge_forest {i : Input} {u v c : i.certified.Atom}
    (forest : (i.certified.moleculeGraph.underlyingSimpleGraph.deleteEdges {s(u,v)}).IsAcyclic)
    (cycle : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c) (hc : cycle.IsCycle)
    (f : Site i) (x y : RingRetainedChemicalPreorder.Direction i f) :
    (do let a ← rebuilt i f ⟨x.val,some f⟩
        let b ← rebuilt i f ⟨y.val,some f⟩
        pure (compareKeys a b)) =
    RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) x y :=
  RingSingleCycleComparison.all_ligands cycle
    (RingCycleEntry.uniqueCycleSupport_of_deleteEdges_isAcyclic forest cycle hc) f x y

/-- Only the selected access path must consist of bridges. Other portions of
its destination set may contain arbitrarily many cycles. -/
private theorem stem_entry {V : Type*} {G : SimpleGraph V} (C : Set V)
    {r a b : V} (p : G.Walk r a) (q : G.Walk r b)
    (hp : p.IsPath) (hq : q.IsPath)
    (bridges : ∀ e ∈ p.edges, G.IsBridge e)
    (connected : ∀ {x y}, x ∈ C → y ∈ C → ∃ w : G.Walk x y, ∀ z ∈ w.support, z ∈ C)
    (ep : FirstEntry C p) (eqn : FirstEntry C q) : a = b ∧ HEq p q := by
  have end_mem : ∀ {x y} (w : G.Walk x y), FirstEntry C w → y ∈ C := by
    intro x y w
    induction w with
    | nil => exact id
    | cons h w ih => exact fun e => ih e.2
  induction p with
  | nil => cases q with
    | nil => exact ⟨rfl,HEq.rfl⟩
    | cons h q => exact False.elim (eqn.1 ep)
  | @cons r t a h p ih =>
    cases q with
    | nil => exact False.elim (ep.1 eqn)
    | @cons _ s b k q =>
      obtain ⟨c,hc⟩ := connected (end_mem _ eqn.2) (end_mem _ ep.2)
      have he := (isBridge_iff_adj_and_forall_walk_mem_edges.mp
        (bridges s(r,t) (by simp))).2 ((Walk.cons k q).append (c.append p.reverse))
      simp only [Walk.edges_append,Walk.edges_reverse,List.mem_append,List.mem_reverse,
        Walk.edges_cons,List.mem_cons] at he
      rw [Walk.cons_isPath_iff] at hp hq
      rcases he with (he | he) | he | he
      · rcases Sym2.eq_iff.mp he with ⟨_,e⟩ | ⟨_,e⟩
        · subst s
          obtain ⟨hab,hh⟩ := ih q hp.1 hq.1
            (fun e he => bridges e (by simp [he])) ep.2 eqn.2
          subst b
          cases hh
          exact ⟨rfl,HEq.rfl⟩
        · exact False.elim (h.ne e.symm)
      · exact False.elim (hq.2 (q.fst_mem_support_of_mem_edges he))
      · exact False.elim (ep.1 (hc _ (c.fst_mem_support_of_mem_edges he)))
      · exact False.elim (hp.2 (p.fst_mem_support_of_mem_edges he))

/-- A bridge stem ending at a feedback vertex, with no earlier cyclic vertex,
fixes every closure origin to the stem's full support. -/
theorem stem_origin {i : Input} {r w : i.certified.Atom}
    (p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r w) (hp : p.IsPath)
    (bridges : ∀ e ∈ p.edges, i.certified.moleculeGraph.underlyingSimpleGraph.IsBridge e)
    (feedback : RingFeedbackRoot.FeedbackRoot i.certified.moleculeGraph.underlyingSimpleGraph w)
    (before : ∀ x ∈ p.support, x ≠ w → ∀ {c}
      (cycle : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c), cycle.IsCycle → x ∉ cycle.support)
    {node addr} (leg : LegitimateOccurrence i.certified r node addr) {d : Nat}
    (dup : node.provenance = .ringDuplicate d) :
    RingSingleCycleOrigin.originPath node d = p.support ∧ d = p.length := by
  classical
  obtain ⟨a,q,cycle,hq,hc,meet,path,depth⟩ := RingSingleCycleOrigin.closure_access leg dup
  have ep : FirstEntry {x | x ∈ cycle.support} p :=
    RingCycleEntry.firstEntry_of_intersection _ p hp (feedback cycle hc) (by
      intro x hx hc'
      by_contra ne
      exact before x hx ne cycle hc hc')
  have eqn : FirstEntry {x | x ∈ cycle.support} q :=
    RingCycleEntry.firstEntry_of_intersection _ q hq cycle.start_mem_support meet
  have conn : ∀ {x y}, x ∈ cycle.support → y ∈ cycle.support →
      ∃ t : i.certified.moleculeGraph.underlyingSimpleGraph.Walk x y,
        ∀ z ∈ t.support, z ∈ cycle.support := by
    intro x y hx hy
    refine ⟨(cycle.takeUntil x hx).reverse.append (cycle.takeUntil y hy),?_⟩
    intro z hz
    simp only [Walk.support_append,Walk.support_reverse,List.mem_append,List.mem_reverse] at hz
    rcases hz with hz | hz
    · exact cycle.support_takeUntil_subset hx hz
    · exact cycle.support_takeUntil_subset hy (List.mem_of_mem_tail hz)
  obtain ⟨rfl,same⟩ := stem_entry _ p q hp hq bridges conn ep eqn
  cases same
  exact ⟨path,depth⟩

theorem common_of_stem {i : Input} {r w : i.certified.Atom}
    (p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r w) (hp : p.IsPath)
    (bridges : ∀ e ∈ p.edges, i.certified.moleculeGraph.underlyingSimpleGraph.IsBridge e)
    (feedback : RingFeedbackRoot.FeedbackRoot i.certified.moleculeGraph.underlyingSimpleGraph w)
    (before : ∀ x ∈ p.support, x ≠ w → ∀ {c}
      (cycle : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c), cycle.IsCycle → x ∉ cycle.support) :
    CommonOrigin i r := by
  intro q t d e qr tr qd td
  have lq := i.certified.carrierOccurrence_legitimate i.single q.occurrence
  have lt := i.certified.carrierOccurrence_legitimate i.single t.occurrence
  rw [qr] at lq
  rw [tr] at lt
  obtain ⟨a,ha⟩ := stem_origin p hp bridges feedback before lq qd
  obtain ⟨b,hb⟩ := stem_origin p hp bridges feedback before lt td
  exact ⟨a.trans b.symm,ha.trans hb.symm⟩

theorem of_stem {i : Input} (f : Site i) {w : i.certified.Atom}
    (p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk f.val.root w) (hp : p.IsPath)
    (bridges : ∀ e ∈ p.edges, i.certified.moleculeGraph.underlyingSimpleGraph.IsBridge e)
    (feedback : RingFeedbackRoot.FeedbackRoot i.certified.moleculeGraph.underlyingSimpleGraph w)
    (before : ∀ x ∈ p.support, x ≠ w → ∀ {c}
      (cycle : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c), cycle.IsCycle → x ∉ cycle.support)
    (x y : RingRetainedChemicalPreorder.Direction i f) :
    (do let a ← rebuilt i f ⟨x.val,some f⟩
        let b ← rebuilt i f ⟨y.val,some f⟩
        pure (compareKeys a b)) =
    RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) x y :=
  RingSingleCycleComparison.of_common_origin f (common_of_stem p hp bridges feedback before) x y

/-- A first cycle entry must be the feedback vertex if the path to that vertex
is unique. The two cycle arcs would otherwise give different simple paths. -/
theorem access_of_unique_path {V : Type*} {G : SimpleGraph V} {r w b : V}
    (reference : G.Walk r w)
    (unique : ∀ t : G.Walk r w, t.IsPath → t = reference)
    (cycle : G.Walk b b) (hc : cycle.IsCycle) (hw : w ∈ cycle.support)
    (q : G.Walk r b) (hq : q.IsPath)
    (meet : ∀ x ∈ q.support, x ∈ cycle.support → x = b) :
    b = w ∧ HEq q reference := by
  classical
  have eqbw : b = w := by
    by_contra ne
    have hwrev : w ∈ cycle.reverse.support := by simpa using hw
    let a := cycle.takeUntil w hw
    let z := cycle.reverse.takeUntil w hwrev
    have ha : a.IsPath := hc.isPath_takeUntil hw
    have hz : z.IsPath := hc.reverse.isPath_takeUntil hwrev
    have joined (t : G.Walk b w) (ht : t.IsPath)
        (sub : ∀ x ∈ t.support, x ∈ cycle.support) : (q.append t).IsPath := by
      apply Walk.IsPath.mk'
      rw [Walk.support_append,List.nodup_append']
      refine ⟨hq.support_nodup,ht.support_nodup.tail,?_⟩
      apply List.disjoint_left.mpr
      intro x hx hxt
      have xb := meet x hx (sub x (List.mem_of_mem_tail hxt))
      subst x
      have nd := ht.support_nodup
      rw [t.support_eq_cons] at nd
      exact (List.nodup_cons.mp nd).1 hxt
    have qa := unique (q.append a) (joined a ha (fun _ h => cycle.support_takeUntil_subset hw h))
    have qz := unique (q.append z) (joined z hz (by
      intro x hx
      have h := cycle.reverse.support_takeUntil_subset hwrev hx
      simpa using h))
    have tails := congrArg Walk.support (qa.trans qz.symm)
    simp only [Walk.support_append] at tails
    have same : a = z := Walk.ext_support (by
      rw [a.support_eq_cons,z.support_eq_cons]
      exact congrArg (List.cons b) (List.append_cancel_left tails))
    have snd := congrArg Walk.snd same
    dsimp [a,z] at snd
    rw [Walk.snd_takeUntil (Ne.symm ne),Walk.snd_takeUntil (Ne.symm ne),Walk.snd_reverse] at snd
    exact hc.snd_ne_penultimate snd
  subst w
  have final := unique q hq
  exact ⟨rfl,heq_of_eq final⟩

/-- The exact feedback-vertex and unique-simple-access-path criterion. -/
theorem common_of_unique_path {i : Input} {r w : i.certified.Atom}
    (reference : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r w)
    (unique : ∀ t : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r w,
      t.IsPath → t = reference)
    (feedback : RingFeedbackRoot.FeedbackRoot i.certified.moleculeGraph.underlyingSimpleGraph w) :
    CommonOrigin i r := by
  have origin {node addr} (leg : LegitimateOccurrence i.certified r node addr) {d : Nat}
      (dup : node.provenance = .ringDuplicate d) :
      RingSingleCycleOrigin.originPath node d = reference.support ∧ d = reference.length := by
    obtain ⟨a,p,cycle,hp,hc,meet,path,depth⟩ := RingSingleCycleOrigin.closure_access leg dup
    obtain ⟨eqn,same⟩ := access_of_unique_path reference unique cycle hc (feedback cycle hc) p hp meet
    subst a
    cases same
    exact ⟨path,depth⟩
  intro q p d e qr pr qd pd
  have lq := i.certified.carrierOccurrence_legitimate i.single q.occurrence
  have lp := i.certified.carrierOccurrence_legitimate i.single p.occurrence
  rw [qr] at lq
  rw [pr] at lp
  obtain ⟨a,ha⟩ := origin lq qd
  obtain ⟨b,hb⟩ := origin lp pd
  exact ⟨a.trans b.symm,ha.trans hb.symm⟩

theorem of_unique_path {i : Input} (f : Site i) {w : i.certified.Atom}
    (reference : i.certified.moleculeGraph.underlyingSimpleGraph.Walk f.val.root w)
    (unique : ∀ t : i.certified.moleculeGraph.underlyingSimpleGraph.Walk f.val.root w,
      t.IsPath → t = reference)
    (feedback : RingFeedbackRoot.FeedbackRoot i.certified.moleculeGraph.underlyingSimpleGraph w)
    (x y : RingRetainedChemicalPreorder.Direction i f) :
    (do let a ← rebuilt i f ⟨x.val,some f⟩
        let b ← rebuilt i f ⟨y.val,some f⟩
        pure (compareKeys a b)) =
    RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) x y :=
  RingSingleCycleComparison.of_common_origin f (common_of_unique_path reference unique feedback) x y

end TetraStereo.Engine.RingForestLigandOrder
assert_kernel_only TetraStereo.Engine.RingForestLigandOrder.of_feedback
assert_kernel_only TetraStereo.Engine.RingForestLigandOrder.of_vertex_forest
assert_kernel_only TetraStereo.Engine.RingForestLigandOrder.of_edge_forest
assert_kernel_only TetraStereo.Engine.RingForestLigandOrder.stem_origin
assert_kernel_only TetraStereo.Engine.RingForestLigandOrder.of_stem

assert_kernel_only TetraStereo.Engine.RingForestLigandOrder.of_unique_path
