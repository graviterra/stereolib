import TetraStereo.Engine.RingOriginAncestry
import TetraStereo.Engine.RingOriginOrderDomain

/-! A sufficient criterion for exact raw reports stated on the molecular
simple graph, with no unfolded digraph or ligand ranking in the hypothesis. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginOrderGraph
open OneCenter SimpleGraph
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingSingleCycleOrigin (originPath pathDistance shared)
open RingOriginOrderDomain (distance Closure PreservesOrder Qualifies)
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A simple path whose first intersection with a cycle is its endpoint. -/
def Access {r a : V} (p : G.Walk r a) : Prop :=
  p.IsPath ∧ ∃ t : G.Walk a a, t.IsCycle ∧ ∀ x ∈ p.support, x ∈ t.support → x = a

def Orders (G : SimpleGraph V) (r : V) (focus : List V) : Prop :=
  ∀ (a b : V) (p : G.Walk r a) (t : G.Walk r b), Access p → Access t →
    (p.length < t.length ↔ pathDistance focus p.support < pathDistance focus t.support)

/-- Only distinct, eligible atoms reached along simple paths from the
requested root can publish an auxiliary on that root's schedule. -/
def Criterion (G : SimpleGraph V) (eligible : V → Bool) (r : V) : Prop :=
  ∀ a, a ≠ r → eligible a = true → ∀ f : G.Walk r a, f.IsPath → Orders G r f.support

open private shared_bounds from TetraStereo.Engine.RingOriginAncestry

/-- An exact graph test using original path lengths and shared prefixes.
The depth of the focus cancels from both sides of the comparison. -/
theorem distance_lt_iff {r a b : V} (f : List V) (p : G.Walk r a) (t : G.Walk r b) :
    pathDistance f p.support < pathDistance f t.support ↔
      p.length + 2 * shared f t.support < t.length + 2 * shared f p.support := by
  have bp := shared_bounds f p.support
  have bt := shared_bounds f t.support
  unfold pathDistance
  simp only [Walk.length_support] at *
  omega

/-- The origins may have different depths and endpoints. A common prefix
length with the active path shifts all distances by the same amount. -/
theorem orders_of_common_prefix {r : V} (f : List V)
    (meet : ∀ (a b : V) (p : G.Walk r a) (t : G.Walk r b), Access p → Access t →
      shared f p.support = shared f t.support) : Orders G r f := by
  intro a b p t hp ht
  rw [distance_lt_iff,meet a b p t hp ht]
  omega

private theorem realize {i : Input} {r a : i.certified.Atom}
    (p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r a) (access : Access p) :
    ∃ q : Arm i, q.occurrence.val.root = r ∧ q.occurrence.val.node.provenance = .ringDuplicate p.length ∧
      originPath q.occurrence.val.node p.length = p.support := by
  obtain ⟨hp,t,ht,meet⟩ := access
  obtain ⟨q,hr,hd,ho⟩ := RingCycleRealization.realize_cycle p t hp ht meet
  exact ⟨⟨q,none⟩,hr,hd,ho⟩

private theorem extract {i : Input} {f : Site i} {q : Arm i} {d : Nat} (c : Closure f q d) :
    ∃ a, ∃ p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk f.val.root a,
      Access p ∧ originPath q.occurrence.val.node d = p.support ∧ d = p.length := by
  obtain ⟨a,p,t,hp,ht,meet,ho,hd⟩ := RingSingleCycleOrigin.closure_access
    (i.certified.carrierOccurrence_legitimate i.single q.occurrence) c.2
  have atRoot : ∃ a, ∃ p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk q.occurrence.val.root a,
      Access p ∧ originPath q.occurrence.val.node d = p.support ∧ d = p.length :=
    ⟨a,p,⟨hp,t,ht,meet⟩,ho,hd⟩
  rwa [←c.1]

theorem at_focus {i : Input} (f : Site i) :
    PreservesOrder f ↔ Orders i.certified.moleculeGraph.underlyingSimpleGraph f.val.root f.val.node.history.reverse := by
  constructor
  · intro order a b p t hp ht
    obtain ⟨q,qr,qd,qp⟩ := realize p hp
    obtain ⟨z,zr,zd,zt⟩ := realize t ht
    simpa only [distance,qp,zt] using order q z _ _ ⟨qr,qd⟩ ⟨zr,zd⟩
  · intro order q z d e c b
    obtain ⟨a,p,hp,qp,hd⟩ := extract c
    obtain ⟨v,t,ht,zt,he⟩ := extract b
    unfold distance
    rw [qp,zt,hd,he]
    exact order a v p t hp ht

theorem criterion_iff {i : Input} (r : i.certified.Atom) :
    Criterion i.certified.moleculeGraph.underlyingSimpleGraph (RingPyramidalPublication.eligible i) r ↔
      Qualifies i r := by
  constructor
  · intro graph f cand
    obtain ⟨root,nonroot,real,a,cur,elig⟩ := cand
    obtain ⟨v,hv,path⟩ := RingGraphPaths.site_path f real
    obtain rfl := Option.some.inj (hv.symm.trans cur)
    have ne : v ≠ r := fun eqn => nonroot (hv.trans (congrArg some eqn))
    apply (at_focus f).mpr
    rw [← RingClosureCycle.support_toWalk path]
    have graph' : Criterion i.certified.moleculeGraph.underlyingSimpleGraph
        (RingPyramidalPublication.eligible i) f.val.root := root.symm ▸ graph
    exact graph' v (root.symm ▸ ne) elig _ (RingClosureCycle.isPath_toWalk path)
  · intro sites a ne eligible f hf
    let path := RingClosureCycle.path_of_walk f hf
    obtain ⟨root,hist,real,cur⟩ := RingGraphPaths.represents_site path
    have cand : RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) r (RingGraphPaths.site path) :=
      ⟨root,fun eqn => ne (Option.some.inj (cur.symm.trans eqn)),real,a,cur,eligible⟩
    have order := (at_focus _).mp (sites _ cand)
    simpa only [root,hist,List.reverse_reverse] using order

theorem raw_of_graph (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (graph : ∀ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms → ∀ r ∈ atoms,
      Criterion i.certified.moleculeGraph.underlyingSimpleGraph (RingPyramidalPublication.eligible i) r) :
    RingOriginMetricReport.fromRaw? m g ids = RingHydrogenReport.fromRaw? m g ids :=
  RingOriginOrderDomain.raw_exact m g ids (fun i atoms trace r mem => (criterion_iff r).mp (graph i atoms trace r mem))

/-- Requested roots already decided from constitution can be certified even
when auxiliary stores on that root's graph differ. -/
def decided (i : Input) (r : i.certified.Atom) : Bool :=
  !RingPyramidalPublication.eligible i r ||
    ((RingPyramidalPublication.focusP i (RingGroupedReport.origin i r)).isNone &&
     (RingZeroMassReport.zeroEarly? i (RingGroupedReport.origin i r)).isSome)

theorem decided_readers {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) (hit : decided i r = true) (a b : RingNestedActivePair.Reader i) :
    RingOriginMetricReport.publish i (RingGroupedReport.origin i r) a =
      RingPyramidalPublication.publish i (RingGroupedReport.origin i r) b := by
  rw [RingOriginRootAll.publish_origin geom]
  cases eligible : RingPyramidalPublication.eligible i r with
  | false =>
    have off : ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) (RingGroupedReport.origin i r) := by
      rintro ⟨_,x,h,hx⟩
      obtain rfl := Option.some.inj ((RingGroupedReport.origin_address i r).2.2.symm.trans h)
      simp [eligible] at hx
    rw [RingChemicalGraphProof.skips i _ a off,RingChemicalGraphProof.skips i _ b off]
  | true =>
    cases hp : RingPyramidalPublication.focusP i (RingGroupedReport.origin i r) <;>
      cases he : RingZeroMassReport.zeroEarly? i (RingGroupedReport.origin i r) <;>
      simp_all [decided,RingPyramidalPublication.publish,RingFullPathConstitution.fastPublish]

theorem root_of_decided {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) (hit : decided i r = true) :
    RingOriginMetricReport.root i r = RingChemicalGraphProof.root i r :=
  decided_readers geom r hit _ _

/-- For final reports one can choose the proof separately at each requested
root and placement. The constitutional branch needs no auxiliary agreement. -/
theorem raw_of_graph_or_decided (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (ok : ∀ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms → ∀ r ∈ atoms,
      decided i r = true ∨ Criterion i.certified.moleculeGraph.underlyingSimpleGraph
        (RingPyramidalPublication.eligible i) r) :
    RingOriginMetricReport.fromRaw? m g ids = RingHydrogenReport.fromRaw? m g ids := by
  apply RingRawComparisonLift.eq_native
  intro i atoms trace
  unfold RingOriginMetricReport.report RingChemicalReport.report?
  apply RingFrameTransport.mapM_congr_mem
  intro r mem
  have agree : RingOriginMetricReport.root i r = RingChemicalGraphProof.root i r := by
    rcases ok i atoms trace r mem with hit | access
    · exact root_of_decided trace.admitted r hit
    · exact RingOriginOrderTransport.root_exact trace.admitted r (RingOriginOrderDomain.queued ((criterion_iff r).mp access))
  rw [agree]
  rfl

end TetraStereo.Engine.RingOriginOrderGraph
assert_kernel_only TetraStereo.Engine.RingOriginOrderGraph.criterion_iff
assert_kernel_only TetraStereo.Engine.RingOriginOrderGraph.raw_of_graph
assert_kernel_only TetraStereo.Engine.RingOriginOrderGraph.raw_of_graph_or_decided
