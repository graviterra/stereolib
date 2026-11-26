import TetraStereo.Engine.RingOriginRootAll

/-! Localize a change in a final descriptor by rerunning the full schedule
with the distance convention switched at one more eligible occurrence. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginCausal
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Rule height sites)
open RingSphereQueue (reader run)
open private first_batch from TetraStereo.Engine.RingSphereQueue

private abbrev eligible (i : Input) := RingPyramidalPublication.eligible i
private abbrev queue (i : Input) (r : i.certified.Atom) := RingEligibleGraph.queue i (eligible i) r

/-- The list contains every eligible non-root occurrence on the requested root slice. -/
def inventory (i : Input) (r : i.certified.Atom) : List (Site i) :=
  (sites i).filter (RingEligibleGraph.candidate (eligible i) r)

theorem mem_inventory {i : Input} {r : i.certified.Atom} {q : Site i} :
    q ∈ inventory i r ↔ RingEligibleGraph.candidate (eligible i) r q := by
  have listed : q ∈ sites i := List.mem_attach ..
  simp [inventory,listed]

/-- Switch the entire local ranking procedure at precisely the selected sites. -/
def policy (i : Input) (selected : List (Site i)) : Rule i := fun q =>
  if q ∈ selected then RingOriginMetricReport.publish i q else RingPyramidalPublication.publish i q

/-- Recompute all batches from the initial store and read the public root on the result. -/
def trial (i : Input) (r : i.certified.Atom) (selected : List (Site i)) :=
  RingPyramidalPublication.publish i (RingGroupedReport.origin i r)
    (reader r (run (policy i selected) r (queue i r) (height i + 1)))

theorem trial_nil (i : Input) (r : i.certified.Atom) :
    trial i r [] = RingChemicalGraphProof.root i r := by
  have eqn : policy i [] = RingPyramidalPublication.publish i := by funext q; simp [policy]
  unfold trial
  rw [eqn]
  rfl

private theorem same_run {i : Input} (r : i.certified.Atom) (a b : Rule i)
    (agree : ∀ d q, q ∈ queue i r d → a q = b q) (n : Nat) :
    run a r (queue i r) n = run b r (queue i r) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run,ih,RingSphereQueue.commit]
    have mapped := List.map_congr_left (l := queue i r (height i - n))
      (f := fun q => (q, a q (reader r (run b r (queue i r) n))))
      (g := fun q => (q, b q (reader r (run b r (queue i r) n))))
      (fun q h => by dsimp only; rw [agree _ q h])
    rw [mapped]

theorem trial_all (i : Input) (r : i.certified.Atom) :
    trial i r (inventory i r) =
      RingPyramidalPublication.publish i (RingGroupedReport.origin i r)
        (reader r (RingSphereQueue.viewOf (RingOriginMetricReport.rows i r (height i + 1)))) := by
  unfold trial RingOriginMetricReport.rows
  rw [RingSphereQueue.stored_eq]
  rw [same_run r (policy i (inventory i r)) (RingOriginMetricReport.publish i) (fun d q h => by
    have listed := mem_inventory.mpr (((RingEligibleGraph.inventory i (eligible i) r) d q).mp h).1
    simp [policy,listed])]

private theorem split_change {α β : Type} (test : List α → β) (xs : List α)
    (changed : test xs ≠ test []) :
    ∃ before q after, xs = before ++ q :: after ∧ test (q :: after) ≠ test after := by
  induction xs with
  | nil => exact (changed rfl).elim
  | cons x xs ih =>
    by_cases rest : test xs = test []
    · exact ⟨[],x,xs,rfl,fun eqn => changed (eqn.trans rest)⟩
    · obtain ⟨pre,q,post,parts,unequal⟩ := ih rest
      exact ⟨x::pre,q,post,congrArg (x :: ·) parts,unequal⟩

/-- A single local change of policy changes the recomputed root. On the
identical preceding store, the two actual local procedures already differ at
that very site. The surrounding choice of conventions is recorded by the cut. -/
structure Switch {i : Input} (r : i.certified.Atom) (q : Site i)
    (before after : List (Site i)) : Prop where
  split : inventory i r = before ++ q :: after
  candidate : RingEligibleGraph.candidate (eligible i) r q
  fresh : q ∉ after
  changesRoot : trial i r (q :: after) ≠ trial i r after
  localDifference : ∃ n < height i + 1, q ∈ queue i r (height i - n) ∧
    run (policy i (q :: after)) r (queue i r) n = run (policy i after) r (queue i r) n ∧
    let prior := reader r (run (policy i after) r (queue i r) n)
    RingOriginMetricReport.publish i q prior ≠ RingPyramidalPublication.publish i q prior

theorem switch_of_change {i : Input} {r : i.certified.Atom}
    (changed : trial i r (inventory i r) ≠ trial i r []) :
    ∃ before q after, Switch r q before after := by
  obtain ⟨before,q,after,split,flip⟩ := split_change (trial i r) _ changed
  have different : run (policy i (q :: after)) r (queue i r) (height i + 1) ≠
      run (policy i after) r (queue i r) (height i + 1) := fun eqn =>
    flip (by unfold trial; rw [eqn])
  obtain ⟨n,bound,t,queued,same,localDiff⟩ := first_batch _ _ _ _ _ different
  have atSite : t = q := by
    by_contra other
    simp [policy,other] at localDiff
  subst t
  have fresh : q ∉ after := by
    intro mem
    simp [policy,mem] at localDiff
  refine ⟨before,q,after,split,((RingEligibleGraph.inventory i (eligible i) r _ q).mp queued).1,
    fresh,flip,n,bound,queued,same,?_⟩
  simpa [policy,fresh,same] using localDiff




theorem trial_all_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) :
    trial i r (inventory i r) = RingOriginMetricReport.root i r := by
  rw [trial_all,RingOriginMetricReport.root,RingOriginRootAll.publish_origin geom]

/-- Every raw disagreement supplies a prepared root, a cut of its eligible
inventory and a single physical occurrence whose policy changes that root
under a full rerun. The same root necessarily has distinct closure origins. -/
theorem raw_switch {m : RawMolecule} {g : SpatialConfiguration} {ids : List Nat}
    (diff : RingOriginMetricReport.fromRaw? m g ids ≠ RingHydrogenReport.fromRaw? m g ids) :
    ∃ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms ∧
      ∃ r ∈ atoms, RingOriginMetricReport.root i r ≠ RingChemicalGraphProof.root i r ∧
        ¬ RingSingleCycleComparison.CommonOrigin i r ∧
        ∃ before q after, Switch r q before after := by
  classical
  obtain ⟨i,atoms,trace,geom,_,unequal⟩ := RingRawComparisonLift.difference_admitted
    RingOriginMetricReport.report RingChemicalReport.report? m g ids diff
  have rootDiff : ∃ r ∈ atoms, RingOriginMetricReport.root i r ≠ RingChemicalGraphProof.root i r := by
    by_contra! same
    apply unequal
    unfold RingOriginMetricReport.report RingChemicalReport.report?
    apply RingFrameTransport.mapM_congr_mem
    intro r mem
    rw [same r mem]
    rfl
  obtain ⟨r,member,changed⟩ := rootDiff
  refine ⟨i,atoms,trace,r,member,changed,fun common =>
    changed (RingOriginMetricReport.root_exact geom r common),switch_of_change ?_⟩
  rwa [trial_all_exact geom,trial_nil]

end TetraStereo.Engine.RingOriginCausal
assert_kernel_only TetraStereo.Engine.RingOriginCausal.raw_switch
