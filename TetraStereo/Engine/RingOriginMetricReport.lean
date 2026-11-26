import TetraStereo.Engine.RingOriginFullKeys
import TetraStereo.Engine.RingOriginMarkWords
import TetraStereo.Engine.RingOriginTetrahedralTrials
import TetraStereo.Engine.RingCommonOriginCriterion

/-! Execute the active-focus duplicate distance throughout constitutional,
stereochemical and marked ligand calculations, including pyramidal trials. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginMetricReport
open OneCenter SimpleGraph
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Arm Site)
open RingActiveDistanceSchedule (Rule height)
open RingNestedActivePair (Reader)
open RingSingleCycleComparison (CommonOrigin)

def marks (i : Input) (f : Site i) (read : Reader i) : RingOriginPyramidalTrials.WordReader i
  | none, _ => some []
  | some atom, q => RingOriginMarkWords.word? i f read atom q

private theorem marks_exact {i : Input} (f : Site i) (common : CommonOrigin i f.val.root)
    (read : Reader i) (mark : Option Nat) (q : Arm i) (on : q.occurrence.val.root = f.val.root) :
    marks i f read mark q = RingFrameTransport.markWord? i read mark q := by
  cases mark with
  | none => rfl
  | some a => exact RingOriginMarkWords.word_exact f common read a q on

/-- Both centre types use the rebuilt full keys and marked words. The
tetrahedral early exit also runs with active-focus constitutional keys. -/
def publish (i : Input) : Rule i := fun f read =>
  let keys := RingOriginFullKeys.active i f read
  let words := marks i f read
  match RingPyramidalPublication.focusP i f with
  | some a => some ((RingOriginPyramidalTrials.dataWith i f keys words).publish (inputGeometry i.certified) a.val)
  | none => match RingOriginPriorityStore.early? i f with
    | some s => some s.letters
    | none => RingOriginTetrahedralTrials.publishWith i f keys words

theorem publish_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (common : CommonOrigin i f.val.root) (read : Reader i) :
    publish i f read = RingPyramidalPublication.publish i f read := by
  obtain ⟨base,a,b,ha,hb,pair⟩ := RingOriginFullKeys.factorization f common
  have rooted (arm : Arm i) (inFrame : arm ∈ RingRetainedAuxiliary.frame i.certified f) :
      arm.occurrence.val.root = f.val.root :=
    i.certified.localizedRerootChildren_root_eq (⟨f,none⟩ : Arm i) arm _
      (i.certified.executableLocalizedRerootChildren_declarative _) inFrame
  cases sel : RingPyramidalPublication.focusP i f with
  | some centre =>
    simp only [publish,RingPyramidalPublication.publish,sel,Option.some.injEq]
    exact (RingOriginPyramidalTrials.pLabels_raw i f read centre (base read) _ _
      (· * a) (· * b) (fun _ _ lt => Nat.mul_lt_mul_of_pos_right lt ha)
      (fun _ _ lt => Nat.mul_lt_mul_of_pos_right lt hb)
      (fun rev q h => (pair read rev q (rooted q h)).1)
      (fun rev q h => (pair read rev q (rooted q h)).2)
      (fun m q h => marks_exact f common read m q (rooted q h))).symm
  | none =>
    simp only [publish,RingPyramidalPublication.publish,sel,RingFullPathConstitution.fastPublish,
      RingOriginPriorityStore.early_exact f common]
    cases hit : RingZeroMassReport.zeroEarly? i f with
    | some s => rfl
    | none =>
      exact RingOriginTetrahedralTrials.publish_raw geom f read (base read) _ _
        (· * a) (· * b) (fun _ _ lt => Nat.mul_lt_mul_of_pos_right lt ha)
        (fun _ _ lt => Nat.mul_lt_mul_of_pos_right lt hb)
        (fun rev q on => (pair read rev q on).1)
        (fun rev q on => (pair read rev q on).2) (marks_exact f common read)

/-- Each batch reads its own previously committed rows. -/
def rows (i : Input) (r : i.certified.Atom) (batches : Nat) :=
  RingSphereQueue.stored (publish i) r (RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) r)
    (height i) batches

theorem rows_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) (common : CommonOrigin i r) (batches : Nat) :
    rows i r batches = RingSphereStore.rows i r batches := by
  unfold rows RingSphereStore.rows
  induction batches with
  | zero => rfl
  | succ n ih =>
    simp only [RingSphereQueue.stored,ih]
    congr 1
    apply List.map_congr_left
    intro q mem
    have on := (((RingEligibleGraph.inventory i _ r) _ q).mp mem).1.1
    rw [publish_exact geom q (on.symm ▸ common)]

def root (i : Input) (r : i.certified.Atom) :=
  publish i (RingGroupedReport.origin i r)
    (RingSphereQueue.reader r (RingSphereQueue.viewOf (rows i r (height i + 1))))

theorem root_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) (common : CommonOrigin i r) : root i r = RingChemicalGraphProof.root i r := by
  unfold root
  rw [rows_exact geom r common,publish_exact geom _ common]
  unfold RingSphereStore.rows
  rw [RingSphereQueue.stored_eq]
  rfl

def report (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun r => (root i r).map fun labels => (r.val,labels)

theorem report_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) (common : ∀ r ∈ atoms, CommonOrigin i r) :
    report i atoms = RingChemicalReport.report? i atoms := by
  unfold report RingChemicalReport.report?
  apply RingFrameTransport.mapM_congr_mem
  intro r mem
  rw [root_exact geom r (common r mem)]
  rfl

def fromRaw? := RingRawComparisonLift.fromRaw report

/-- Every raw request whose reached roots qualify gives the entire public
raw response, including ID resolution, implicit hydrogens and placement consensus. -/
theorem raw_exact (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (qualifies : ∀ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms →
      ∀ r ∈ atoms, CommonOrigin i r) :
    fromRaw? m g ids = RingHydrogenReport.fromRaw? m g ids :=
  RingRawComparisonLift.eq_native report m g ids (fun i atoms reached =>
    report_exact reached.admitted atoms (qualifies i atoms reached))

/-- A sufficient condition on molecular graphs alone, at the actual prepared roots. -/
theorem raw_of_graph (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (graph : ∀ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms → ∀ r ∈ atoms,
      RingCommonOriginCriterion.GraphCriterion i r) :
    fromRaw? m g ids = RingHydrogenReport.fromRaw? m g ids :=
  raw_exact m g ids (fun i atoms trace r mem => RingCommonOriginCriterion.sufficient (graph i atoms trace r mem))

/-- A single edge deletion leaving a forest suffices at every original root.
The proof gets its cycle witness directly from an actual retained duplicate. -/
theorem common_of_edge_deletion {i : Input} {u v : i.certified.Atom}
    (forest : (i.certified.moleculeGraph.underlyingSimpleGraph.deleteEdges {s(u,v)}).IsAcyclic)
    (r : i.certified.Atom) : CommonOrigin i r := by
  intro x y d e xr yr xd yd
  obtain ⟨_,_,cycle,_,hc,_⟩ := RingSingleCycleOrigin.closure_access
    (i.certified.carrierOccurrence_legitimate i.single x.occurrence) xd
  exact RingSingleCycleOrigin.common_origin cycle
    (RingCycleEntry.uniqueCycleSupport_of_deleteEdges_isAcyclic forest cycle hc)
    x.occurrence y.occurrence (xr.trans yr.symm) xd yd

theorem raw_of_edge_deletion (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (graph : ∀ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms →
      ∃ u v : i.certified.Atom, (i.certified.moleculeGraph.underlyingSimpleGraph.deleteEdges {s(u,v)}).IsAcyclic) :
    fromRaw? m g ids = RingHydrogenReport.fromRaw? m g ids := by
  apply raw_exact
  intro i atoms trace r _
  obtain ⟨u,v,forest⟩ := graph i atoms trace
  exact common_of_edge_deletion forest r

/-- Any disagreement of raw reports requires a reached, admitted molecular
graph on which deleting any one edge still leaves a cycle. -/
theorem raw_disagreement {m : RawMolecule} {g : SpatialConfiguration} {ids : List Nat}
    (diff : fromRaw? m g ids ≠ RingHydrogenReport.fromRaw? m g ids) :
    ∃ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms ∧
      LocalizedChemicalRing.coordinatesAdmitted i = true ∧ atoms.map Fin.val = ids ∧
      ∀ u v : i.certified.Atom, ¬ (i.certified.moleculeGraph.underlyingSimpleGraph.deleteEdges {s(u,v)}).IsAcyclic := by
  obtain ⟨i,atoms,reached,geom,requested,different⟩ :=
    RingRawComparisonLift.difference_admitted report RingChemicalReport.report? m g ids diff
  exact ⟨i,atoms,reached,geom,requested,fun _ _ forest =>
    different (report_exact geom atoms (fun r _ => common_of_edge_deletion forest r))⟩

end TetraStereo.Engine.RingOriginMetricReport
assert_kernel_only TetraStereo.Engine.RingOriginMetricReport.publish_exact
assert_kernel_only TetraStereo.Engine.RingOriginMetricReport.rows_exact
assert_kernel_only TetraStereo.Engine.RingOriginMetricReport.raw_of_graph
assert_kernel_only TetraStereo.Engine.RingOriginMetricReport.raw_disagreement
