import TetraStereo.Examples.DecalinRootRanking
import TetraStereo.Examples.DecalinPublishedCoordinates

/-! Public reports at the two decalin fusion atoms from their native ligand orders. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinPublicReport
open Engine OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingGroupedTrials (atom)
open RingGroupedReport (origin)
open RingFullPathTrialReadings (trialKey trials Outcome hand?)
open RingNestedActivePair (Frame)
open RingFullPathPublication (Ballots crossed)
open DecalinFrames (molecule junctionRow fusionLabel expected)
open RingWrittenPHReadings (geometry)
open DecalinRootWords (publicRead)
open DecalinLigandOrder (ranked)
open private graph_rows frame_perm from TetraStereo.Examples.DecalinFrames
open private lift_row from TetraStereo.Examples.DecalinAuxiliary
open private swap_middle from TetraStereo.Examples.DecalinPathSwap
open private keys_exact from TetraStereo.Engine.RingFullPathPublication

private def vote (near far : RS) : RS := if far = .R then near else near.swap

private theorem physical (g : Geometry) (j : Fin 2) (near far : RS)
    (seen : readback? g (junctionRow j.val) = some near) (rev : Bool) :
    readback? (if rev then mirror g else g) (ranked j (if rev then far.swap else far)) =
      some (vote near far) := by
  fin_cases j <;> cases near <;> cases far <;> cases rev <;>
    dsimp [ranked,junctionRow,RS.swap,vote] at * <;>
    (try rw [readback_mirror]) <;>
    first | exact seen | (rw [seen]; done) | (rw [seen]; rfl) | (rw [swap_middle,seen]; done) | (rw [swap_middle,seen]; rfl)

private theorem rank_facts : ∀ (j : Fin 2) (h : RS),
    (ranked j h).Perm (junctionRow j.val) ∧
    (ranked j h).Pairwise (fun a b => (ranked j h).idxOf a < (ranked j h).idxOf b) := by
  intro j h
  fin_cases j <;> cases h <;> decide +kernel

private theorem ballots {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (small : root.val < 2) (fr : Frame i (origin i root)) (near far : RS)
    (localSense : readback? (geometry i.spatial) (junctionRow root.val) = some near)
    (remote : readback? (geometry i.spatial) (junctionRow (1-root.val)) = some far)
    (rev : Bool) : ∃ ks, Ballots fr (publicRead i root) rev ks [some (vote near far)] := by
  obtain ⟨ks,got,reads⟩ := keys_exact fr (RingChemicalGraphProof.ready geom _) rev
  have cmp := DecalinRootRanking.frame_order graph geom root small fr far remote rev ks got
  let j : Fin 2 := ⟨root.val,small⟩
  let h := if rev then far.swap else far
  let w (s : Fin 4) := trialKey (ks s) []
  obtain ⟨phys,ascending⟩ := rank_facts j h
  have all := frame_perm fr
  have same : root = fr.center.val := Option.some.inj
    ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2
  rw [graph,←same] at all
  obtain ⟨row,ids,perm⟩ := lift_row (atom fr) (phys.trans ((graph_rows j).symm.trans all.symm))
  have rankedRow : row.Pairwise (fun a b => w b < w a) := by
    have asc : (row.map (atom fr)).Pairwise
        (fun a b => (ranked j h).idxOf a < (ranked j h).idxOf b) := ids ▸ ascending
    apply (List.pairwise_map.mp asc).imp
    intro a b ab
    apply (DeclarativeCIP.compareLex_eq_lt_iff_of compare RingFullPathConstitution.word_lt
      (fun _ _ => Std.compare_eq_eq_iff_eq) _ _).mp
    exact (cmp b a).trans (Nat.compare_eq_lt.mpr ab)
  have nd : (row.map w).Nodup := List.pairwise_map.mpr (rankedRow.imp fun x => ne_of_gt x)
  have on := (List.nodup_map_iff_inj_on (List.nodup_finRange 4)).mp ((perm.map _).nodup_iff.mp nd)
  have inj : Function.Injective w := fun a b => on a (List.mem_finRange _) b (List.mem_finRange _)
  have empty : RingFullPathEligibility.tiedSlots ks = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    obtain ⟨b,diff,eqn⟩ := (RingFullPathEligibility.mem_tied _ _).mp ha
    exact diff (inj (congrArg (fun k => trialKey k []) eqn))
  refine ⟨ks,(reads _).mpr rfl,?_⟩
  simp only [trials,RingFullPathEligibility.candidates,empty,List.length_nil]
  refine .cons ⟨fun _ => [],fun _ => rfl,Outcome.hand inj
    ⟨perm,List.pairwise_map.mpr (rankedRow.imp le_of_lt)⟩ ?_⟩ .nil
  unfold hand?
  rw [RingWrittenPHReadings.inputGeometry_eq]
  change readback? _ (row.map (atom fr)) = _
  rw [←ids]
  exact physical _ j near far localSense rev

/-- Both independently read geometries publish the same lowercase descriptor. -/
theorem junction {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (small : root.val < 2) (near far : RS)
    (localSense : readback? (geometry i.spatial) (junctionRow root.val) = some near)
    (remote : readback? (geometry i.spatial) (junctionRow (1-root.val)) = some far) :
    RingChemicalGraphProof.root i root = some (some (fusionLabel near far)) := by
  let q := origin i root
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor root) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,graph]
    exact (graph_rows ⟨root.val,small⟩).length_eq.trans (by unfold junctionRow; split <;> rfl)
  let c : i.certified.TetrahedralCenter := ⟨root,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr degree⟩
  have recg := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mpr ⟨rfl,rfl⟩
  obtain ⟨fr,_⟩ := RingGroupedGeometry.frame_exists recg
  obtain ⟨x,hx⟩ := ballots graph geom root small fr near far localSense remote false
  obtain ⟨y,hy⟩ := ballots graph geom root small fr near far localSense remote true
  have both := RingFullPathPublication.TwoGeometry.centre hx hy
  have label : crossed [some (vote near far)] [some (vote near far)] = some (fusionLabel near far) := by
    cases near <;> cases far <;> rfl
  rw [label] at both
  have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) root degree
  have noP : RingPyramidalPublication.focusP i q = none := by
    change (some root).filter (RingPyramidalPublication.phosphorus i) = none
    simp [off]
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i),←RingChemicalGraphProof.state,
    RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,noP,
    RingFullPathConstitution.fast_local geom (RingChemicalGraphProof.ready geom _)]
  exact (RingFullPathPublication.two_geometry_iff geom _ _ (RingChemicalGraphProof.ready geom _) _).mpr both

open private atom from TetraStereo.Examples.DecalinFrames
open private row? from TetraStereo.Engine.RingChemicalReport

theorem raw_pair {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (a b : RS)
    (ha : readback? (geometry i.spatial) (junctionRow 0) = some a)
    (hb : readback? (geometry i.spatial) (junctionRow 1) = some b) :
    RingHydrogenReport.fromRaw? molecule i.spatial [0,1] = some (expected a b [0,1]) := by
  let x := atom i graph 0
  let y := atom i graph 1
  have left := junction graph geom x (by exact (by decide : 0 < 2)) a b ha hb
  have right := junction graph geom y (by exact (by decide : 1 < 2)) b a hb ha
  have symm : fusionLabel b a = fusionLabel a b := by cases a <;> cases b <;> rfl
  rw [symm] at right
  change RingHydrogenReport.fromRaw? molecule i.spatial ([x,y].map Fin.val) = _
  rw [←graph,RingWrittenPHReadings.fromRaw_closed_report i (graph ▸ DecalinFrames.closed) geom]
  simp [RingChemicalReport.report?,row?,left,right,List.mapM_cons,expected]
  exact ⟨rfl,rfl⟩

open DecalinPublishedCoordinates
open private input211 input212 from TetraStereo.Examples.DecalinPublishedCoordinates

/-- Every admitted coordinate table on this graph agrees with the independent two-determinant
specification on every raw query, including repeated and invalid atom IDs. -/
theorem raw_agreement (i : Input) (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids = DecalinFrames.independentReport? i.spatial ids := by
  obtain ⟨u,v,w,z⟩ := source_hands
  have c : LocalizedChemicalRing.admitRawSpatial? molecule vs211 = some input211 := (Option.some_get _).symm
  have t : LocalizedChemicalRing.admitRawSpatial? molecule vs212 = some input212 := (Option.some_get _).symm
  obtain ⟨cm,cg⟩ := RingChemicalReport.admission_fields c
  obtain ⟨tm,tg⟩ := RingChemicalReport.admission_fields t
  apply complete_of_sdf_rows _ _ i graph geom ids
  · rw [←cg] at u v ⊢
    exact raw_pair cm source_admitted.1 _ _ u v
  · rw [←tg] at w z ⊢
    exact raw_pair tm source_admitted.2 _ _ w z

end TetraStereo.Examples.DecalinPublicReport
assert_kernel_only TetraStereo.Examples.DecalinPublicReport.junction
assert_kernel_only TetraStereo.Examples.DecalinPublicReport.raw_agreement
