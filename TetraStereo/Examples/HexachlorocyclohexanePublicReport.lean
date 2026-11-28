import TetraStereo.Examples.HexachlorocyclohexanePublicRanking
import TetraStereo.Examples.BlueBookHexachlorocyclohexaneSeries
import TetraStereo.Examples.MixedHalogenSpiro
import TetraStereo.Examples.HexachlorocyclohexaneSignedOrder
import TetraStereo.Examples.AntipodalCyclohexaneReport

/-! Public raw reports on the fully written HCH graph from the six local
tetrahedral signs and the independently justified recursive assignments. -/
set_option autoImplicit false
namespace TetraStereo.Examples.HexachlorocyclohexanePublicReport
open Engine OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingGroupedTrials (atom)
open RingGroupedReport (origin)
open RingFullPathTrialReadings (trialKey)
open RingNestedActivePair (Frame)
open RingFullPathPublication (Ballots)
open BlueBookHexachlorocyclohexane (molecule)
open HexachlorocyclohexaneFamily (fixedFrame forwardSite hand reading Assignment assign? Nondegenerate)
open HexachlorocyclohexaneSignedOrder (winner ballot)
open RingWrittenPHReadings (geometry)
open private frame_perm canonical_perm from TetraStereo.Examples.DecalinFrames
open private strict_ballot from TetraStereo.Examples.AntipodalCyclohexaneReport
open private calibrated from TetraStereo.Engine.RingRetainedAuxiliary
open private row? from TetraStereo.Engine.RingChemicalReport
open private toAtom bound from TetraStereo.Engine.RingAtomicNeighborOrder

open AntipodalCyclohexaneWords (publicRead)
open HexachlorocyclohexanePublicRanking (ranked)
open private row from TetraStereo.Examples.HexachlorocyclohexanePublicRanking
open HexachlorocyclohexanePublicStore (nonflat)
open private graphRows from TetraStereo.Examples.HexachlorocyclohexanePublicStore

private theorem closed : RingHydrogenCompletion.plan molecule = [] := by decide +kernel
private theorem size_bound {i : Input} (raw : i.molecule = molecule) (a : i.certified.Atom) : a.val < 18 := by
  simpa only [raw] using bound i a

private def incident (a : Nat) := (List.range molecule.atomCount).filter fun n => 0 < molecule.bondOrder a n
private theorem rank_facts (r : Fin 6) (p : Fin 32) (rev : Bool) :
    (ranked r p rev).Perm (fixedFrame r.val) ∧
    (ranked r p rev).Pairwise (fun a b => (ranked r p rev).idxOf a < (ranked r p rev).idxOf b) := by
  unfold ranked row
  split <;> fin_cases r <;> decide +kernel

private theorem physical (g : Geometry) (r : Fin 6) (p : Fin 32) (near : RS)
    (seen : readback? g (fixedFrame r.val) = some near) (rev : Bool) :
    readback? (if rev then mirror g else g) (ranked r p rev) = some (ballot p near rev) := by
  have swapped := LocalizedMarkedTerminalGaugeSwap.readback_swap23 g (r.val+6) ((r.val+5)%6) ((r.val+1)%6) (r.val+12)
  unfold fixedFrame at seen
  rw [seen] at swapped
  cases rev <;> simp only [Bool.false_eq_true,if_false,if_true,ranked,row,ballot,readback_mirror]
    <;> split <;> cases near <;> simp_all [fixedFrame,RS.swap]

/-- Descriptor pair encoded by the independently justified actual/mirror readings. -/
def labels (p : Fin 32) (near : RS) : RingNestedActivePair.Labels :=
  let w := reading p near
  (RingNestedActivePair.label w.actual w.reflected,RingNestedActivePair.label w.reflected w.actual)

theorem carbon {i : Input} (raw : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : i.certified.Atom)
    (r : Fin 6) (atRoot : v.val = r.val) (cfg : Assignment (geometry i.spatial) r) :
    RingChemicalGraphProof.root i v = some (some (labels cfg.profile cfg.center)) := by
  let q := origin i v
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,raw,atRoot]
    exact (graphRows r.val r.isLt).length_eq.trans rfl
  let c : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr degree⟩
  have recg := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mpr ⟨rfl,rfl⟩
  obtain ⟨fr,_⟩ := RingGroupedGeometry.frame_exists recg
  have one (rev : Bool) : ∃ ks, Ballots fr (publicRead i v) rev ks [some (ballot cfg.profile cfg.center rev)] := by
    obtain ⟨phys,asc⟩ := rank_facts r cfg.profile rev
    have all := frame_perm fr
    have focus : v = fr.center.val := Option.some.inj
      ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2
    rw [raw,←focus,atRoot] at all
    exact strict_ballot fr _ (RingChemicalGraphProof.ready geom _) rev _ (phys.trans ((graphRows r.val r.isLt).symm.trans all.symm))
      asc (HexachlorocyclohexanePublicRanking.frame_order raw geom v r atRoot fr cfg.profile cfg.neighborReads rev) _ (physical _ r _ _ cfg.focusRead rev)
  obtain ⟨x,hx⟩ := one false
  obtain ⟨y,hy⟩ := one true
  have both := RingFullPathPublication.TwoGeometry.centre hx hy
  rw [(HexachlorocyclohexaneSignedOrder.ballots cfg.profile cfg.center).2.2.1] at both
  have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) v degree
  have noP : RingPyramidalPublication.focusP i q = none := by
    change (some v).filter (RingPyramidalPublication.phosphorus i) = none
    simp [off]
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i),←RingChemicalGraphProof.state,
    RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,noP,
    RingFullPathConstitution.fast_local geom (RingChemicalGraphProof.ready geom _)]
  exact (RingFullPathPublication.two_geometry_iff geom _ _ (RingChemicalGraphProof.ready geom _) _).mpr both

/-- On every carbon the published label pair has a recursively supported
chemical reading; both components agree with the original and reflected readings in the recursive specification. -/
theorem supported_carbon {i : Input} (raw : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : i.certified.Atom)
    (r : Fin 6) (atRoot : v.val = r.val) :
    ∃ w : RingChemicalPriority.Recursive.Reading, ∃ pair : RingNestedActivePair.Labels,
      RingChemicalPriority.Recursive.Supported molecule (geometry i.spatial) [r.val] w ∧
      RingChemicalGraphProof.root i v = some (some pair) ∧
      w.label = some pair.1 ∧ w.reverse.label = some pair.2 := by
  obtain ⟨cfg,_⟩ := Option.isSome_iff_exists.mp ((HexachlorocyclohexaneFamily.assignment_iff _ r).mpr (nonflat raw geom))
  refine ⟨reading cfg.profile cfg.center,labels cfg.profile cfg.center,cfg.justified,
    carbon raw geom v r atRoot cfg,?_⟩
  unfold labels
  generalize reading cfg.profile cfg.center = w
  obtain ⟨(_|_),(_|_)⟩ := w <;> exact ⟨rfl,rfl⟩

private theorem leaf {i : Input} (raw : i.molecule = molecule) (v : i.certified.Atom) (off : 6 ≤ v.val) :
    RingChemicalGraphProof.root i v = some none := by
  have facts : ∀ a : Fin 18, 6 ≤ a.val → (incident a.val).length = 1 ∧
      RingAtomicNeighborOrder.neutralPyramidal molecule a.val = false := by decide +kernel
  obtain ⟨one,notP⟩ := facts ⟨v.val,size_bound raw v⟩ off
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 1 := by
    rw [RingAtomicNeighborOrder.degree_eq,raw]
    exact (RingStereoSiblingPass.legal_order _ _).perm.length_eq.trans one
  have gate : RingPyramidalPublication.phosphorus i v = false := by
    change (RingAtomicNeighborOrder.neutralPyramidal i.molecule v.val && _) = false
    simp [raw,notP]
  have inactive : ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) (origin i v) := by
    rintro ⟨_,b,current,on⟩
    obtain rfl : v = b := Option.some.inj current
    simp [RingPyramidalPublication.eligible,degree,gate] at on
  exact (RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) v).trans
    ((RingChemicalGraphProof.state_eq i _).trans (RingChemicalGraphProof.skips i _ _ inactive))

def expectedRow? (g : Geometry) (n : Nat) : Option (Nat × Option RingNestedActivePair.Labels) :=
  if h : n < 6 then (assign? g ⟨n,h⟩).map fun cfg => (n,some (labels cfg.profile cfg.center))
  else if n < 18 then some (n,none) else none

def expected? (x : SpatialConfiguration) (ids : List Nat) := ids.mapM (expectedRow? (geometry x))

theorem raw_agreement (i : Input) (raw : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids = expected? i.spatial ids := by
  by_cases good : ids.all (· < 18) = true
  · let vs := ids.attach.map fun n => toAtom i n.val (by rw [raw]; exact of_decide_eq_true (List.all_eq_true.mp good _ n.property))
    have resolved : vs.map Fin.val = ids := by simp [vs,List.map_map,Function.comp_def,toAtom]
    have native := RingWrittenPHReadings.fromRaw_closed_report i (raw ▸ closed) geom vs
    rw [raw,resolved] at native
    rw [native,expected?,←resolved,List.mapM_map]
    apply RingFrameTransport.mapM_congr_mem
    intro v _
    by_cases hc : v.val < 6
    · let r : Fin 6 := ⟨v.val,hc⟩
      obtain ⟨cfg,found⟩ := Option.isSome_iff_exists.mp ((HexachlorocyclohexaneFamily.assignment_iff _ r).mpr (nonflat raw geom))
      dsimp only [r] at found
      simp [row?,expectedRow?,hc,found,carbon raw geom v r rfl cfg]
    · simp [row?,expectedRow?,hc,size_bound raw v,leaf raw v (by omega)]
  · have failed : RingMolecularReport.resolve i ids = none := by
      cases h : RingMolecularReport.resolve i ids with
      | none => rfl
      | some vs =>
        exfalso
        apply good
        rw [← (RingMolecularReport.resolve_iff ..).mp h]
        apply List.all_eq_true.mpr
        intro n hn
        obtain ⟨v,_,rfl⟩ := List.mem_map.mp hn
        exact decide_eq_true (size_bound raw v)
    have none : expected? i.spatial ids = none := by
      cases out : expected? i.spatial ids with
      | none => rfl
      | some rows =>
        exfalso
        apply good
        apply List.all_eq_true.mpr
        intro n hn
        obtain ⟨row,_,someRow⟩ := RingRetainedReferenceGroup.forInput out hn
        apply decide_eq_true
        by_contra! bad
        simp [expectedRow?,show ¬ n < 6 by omega,show ¬ n < 18 by omega] at someRow
    have accepted := RingSpatialTransport.readmit i
    rw [raw] at accepted
    simp [RingHydrogenReport.fromRaw_closed_eq closed,RingChemicalReport.fromRaw?,accepted,failed,none]

/-- Project the actual-coordinate descriptor from each public report row. -/
def actualLetters (rows : RingGroupedReport.Report) :=
  rows.mapM fun row => row.2.map Prod.fst

private theorem first_label (p : Fin 32) (h : RS) :
    (reading p h).label = some (labels p h).1 := by
  unfold labels
  generalize reading p h = w
  obtain ⟨(_|_),(_|_)⟩ := w <;> rfl

/-- Public raw letters and the recursive source assignment agree in any
requested carbon locant order, including repeated locants. -/
theorem raw_letters (i : Input) (raw : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (locants : List (Fin 6)) :
    (RingHydrogenReport.fromRaw? molecule i.spatial (locants.map Fin.val)).bind actualLetters =
      locants.mapM (fun r => do
        let a ← assign? (geometry i.spatial) r
        (reading a.profile a.center).label) := by
  let sourceRow (r : Fin 6) := (assign? (geometry i.spatial) r).bind fun a => (reading a.profile a.center).label
  rw [raw_agreement i raw geom]
  change ((locants.map Fin.val).mapM (expectedRow? (geometry i.spatial))).bind actualLetters = locants.mapM sourceRow
  induction locants with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨cfg,found⟩ := Option.isSome_iff_exists.mp ((HexachlorocyclohexaneFamily.assignment_iff _ r).mpr (nonflat raw geom))
    have head : expectedRow? (geometry i.spatial) r.val = some (r.val,some (labels cfg.profile cfg.center)) := by
      simp [expectedRow?,r.isLt,found]
    have src : sourceRow r = some (labels cfg.profile cfg.center).1 := by simp [sourceRow,found,first_label]
    simp only [List.map_cons,List.mapM_cons,head,src,←ih]
    cases tail : (rs.map Fin.val).mapM (expectedRow? (geometry i.spatial)) with
    | none => rfl
    | some xs =>
      change actualLetters ((r.val,some (labels cfg.profile cfg.center))::xs) = _
      simp [actualLetters,List.mapM_cons]

open BlueBookHexachlorocyclohexaneSeries (faces series SourceRow)
open private coordinates_of_neighbor_volumes from TetraStereo.Examples.MixedHalogenSpiro

/-- Materialize the series' coordinate lookup in the original eighteen-atom order. -/
def faceSpatial (mask : Fin 64) : SpatialConfiguration :=
  ⟨List.ofFn (fun n : Fin 18 => (faces mask n.val).getD ⟨0,0,0⟩)⟩

theorem face_geometry (mask : Fin 64) : geometry (faceSpatial mask) = faces mask := by
  funext n
  by_cases hn : n < 18
  · have full : (faces mask n).isSome := by
      unfold faces BlueBookHexachlorocyclohexane.geometry
      split
      · split <;> simp [BlueBookHexachlorocyclohexane.spatial] <;> omega
      · rw [List.getElem?_eq_getElem hn]; rfl
    obtain ⟨p,hp⟩ := Option.isSome_iff_exists.mp full
    unfold geometry faceSpatial
    rw [List.getElem?_ofFn,dif_pos hn]
    simp only [hp,Option.getD_some]
  · have high : ¬(6 ≤ n ∧ n < 18 ∧ (mask.val.testBit (n%6) != (37 : Nat).testBit (n%6)) = true) := by omega
    unfold geometry faceSpatial faces BlueBookHexachlorocyclohexane.geometry
    rw [List.getElem?_ofFn,dif_neg hn,if_neg high,List.getElem?_eq_none (by change 18 ≤ n; omega)]

private def base := (LocalizedChemicalRing.admitRawSpatial? molecule BlueBookHexachlorocyclohexane.spatial).get (by decide +kernel)

private theorem base_graph : base.molecule = molecule := (RingChemicalReport.admission_fields
  (show LocalizedChemicalRing.admitRawSpatial? molecule BlueBookHexachlorocyclohexane.spatial = some base from (Option.some_get _).symm)).1

private def faceInput (mask : Fin 64) := RingSpatialTransport.atGeometry base (faceSpatial mask)
  (by change (List.ofFn _).length = 18; simp)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 5000000 in
private theorem series_admitted : ∀ row ∈ series, LocalizedChemicalRing.coordinatesAdmitted (faceInput row.mask) = true := by
  intro row mem
  simp only [series,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> apply coordinates_of_neighbor_volumes <;> decide +kernel

/-- All seven published locant sequences and exact uppercase/lowercase letters
are returned by the public raw API on their materialized coordinate tables. -/
theorem seven_published_raw (row : SourceRow) (mem : row ∈ series) :
    (RingHydrogenReport.fromRaw? molecule (faceSpatial row.mask) (row.locants.map Fin.val)).bind actualLetters =
      some row.expected := by
  have h := raw_letters (faceInput row.mask) base_graph (series_admitted row mem) row.locants
  change (RingHydrogenReport.fromRaw? molecule (faceSpatial row.mask) _).bind actualLetters = _ at h
  change _ = row.locants.mapM (fun r => (assign? (geometry (faceSpatial row.mask)) r).bind
    fun a => (reading a.profile a.center).label) at h
  rw [face_geometry] at h
  exact h.trans (BlueBookHexachlorocyclohexaneSeries.seven_published_reports row mem)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 5000000 in
/-- Example 3 on its separately supplied, explicitly written coordinate table,
in ring-atom order C-1 through C-6. -/
theorem example_three_raw :
    (RingHydrogenReport.fromRaw? molecule BlueBookHexachlorocyclohexane.spatial [0,1,2,3,4,5]).bind actualLetters =
      some [.chiral .R,.chiral .R,.chiral .R,.chiral .R,.chiral .S,.chiral .S] := by
  have admitted : LocalizedChemicalRing.coordinatesAdmitted base = true :=
    coordinates_of_neighbor_volumes _ (by decide +kernel)
  have result := raw_letters base base_graph admitted (List.finRange 6)
  change (RingHydrogenReport.fromRaw? molecule BlueBookHexachlorocyclohexane.spatial [0,1,2,3,4,5]).bind actualLetters =
    (List.finRange 6).mapM (fun r => (assign? BlueBookHexachlorocyclohexane.geometry r).bind
      fun a => (reading a.profile a.center).label) at result
  exact result.trans (by decide +kernel)

end TetraStereo.Examples.HexachlorocyclohexanePublicReport
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicReport.raw_agreement
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicReport.supported_carbon
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicReport.seven_published_raw
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicReport.example_three_raw
