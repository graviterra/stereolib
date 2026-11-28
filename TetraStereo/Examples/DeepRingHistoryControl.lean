import TetraStereo.Examples.RingDeepHistoryComparison
import TetraStereo.Examples.DecalinPublishedCoordinates
import TetraStereo.Examples.DecalinEarlierTie
import TetraStereo.Examples.PairedCyclopropylDonorStore

/-! Deep constitutional comparisons on the unmodified, hydrogen-explicit
decalin graph of the two published cis/trans validation records. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DeepRingHistoryControl
open OneCenter Engine
open LocalizedChemicalRing (Input)
open RingGroupedReport (origin)
open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)
open RingNestedActivePair (Frame)
open DecalinFrames (molecule)
open DecalinAuxiliary (history)
open private frame_perm from TetraStereo.Examples.DecalinFrames
open private start from TetraStereo.Examples.DecalinEarlierTie
open private input211 input212 from TetraStereo.Examples.DecalinPublishedCoordinates
open private retainedKey twoShells_eq from TetraStereo.Examples.PairedCyclopropylDonorStore

/-- The deep strict comparison originates at a methylene, the full tie at
a fusion carbon. All four outward arms begin at a methylene carbon. -/
def focus (strict : Bool) : Fin 28 := if strict then 4 else 0
def secondArm (strict : Bool) : Nat := if strict then 5 else 6
private def neighbors (strict : Bool) : List Nat := if strict then [2,5,16,17] else [1,2,6,10]

private theorem rows (s : Bool) :
    (RingAtomicNeighborOrder.neighbors molecule (focus s).val).Perm (neighbors s) := by
  apply (RingStereoSiblingPass.legal_order _ _).perm.trans
  cases s <;> decide +kernel

theorem two_shells (s : Bool) :
    PairedCyclopropylDonorStore.twoShells molecule [(focus s).val] 2 = [[6],[6,1,1]] ∧
    PairedCyclopropylDonorStore.twoShells molecule [(focus s).val] (secondArm s) = [[6],[6,1,1]] := by
  rw [twoShells_eq]
  cases s <;> decide +kernel

/-- Each comparison uses distinct actual arms of a recognized four-slot frame.
Both original coordinate records admit such frames. -/
theorem actual_slots {i : Input} (raw : i.molecule = molecule) (s : Bool) :
    ∃ (v : i.certified.Atom) (fr : Frame i (origin i v)) (a b : Fin 4),
      v.val = (focus s).val ∧
      history (cursor fr a).occurrence = [2,(focus s).val] ∧
      history (cursor fr b).occurrence = [secondArm s,(focus s).val] ∧
      atom fr a = 2 ∧ atom fr b = secondArm s ∧ a ≠ b := by
  let v : i.certified.Atom := (RingHydrogenSpelling.rawVertices i raw).symm (focus s)
  have hv : v.val = (focus s).val := rfl
  have deg : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,raw,hv,(rows s).length_eq]
    cases s <;> rfl
  let t : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr deg⟩
  have recognized := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff (origin i v) t).mpr ⟨rfl,rfl⟩
  obtain ⟨fr,_⟩ := RingGroupedGeometry.frame_exists recognized
  have centre : v = fr.center.val := Option.some.inj
    ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2
  have ids := frame_perm fr
  rw [raw,←centre,hv] at ids
  have members : ((List.finRange 4).map (atom fr)).Perm (neighbors s) := ids.trans (rows s)
  obtain ⟨a,_,ha⟩ := List.mem_map.mp (members.mem_iff.mpr (show 2 ∈ neighbors s by cases s <;> decide))
  obtain ⟨b,_,hb⟩ := List.mem_map.mp (members.mem_iff.mpr
    (show secondArm s ∈ neighbors s by cases s <;> decide))
  exact ⟨v,fr,a,b,hv,by rw [start,ha,hv],by rw [start,hb,hv],ha,hb,
    fun eq => (show 2 ≠ secondArm s by cases s <;> decide) (ha.symm.trans (eq ▸ hb))⟩

theorem source_inputs :
    ∀ g ∈ [DecalinPublishedCoordinates.vs211,DecalinPublishedCoordinates.vs212],
      ∃ i : Input, LocalizedChemicalRing.admitRawSpatial? molecule g = some i ∧
        LocalizedChemicalRing.coordinatesAdmitted i = true := by
  intro g mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl
  · exact ⟨input211,(Option.some_get _).symm,DecalinPublishedCoordinates.source_admitted.1⟩
  · exact ⟨input212,(Option.some_get _).symm,DecalinPublishedCoordinates.source_admitted.2⟩

open RingRetainedChemicalTrace (Key Observation WellFormed assemble)
open private Valid pack collect checked from TetraStereo.Engine.RingLigandTreeComparison
open private column_eq from TetraStereo.Examples.DecalinAuxiliary
open RingDeepHistoryPathOrder (Edge observation? tree children)

private def combine (o : Observation) (ks : List Valid) : Valid :=
  let cs := ks.map Subtype.val
  let k : Key := ⟨o,DecalinAuxiliary.column o cs .atomic,DecalinAuxiliary.column o cs .duplicate,
    DecalinAuxiliary.column o cs .mass⟩
  ⟨k,by
    have same : k = (pack o ks).val := by simp [k,cs,pack,assemble,column_eq]
    exact same ▸ (pack o ks).property⟩

private theorem pack_eq (o : Observation) (ks : List Valid) : pack o ks = combine o ks := by
  apply Subtype.ext
  simp [pack,assemble,column_eq,combine]

private def fold (m : RawMolecule) : Nat → Edge → Option Valid
  | 0,_ => none
  | n+1,e => (observation? m e).bind fun o => ((children m e).mapM (fold m n)).map (combine o)

private theorem fold_exact (m : RawMolecule) (n : Nat) (e : Edge) :
    checked n (tree m n e) = fold m n e := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
    change ((observation? m e).bind fun o => (((children m e).map (tree m n)).mapM (checked n)).map (pack o)) = _
    have packing : pack = combine := funext fun o => funext (pack_eq o)
    simp only [List.mapM_map,Function.comp_def,packing,ih,fold]

private theorem raw_key (m : RawMolecule) (p h : List Nat) :
    RingDeepHistoryPathOrder.key? m p h =
      (fold m (2 * (m.atomCount + 1 + 1) + 1) (p,h)).map Subtype.val := by
  unfold RingDeepHistoryPathOrder.key? RingLigandTreeComparison.reconstruct
  exact congrArg (Option.map Subtype.val) (fold_exact m _ (p,h))

/-- The first two atomic spheres coincide. The first group of the third
sphere contains C,C,H through atom 2 and C,H,H through atom 5. -/
private def firstThree (a : Nat) :=
  (RingDeepHistoryPathOrder.key? molecule [4] [a,4]).map fun k => k.atomic.word.take 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem first_difference :
    firstThree 2 = some [[6],[6,1,1],[6,1,1],[6,6,1]] ∧
    firstThree 5 = some [[6],[6,1,1],[6,1,1],[6,1,1]] := by
  unfold firstThree
  simp only [raw_key]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem deep_result (s : Bool) :
    RingDeepHistoryPathOrder.compare? molecule ([(focus s).val],[2,(focus s).val])
      ([(focus s).val],[secondArm s,(focus s).val]) = some (if s then .gt else .eq) := by
  unfold RingDeepHistoryPathOrder.compare?
  simp only [raw_key]
  cases s <;> decide +kernel

/-- Only this isotope control differs from the two published decalin records.
Replacing a single carbon by carbon-13 breaks the fusion-arm tie at mass. -/
def isotopeControl : RawMolecule :=
  {molecule with atoms := molecule.atoms.set 4 {AtomSpec.aliphatic .C with isotope? := some 13}}

private def stageOrders (m : RawMolecule) (p : List Nat) (a b : Nat) : Option (List Ordering) := do
  let x ← RingDeepHistoryPathOrder.key? m p (a::p)
  let y ← RingDeepHistoryPathOrder.key? m p (b::p)
  return [compare x.atomic.word y.atomic.word, compare x.duplicate.word y.duplicate.word,
    compare x.mass.word y.mass.word]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem remote_isotope : stageOrders isotopeControl [0] 2 6 = some [.eq,.eq,.gt] := by
  unfold stageOrders
  simp only [raw_key]
  decide +kernel

/-- Both closures end at carbon. Atom 3 closes to the root, atom 0 to a later
visited carbon on the very same path. Only the duplicate-origin column differs. -/
theorem closure_origins :
    let p := [1,8,9,7,6,0,2,4,5,3]
    p.Nodup ∧
      (p.zip p.tail).all (fun bond => 0 < molecule.bondOrder bond.1 bond.2) = true ∧
      0 < molecule.bondOrder 1 3 ∧ 0 < molecule.bondOrder 1 0 ∧
      stageOrders molecule p 3 0 = some [.eq,.gt,.eq] := by
  dsimp only
  unfold stageOrders
  simp only [raw_key]
  decide +kernel

/-- An actual frame of every structurally admitted decalin input realizes
both the deep strict order at atom 4 and the all-column tie at atom 0. -/
theorem molecular_result {i : Input} (raw : i.molecule = molecule) (s : Bool) :
    ∃ (v : i.certified.Atom) (fr : Frame i (origin i v)) (a b : Fin 4),
      v.val = (focus s).val ∧ atom fr a = 2 ∧ atom fr b = secondArm s ∧ a ≠ b ∧
      RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i (origin i v))
        (fr.direction a) (fr.direction b) = some (if s then .gt else .eq) := by
  obtain ⟨v,fr,a,b,id,path,other,ha,hb,ne⟩ := actual_slots raw s
  refine ⟨v,fr,a,b,id,ha,hb,ne,?_⟩
  rw [←RingDeepHistoryComparison.compare_exact]
  change RingDeepHistoryPathOrder.compare? i.molecule (history (origin i v),history (cursor fr a).occurrence)
    (history (origin i v),history (cursor fr b).occurrence) = _
  rw [raw,path,other]
  change RingDeepHistoryPathOrder.compare? molecule ([v.val],_) ([v.val],_) = _
  rw [id]
  exact deep_result s

end TetraStereo.Examples.DeepRingHistoryControl
assert_kernel_only TetraStereo.Examples.DeepRingHistoryControl.actual_slots
assert_kernel_only TetraStereo.Examples.DeepRingHistoryControl.source_inputs
assert_kernel_only TetraStereo.Examples.DeepRingHistoryControl.first_difference
assert_kernel_only TetraStereo.Examples.DeepRingHistoryControl.molecular_result
