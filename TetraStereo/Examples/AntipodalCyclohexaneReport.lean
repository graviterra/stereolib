import TetraStereo.Examples.AntipodalCyclohexaneRanking
import TetraStereo.Examples.AntipodalCyclohexaneTransport

/-! Complete public reports for fully written cyclohexane-1,4-diol from the
two ordered local tetrahedral determinants. -/
set_option autoImplicit false
namespace TetraStereo.Examples.AntipodalCyclohexaneReport
open Engine OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingGroupedTrials (atom)
open RingGroupedReport (origin)
open RingFullPathTrialReadings (trialKey trials Outcome hand?)
open RingNestedActivePair (Frame Reader)
open RingFullPathPublication (Ballots crossed)
open AntipodalCyclohexaneHands (molecule frameRow opposite)
open AntipodalCyclohexaneTransport (Selected)
open RingWrittenPHReadings (geometry)
open private frame_perm from TetraStereo.Examples.DecalinFrames
open private lift_row graphRows from TetraStereo.Examples.AntipodalCyclohexaneHands
open private swap_middle from TetraStereo.Examples.DecalinPathSwap
open private keys_exact from TetraStereo.Engine.RingFullPathPublication
open private closed atom_bound from TetraStereo.Examples.AntipodalCyclohexaneTransport
open private row? from TetraStereo.Engine.RingChemicalReport
open private toAtom from TetraStereo.Engine.RingAtomicNeighborOrder

private def other (r : Fin 2) : Fin 2 := ⟨1-r.val,by omega⟩
open AntipodalCyclohexaneRanking (ranked)
open AntipodalCyclohexaneWords (publicRead)

private def vote (near far : RS) : RS := if far = .R then near.swap else near

private theorem physical (g : Geometry) (r : Fin 2) (near far : RS)
    (seen : readback? g (frameRow (other r)) = some near) (rev : Bool) :
    readback? (if rev then mirror g else g) (ranked r (if rev then far.swap else far)) =
      some (vote near far) := by
  fin_cases r <;> cases near <;> cases far <;> cases rev <;>
    dsimp [ranked,AntipodalCyclohexaneWords.ringArm,other,frameRow,RS.swap,vote] at * <;>
    (try rw [readback_mirror]) <;>
    first | exact seen | (rw [seen]; done) | (rw [seen]; rfl) | (rw [swap_middle,seen]; done) | (rw [swap_middle,seen]; rfl)

private theorem rank_facts : ∀ (r : Fin 2) (h : RS),
    (ranked r h).Perm (frameRow (other r)) ∧
    (ranked r h).Pairwise (fun a b => (ranked r h).idxOf a < (ranked r h).idxOf b) := by
  intro r h
  fin_cases r <;> cases h <;> decide +kernel

/-- A strict physical ligand order leaves exactly one ordinary ballot and
therefore no promoted-atom trials. -/
private theorem strict_ballot {i : Input} {q : RingActivePairs.Site i} (fr : Frame i q)
    (read : Reader i) (ready : RingGroupedStereo.Ready q read) (rev : Bool)
    (priority : List Nat) (all : priority.Perm (fr.atoms (List.finRange 4)))
    (ascending : priority.Pairwise (fun a b => priority.idxOf a < priority.idxOf b))
    (cmp : ∀ ks, RingFullPathPublication.keys? fr read rev = some ks → ∀ a b,
      compare (trialKey (ks a) []) (trialKey (ks b) []) =
        compare (priority.idxOf (atom fr b)) (priority.idxOf (atom fr a)))
    (vote : RS) (sense : readback? (if rev then mirror (geometry i.spatial) else geometry i.spatial) priority = some vote) :
    ∃ ks, Ballots fr read rev ks [some vote] := by
  obtain ⟨ks,got,reads⟩ := keys_exact fr ready rev
  let w (s : Fin 4) := trialKey (ks s) []
  obtain ⟨row,ids,perm⟩ := lift_row (atom fr) all
  have rankedRow : row.Pairwise (fun a b => w b < w a) := by
    have asc : (row.map (atom fr)).Pairwise (fun a b => priority.idxOf a < priority.idxOf b) := ids ▸ ascending
    apply (List.pairwise_map.mp asc).imp
    intro a b ab
    apply (DeclarativeCIP.compareLex_eq_lt_iff_of compare RingFullPathConstitution.word_lt
      (fun _ _ => Std.compare_eq_eq_iff_eq) _ _).mp
    exact (cmp ks got b a).trans (Nat.compare_eq_lt.mpr ab)
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
  rwa [←ids]

def label (a b : RS) : RingNestedActivePair.Labels :=
  let d := LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric (if a = b then .s else .r)
  (d,d)

private theorem opposite_other (r : Fin 2) : opposite (other r) = 3*r.val := by fin_cases r <;> decide

theorem junction {i : Input} (raw : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (r : Fin 2) (atRoot : root.val = 3*r.val) (near far : RS)
    (localSense : readback? (geometry i.spatial) (frameRow (other r)) = some near)
    (remote : readback? (geometry i.spatial) (frameRow r) = some far) :
    RingChemicalGraphProof.root i root = some (some (label near far)) := by
  let q := origin i root
  have ids : root.val = opposite (other r) := atRoot.trans (opposite_other r).symm
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor root) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,raw,ids]
    exact (graphRows (other r)).length_eq.trans (by unfold frameRow; split <;> rfl)
  let c : i.certified.TetrahedralCenter := ⟨root,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr degree⟩
  have recg := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mpr ⟨rfl,rfl⟩
  obtain ⟨fr,_⟩ := RingGroupedGeometry.frame_exists recg
  have ballot (rev : Bool) : ∃ ks, Ballots fr (publicRead i root) rev ks [some (vote near far)] := by
    let h := if rev then far.swap else far
    obtain ⟨phys,asc⟩ := rank_facts r h
    have all := frame_perm fr
    have focus : root = fr.center.val := Option.some.inj
      ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2
    rw [raw,←focus,ids] at all
    exact strict_ballot fr _ (RingChemicalGraphProof.ready geom _) rev _ (phys.trans ((graphRows _).symm.trans all.symm))
      asc (AntipodalCyclohexaneRanking.frame_order raw geom root r atRoot fr far remote rev) _ (physical _ r near far localSense rev)
  obtain ⟨x,hx⟩ := ballot false
  obtain ⟨y,hy⟩ := ballot true
  have both := RingFullPathPublication.TwoGeometry.centre hx hy
  have out : crossed [some (vote near far)] [some (vote near far)] = some (label near far) := by
    cases near <;> cases far <;> rfl
  rw [out] at both
  have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) root degree
  have noP : RingPyramidalPublication.focusP i q = none := by
    change (some root).filter (RingPyramidalPublication.phosphorus i) = none
    simp [off]
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i),←RingChemicalGraphProof.state,
    RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,noP,
    RingFullPathConstitution.fast_local geom (RingChemicalGraphProof.ready geom _)]
  exact (RingFullPathPublication.two_geometry_iff geom _ _ (RingChemicalGraphProof.ready geom _) _).mpr both

/-- The determinant specification rejects invalid atom IDs and reports both
readings of the same lowercase letter at atoms 0 and 3. -/
def expected? (x : SpatialConfiguration) (ids : List Nat) : Option RingGroupedReport.Report := do
  guard (ids.all (· < 20))
  let a ← readback? (geometry x) (frameRow 0)
  let b ← readback? (geometry x) (frameRow 1)
  return ids.map fun n => (n,if n = 0 ∨ n = 3 then some (label a b) else none)

theorem raw_agreement (i : Input) (raw : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids = expected? i.spatial ids := by
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (AntipodalCyclohexaneHands.nonflat raw geom 0)
  obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp (AntipodalCyclohexaneHands.nonflat raw geom 1)
  by_cases good : ids.all (· < 20) = true
  · let vs := ids.attach.map fun n => toAtom i n.val (by rw [raw]; exact of_decide_eq_true (List.all_eq_true.mp good _ n.property))
    have resolved : vs.map Fin.val = ids := by simp [vs,List.map_map,Function.comp_def,toAtom]
    have native := RingWrittenPHReadings.fromRaw_closed_report i (raw ▸ closed) geom vs
    rw [raw,resolved] at native
    rw [native]
    have rows (v : i.certified.Atom) :
        row? v = some (v.val,if v.val = 0 ∨ v.val = 3 then some (label a b) else none) := by
      by_cases sel : Selected v.val
      · have out : RingChemicalGraphProof.root i v = some (some (label a b)) := by
          rcases sel with eq|eq
          · have xf := junction raw geom v 0 eq b a hb ha
            have symm : label b a = label a b := by cases a <;> cases b <;> rfl
            exact symm ▸ xf
          · exact junction raw geom v 1 eq a b ha hb
        simp [row?,out,show v.val = 0 ∨ v.val = 3 from sel]
      · simp [row?,AntipodalCyclohexaneTransport.unselected raw geom v sel,
          show ¬ (v.val = 0 ∨ v.val = 3) from sel]
    simp only [expected?,good,ha,hb,guard_true,pure,bind,Option.bind_some]
    rw [←resolved,List.map_map]
    change vs.mapM row? = some (vs.map _)
    induction vs with
    | nil => rfl
    | cons v vs ih => simp [List.mapM_cons,rows,ih,Function.comp_def]
  · have absent : RingMolecularReport.resolve i ids = none := by
      cases h : RingMolecularReport.resolve i ids with
      | none => rfl
      | some vs =>
        exfalso
        apply good
        rw [← (RingMolecularReport.resolve_iff ..).mp h]
        apply List.all_eq_true.mpr
        intro n hn
        obtain ⟨v,_,rfl⟩ := List.mem_map.mp hn
        exact decide_eq_true (atom_bound raw v)
    have accepted := RingSpatialTransport.readmit i
    rw [raw] at accepted
    simp [RingHydrogenReport.fromRaw_closed_eq closed,RingChemicalReport.fromRaw?,accepted,absent,expected?,good]

/-- Both selected carbons publish the same pseudoasymmetric descriptor on
the actual and mirrored readings. -/
theorem raw_pair (i : Input) (raw : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (a b : RS)
    (ha : readback? (geometry i.spatial) (frameRow 0) = some a)
    (hb : readback? (geometry i.spatial) (frameRow 1) = some b) :
    RingHydrogenReport.fromRaw? molecule i.spatial [0,3] =
      some [(0,some (label a b)),(3,some (label a b))] := by
  rw [raw_agreement i raw geom]
  simp [expected?,ha,hb]

end TetraStereo.Examples.AntipodalCyclohexaneReport
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneReport.junction
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneReport.raw_agreement
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneReport.raw_pair
