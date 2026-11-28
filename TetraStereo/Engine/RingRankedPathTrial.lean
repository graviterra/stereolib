import TetraStereo.Engine.RingRule4bPathOrder
import TetraStereo.Engine.RingRule5PathOrder
import TetraStereo.Engine.RingTrialInventoryOrder
import TetraStereo.Engine.RingStereoInventoryReport
import TetraStereo.Engine.RingBinaryPairScore

/-! Compare entire ranked sphere tables at the two stereochemical pair rules.
The priority uses a single occurrence inventory per ligand and the trial's mark. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingRankedPathTrial
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Frame)
open RingActivePairReport (Slot)
open RingOrdinaryLigandInventory (Observation observe? assemble)
open RingRetainedChemicalTrace (Word)
open RingRule5Shape (Valid On)
open RingStereoSphereInventory (inventory? reading)
open RingSignedInventoryLayers (projectInventory)
open RingTrialInventoryOrder (observation? priority)
open private rank_projects from TetraStereo.Engine.RingStereoStageProjection

/-- The first non-tie is the result. The final field compares the active nominations. -/
def comparePaths (x y : Observation × Word) : Ordering :=
  let a := x.1
  let b := y.1
  (compare a.1.dropLast b.1.dropLast).then <|
    (compare (RingRule4bPathOrder.canonical (RingStereoStageProjection.inventory a.2))
      (RingRule4bPathOrder.canonical (RingStereoStageProjection.inventory b.2))).then <|
    (compare (a.1.getLast?.getD []) (b.1.getLast?.getD [])).then <|
    (compare (projectInventory .R a.2) (projectInventory .R b.2)).then (compare x.2 y.2)

private theorem fields {i : Input} {r : Reader i} {rev : Bool} {q : Arm i} {x : Observation}
    (obs : observe? i r rev q = some x) :
    RingUnitTypeTransitions.key i r rev q = x.1.dropLast ∧
    RingRule5Shape.key i r rev q = x.1 ∧
    x.1 = x.1.dropLast ++ [x.1.getLast?.getD []] ∧
    inventory? i r rev [.lowercase] q = some x.2 ∧
    inventory? i r rev [] q = some (RingStereoStageProjection.inventory x.2) := by
  obtain ⟨k,hk,rest⟩ := Option.bind_eq_some_iff.mp obs
  obtain ⟨z,hz,done⟩ := Option.bind_eq_some_iff.mp rest
  obtain rfl := Option.some.inj done
  obtain ⟨u,hu,deep⟩ := rank_projects i r rev q k hk
  exact ⟨by simp [RingUnitTypeTransitions.key,hu,deep],by simp [RingRule5Shape.key,hk],
    by simp [RingStereoSiblingPass.Branch.deep],hz,RingStereoStageProjection.inventory_projects i r rev q z hz⟩

/-- The proof uses equal earlier fields only after the direct comparison reaches
them. Earlier distinctions can decide immediately, including for unrelated ligands. -/
theorem agrees {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    {rev : Bool} {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    {x y : Observation} (hx : observe? i r rev a = some x) (hy : observe? i r rev b = some y) (m n : Word) :
    comparePaths (x,m) (y,n) = compare (priority (x,m)) (priority (y,n)) := by
  obtain ⟨ua,la,ax,hf,hc⟩ := fields hx
  obtain ⟨ub,lb,ay,jf,jc⟩ := fields hy
  simp only [comparePaths,priority,RingFullPathTrialReadings.trialKey,assemble,List.compare_cons_cons,
    RingBinaryPairScore.compare_bits,List.compare_nil_nil,Ordering.then_eq]
  by_cases early : x.1.dropLast = y.1.dropLast
  · have ties := ua.trans (early.trans ub.symm)
    rw [RingRule4bPathOrder.canonical_compare ready va vb oa ob ties hc jc]
    by_cases lower : x.1.getLast?.getD [] = y.1.getLast?.getD []
    · have same : x.1 = y.1 := ax.trans (by rw [early,lower,←ay])
      rw [RingRule5PathOrder.inventory_compare ready va vb oa ob (la.trans (same.trans lb.symm)) hf jf .R .R]
    · have ne := mt Std.compare_eq_eq_iff_eq.mp lower
      cases h : compare (x.1.getLast?.getD []) (y.1.getLast?.getD []) <;> first | rfl | exact (ne h).elim
  · have ne := mt Std.compare_eq_eq_iff_eq.mp early
    cases h : compare x.1.dropLast y.1.dropLast <;> first | rfl | exact (ne h).elim

/-- At every reached tetrahedral site this computes the direction of every public
ligand comparison, including ties, from the ranked paths and the nominated positions. -/
theorem public_order {i : Input} {f : Site i} (fr : Frame i f)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom} {batch : Nat}
    (called : RingGlobalComparison.Called i root batch f) :
    let r := RingGlobalComparison.prior i root batch
    ∃ out, RingResidualPairDecision.atSite? i root batch f = some out ∧
      ∀ t ∈ out, ∀ (rev : Bool) (a b : Slot),
        ∃ x y, observation? fr r rev t.nomination a = some x ∧ observation? fr r rev t.nomination b = some y ∧
          comparePaths x y = (t.table rev)[a.val][b.val].order ∧
          ((t.table rev)[a.val][b.val] = .tie ↔ x = y) := by
  intro r
  obtain ⟨out,found,ok⟩ := RingTrialInventoryOrder.public_pair fr geom called
  refine ⟨out,found,?_⟩
  intro t mem rev a b
  obtain ⟨x,y,hx,hy,comp,tie⟩ := ok t mem rev a b
  have ready : RingGroupedStereo.Ready f r := by
    dsimp [r]
    rw [RingGlobalComparison.prior_exact called]
    exact RingChemicalGraphProof.ready geom f
  have obs (s : Slot) (z : Observation × Word) (h : observation? fr r rev t.nomination s = some z) :
      observe? i r rev (RingGroupedCentre.cursor fr s) = some z.1 := by
    obtain ⟨u,hu,rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v,_,done⟩ := Option.bind_eq_some_iff.mp rest
    obtain rfl := Option.some.inj done
    exact hu
  exact ⟨x,y,hx,hy,(agrees ready (RingGroupedCentre.valid fr a) (RingGroupedCentre.valid fr b)
    (fr.direction a).property.1 (fr.direction b).property.1 (obs a x hx) (obs b y hy) x.2 y.2).trans comp,tie⟩

/-- Compute the comparison from the inventory evaluator's own preceding sphere
store. The only trial input beyond the molecular frame is the nominated slot. -/
def atCut? {i : Input} {f : Site i} (fr : Frame i f) (root : i.certified.Atom) (cut : Nat)
    (rev : Bool) (nomination : Option Slot) (a b : Slot) : Option Ordering := do
  let rows := RingStereoInventoryReport.rows i root cut
  let r := RingSphereQueue.reader root (RingSphereQueue.viewOf rows)
  let x ← observation? fr r rev nomination a
  let y ← observation? fr r rev nomination b
  return comparePaths x y

/-- Both the ordered rows and every trial direction agree at every reached cut.
The independent side supplies its own previously computed auxiliary hands. -/
theorem sphere_order {i : Input} {f : Site i} (fr : Frame i f)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom} (cut : Nat)
    (called : RingGlobalComparison.Called i root (RingActiveDistanceSchedule.height i + 1 - cut) f) :
    let batch := RingActiveDistanceSchedule.height i + 1 - cut
    RingStereoInventoryReport.rows i root cut = RingSphereStore.rows i root batch ∧
      ∃ out, RingResidualPairDecision.atSite? i root batch f = some out ∧
        ∀ t ∈ out, ∀ (rev : Bool) (a b : Slot),
          atCut? fr root cut rev t.nomination a b = some ((t.table rev)[a.val][b.val].order) := by
  dsimp only
  have rows := RingStereoInventoryReport.rows_exact i root cut
  obtain ⟨out,found,allTrials⟩ := public_order fr geom called
  refine ⟨rows,out,found,?_⟩
  intro t mem rev a b
  obtain ⟨x,y,hx,hy,cmp,_⟩ := allTrials t mem rev a b
  unfold atCut?
  rw [rows]
  change (do
    let x ← observation? fr (RingGlobalComparison.prior i root _) rev t.nomination a
    let y ← observation? fr (RingGlobalComparison.prior i root _) rev t.nomination b
    pure (comparePaths x y)) = _
  simp [hx,hy,cmp]

end TetraStereo.Engine.RingRankedPathTrial
assert_kernel_only TetraStereo.Engine.RingRankedPathTrial.public_order
assert_kernel_only TetraStereo.Engine.RingRankedPathTrial.sphere_order
