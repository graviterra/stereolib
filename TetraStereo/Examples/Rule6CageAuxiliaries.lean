import TetraStereo.Engine.RingPromotionOrder
import TetraStereo.Engine.RingCarbonReport

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace TetraStereo.Examples.Rule6CageAuxiliaries
open OneCenter Engine.RingChemicalPriority LocalizedGenericMarkedRecalculation

/-- The three cage carbons are joined cyclically by O–CH₂ paths. The order of
the two atoms on each path distinguishes the two ways around the perimeter. -/
def cage : RawMolecule where
  atoms := (List.replicate 4 Element.C ++ List.replicate 3 Element.O ++ List.replicate 3 Element.C ++
    List.replicate 10 Element.H).map AtomSpec.aliphatic
  bonds := (([(0,10)] : List (Nat × Nat)) ++ (List.range 3).flatMap (fun k =>
    [(0,1+k),(1+k,4+k),(4+k,7+k),(7+k,1+(k+1)%3),(1+k,11+k),(7+k,14+2*k),(7+k,15+2*k)]))
    |>.map fun (a,b) => ⟨a,b,.single⟩
def xyz : SpatialConfiguration := ⟨[⟨0,0,0⟩,⟨3,0,0⟩,⟨0,3,0⟩,⟨0,0,3⟩,
  ⟨4,1,1⟩,⟨1,4,1⟩,⟨1,1,4⟩,⟨2,3,1⟩,⟨1,2,3⟩,⟨3,1,2⟩,⟨-1,-1,-1⟩,
  ⟨5,-2,-3⟩,⟨-3,5,-2⟩,⟨-2,-3,5⟩,⟨2,4,3⟩,⟨2,4,0⟩,⟨3,2,4⟩,⟨0,2,4⟩,⟨4,3,2⟩,⟨4,0,2⟩]⟩

/-- Replace the bridgehead hydrogen on each cage by a bond to carbon zero.
The two copies are geometrical enantiomorphs. The remaining ligands of carbon
zero are fluorine and hydrogen. All atom indices and hydrogens are explicit. -/
def cageIndex (side i : Nat) := 3 + 19 * side + (if i < 10 then i else i-1)

private def withoutBridgeheadH {α : Type} (xs : List α) := xs.take 10 ++ xs.drop 11

def twins : RawMolecule where
  atoms := [.aliphatic .C,.aliphatic .F,.aliphatic .H] ++
    withoutBridgeheadH cage.atoms ++ withoutBridgeheadH cage.atoms
  bonds := [⟨0,1,.single⟩,⟨0,2,.single⟩] ++ [0,1].flatMap fun side =>
    ⟨0,cageIndex side 0,.single⟩ :: cage.bonds.filterMap fun b =>
      if b.source = 10 ∨ b.target = 10 then none
      else some ⟨cageIndex side b.source,cageIndex side b.target,b.kind⟩

private def shift (v : CartesianPoint3) : CartesianPoint3 := ⟨v.x+4,v.y+4,v.z+4⟩
def twinGeometry : Geometry :=
  let left := (withoutBridgeheadH xyz.positions).map shift
  fun i => ([⟨0,0,0⟩,⟨0,-2,1⟩,⟨0,1,-2⟩] ++ left ++ left.map CartesianPoint3.reflectX)[i]?

def exchange (i : Nat) := if i < 3 then i else if i < 22 then i+19 else i-19
/-- The arm exchange is an actual molecular reflection. It fixes the central
carbon, fluorine and hydrogen and exchanges the complete decorated cages. -/
theorem molecular_reflection :
    twins.atomCount = 41 ∧ exchange 0 = 0 ∧ exchange 1 = 1 ∧ exchange 2 = 2 ∧ exchange 3 = 22 ∧
    (∀ i : Fin 41, exchange (exchange i) = i ∧
      twins.atoms[exchange i]? = twins.atoms[i.val]? ∧ twinGeometry (exchange i) = mirror twinGeometry i) ∧
    ∀ i j : Fin 41, twins.bondOrder (exchange i) (exchange j) = twins.bondOrder i j := by decide +kernel

/-- Positive integer barycentric weights for the central carbon, both
bridgeheads, and the peripheral carbons and methylenes. -/
def ligandWeight (i j : Nat) : Nat :=
  if i = 0 then (if j = 1 ∨ j = 2 then 8 else 1)
  else if i = 3 ∨ i = 22 then (if j = 0 then 3 else 4)
  else 1

def inside (i : Nat) : Prop :=
  let ns := twins.writtenNeighbors i
  ns.length = 4 ∧ (readback? twinGeometry ns).isSome = true ∧
  ∀ k : Fin 3,
    let coord (v : CartesianPoint3) := if k = 0 then v.x else if k = 1 then v.y else v.z
    let w (j : Nat) : ℚ := ligandWeight i j
    (ns.mapM (fun j => (twinGeometry j).map fun v => w j * coord v)).map List.sum =
      (twinGeometry i).map (fun v => (ns.map w).sum * coord v)

instance (i : Nat) : Decidable (inside i) := by unfold inside; infer_instance

theorem carbon_frames_interior :
    (∀ i j : Nat, 0 < ligandWeight i j) ∧
    ∀ i : Fin 41, (twins.atoms[i.val]?).any (fun a => a.element == .C) = true →
      (twinGeometry i).isSome = true ∧ inside i := by
  constructor
  · intro i j
    unfold ligandWeight
    split_ifs <;> decide
  · decide +kernel

def hints : List Nat → Option Recursive.Frame
  | [0] => some ⟨.five,1,3,22,2,exchange,false⟩
  | _ => none

def deriveTwin (p : List Nat) := Promotion.deriveAt twins twinGeometry hints (fun _ => 2) 4 p

private def bridge (i : Nat) := Promotion.checkAt? twins twinGeometry [0,i] 1
  (Promotion.deriveAt twins twinGeometry hints (fun _ => 2) 1)

private def bridgeSummary (i : Nat) := (bridge i).map fun c =>
  ((c.actual,c.reflected), c.trials.map (fun t => (t.mark,t.order)))

theorem left_promotions : bridgeSummary 3 = some ((some .S,some .R),
    [(4,[0,4,6,5]),(5,[0,5,4,6]),(6,[0,6,5,4])]) := by decide +kernel

theorem right_promotions : bridgeSummary 22 = some ((some .R,some .S),
    [(23,[0,23,25,24]),(24,[0,24,23,25]),(25,[0,25,24,23])]) := by decide +kernel

private theorem bridge_justified {i a b orders} (ok : bridgeSummary i = some ((some a,some b),orders)) :
    Promotion.Justified twins twinGeometry [0,i] ⟨a,b⟩ := by
  obtain ⟨c,_,eq⟩ := Option.map_eq_some_iff.mp ok
  obtain ⟨raw,_⟩ := Prod.mk.inj eq
  obtain ⟨actual,mirrored⟩ := Prod.mk.inj raw
  exact .promotion c.experiment c.children c.allTrials
    (c.actualResult.trans (congrArg some actual)) (c.reflectedResult.trans (congrArg some mirrored))

private def descriptors (i : Nat) (bridgeHand peripheral : RS) : Recursive.Facts := Id.run do
  let some n := occurrence? twins [0,i] | return []
  let some qs := carbonSites twins (twins.atomCount+1) n | return []
  return qs.map fun p =>
    let hand := if p = [0,i] then bridgeHand else peripheral
    (p,⟨hand,hand.swap⟩)

private def left := descriptors 3 .S .R
private def right := descriptors 22 .R .S

private def atomicRead (p : List Nat) : Option Recursive.Reading := do
  let order ← atomicOrder? twins p 2
  Recursive.geometric twinGeometry order order

private theorem atomic_proof {p r} (h : atomicRead p = some r) :
    Promotion.Justified twins twinGeometry p r := by
  unfold atomicRead at h
  cases order : atomicOrder? twins p 2 with
  | none => simp [order] at h
  | some atoms => exact .ordinary (.atomic order (by simpa [order] using h))

private theorem left_children : ∀ x ∈ left,
    x = ([0,3],⟨.S,.R⟩) ∨ atomicRead x.1 = some x.2 := by decide +kernel

private theorem right_children : ∀ x ∈ right,
    x = ([0,22],⟨.R,.S⟩) ∨ atomicRead x.1 = some x.2 := by decide +kernel

private def middle : Recursive.Frame := ⟨.five,1,3,22,2,exchange,false⟩

/-- Rule 5 uses both Rule 6 bridgehead descriptors from this very digraph. The
root has a positive lowercase r assignment: its raw reading is R on both sides. -/
theorem twin_chemical_proof : Promotion.Justified twins twinGeometry [0] ⟨.R,.R⟩ := by
  apply Promotion.Justified.stereo (d := 2) (f := middle) (ls := left) (rs := right)
  · decide +kernel
  · intro x hx
    rcases left_children x hx with rfl | leaf
    · exact bridge_justified left_promotions
    · exact atomic_proof leaf
  · intro x hx
    rcases right_children x hx with rfl | leaf
    · exact bridge_justified right_promotions
    · exact atomic_proof leaf

/-- Both rings of spiro[2.2]pentane consist of two CH₂ groups sharing the
central carbon. The four root ligands tie, and every promotion leaves a tie. -/
def spiroPentane : RawMolecule where
  atoms := List.replicate 5 (AtomSpec.aliphatic .C) ++ List.replicate 8 (AtomSpec.aliphatic .H)
  bonds := (([(0,1),(0,2),(1,2),(0,3),(0,4),(3,4)] : List (Nat × Nat)) ++
    (List.range 4).flatMap fun i => [(i+1,5+2*i),(i+1,6+2*i)]).map fun (a,b) => ⟨a,b,.single⟩

private def spiroTest := Promotion.checkAt? spiroPentane (fun _ => none) [0] 0 (fun _ => none)

/-- A graph-only refusal on this four-way ring is valid for every geometry. -/
theorem spiroPentane_no_descriptor :
    ∃ e : Promotion.Experiment spiroPentane [0], ∃ ts : List Promotion.Trial,
      (∀ a ∈ e.arms, a.facts = []) ∧ e.trials? = some ts ∧ ts.map (·.mark) = [1,2,3,4] ∧
      ∀ g, Promotion.result g ts = some none := by
  have ok : (spiroTest.map fun c =>
      (c.experiment.arms.all (fun a => a.facts.isEmpty),c.trials.map (·.mark),
        c.trials.all (fun t => !t.unique))) = some (true,[1,2,3,4],true) := by decide +kernel
  obtain ⟨c,_,row⟩ := Option.map_eq_some_iff.mp ok
  obtain ⟨empty,data⟩ := Prod.mk.inj row
  obtain ⟨marks,tied⟩ := Prod.mk.inj data
  refine ⟨c.experiment,c.trials,?_,c.allTrials,marks,?_⟩
  · simpa using empty
  · exact Promotion.result_of_tied (by simpa using tied)

private def rootRefusal : Option (Option (List Nat)) := (RingAuxiliaryInventory.classify? spiroPentane (fun _ => none)
  (fun _ => none) (fun _ => 0) 1 [0]).map fun
    | .promotionTie c => some (c.structural.trials.map Promotion.Trial.mark)
    | _ => none

/-- Every choice of promoted neighbor at C0 leaves a fully matched pair. -/
theorem central_promotion_refusal : rootRefusal = some (some [1,2,3,4]) := by decide +kernel

private theorem root_label :
    (Engine.RingCarbonReport.atCarbon? spiroPentane (fun _ => none) 1 (fun _ => none)
      (fun _ => 0) 0).map Engine.RingCarbonReport.Verdict.label = some none := by
  apply Eq.trans (Engine.RingCarbonReport.atCarbon?_label_of_no_hydrogens
    (by decide +kernel) (by decide +kernel) (by decide +kernel))
  generalize val : RingAuxiliaryInventory.classify? spiroPentane (fun _ => none)
    (fun _ => none) (fun _ => 0) 1 [0] = v
  have h := central_promotion_refusal
  simp only [rootRefusal,val] at h
  cases v with
  | none => simp at h
  | some r => cases r <;> first | rfl | simp at h

/-- All five carbon roots of spiro[2.2]pentane are included even without
coordinates. C0 has a structural Rule 6 refusal. Each CH₂ root has a
separate pair of identical terminal hydrogens. -/
theorem spiroPentane_carbon_report :
    (Engine.classifyRingCarbons? spiroPentane (fun _ => none) 1 (fun _ => none) (fun _ => 0)).map
      Engine.RingCarbonReport.Report.labels =
        some [(0,none),(1,none),(2,none),(3,none),(4,none)] := by
  have ids : Engine.RingCarbonReport.carbons spiroPentane = [0,1,2,3,4] := by decide +kernel
  have domain : saturatedWithHalogens spiroPentane = true := by decide +kernel
  have result := Engine.classifyRingCarbons?_labels_of_rows
    (g := (fun _ => none)) (fuel := 1) (hint := fun _ => none) (radius := fun _ => 0)
    (fun _ => none) domain (fun i hi => by
      rw [ids] at hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact root_label
      all_goals apply Engine.RingCarbonReport.atCarbon?_label_of_hydrogens domain <;> decide +kernel)
  simpa only [ids] using result

end TetraStereo.Examples.Rule6CageAuxiliaries
assert_kernel_only TetraStereo.Examples.Rule6CageAuxiliaries.twin_chemical_proof
assert_kernel_only TetraStereo.Examples.Rule6CageAuxiliaries.molecular_reflection
assert_kernel_only TetraStereo.Examples.Rule6CageAuxiliaries.carbon_frames_interior
assert_kernel_only TetraStereo.Examples.Rule6CageAuxiliaries.spiroPentane_no_descriptor
assert_kernel_only TetraStereo.Examples.Rule6CageAuxiliaries.central_promotion_refusal
assert_kernel_only TetraStereo.Examples.Rule6CageAuxiliaries.spiroPentane_carbon_report
