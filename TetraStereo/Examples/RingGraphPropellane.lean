import TetraStereo.Engine.RingComparisonAgreement
import TetraStereo.Examples.LocalizedChemicalRingPropellaneLifetime

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option Elab.async false

namespace TetraStereo.Examples.RingGraphPropellane
open TetraStereo.OneCenter TetraStereo.Engine TetraStereo.Examples
open RingChemicalPriority LocalizedGenericMarkedRecalculation

private abbrev mol := LocalizedChemicalRingPropellaneLifetime.parsedMol
private def geom : Geometry := fun i => LocalizedChemicalRingPropellaneLifetime.spatial.positions[i]?

private def handAt (g : Geometry) (p : List Nat) : Option RS := do
  let rank ← IsotopePriority.rank? mol p
  readback? g rank.order

private def observe (g : Geometry) (p : List Nat) (a b other : Nat) := do
  let cmp ← IsotopePriority.compareIncident? mol p a b
  let x ← handAt g (p ++ [a,other])
  let y ← handAt g (p ++ [b,other])
  return (cmp.ordering,x,y,CentresRing.PairList.singletonValue x y)

private def six (g : Geometry) := [(2,4,3),(3,4,2),(4,3,2)].flatMap fun (root,l,r) =>
  [observe g [root,0] l r 1, observe g [root,1] l r 0]

private def derived (g : Geometry) (ps : List (List Nat)) : Option InventoryPriority.Entries := ps.mapM fun p => do
  let d ← ReferenceDerivation.derive? mol g 3 4 p
  return (p,d.verdict)

private def assigned (es : InventoryPriority.Entries) := es.filterMap fun x => x.2.map fun v => (x.1,v.actual)

private structure ArmResult where
  left : Nat
  right : Nat
  ruleFive : Bool
  actualLeftWins : Bool
  reflectedLeftWins : Bool
  leftHands : List (List Nat × RS)
  rightHands : List (List Nat × RS)
  deriving DecidableEq

private def complete (g : Geometry) (p : List Nat) : Option ArmResult := do
  let f ← SignedPair.frame? mol p 3
  let l ← derived g f.leftPaths
  let r ← derived g f.rightPaths
  let step ← DiscoveredPriority.check? f l r
  return ⟨f.left.ligand,f.right.ligand,step.basis.five,step.actualWins,step.reflectedWins,
    assigned l,assigned r⟩

/-- The six ordered bridge comparisons have tied constitutional keys. The strict
constitutional orders at the deeper occurrences give the indicated coordinate hands. -/
theorem six_scores :
    let neg := some (Ordering.eq,RS.S,RS.R,(-2 : Int))
    let pos := some (Ordering.eq,RS.R,RS.S,(2 : Int))
    six geom = [neg,pos,pos,neg,neg,pos] ∧
    six (mirror geom) = [pos,neg,neg,pos,pos,neg] := by
  constructor <;> decide +kernel

/-- Every candidate on both arms is evaluated recursively. Exactly one assignment
survives on each side. The checked earlier-rule comparison permits the order to
reverse on reflection at this particular auxiliary focus. -/
theorem complete_arms :
    complete geom [2,0] = some ⟨3,4,true,true,false,[([2,0,3,1],RS.R)],[([2,0,4,1],RS.S)]⟩ := by
  decide +kernel

/-- Read the complete two-arm certificate in the requested operand order. Both
singleton paths must belong to their own arm, and the two geometric winners must
agree with the Rule 5 sign and its reflection. -/
private def comparison (g : Geometry) (focus : List Nat) (left right distal : Nat) : Option Int := do
  let c ← complete g focus
  guard c.ruleFive
  let (ls,rs,wins,reflected) ←
    if (c.left,c.right) = (left,right) then some (c.leftHands,c.rightHands,c.actualLeftWins,c.reflectedLeftWins)
    else if (c.right,c.left) = (left,right) then some (c.rightHands,c.leftHands,!c.actualLeftWins,!c.reflectedLeftWins)
    else none
  let [(lp,lh)] := ls | none
  let [(rp,rh)] := rs | none
  guard (lp = focus ++ [left,distal] ∧ rp = focus ++ [right,distal])
  let score := CentresRing.PairList.singletonValue lh rh
  guard (wins = decide (0 < score) ∧ reflected = decide (score < 0))
  return score

private def completeScores (g : Geometry) := [(2,4,3),(3,4,2),(4,3,2)].flatMap fun (root,l,r) =>
  [comparison g [root,0] l r 1, comparison g [root,1] l r 0]

theorem all_six_complete :
    completeScores geom = [some (-2),some 2,some 2,some (-2),some (-2),some 2] ∧
    completeScores (mirror geom) = [some 2,some (-2),some (-2),some 2,some 2,some (-2)] := by
  constructor <;> decide +kernel

end TetraStereo.Examples.RingGraphPropellane

assert_kernel_only TetraStereo.Examples.RingGraphPropellane.six_scores
assert_kernel_only TetraStereo.Examples.RingGraphPropellane.complete_arms
assert_kernel_only TetraStereo.Examples.RingGraphPropellane.all_six_complete
