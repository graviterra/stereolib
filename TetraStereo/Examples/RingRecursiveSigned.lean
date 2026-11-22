import TetraStereo.Engine.RingNestedFrameCoverage
import TetraStereo.Engine.RingRecursiveSignedReport
import TetraStereo.Engine.LocalizedChemicalRingPhysicalCertificate
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000
set_option Elab.async false

namespace TetraStereo.Examples.RingRecursiveSigned
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation
/-- Four spokes reach the same central carbon. Each outer segment follows
spoke carbon, ether oxygen, methylene carbon, then the next spoke carbon. -/
def molecule : RawMolecule where
  atoms := List.replicate 5 (.aliphatic .C) ++ List.replicate 4 (.aliphatic .O) ++
    List.replicate 4 (.aliphatic .C) ++ List.replicate 12 (.aliphatic .H)
  bonds := ((List.range 4).flatMap fun i =>
    [(0,1+i),(1+i,5+i),(5+i,9+i),(9+i,1+(i+1)%4),
     (1+i,13+i),(9+i,17+2*i),(9+i,18+2*i)]).map fun (a,b) => ⟨a,b,.single⟩


def xyz : SpatialConfiguration :=
  ⟨[⟨0,0,0⟩,⟨4,4,4⟩,⟨4,-4,-4⟩,⟨-4,4,-4⟩,⟨-4,-4,4⟩,
     ⟨8,6,10⟩,⟨-2,-12,4⟩,⟨-6,10,6⟩,⟨-10,-2,-8⟩,⟨6,-2,-12⟩,
     ⟨-4,8,-2⟩,⟨0,-4,0⟩,⟨6,0,6⟩,⟨2,10,0⟩,⟨12,-2,-8⟩,
     ⟨-6,-2,-20⟩,⟨-6,-10,24⟩,⟨14,-1,-31⟩,⟨-2,-9,-23⟩,⟨-7,26,6⟩,
     ⟨-3,14,-14⟩,⟨-5,-17,-7⟩,⟨15,-5,-3⟩,⟨25,-9,4⟩,⟨5,7,24⟩]⟩
def geometry : Geometry := fun i => xyz.positions[i]?

def input := (LocalizedChemicalRing.admitRawSpatial? molecule xyz).get (by decide +kernel)

open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission

private def rawVolume (a b c d : Nat) : Option ℚ := do
  return CartesianPoint3.orientedVolume (← geometry a) (← geometry b) (← geometry c) (← geometry d)

/-- Enumerate ordered quadruples of bonded sites, without choosing the
physical frame's ordering. Every quadruple with distinct sites has nonzero volume. -/
private theorem neighbor_volumes (atom : Fin 25) :
    let ns := molecule.canonicalIncidentNeighbors atom.val
    ns.all (fun a => ns.all (fun b => ns.all (fun c => ns.all (fun d =>
      !decide [a,b,c,d].Nodup || (rawVolume a b c d).any (fun v => decide (v ≠ 0)))))) = true := by
  revert atom
  decide +kernel

theorem admitted : saturatedWithHalogens molecule = true ∧
    LocalizedChemicalRing.admitRawSpatial? molecule xyz = some input ∧
    LocalizedChemicalRing.coordinatesAdmitted input = true := by
  refine ⟨by decide +kernel,(Option.some_get _).symm,?_⟩
  apply decide_eq_true
  intro center
  let mol := actualCanonicalMolecule input.certified
  let id (i : Fin 4) := (mol.ligandAtomAt center i).val
  have member (i : Fin 4) : id i ∈ molecule.canonicalIncidentNeighbors center.val.val := by
    apply (input.molecule.mem_canonicalIncidentNeighbors_iff _ input.admissible.1.1 _).mpr
    exact (LocalizedChemicalRingPhysicalSense.adj_iff input.molecule input.certified input.agreement
      input.admissible.1.1 input.admissible.1.2 input.supported _ _).mp (mol.ligandAtomAt_adj center i)
  have inj : Function.Injective id := Fin.val_injective.comp (mol.ligandAtomAt_injective center)
  have distinct : [id 0,id 1,id 2,id 3].Nodup := by
    simp [List.nodup_cons,inj.eq_iff]
  have all := neighbor_volumes center.val
  have first := List.all_eq_true.mp all _ (member 0)
  have second := List.all_eq_true.mp first _ (member 1)
  have third := List.all_eq_true.mp second _ (member 2)
  have fourth := List.all_eq_true.mp third _ (member 3)
  simp only [distinct,decide_true,Bool.not_true,Bool.false_or] at fourth
  obtain ⟨v,vol,nz⟩ := (Option.any_eq_true _ _).mp fourth
  apply (centerAdmitted_iff _ _).mpr
  exact ⟨v,vol,of_decide_eq_true nz⟩

/-- Every molecular carbon equals the barycenter of its four neighbors,
and all four points have nonzero signed volume. -/
theorem carbon_geometries : (RingCarbonReport.carbons molecule).all (fun i =>
    let ns := molecule.writtenNeighbors i
    (readback? geometry ns).isSome && [CartesianPoint3.x, CartesianPoint3.y, CartesianPoint3.z].all (fun axis =>
      ((ns.mapM fun j => (geometry j).map axis).map List.sum) == ((geometry i).map fun x => 4 * axis x))) = true := by
  decide +kernel

def markedOrders : List (Nat × List Nat) :=
  [(1,[1,4,2,3]),(2,[2,1,3,4]),(3,[3,2,4,1]),(4,[4,3,1,2])]

/-- The four rotations give alternating hands at these actual coordinates. -/
theorem cancelling_hands : markedOrders.map (fun (_,order) => readback? geometry order) =
    [some .S,some .R,some .S,some .R] ∧
    markedOrders.map (fun (_,order) => readback? (mirror geometry) order) =
    [some .R,some .S,some .R,some .S] := by decide +kernel

/-- Whenever the wheel gives its observed cyclic orders, its refusal is
independent of the numerical coordinates and of trial enumeration. -/
theorem four_orders_force_refusal {g : Geometry} (s : ReferenceFrame.Population molecule g [0])
    (ranked : (s.trials.map (fun t => (ReferenceFrame.orders s.frame.ids t.table false).head?)).Perm
      (markedOrders.map (fun row => some row.2))) : s.signedDescriptor = none :=
  s.four_cycle_refuses (a := 1) (b := 4) (c := 2) (d := 3) ranked

/-- Run the complete molecular derivation and check the chemical order
selected under every mark, on both geometries. -/
def validate : IO Unit := do
  let some c := RecursiveSigned.derive? molecule geometry 3 molecule.atomCount [0] |
    throw (IO.userError "missing signed wheel certificate")
  let .promotion pop := c.step | throw (IO.userError "wheel did not reach promotion")
  let actual := pop.trials.map fun t =>
    (t.mark, ReferenceFrame.orders pop.frame.ids t.table false, ReferenceFrame.orders pop.frame.ids t.table true)
  unless actual == markedOrders.map (fun (k,o) => (k,[o],[o])) do
    throw (IO.userError s!"unexpected molecular orders {repr actual}")
  unless c.verdict.isNone && pop.consensus?.isNone && pop.signedDescriptor.isNone &&
      pop.hands false == [some .S,some .R,some .S,some .R] &&
      pop.hands true == [some .R,some .S,some .R,some .S] do
    throw (IO.userError "mixed strict trials did not cancel")
  unless (ReferenceDerivation.derive? molecule geometry 3 molecule.atomCount [0]).isNone do
    throw (IO.userError "old consensus unexpectedly resolved")

#eval validate

end TetraStereo.Examples.RingRecursiveSigned

assert_kernel_only TetraStereo.Examples.RingRecursiveSigned.admitted
assert_kernel_only TetraStereo.Examples.RingRecursiveSigned.carbon_geometries
assert_kernel_only TetraStereo.Examples.RingRecursiveSigned.cancelling_hands

assert_kernel_only TetraStereo.Examples.RingRecursiveSigned.four_orders_force_refusal
