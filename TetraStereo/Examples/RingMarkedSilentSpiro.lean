import TetraStereo.Engine.RingMarkedSilentRefusal
import TetraStereo.Engine.LocalizedChemicalRingPhysicalCertificate

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

namespace TetraStereo.Examples.RingMarkedSilentSpiro
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation

/-- 5-Thiaspiro[2.3]hexane: a cyclopropane and a thietane share C0.
The two CH₂ carbons on each side are equivalent. The two sides are
constitutionally distinct because only one ring contains sulfur. -/
def molecule : RawMolecule where
  atoms := List.replicate 5 (.aliphatic .C) ++ [.aliphatic .S] ++ List.replicate 8 (.aliphatic .H)
  bonds := ([(0,1),(0,2),(1,2),(0,3),(0,4),(3,5),(4,5),(1,6),(1,7),(2,8),(2,9),
    (3,10),(3,11),(4,12),(4,13)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

def spatial : SpatialConfiguration := ⟨[⟨0,0,0⟩,⟨2,2,2⟩,⟨2,-2,-2⟩,⟨-2,2,-2⟩,⟨-2,-2,2⟩,⟨-4,0,0⟩,
  ⟨4,3,6⟩,⟨2,7,4⟩,⟨4,-3,-6⟩,⟨2,-7,-4⟩,⟨-3,5,-1⟩,⟨-1,3,-7⟩,⟨-3,-5,1⟩,⟨-1,-3,7⟩]⟩

def geometry : Geometry := fun i => spatial.positions[i]?
def input := (LocalizedChemicalRing.admitRawSpatial? molecule spatial).get (by decide +kernel)

open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission

private def rawVolume (a b c d : Nat) : Option ℚ := do
  return CartesianPoint3.orientedVolume (← geometry a) (← geometry b) (← geometry c) (← geometry d)

/-- Enumerate ordered quadruples of bonded sites, without choosing the
physical frame's ordering. Every quadruple with distinct sites has nonzero volume. -/
private theorem neighbor_volumes (atom : Fin 14) :
    let ns := molecule.canonicalIncidentNeighbors atom.val
    ns.all (fun a => ns.all (fun b => ns.all (fun c => ns.all (fun d =>
      !decide [a,b,c,d].Nodup || (rawVolume a b c d).any (fun v => decide (v ≠ 0)))))) = true := by
  revert atom
  decide +kernel

theorem admitted : LocalizedChemicalRing.admitRawSpatial? molecule spatial = some input ∧
    LocalizedChemicalRing.coordinatesAdmitted input = true := by
  refine ⟨(Option.some_get _).symm,?_⟩
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

/-- Each of the five carbons is the barycenter of its four neighbors, and the
four neighbors span a tetrahedron of nonzero volume at each carbon. -/
theorem carbon_geometries : RingCarbonReport.carbons molecule = [0,1,2,3,4] ∧
    (RingCarbonReport.carbons molecule).all (fun i =>
      let ns := molecule.writtenNeighbors i
      (readback? geometry ns).isSome && [CartesianPoint3.x, CartesianPoint3.y, CartesianPoint3.z].all (fun axis =>
        ((ns.mapM fun j => (geometry j).map axis).map List.sum) == ((geometry i).map fun x => 4 * axis x))) = true := by
  decide +kernel


theorem certified : (RingMarkedSilentRefusal.discover? input 1 0).isSome = true := by decide +kernel

def certificate := (RingMarkedSilentRefusal.discover? input 1 0).get certified

theorem marked_trials : certificate.pop.trials.map ReferenceFrame.Trial.mark = [1,2,3,4] := by decide +kernel

theorem result : certificate.pop.consensus? = some none := certificate.refusal

end TetraStereo.Examples.RingMarkedSilentSpiro

assert_kernel_only TetraStereo.Examples.RingMarkedSilentSpiro.admitted
assert_kernel_only TetraStereo.Examples.RingMarkedSilentSpiro.carbon_geometries
assert_kernel_only TetraStereo.Examples.RingMarkedSilentSpiro.certified
assert_kernel_only TetraStereo.Examples.RingMarkedSilentSpiro.marked_trials
assert_kernel_only TetraStereo.Examples.RingMarkedSilentSpiro.result
