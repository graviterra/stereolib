import TetraStereo.Engine.RingReferenceObservationSupport
import TetraStereo.Engine.CentresRing

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace TetraStereo.Examples.RingDioxetaneReferenceSupport
open OneCenter Engine LocalizedChemicalRingJointPreparedSourceQueries
open LocalizedChemicalRingRegeneratedLifetime RingReachableReferencePolicy

/-- The two carbons of 2,4-difluoro-1,3-dioxetane are both incident to
the very same pair of bridging oxygen atoms. Each also carries H and F. -/
def molecule : RawMolecule where
  atoms := [.aliphatic .C,.aliphatic .C,.aliphatic .O,.aliphatic .O,
    .aliphatic .H,.aliphatic .F,.aliphatic .H,.aliphatic .F]
  bonds := ([(0,2),(0,3),(1,2),(1,3),(0,4),(0,5),(1,6),(1,7)] :
    List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

def spatial : SpatialConfiguration :=
  ⟨[⟨-1,0,0⟩,⟨1,0,0⟩,⟨0,1,0⟩,⟨0,-1,0⟩,
     ⟨-2,0,1⟩,⟨-2,0,-1⟩,⟨2,0,-1⟩,⟨2,0,1⟩]⟩

def input := (LocalizedChemicalRing.admitRawSpatial? molecule spatial).get (by decide +kernel)
private def geometry : LocalizedGenericMarkedRecalculation.Geometry := fun n => spatial.positions[n]?

open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission

private def rawVolume (a b c d : Nat) : Option ℚ := do
  return CartesianPoint3.orientedVolume (← geometry a) (← geometry b) (← geometry c) (← geometry d)

/-- Enumerate ordered quadruples of bonded sites, without choosing the
physical frame's ordering. Every quadruple with distinct sites has nonzero volume. -/
private theorem neighbor_volumes (atom : Fin 8) :
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


theorem centers : ∀ c : input.certified.Atom,
    c ∈ input.certified.moleculeGraph.tetrahedralCenterSet ↔ c.val = 0 ∨ c.val = 1 := by decide +kernel

private abbrev oxygenA : input.certified.Atom := ⟨2,by decide +kernel⟩
private abbrev oxygenB : input.certified.Atom := ⟨3,by decide +kernel⟩

/-- Both detected centers have the two oxygen neighbors. At either center
these are the only distinct neighbors with the same atomic number. -/
theorem shared_oxygen : ∀ c : input.certified.Atom, c ∈ input.certified.moleculeGraph.tetrahedralCenterSet →
    input.certified.moleculeGraph.Adj c oxygenA ∧ input.certified.moleculeGraph.Adj c oxygenB ∧
    ∀ a b : input.certified.Atom, input.certified.moleculeGraph.Adj c a →
      input.certified.moleculeGraph.Adj c b → a ≠ b →
      input.certified.moleculeGraph.atomZ a = input.certified.moleculeGraph.atomZ b →
        (a = oxygenA ∧ b = oxygenB) ∨ (a = oxygenB ∧ b = oxygenA) := by decide +kernel

noncomputable abbrev molecularFrames := frames input.certified molecule input.agreement
  input.admissible input.supported input.single

/-- The two fully regenerated reference policies give the same complete
assignment or refusal on every unmarked occurrence and both geometry sides. -/
theorem policies (q : SourceQuery input.certified molecule)
    (g : LocalizedGenericMarkedRecalculation.Geometry) :
    accumulated input.single molecularFrames g [] q = replaced input.single molecularFrames g [] q :=
  RingReferenceObservationSupport.agree_of_common_equal_element_neighbors input.single molecularFrames
    input.admissible oxygenA oxygenB (fun c => (shared_oxygen c.val c.property).2.2) q g

/-- At both carbon centers, the fully regenerated replacement policy gives
precisely the corresponding row of the actual public report. -/
theorem public_report (profile : LocalizedChemicalRing.Profile)
    (c : input.certified.detectedMultiCenterMolecule.Center) (value : Option LocalizedTetrahedralRSPseudoDescriptor) :
    (c.val.val,value) ∈ LocalizedChemicalRing.analyze profile input ↔
      replaced input.single molecularFrames (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) []
        (LocalizedChemicalRingJointPreparedSourceModelExistence.finalQuery input.certified molecule input.agreement c) = value :=
  RingReferenceObservationSupport.report_of_common_equal_element_neighbors input profile oxygenA oxygenB
    (fun center => (shared_oxygen center.val center.property).2.2) c value

end TetraStereo.Examples.RingDioxetaneReferenceSupport
assert_kernel_only TetraStereo.Examples.RingDioxetaneReferenceSupport.admitted
assert_kernel_only TetraStereo.Examples.RingDioxetaneReferenceSupport.centers
assert_kernel_only TetraStereo.Examples.RingDioxetaneReferenceSupport.shared_oxygen
assert_kernel_only TetraStereo.Examples.RingDioxetaneReferenceSupport.policies
assert_kernel_only TetraStereo.Examples.RingDioxetaneReferenceSupport.public_report
