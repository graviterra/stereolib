import TetraStereo.Engine.RingReferenceFirstSphere
import TetraStereo.Engine.CentresRing

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 50000
set_option Elab.async false

namespace TetraStereo.Examples.RingSpiroReferenceSeparation
open OneCenter Engine Engine.CentresRing
open LocalizedChemicalRingJointPreparedSourceQueries LocalizedChemicalRingRegeneratedLifetime
open RingReachableReferencePolicy

/-- Two O–C(H)(F)–S rings share their tetrahedral spiro carbon C0. The
two fluorinated carbons have four different elements among their neighbors. -/
def molecule : RawMolecule where
  atoms := [.aliphatic .C,.aliphatic .O,.aliphatic .S,.aliphatic .O,.aliphatic .S,
    .aliphatic .C,.aliphatic .C,.aliphatic .H,.aliphatic .F,.aliphatic .H,.aliphatic .F]
  bonds := ([(0,1),(0,2),(0,3),(0,4),(1,5),(2,5),(3,6),(4,6),(5,7),(5,8),(6,9),(6,10)] :
    List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

def spatial : SpatialConfiguration :=
  ⟨[⟨0,0,0⟩,⟨2,0,1⟩,⟨0,2,-1⟩,⟨-2,0,1⟩,⟨0,-2,-1⟩,⟨2,2,2⟩,⟨-2,-2,2⟩,
    ⟨3,2,2⟩,⟨2,3,2⟩,⟨-3,-2,2⟩,⟨-2,-3,2⟩]⟩

def input := (LocalizedChemicalRing.admitRawSpatial? molecule spatial).get (by decide +kernel)

def geometry : LocalizedGenericMarkedRecalculation.Geometry := fun n => spatial.positions[n]?

open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission

private def rawVolume (a b c d : Nat) : Option ℚ := do
  return CartesianPoint3.orientedVolume (← geometry a) (← geometry b) (← geometry c) (← geometry d)

/-- Enumerate ordered quadruples of bonded sites, without choosing the
physical frame's ordering. Every quadruple with distinct sites has nonzero volume. -/
private theorem neighbor_volumes (atom : Fin 11) :
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

theorem detected : ∀ c : input.certified.Atom,
    c ∈ input.certified.moleculeGraph.tetrahedralCenterSet ↔
      c.val ∈ ([0,5,6] : List Nat) := by decide +kernel

private theorem apart : ∀ c a b : input.certified.Atom,
    c ∈ input.certified.moleculeGraph.tetrahedralCenterSet → c.val ≠ 0 →
    input.certified.moleculeGraph.Adj c a → input.certified.moleculeGraph.Adj c b →
    input.certified.moleculeGraph.atomZ a = input.certified.moleculeGraph.atomZ b → a = b := by
  decide +kernel

noncomputable abbrev molecularFrames := frames input.certified molecule input.agreement
  input.admissible input.supported input.single

/-- Every possible mark-free collision on every original real occurrence
is confined to the one spiro atom, though the graph has three detected centers. -/
theorem only_spiro (q : SourceQuery input.certified molecule)
    (collision : ¬ Function.Injective (structuralColumn input.single molecularFrames q)) :
    q.val.atom = 0 :=
  RingReferenceFirstSphere.only_exceptional_atom input.single input.agreement input.admissible
    input.supported 0 (fun c diff a b => apart c.val a b c.property diff) q collision

/-- Full equality includes the original hand, mirror casing and refusal at
every unmarked query, even when the call originates below another center. -/
theorem policies (q : SourceQuery input.certified molecule)
    (g : LocalizedGenericMarkedRecalculation.Geometry) :
    accumulated input.single molecularFrames g [] q = replaced input.single molecularFrames g [] q :=
  RingReferenceFirstSphere.agree_of_one_repeated_element_center input.single input.agreement
    input.admissible input.supported 0 (fun c diff a b => apart c.val a b c.property diff) q g

end TetraStereo.Examples.RingSpiroReferenceSeparation

assert_kernel_only TetraStereo.Examples.RingSpiroReferenceSeparation.admitted
assert_kernel_only TetraStereo.Examples.RingSpiroReferenceSeparation.detected
assert_kernel_only TetraStereo.Examples.RingSpiroReferenceSeparation.only_spiro
assert_kernel_only TetraStereo.Examples.RingSpiroReferenceSeparation.policies
