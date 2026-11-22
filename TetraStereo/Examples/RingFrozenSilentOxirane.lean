import TetraStereo.Engine.CentresRingDerived

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace TetraStereo.Examples.RingFrozenSilentOxirane
open OneCenter Engine CentresRing LocalizedGenericMarkedRecalculation
open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission

/-- C0 and C1 form an oxirane with O2. C1 is CH₂. C0 bears two N(OH)₂
groups, so the O siblings at both nitrogens are distinct nonterminal sites. -/
def molecule : RawMolecule where
  atoms := ([.C,.C,.O,.N,.N,.O,.O,.O,.O,.H,.H,.H,.H,.H,.H] :
    List Element).map AtomSpec.aliphatic
  bonds := ([(0,1),(1,2),(2,0),(0,3),(0,4),(3,5),(3,6),(4,7),(4,8),
    (5,9),(6,10),(7,11),(8,12),(1,13),(1,14)] : List (Nat × Nat)).map
    (fun (a,b) => ⟨a,b,.single⟩)

private def moment (t : ℚ) : CartesianPoint3 := ⟨t,t*t,t*t*t⟩
def spatial : SpatialConfiguration := ⟨(List.range 15).map fun n => moment n⟩
def geometry : Geometry := fun n => spatial.positions[n]?
def input := (LocalizedChemicalRing.admitRawSpatial? molecule spatial).get (by decide +kernel)

private theorem point : ∀ a : input.certified.Atom,
    input.certified.spatialPointAt? a = some (moment a.val) := by decide +kernel

theorem admitted : LocalizedChemicalRing.admitRawSpatial? molecule spatial = some input ∧
    LocalizedChemicalRing.coordinatesAdmitted input = true := by
  refine ⟨(Option.some_get _).symm,decide_eq_true ?_⟩
  intro center
  let mol := actualCanonicalMolecule input.certified
  let x (s : Fin 4) : ℚ := (mol.ligandAtomAt center s).val
  have distinct (a b : Fin 4) (ne : a ≠ b) : x a ≠ x b := by
    intro eqn
    change ((mol.ligandAtomAt center a).val : ℚ) = (mol.ligandAtomAt center b).val at eqn
    exact ne (mol.ligandAtomAt_injective center (Fin.ext (by exact_mod_cast eqn)))
  have volume (a b c d : ℚ) :
      CartesianPoint3.orientedVolume (moment a) (moment b) (moment c) (moment d) =
        (d-a)*(a-b)*(a-c)*(b-c)*(b-d)*(c-d) := by unfold moment CartesianPoint3.orientedVolume; ring
  apply (centerAdmitted_iff _ _).mpr
  refine ⟨CartesianPoint3.orientedVolume (moment (x 0)) (moment (x 1)) (moment (x 2)) (moment (x 3)),?_,?_⟩
  · simp [coordinateVolume?,point,x,mol]
  · rw [volume]
    repeat' apply mul_ne_zero
    all_goals exact sub_ne_zero.mpr (distinct _ _ (by decide))

theorem detected : ∀ c : input.certified.Atom,
    c ∈ input.certified.moleculeGraph.tetrahedralCenterSet ↔ c.val ∈ ([0,1] : List Nat) := by
  decide +kernel

/-- The only external traversal inputs are the discovered addresses and starting
orders. Slot comparisons, marks, detached state, publications and letters are calculated. -/
def layout : Molecular.Layout :=
  ⟨1, [[0,1],[0,2,1]], [[0,2,13,14],[0,2,13,14]], [[2,1,3,4],[1,2,3,4]]⟩

abbrev Store := List (List Nat × String)
abbrev CallRead := List Nat × Store × Option Nat × Option Molecular.Rule × Int
abbrev Readout := String × Store × List CallRead

def reads (g : Geometry) : Option Readout := (Molecular.derive molecule g layout).map fun d =>
  (d.trace.label,d.published.map (fun p => (p.path,p.code)),
    (d.calls.filter fun c => c.comparison.left == 3 && c.comparison.right == 4).map fun c =>
      (c.frame.focus,c.frame.visible.map (fun p => (p.path,p.code)),c.frame.mark,c.winner,c.comparison.value))

/-- On each path the source sorting pass compares N3 and N4 twice, once in the
sort and once when forming priority groups. Each call exhausts the rules with
score zero and no active mark. Both C0 publications and the C1 report refuse. -/
theorem retained_calls (rev : Bool) :
    reads (if rev then mirror geometry else geometry) =
      some ("-", [([1,0],"-"),([1,2,0],"-")],
        [([1,2,0],[],none,none,0),([1,2,0],[],none,none,0),
         ([1,0],[([1,2,0],"-")],none,none,0),([1,0],[([1,2,0],"-")],none,none,0)]) := by
  cases rev <;> rfl

/-- Complete comparisons at each of the two occurrence/store combinations
identified in the actual scheduled calls. Physical ligand order is C1,O2,N3,N4. -/
def fullMatrix (far : Bool) : Option (List Int) := do
  let frame : Molecular.Frame := ⟨molecule,if far then [1,2,0] else [1,0],
    if far then [] else [⟨[1,2,0],"-"⟩],none,false⟩
  let comparator ← Molecular.prepare frame
  let ids := [1,2,3,4]
  let rows ← ids.mapM fun a => ids.mapM fun b => do
    if a = b then return (0 : Int)
    let tests ← comparator a b
    return (← Molecular.decideSteps (Molecular.results tests.val)).2
  return rows.flatten

def expectedMatrix : List Int :=
  [0,-1,-1,-1, 1,0,1,1, 1,-1,0,0, 1,-1,0,0]

theorem full_matrix (far : Bool) : fullMatrix far = some expectedMatrix := by
  cases far <;> rfl

end TetraStereo.Examples.RingFrozenSilentOxirane

assert_kernel_only TetraStereo.Examples.RingFrozenSilentOxirane.admitted
assert_kernel_only TetraStereo.Examples.RingFrozenSilentOxirane.detected
assert_kernel_only TetraStereo.Examples.RingFrozenSilentOxirane.retained_calls

assert_kernel_only TetraStereo.Examples.RingFrozenSilentOxirane.full_matrix
