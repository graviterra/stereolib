import TetraStereo.Engine.RingRecursiveSignedReport
import TetraStereo.Engine.LocalizedChemicalRingPhysicalCertificate

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

namespace TetraStereo.Examples.RingTerminalPairCoverage
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation

/-- 2,2-Difluorothiirane, with ring atoms C0, C1 and S2. -/
def molecule : RawMolecule where
  atoms := [.aliphatic .C,.aliphatic .C,.aliphatic .S,.aliphatic .F,
    .aliphatic .F,.aliphatic .H,.aliphatic .H]
  bonds := ([(0,1),(1,2),(2,0),(0,3),(0,4),(1,5),(1,6)] :
    List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

def spatial : SpatialConfiguration :=
  ⟨[⟨0,0,0⟩,⟨2,0,0⟩,⟨1,2,0⟩,⟨-2,-1,2⟩,⟨-1,-1,-2⟩,⟨3,-1,2⟩,⟨4,-1,-2⟩]⟩

def geometry : Geometry := fun i => spatial.positions[i]?

def input := (LocalizedChemicalRing.admitRawSpatial? molecule spatial).get (by decide +kernel)

open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission

private def rawVolume (a b c d : Nat) : Option ℚ := do
  return CartesianPoint3.orientedVolume (← geometry a) (← geometry b) (← geometry c) (← geometry d)

/-- Enumerate ordered quadruples of bonded sites, without choosing the
physical frame's ordering. Every quadruple with distinct sites has nonzero volume. -/
private theorem neighbor_volumes (atom : Fin 7) :
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

/-- Each of the two carbons is the barycenter of its four neighbors, and the
four neighbors span a tetrahedron of nonzero volume at each carbon. -/
theorem carbon_geometries : RingCarbonReport.carbons molecule = [0,1] ∧
    (RingCarbonReport.carbons molecule).all (fun i =>
      let ns := molecule.writtenNeighbors i
      (readback? geometry ns).isSome && [CartesianPoint3.x, CartesianPoint3.y, CartesianPoint3.z].all (fun axis =>
        ((ns.mapM fun j => (geometry j).map axis).map List.sum) == ((geometry i).map fun x => 4 * axis x))) = true := by
  decide +kernel

/-- Rule 1a cannot give a strict four-ligand order when two distinct
incident cursors have the same atomic-number tree. -/
private theorem tied_trees {m : RawMolecule} {p : List Nat} {d : Nat}
    {f : RawMolecule.CanonicalBranchNode} {l r : CanonicalRerootCursor}
    (atFocus : occurrence? m p = some f)
    (left : l ∈ occurrenceLigandCursors m f) (right : r ∈ occurrenceLigandCursors m f)
    (distinct : l ≠ r) (tied : atomicTree m 3 d l = atomicTree m 3 d r) :
    atomicOrder? m p d = none := by
  unfold atomicOrder?
  cases h : atomicRanking? m p d with
  | none => rfl
  | some ranking =>
    exfalso
    have site : ranking.focus = f := Option.some.inj (ranking.reached.symm.trans atFocus)
    have ls := ranking.complete.mem_iff.mpr (show l ∈ occurrenceLigandCursors m ranking.focus by simpa [site] using left)
    have rs := ranking.complete.mem_iff.mpr (show r ∈ occurrenceLigandCursors m ranking.focus by simpa [site] using right)
    obtain ⟨a,ha,la⟩ := List.mem_map.mp ls
    obtain ⟨b,hb,rb⟩ := List.mem_map.mp rs
    rw [← la,← rb] at tied
    have trees := Option.some.inj (a.molecular.symm.trans (tied.trans b.molecular))
    have keys : a.key = b.key := by rw [a.exactKey,b.exactKey,trees]
    have unique : (ranking.arms.map AtomicArm.key).Nodup :=
      List.pairwise_map.mpr (ranking.strict.imp fun less => ne_of_gt less)
    have equal := List.inj_on_of_nodup_map unique ha hb keys
    exact distinct (la.symm.trans ((congrArg AtomicArm.cursor equal).trans rb))

private def carbon := (occurrence? molecule [0]).get (by decide +kernel)
private def f3 := ((occurrenceLigandCursors molecule carbon).find? fun c => c.node.atom == 3).get (by decide +kernel)
private def f4 := ((occurrenceLigandCursors molecule carbon).find? fun c => c.node.atom == 4).get (by decide +kernel)

private theorem equal_trees (depth : Nat) : atomicTree molecule 3 depth f3 = atomicTree molecule 3 depth f4 := by
  have left : molecule.atoms[f3.node.atom]? = some (AtomSpec.aliphatic .F) := by decide +kernel
  have right : molecule.atoms[f4.node.atom]? = some (AtomSpec.aliphatic .F) := by decide +kernel
  have leaf : f3.children molecule = [] := by decide +kernel
  have other : f4.children molecule = [] := by decide +kernel
  cases depth <;> simp [atomicTree,left,right,leaf,other,AtomSpec.aliphatic]

theorem atomic_order_missing (depth : Nat) : atomicOrder? molecule [0] depth = none :=
  tied_trees (Option.some_get _).symm (by decide +kernel : f3 ∈ occurrenceLigandCursors molecule carbon)
    (by decide +kernel : f4 ∈ occurrenceLigandCursors molecule carbon) (by decide +kernel) (equal_trees depth)

/-- The earlier local isotope and recursive signed constructors both miss
the fluorine pair at every depth and recursion fuel, even with arbitrary geometry. -/
theorem previous_evaluators_missing (g : Geometry) (depth fuel : Nat) :
    LocalIsotopeCarbonReport.at? molecule g depth 0 = none ∧
    RecursiveSigned.derive? molecule g depth fuel [0] = none := by
  constructor
  · cases h : LocalIsotopeCarbonReport.at? molecule g depth 0 with
    | none => rfl
    | some v =>
      have found := (LocalIsotopeCarbonReport.at?_isSome_iff molecule g depth 0).mp (by rw [h]; rfl)
      have hh : (RingCarbonReport.hydrogens? molecule 0).isNone = true := by decide +kernel
      have ht : (LocalIsotopeCarbonReport.hydrogenTie? molecule 0).isNone = true := by decide +kernel
      have rk : (LocalIsotopeCarbonReport.ranking? molecule 0).isNone = true := by decide +kernel
      rw [AtomicCarbonReport.at?_isSome_iff] at found
      simp [Option.isNone_iff_eq_none.mp hh,Option.isNone_iff_eq_none.mp ht,
        Option.isNone_iff_eq_none.mp rk,atomic_order_missing] at found
  · have outside : saturatedWithHalogens molecule = false := by decide +kernel
    cases fuel <;> simp [RecursiveSigned.derive?,outside]

/-- The exact ligands giving the previously missed constitutional equality
are the two singly bonded fluorines at sites 3 and 4. -/
theorem fluorine_pair :
    RingTerminalPair.Equivalent molecule ⟨0,by decide +kernel⟩
      ⟨3,by decide +kernel⟩ ⟨4,by decide +kernel⟩ := by decide +kernel

theorem fluorine_pair_found : (RingTerminalPair.check? molecule 0).isSome = true :=
  (RingTerminalPair.check?_isSome_iff ..).mpr
    ⟨by decide +kernel,by decide +kernel,_,_,fluorine_pair⟩

/-- C1 already has an independent hydrogen-pair certificate from the
earlier constructor, for every geometry and depth. -/
theorem methylene_previously_covered (g : Geometry) (depth : Nat) :
    (AtomicCarbonReport.at? molecule g depth 1).isSome = true :=
  (AtomicCarbonReport.at?_isSome_iff ..).mpr (Or.inl (by decide +kernel))

theorem hydrogen_pair :
    RingTerminalPair.Equivalent molecule ⟨1,by decide +kernel⟩
      ⟨5,by decide +kernel⟩ ⟨6,by decide +kernel⟩ := by decide +kernel

/-- The public signed evaluator always returns both certified refusals.
The full two-carbon inventory and its order hold at every search depth. -/
theorem report_all_depths (depth : Nat) :
    (RecursiveSigned.report? input depth).map RecursiveSigned.Report.labels =
      some [(0,none),(1,none)] := by
  have covered (i : Nat) (hi : i ∈ RingCarbonReport.carbons input.molecule) :
      ∃ h : i < input.molecule.atomCount, RingTerminalPair.Focus input.molecule i ∧
        ∃ a b, RingTerminalPair.Equivalent input.molecule ⟨i,h⟩ a b := by
    change i ∈ ([0,1] : List Nat) at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨by decide +kernel,by decide +kernel,_,_,fluorine_pair⟩
    · exact ⟨by decide +kernel,by decide +kernel,_,_,hydrogen_pair⟩
  obtain ⟨report,found,labels⟩ := RecursiveSigned.terminal_carbon_report input depth covered
  exact (congrArg (Option.map RecursiveSigned.Report.labels) found).trans (congrArg some labels)

end TetraStereo.Examples.RingTerminalPairCoverage

assert_kernel_only TetraStereo.Examples.RingTerminalPairCoverage.admitted
assert_kernel_only TetraStereo.Examples.RingTerminalPairCoverage.carbon_geometries
assert_kernel_only TetraStereo.Examples.RingTerminalPairCoverage.atomic_order_missing
assert_kernel_only TetraStereo.Examples.RingTerminalPairCoverage.previous_evaluators_missing
assert_kernel_only TetraStereo.Examples.RingTerminalPairCoverage.fluorine_pair
assert_kernel_only TetraStereo.Examples.RingTerminalPairCoverage.fluorine_pair_found
assert_kernel_only TetraStereo.Examples.RingTerminalPairCoverage.methylene_previously_covered
assert_kernel_only TetraStereo.Examples.RingTerminalPairCoverage.hydrogen_pair
assert_kernel_only TetraStereo.Examples.RingTerminalPairCoverage.report_all_depths
