import TetraStereo.Engine.RingConstitutionalCoverage
import TetraStereo.Engine.RingLocalInversion
import TetraStereo.Engine.LocalizedChemicalRingPhysicalCertificate

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

namespace TetraStereo.Examples.RingDimethylThiiraneBoundary
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation

/-- The thiirane ring is C0–C1–S2. At C0, the two substituents are
methyl carbons 3 and 4. Carbon 1 is a methylene. -/
def molecule : RawMolecule where
  atoms := [.aliphatic .C,.aliphatic .C,.aliphatic .S,.aliphatic .C,.aliphatic .C] ++
    List.replicate 8 (.aliphatic .H)
  bonds := ([(0,1),(1,2),(2,0),(0,3),(0,4),(1,5),(1,6),(3,7),(3,8),(3,9),
    (4,10),(4,11),(4,12)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

def spatial : SpatialConfiguration :=
  ⟨[⟨0,0,0⟩,⟨0,-2,2⟩,⟨0,2,2⟩,⟨2,0,-2⟩,⟨-2,0,-2⟩,
    ⟨2,-5,3⟩,⟨-2,-5,3⟩,⟨3,2,-2⟩,⟨2,-1,-4⟩,⟨3,-1,-2⟩,
    ⟨-3,2,-2⟩,⟨-2,-1,-4⟩,⟨-3,-1,-2⟩]⟩

def geometry : Geometry := fun i => spatial.positions[i]?

def input := (LocalizedChemicalRing.admitRawSpatial? molecule spatial).get (by decide +kernel)

open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission

private def rawVolume (a b c d : Nat) : Option ℚ := do
  return CartesianPoint3.orientedVolume (← geometry a) (← geometry b) (← geometry c) (← geometry d)

/-- Enumerate ordered quadruples of bonded sites, without choosing the
physical frame's ordering. Every quadruple with distinct sites has nonzero volume. -/
private theorem neighbor_volumes (atom : Fin 13) :
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

/-- Each of the four carbons is the barycenter of its four neighbors, and the
four neighbors span a tetrahedron of nonzero volume at each carbon. -/
theorem carbon_geometries : RingCarbonReport.carbons molecule = [0,1,3,4] ∧
    (RingCarbonReport.carbons molecule).all (fun i =>
      let ns := molecule.writtenNeighbors i
      (readback? geometry ns).isSome && [CartesianPoint3.x, CartesianPoint3.y, CartesianPoint3.z].all (fun axis =>
        ((ns.mapM fun j => (geometry j).map axis).map List.sum) == ((geometry i).map fun x => 4 * axis x))) = true := by
  decide +kernel

open CertifiedLocalizedCIPInput Certificate.CanonicalSphereKey

/-- Reflection fixes all three ring sites and exchanges the complete methyl
groups. On the methylene it exchanges its two identical hydrogens. -/
def exchange (i : Nat) : Nat := [0,1,2,4,3,6,5,10,11,12,7,8,9][i]?.getD i

theorem methyl_symmetry : Reflects molecule geometry exchange ∧
    exchange 0 = 0 ∧ exchange 1 = 1 ∧ exchange 2 = 2 ∧ exchange 3 = 4 ∧ exchange 4 = 3 := by
  constructor
  · constructor <;> decide +kernel
  · decide +kernel

private def focus := canonicalCenterRoot 0
private def methyl (i : Nat) := ((occurrenceLigandCursors molecule focus).find? fun c => c.node.atom == i).getD
  ⟨focus,none⟩

private theorem terminal_H (c : CanonicalRerootCursor)
    (h : molecule.atoms[c.node.atom]? = some (AtomSpec.aliphatic .H)) (leaf : c.children molecule = [])
    (d : Nat) : atomicTree molecule 3 d c = some (.node 1 []) := by
  cases d <;> simp [atomicTree,h,leaf,AtomSpec.aliphatic,Element.atomicNumber]

private theorem map_hydrogens (cs : List CanonicalRerootCursor) (d : Nat)
    (leaves : ∀ c ∈ cs, molecule.atoms[c.node.atom]? = some (AtomSpec.aliphatic .H) ∧ c.children molecule = []) :
    cs.mapM (atomicTree molecule 3 d) = some (List.replicate cs.length (.node 1 [])) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨atom,leaf⟩ := leaves c List.mem_cons_self
    have rest := ih (fun z hz => leaves z (List.mem_cons_of_mem _ hz))
    simp [List.mapM_cons,terminal_H c atom leaf d,rest,List.replicate_succ]

private theorem methylTree (c : CanonicalRerootCursor) (d : Nat)
    (atom : molecule.atoms[c.node.atom]? = some (AtomSpec.aliphatic .C))
    (three : (c.children molecule).length = 3)
    (leaves : ∀ h ∈ c.children molecule, molecule.atoms[h.node.atom]? = some (AtomSpec.aliphatic .H) ∧ h.children molecule = []) :
    atomicTree molecule 3 d c = some (.node 6 (if d = 0 then [] else List.replicate 3 (.node 1 []))) := by
  cases d with
  | zero => simp [atomicTree,atom,AtomSpec.aliphatic,Element.atomicNumber]
  | succ k =>
    simp [atomicTree,atom,AtomSpec.aliphatic,Element.atomicNumber,three,map_hydrogens _ k leaves]

theorem tied_methyls (d : Nat) : atomicTree molecule 3 d (methyl 3) = atomicTree molecule 3 d (methyl 4) := by
  rw [methylTree (methyl 3) d (by decide +kernel) (by decide +kernel) (by decide +kernel),
      methylTree (methyl 4) d (by decide +kernel) (by decide +kernel) (by decide +kernel)]

/-- The two complete arms agree on atom and mass, duplicate priority, unit
class and both stereochemical tags. Neither methyl has a candidate auxiliary
occurrence. This proof reads only these arms of the sulfur-containing graph. -/
theorem complete_methyl_equivalence :
    IsotopePriority.TreesMatch molecule (CursorTie.observe? molecule [0] [])
      (IsotopePriority.budget molecule+1) (methyl 3) (methyl 4) ∧
    carbonSites molecule (molecule.atomCount+1) (methyl 3).node = some [] ∧
    carbonSites molecule (molecule.atomCount+1) (methyl 4).node = some [] := by
  refine ⟨IsotopePriority.treesMatch_sound ?_,?_⟩ <;> decide +kernel

theorem no_atomic_order (d : Nat) : atomicOrder? molecule [0] d = none := by
  unfold atomicOrder?
  cases h : atomicRanking? molecule [0] d with
  | none => rfl
  | some r =>
    exfalso
    obtain ⟨n,hn,_,_,unique⟩ := (atomicRanking?_isSome_iff_keys molecule [0] d).mp (by rw [h]; rfl)
    have same : occurrence? molecule [0] = some focus := by decide +kernel
    have atRoot : n = focus := Option.some.inj (hn.symm.trans same)
    rw [atRoot] at unique
    have l : methyl 3 ∈ occurrenceLigandCursors molecule focus := by decide +kernel
    have r : methyl 4 ∈ occurrenceLigandCursors molecule focus := by decide +kernel
    have diff : methyl 3 ≠ methyl 4 := by decide +kernel
    apply diff
    apply List.inj_on_of_nodup_map unique l r
    simp [molecularAtomicKey?,tied_methyls d]

/-- Every other carbon carries at least two directly bonded equivalent
hydrogens and already has a terminal-pair refusal at every sphere depth. -/
theorem other_carbons : ∀ i ∈ RingCarbonReport.carbons molecule, i ≠ 0 →
    (RingTerminalPair.check? molecule i).isSome = true := by decide +kernel

/-- The sulfur atom is admitted by the public localized input, while the two
recursively signed engines require the restricted element list at their frame. -/
theorem four_routes_missing (g : Geometry) (d : Nat) :
    LocalIsotopeCarbonReport.at? molecule g d 0 = none ∧
    RingTerminalPair.check? molecule 0 = none ∧
    RecursiveSigned.derive? molecule g d molecule.atomCount [0] = none ∧
    FrozenSigned.check? molecule g d 0 = none := by
  have outside : saturatedWithHalogens molecule = false := by decide +kernel
  constructor
  · cases h : LocalIsotopeCarbonReport.at? molecule g d 0 with
    | none => rfl
    | some v =>
      have found := (LocalIsotopeCarbonReport.at?_isSome_iff molecule g d 0).mp (by rw [h]; rfl)
      have hh : (RingCarbonReport.hydrogens? molecule 0).isNone = true := by decide +kernel
      have ht : (LocalIsotopeCarbonReport.hydrogenTie? molecule 0).isNone = true := by decide +kernel
      have rk : (LocalIsotopeCarbonReport.ranking? molecule 0).isNone = true := by decide +kernel
      rw [AtomicCarbonReport.at?_isSome_iff] at found
      simp [Option.isNone_iff_eq_none.mp hh,Option.isNone_iff_eq_none.mp ht,
        Option.isNone_iff_eq_none.mp rk,no_atomic_order] at found
  constructor
  · exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  constructor
  · cases fuel : molecule.atomCount <;> simp [RecursiveSigned.derive?,outside]
  · cases h : FrozenSigned.check? molecule g d 0 with
    | none => rfl
    | some c =>
      have built := c.frame.built
      simp [ReferenceFrame.molecularFrame?,outside] at built

/-- At each depth the four original routes still miss carbon 0. The public
report now succeeds exactly when the silent-arm comparison proves the methyl
tie. All four omitted letters then have chemical refusal evidence. -/
theorem public_projection (d : Nat) :
    (RecursiveSigned.report? input d).map RecursiveSigned.Report.labels =
      if (RingSilentPair.check? molecule d 0).isSome then some [(0,none),(1,none),(3,none),(4,none)] else none := by
  rw [RecursiveSigned.report_labels]
  have raw : input.molecule = molecule := by decide +kernel
  rw [raw,carbon_geometries.1]
  let g := LocalizedChemicalRingPhysicalSense.inputGeometry input.certified
  have rest (i : Nat) (mem : i ∈ [1,3,4]) :
      (RecursiveSigned.carbon? molecule g d i).map (fun v => (i,v.label)) = some (i,none) := by
    have member : i ∈ RingCarbonReport.carbons molecule := carbon_geometries.1 ▸ List.mem_cons_of_mem 0 mem
    have ne : i ≠ 0 := by rintro rfl; simp at mem
    obtain ⟨pair,h⟩ := Option.isSome_iff_exists.mp (other_carbons i member ne)
    simp [RecursiveSigned.carbon?,h,RecursiveSigned.CarbonVerdict.label]
  have missing := four_routes_missing g d
  have frozen : FrozenSigned.checkWith? (RecursiveSigned.cacheAtRoot molecule g d 0) 0 = none := missing.2.2.2
  have center : (RecursiveSigned.carbon? molecule g d 0).map (fun v => (0,v.label)) =
      (RingSilentPair.check? molecule d 0).map (fun _ => (0,none)) := by
    simp only [RecursiveSigned.carbon?,missing.2.1,missing.1,RecursiveSigned.cacheAtRoot_exact,
      missing.2.2.1,frozen]
    cases RingSilentPair.check? molecule d 0 <;> rfl
  change ([0,1,3,4] : List Nat).mapM (m := Option) (fun i =>
    (RecursiveSigned.carbon? molecule g d i).map fun v => (i,v.label)) = _
  simp only [List.mapM_cons,center,rest 1 (by simp),rest 3 (by simp),rest 4 (by simp),List.mapM_nil]
  cases RingSilentPair.check? molecule d 0 <;> rfl

theorem insufficient_at_depth_zero : RecursiveSigned.report? input 0 = none := by
  have no : (RingSilentPair.check? molecule 0 0).isSome = false := by decide +kernel
  have projection := public_projection 0
  rw [no,if_neg (by decide)] at projection
  exact Option.map_eq_none_iff.mp projection

theorem public_at_depth_one :
    (RecursiveSigned.report? input 1).map RecursiveSigned.Report.labels =
      some [(0,none),(1,none),(3,none),(4,none)] := by
  have succeeds : (RingSilentPair.check? molecule 1 0).isSome = true := by decide +kernel
  rw [public_projection,succeeds,if_pos rfl]

/-- One deuteration breaks the constitutional equivalence. Labelling the
matching terminal hydrogen on the second methyl restores the tie. -/
def unilateralD : RawMolecule := {molecule with
  atoms := molecule.atoms.set 7 { AtomSpec.aliphatic .H with isotope? := some 2 } }

theorem one_methyl_D : (RingSilentPair.check? unilateralD 1 0).isNone = true := by decide +kernel

def symmetricD : RawMolecule := {unilateralD with
  atoms := unilateralD.atoms.set 10 { AtomSpec.aliphatic .H with isotope? := some 2 } }

theorem both_methyl_D : (RingSilentPair.check? symmetricD 1 0).isSome = true := by decide +kernel

private def atom (i : Fin 13) : input.certified.Atom := ⟨i.val, i.isLt⟩

/-- This one atom permutation fixes both methylene hydrogens and exchanges
the methyl groups with one additional transposition among their hydrogens.
It reverses the central frame and transports the other three center signs. -/
def localExchange : Equiv.Perm input.certified.Atom :=
  Equiv.swap (atom 3) (atom 4) * Equiv.swap (atom 7) (atom 11) *
    Equiv.swap (atom 8) (atom 10) * Equiv.swap (atom 9) (atom 12)

private abbrev mol := actualCanonicalMolecule input.certified
def target : mol.Center := ⟨atom 0,by decide +kernel⟩

private def methylene : mol.Center := ⟨atom 1,by decide +kernel⟩
private def leftMethyl : mol.Center := ⟨atom 3,by decide +kernel⟩
private def rightMethyl : mol.Center := ⟨atom 4,by decide +kernel⟩

private def partners (a : input.certified.Atom) (k : Fin 4) : input.certified.Atom :=
  atom ((if a.val = 0 then ![1,2,3,4] else if a.val = 1 then ![0,2,5,6]
    else if a.val = 3 then ![0,7,8,9] else ![0,10,11,12] : Fin 4 → Fin 13) k)

private theorem canonical_neighbors (c : mol.Center) (k : Fin 4) :
    mol.ligandAtomAt c k = partners c.val k := by
  have cases (a : input.certified.Atom) : a ∈ mol.centers → a = atom 0 ∨ a = atom 1 ∨ a = atom 3 ∨ a = atom 4 := by
    revert a
    decide +kernel
  have list (a : input.certified.Atom) (atCenter : a ∈ mol.centers) :
      (input.certified.moleculeGraph.neighborFinset a).sort (· ≤ ·) = List.ofFn (partners a) := by
    have finite : input.certified.moleculeGraph.neighborFinset a = (List.ofFn (partners a)).toFinset := by
      ext b
      rw [input.certified.moleculeGraph.mem_neighborFinset]
      rcases cases a atCenter with rfl | rfl | rfl | rfl <;> revert b <;> decide +kernel
    rw [finite]
    rcases cases a atCenter with rfl | rfl | rfl | rfl
    all_goals apply (List.toFinset_sort (· ≤ ·) (by decide +kernel)).mpr; decide +kernel
  have sorted := list c.val c.property
  unfold mol actualCanonicalMolecule MultiCenterMolecule.ligandAtomAt canonicalLigandAtom canonicalNeighborList
  simp [sorted]
  fin_cases k <;> rfl

open FinitePhysicalBranchTransport

private def partnerSlot (a b : input.certified.Atom) : Fin 4 :=
  if partners a 0 = b then 0 else if partners a 1 = b then 1 else if partners a 2 = b then 2 else 3

private theorem local_slots (c d : mol.Center) :
    localFun mol localExchange c d =
      (fun k => partnerSlot d.val (localExchange (partners c.val k))) := by
  funext k
  simp only [localFun,ligIndex,canonical_neighbors,partnerSlot]

/-- Replace the abstract permutation sign with its inversion product on the
four ligand positions; this checks only one candidate and four small frames. -/
private theorem computableSign (c : mol.Center) (flip : Bool) :
    signOK mol (coordinateCfg input.certified) flip localExchange c =
      (if h : localExchange c.val ∈ mol.centers then
        decide (funSign (coordinateCfg input.certified c) *
          funSign (localFun mol localExchange c ⟨localExchange c.val,h⟩) =
          (if flip then -1 else 1) * funSign (coordinateCfg input.certified ⟨localExchange c.val,h⟩))
       else false) := by
  simp only [signOK,funSign_perm]

theorem local_inversion_candidate :
    RingLocalInversion.candidate mol (RingLocalInversion.coordinateAtom input)
      (coordinateCfg input.certified) target localExchange = true := by
  unfold RingLocalInversion.candidate
  simp only [Bool.and_eq_true,decide_eq_true_iff]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,by decide +kernel⟩,?_⟩
  intro d
  obtain ⟨i,mem⟩ := d
  have cases (a : input.certified.Atom) : a ∈ mol.centers → a = atom 0 ∨ a = atom 1 ∨ a = atom 3 ∨ a = atom 4 := by
    revert a
    decide +kernel
  rcases cases i mem with rfl | rfl | rfl | rfl
  · exact (by simp only [computableSign,coordinateCfg,coordinateVolume?,local_slots,canonical_neighbors]; decide +kernel : FinitePhysicalBranchTransport.signOK mol (coordinateCfg input.certified)
        true localExchange target = true)
  · exact (by simp only [computableSign,coordinateCfg,coordinateVolume?,local_slots,canonical_neighbors]; decide +kernel : FinitePhysicalBranchTransport.signOK mol (coordinateCfg input.certified)
        false localExchange methylene = true)
  · exact (by simp only [computableSign,coordinateCfg,coordinateVolume?,local_slots,canonical_neighbors]; decide +kernel : FinitePhysicalBranchTransport.signOK mol (coordinateCfg input.certified)
        false localExchange leftMethyl = true)
  · exact (by simp only [computableSign,coordinateCfg,coordinateVolume?,local_slots,canonical_neighbors]; decide +kernel : FinitePhysicalBranchTransport.signOK mol (coordinateCfg input.certified)
        false localExchange rightMethyl = true)

theorem equivalent_to_target_inversion :
    RingLocalInversion.fromCoordinates input admitted.2 target = true := by
  apply (RingLocalInversion.fromCoordinates_spec input admitted.2 target).2.1.mpr
  obtain ⟨e,_,physical⟩ := (RingLocalInversion.candidate_iff ..).mp local_inversion_candidate
  exact ⟨e,physical⟩

end TetraStereo.Examples.RingDimethylThiiraneBoundary

assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.admitted
assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.carbon_geometries
assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.methyl_symmetry
assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.tied_methyls
assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.no_atomic_order
assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.four_routes_missing
assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.public_projection
assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.insufficient_at_depth_zero
assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.public_at_depth_one

assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.complete_methyl_equivalence

assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.equivalent_to_target_inversion

assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.other_carbons

assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.one_methyl_D
assert_kernel_only TetraStereo.Examples.RingDimethylThiiraneBoundary.both_methyl_D
