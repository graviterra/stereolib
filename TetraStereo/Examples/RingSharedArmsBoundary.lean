import TetraStereo.Engine.RingConstitutionalCoverage
import TetraStereo.Engine.LocalizedChemicalRingPhysicalCertificate

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

namespace TetraStereo.Examples.RingSharedArmsBoundary
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation



def molecule : RawMolecule where
  atoms := [.aliphatic .C,.aliphatic .C,.aliphatic .C,.aliphatic .S,.aliphatic .F] ++
    List.replicate 5 (.aliphatic .H)
  bonds := ([(0,1),(0,2),(1,3),(2,3),(0,4),(0,5),(1,6),(1,7),(2,8),(2,9)] :
    List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

def spatial : SpatialConfiguration :=
  ⟨[⟨0,0,0⟩,⟨2,0,2⟩,⟨-2,0,2⟩,⟨0,3,4⟩,⟨0,2,-2⟩,⟨0,-2,-2⟩,
    ⟨4,1,0⟩,⟨4,-4,4⟩,⟨-4,1,0⟩,⟨-4,-4,4⟩]⟩

def geometry : Geometry := fun i => spatial.positions[i]?

def input := (LocalizedChemicalRing.admitRawSpatial? molecule spatial).get (by decide +kernel)

open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission

private def rawVolume (a b c d : Nat) : Option ℚ := do
  return CartesianPoint3.orientedVolume (← geometry a) (← geometry b) (← geometry c) (← geometry d)

/-- Enumerate ordered quadruples of bonded sites, without choosing the
physical frame's ordering. Every quadruple with distinct sites has nonzero volume. -/
private theorem neighbor_volumes (atom : Fin 10) :
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

/-- Each of the three carbons is the barycenter of its four neighbors, and the
four neighbors span a tetrahedron of nonzero volume at each carbon. -/
theorem carbon_geometries : RingCarbonReport.carbons molecule = [0,1,2] ∧
    (RingCarbonReport.carbons molecule).all (fun i =>
      let ns := molecule.writtenNeighbors i
      (readback? geometry ns).isSome && [CartesianPoint3.x, CartesianPoint3.y, CartesianPoint3.z].all (fun axis =>
        ((ns.mapM fun j => (geometry j).map axis).map List.sum) == ((geometry i).map fun x => 4 * axis x))) = true := by
  decide +kernel

open CertifiedLocalizedCIPInput Certificate.CanonicalSphereKey

private def focus := canonicalCenterRoot 0
private def arm (i : Nat) := ((occurrenceLigandCursors molecule focus).find? fun c => c.node.atom == i).getD
  ⟨focus,none⟩

/-- All children have been visited before the specified horizon in this
retained digraph. Extra fuel has no effect on the atomic-number tree. -/
def exhausted (m : RawMolecule) : Nat → CanonicalRerootCursor → Bool
  | 0,_ => false
  | n+1,c => (c.children m).all (exhausted m n)

private theorem mapM_agree {α β : Type} (xs : List α) (f h : α → Option β)
    (agree : ∀ x ∈ xs, f x = h x) : xs.mapM f = xs.mapM h := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons,List.mapM_cons,agree x List.mem_cons_self,
      ih (fun a ha => agree a (List.mem_cons_of_mem _ ha))]

theorem atomic_tree_stable {m : RawMolecule} {c : CanonicalRerootCursor} {n : Nat}
    (doneAll : exhausted m n c = true) (width extra : Nat) :
    atomicTree m width (n+extra) c = atomicTree m width n c := by
  induction n generalizing c with
  | zero => contradiction
  | succ n ih =>
    have agree := mapM_agree (c.children m) (atomicTree m width (n+extra)) (atomicTree m width n)
      (fun x hx => ih ((List.all_eq_true.mp doneAll) x hx))
    rw [Nat.succ_add]
    simp only [atomicTree,agree]

/-- The two arms have the same atom-number tree at every observation depth.
Both complete traversals have already terminated by the fifth sphere. -/
theorem tied_at_every_depth (depth : Nat) :
    atomicTree molecule 3 depth (arm 1) = atomicTree molecule 3 depth (arm 2) := by
  by_cases low : depth < 5
  · have small : ∀ k : Fin 5, atomicTree molecule 3 k.val (arm 1) = atomicTree molecule 3 k.val (arm 2) := by
      intro k
      fin_cases k <;> rfl
    exact small ⟨depth,low⟩
  · have h : depth = 5 + (depth-5) := by omega
    rw [h,atomic_tree_stable (m:=molecule) (n:=5) (c:=arm 1) (by decide +kernel),
      atomic_tree_stable (m:=molecule) (n:=5) (c:=arm 2) (by decide +kernel)]
    rfl

/-- Both earlier-stereo inventories are empty. On the two retained ring arms
the complete labelled trees agree through mass, ring-duplicate priority, unit
class and both stereo tags, including their closures at C0. -/
theorem matched_arms :
    IsotopePriority.TreesMatch molecule (CursorTie.observe? molecule [0] [])
      (IsotopePriority.budget molecule+1) (arm 1) (arm 2) ∧
    carbonSites molecule (molecule.atomCount+1) (arm 1).node = some [] ∧
    carbonSites molecule (molecule.atomCount+1) (arm 2).node = some [] := by
  refine ⟨IsotopePriority.treesMatch_sound ?_,?_⟩ <;> decide +kernel

theorem no_atomic_order_of_equal_trees {m : RawMolecule} {root : Nat}
    {f : RawMolecule.CanonicalBranchNode} {a b : CanonicalRerootCursor} {d : Nat}
    (site : occurrence? m [root] = some f) (left : a ∈ occurrenceLigandCursors m f)
    (right : b ∈ occurrenceLigandCursors m f) (distinct : a ≠ b)
    (trees : atomicTree m 3 d a = atomicTree m 3 d b) : atomicOrder? m [root] d = none := by
  unfold atomicOrder?
  cases h : atomicRanking? m [root] d with
  | none => rfl
  | some r =>
    exfalso
    obtain ⟨n,hn,_,_,unique⟩ := (atomicRanking?_isSome_iff_keys m [root] d).mp (by rw [h]; rfl)
    rw [Option.some.inj (hn.symm.trans site)] at unique
    apply distinct
    apply List.inj_on_of_nodup_map unique left right
    simp [molecularAtomicKey?,trees]

theorem no_atomic_order (d : Nat) : atomicOrder? molecule [0] d = none :=
  no_atomic_order_of_equal_trees (f:=focus) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (tied_at_every_depth d)

/-- The pendant-arm test requires two distinct individually silent arms.
This condition is independent of the depth used to compare the other arms. -/
def silentWalk (m : RawMolecule) (c : CanonicalRerootCursor) : Bool :=
  (RingSilentPair.walk? m (IsotopePriority.budget m+1) c).any fun xs =>
    xs.all fun s => decide (RingSilentPair.SilentSite m s)

theorem silent_pair_needs_two {m depth i} (cert : RingSilentPair.Certificate m depth i) :
    silentWalk m cert.left = true ∧ silentWalk m cert.right = true := by
  constructor
  · simp only [silentWalk,cert.full.1,Option.any_some,List.all_eq_true,decide_eq_true_eq]
    exact fun x hx => cert.silent x (List.mem_append_left _ hx)
  · simp only [silentWalk,cert.full.2,Option.any_some,List.all_eq_true,decide_eq_true_eq]
    exact fun x hx => cert.silent x (List.mem_append_right _ hx)

/-- Sulfur 3 occurs in both complete walks. The remaining target ligands
are H and F; only the H walk satisfies all of the pendant-arm site tests. -/
theorem shared_sulfur :
    (RingSilentPair.walk? molecule (IsotopePriority.budget molecule+1) (arm 1)).any (fun xs =>
      xs.any fun c => c.node.atom == 3) = true ∧
    (RingSilentPair.walk? molecule (IsotopePriority.budget molecule+1) (arm 2)).any (fun xs =>
      xs.any fun c => c.node.atom == 3) = true ∧
    (∀ c ∈ occurrenceLigandCursors molecule focus, silentWalk molecule c = true ↔ c.node.atom = 5) := by
  decide +kernel

theorem no_silent_pair_of_at_most_one {m : RawMolecule} {i depth f}
    (site : occurrence? m [i] = some f)
    (only : ∀ a ∈ occurrenceLigandCursors m f, ∀ b ∈ occurrenceLigandCursors m f,
      silentWalk m a = true → silentWalk m b = true → a.node.atom = b.node.atom) :
    RingSilentPair.check? m depth i = none := by
  cases h : RingSilentPair.check? m depth i with
  | none => rfl
  | some c =>
    have atFocus : c.focus = f := Option.some.inj (c.reached.symm.trans site)
    obtain ⟨l,r⟩ := silent_pair_needs_two c
    exact False.elim (c.distinct (only _ (atFocus ▸ c.leftAt) _ (atFocus ▸ c.rightAt) l r))

theorem no_silent_pair (d : Nat) : RingSilentPair.check? molecule d 0 = none :=
  no_silent_pair_of_at_most_one (f:=focus) (by decide +kernel) (fun a ha b hb l r =>
    ((shared_sulfur.2.2 a ha).mp l).trans ((shared_sulfur.2.2 b hb).mp r).symm)

/-- All five routes in this public evaluator fail at C0 for any depth and
any geometry. Changing the coordinate data cannot replace missing comparison
coverage for the two branches of the shared sulfur ring. -/
theorem five_routes_missing (g : Geometry) (d : Nat) :
    LocalIsotopeCarbonReport.at? molecule g d 0 = none ∧
    RingTerminalPair.check? molecule 0 = none ∧
    RecursiveSigned.derive? molecule g d molecule.atomCount [0] = none ∧
    FrozenSigned.check? molecule g d 0 = none ∧ RingSilentPair.check? molecule d 0 = none := by
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
  refine ⟨?_,no_silent_pair d⟩
  cases h : FrozenSigned.check? molecule g d 0 with
  | none => rfl
  | some c =>
    have built := c.frame.built
    simp [ReferenceFrame.molecularFrame?,outside] at built

theorem no_depth (d : Nat) : RecursiveSigned.report? input d = none := by
  cases h : RecursiveSigned.report? input d with
  | none => rfl
  | some r =>
    have covered := (RecursiveSigned.report?_isSome_iff input d).mp (by rw [h]; rfl)
    have site : 0 ∈ RingCarbonReport.carbons input.molecule := by decide +kernel
    have atSite := covered 0 site
    have raw : input.molecule = molecule := by decide +kernel
    rw [raw] at atSite
    obtain ⟨one,two,three,four,five⟩ := five_routes_missing (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) d
    simp [one,two,three,four,five] at atSite

theorem universal_coverage_false :
    ¬ (∀ i : LocalizedChemicalRing.Input, LocalizedChemicalRing.coordinatesAdmitted i = true →
       ∃ d, (RecursiveSigned.report? i d).isSome = true) := by
  intro claimed
  obtain ⟨d,result⟩ := claimed input admitted.2
  simp [no_depth d] at result

/-- The molecular reflection fixes C0, sulfur, F and the target H while
exchanging the two paths and all corresponding methylene hydrogens. -/
def exchange (i : Nat) : Nat := [0,2,1,3,4,5,8,9,6,7][i]?.getD i

theorem reflection : Reflects molecule geometry exchange ∧ exchange 0 = 0 ∧ exchange 1 = 2 := by
  constructor
  · constructor <;> decide +kernel
  · decide +kernel

end TetraStereo.Examples.RingSharedArmsBoundary

assert_kernel_only TetraStereo.Examples.RingSharedArmsBoundary.admitted
assert_kernel_only TetraStereo.Examples.RingSharedArmsBoundary.carbon_geometries
assert_kernel_only TetraStereo.Examples.RingSharedArmsBoundary.tied_at_every_depth
assert_kernel_only TetraStereo.Examples.RingSharedArmsBoundary.no_silent_pair
assert_kernel_only TetraStereo.Examples.RingSharedArmsBoundary.five_routes_missing
assert_kernel_only TetraStereo.Examples.RingSharedArmsBoundary.no_depth
assert_kernel_only TetraStereo.Examples.RingSharedArmsBoundary.universal_coverage_false
assert_kernel_only TetraStereo.Examples.RingSharedArmsBoundary.reflection

assert_kernel_only TetraStereo.Examples.RingSharedArmsBoundary.matched_arms
