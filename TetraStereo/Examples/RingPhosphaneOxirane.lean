import TetraStereo.Engine.RingPyramidalConstitution
import TetraStereo.Engine.RingPhysicalSignatures

/-! The phosphane-substituted oxirane with two stereogenic phosphorus arms. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRawRenumbering (molecularRecord)

/-- Fully explicit phosphane-substituted oxirane from LocalRuleCoverage. -/
def molecule : RawMolecule where
  atoms := [.aliphatic .C,.aliphatic .P,.aliphatic .P,.aliphatic .O,.aliphatic .C,
    .aliphatic .Cl,.aliphatic .F,.aliphatic .Cl,.aliphatic .F,.aliphatic .H,.aliphatic .H]
  bonds := [⟨0,1,.single⟩,⟨0,2,.single⟩,⟨0,3,.single⟩,⟨0,4,.single⟩,⟨3,4,.single⟩,
    ⟨1,5,.single⟩,⟨1,6,.single⟩,⟨2,7,.single⟩,⟨2,8,.single⟩,⟨4,9,.single⟩,⟨4,10,.single⟩]

abbrev IDs := Fin 11

def atomEquiv (i : Input) (raw : i.molecule = molecule) : i.certified.Atom ≃ IDs := rawVertices i raw
def atom (i : Input) (raw : i.molecule = molecule) (n : IDs) : i.certified.Atom := (atomEquiv i raw).symm n

@[simp] theorem atom_val (i : Input) (raw : i.molecule = molecule) (n : IDs) : (atom i raw n).val = n.val := rfl
@[simp] theorem equiv_val (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) :
    (atomEquiv i raw a).val = a.val := rfl
@[simp] theorem atom_equiv (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) :
    atom i raw (atomEquiv i raw a) = a := (atomEquiv i raw).symm_apply_apply a

theorem atom_injective (i : Input) (raw : i.molecule = molecule) : Function.Injective (atom i raw) :=
  (atomEquiv i raw).symm.injective

theorem raw_bond (i : Input) (raw : i.molecule = molecule) (n m : IDs) :
    i.molecule.bondOrder (atom i raw n).val (atom i raw m).val = molecule.bondOrder n.val m.val := by rw [raw]; rfl

theorem raw_adj (i : Input) (raw : i.molecule = molecule) (n m : IDs) :
    i.certified.moleculeGraph.Adj (atom i raw n) (atom i raw m) ↔ 0 < molecule.bondOrder n.val m.val := by
  rw [LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement
    i.admissible.1.1 i.admissible.1.2 i.supported,raw_bond]

def neighborEquiv (i : Input) (raw : i.molecule = molecule) (n : IDs) :
    {m : IDs // 0 < molecule.bondOrder n.val m.val} ≃ i.certified.moleculeGraph.Neighbor (atom i raw n) where
  toFun m := ⟨atom i raw m.val,(raw_adj i raw n m.val).mpr m.property⟩
  invFun a := ⟨atomEquiv i raw a.val,(raw_adj i raw n _).mp (by simpa using a.property)⟩
  left_inv m := Subtype.ext ((atomEquiv i raw).apply_symm_apply m.val)
  right_inv a := Subtype.ext (atom_equiv i raw a.val)

theorem raw_degrees : ∀ n : IDs, Fintype.card {m : IDs // 0 < molecule.bondOrder n.val m.val} =
    (![4,3,3,2,4,1,1,1,1,1,1] n) := by decide +kernel

theorem center_ids (i : Input) (raw : i.molecule = molecule) (c : i.certified.TetrahedralCenter) :
    c.val = atom i raw 0 ∨ c.val = atom i raw 4 := by
  have degree := (i.certified.moleculeGraph.mem_tetrahedralCenterSet c.val).mp c.property
  change Fintype.card (i.certified.moleculeGraph.Neighbor c.val) = 4 at degree
  let n := atomEquiv i raw c.val
  have same : atom i raw n = c.val := atom_equiv i raw c.val
  rw [←same,← Fintype.card_congr (neighborEquiv i raw n),raw_degrees] at degree
  have finite : ∀ k : IDs, (![4,3,3,2,4,1,1,1,1,1,1] k) = 4 → k = 0 ∨ k = 4 := by decide +kernel
  have values : n = 0 ∨ n = 4 := finite n degree
  rcases values with eq | eq <;> simp_all

private theorem pair_rows :
    (∀ a : IDs, molecule.bondOrder 9 a.val = if a = 4 then 1 else 0) ∧
    (∀ a : IDs, molecule.bondOrder 10 a.val = if a = 4 then 1 else 0) := by decide +kernel

private theorem leaf_row (i : Input) (raw : i.molecule = molecule) (u parent : IDs)
    (row : ∀ a : IDs, molecule.bondOrder u.val a.val = if a = parent then 1 else 0) :
    ∀ a : i.certified.Atom, i.molecule.bondOrder (atom i raw u).val a.val =
      if a = atom i raw parent then 1 else 0 := by
  intro a
  rw [←atom_equiv i raw a,raw_bond,row]
  simp only [(atom_injective i raw).eq_iff]

def pairAtFour (i : Input) (raw : i.molecule = molecule) (c : i.certified.TetrahedralCenter)
    (center : c.val = atom i raw 4) : TwinPair i where
  c := c
  u := atom i raw 9
  v := atom i raw 10
  distinct := (atom_injective i raw).ne (by decide +kernel)
  records := by rw [raw]; rfl
  lu := by rw [center]; exact leaf_row i raw 9 4 pair_rows.1
  lv := by rw [center]; exact leaf_row i raw 10 4 pair_rows.2

theorem all_other_tetra_twins (i : Input) (raw : i.molecule = molecule)
    (c : i.certified.TetrahedralCenter) (other : c.val ≠ atom i raw 0) : ∃ p : TwinPair i, p.c = c := by
  rcases center_ids i raw c with zero | four
  · exact False.elim (other zero)
  · exact ⟨pairAtFour i raw c four,rfl⟩

theorem phosphorus_ids (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) :
    RingPyramidalPublication.phosphorus i a = true ↔ a = atom i raw 1 ∨ a = atom i raw 2 := by
  obtain ⟨n,rfl⟩ := (atomEquiv i raw).symm.surjective a
  change RingPyramidalPublication.phosphorus i (atom i raw n) = true ↔ atom i raw n = atom i raw 1 ∨ atom i raw n = atom i raw 2
  unfold RingPyramidalPublication.phosphorus
  rw [← Fintype.card_congr (neighborEquiv i raw n),raw_degrees]
  simp only [atom_val,(atom_injective i raw).eq_iff]
  rw [raw]
  fin_cases n <;> simp [molecule,AtomSpec.aliphatic]

theorem eligible_ids (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) :
    RingPyramidalPublication.eligible i a = true ↔
      a = atom i raw 0 ∨ a = atom i raw 1 ∨ a = atom i raw 2 ∨ a = atom i raw 4 := by
  obtain ⟨n,rfl⟩ := (atomEquiv i raw).symm.surjective a
  change RingPyramidalPublication.eligible i (atom i raw n) = true ↔
    atom i raw n = atom i raw 0 ∨ atom i raw n = atom i raw 1 ∨
      atom i raw n = atom i raw 2 ∨ atom i raw n = atom i raw 4
  unfold RingPyramidalPublication.eligible RingPyramidalPublication.phosphorus
  rw [← Fintype.card_congr (neighborEquiv i raw n),raw_degrees]
  simp only [atom_val,(atom_injective i raw).eq_iff]
  rw [raw]
  fin_cases n <;> simp [molecule,AtomSpec.aliphatic]

/-- The source raw graph itself passes endpoint/uniqueness and written-neighbor admission. -/
theorem raw_admissible : molecule.StereochemicalAdmissible :=
  molecule.stereochemicalAdmissible?_eq_true_iff.mp (by decide)

def rootCenter (i : Input) (raw : i.molecule = molecule) : i.certified.TetrahedralCenter :=
  ⟨atom i raw 0,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr (by
    change Fintype.card (i.certified.moleculeGraph.Neighbor (atom i raw 0)) = 4
    rw [← Fintype.card_congr (neighborEquiv i raw 0)]
    decide)⟩

/-- The actual graph symmetry exchanges the two phosphorus arms and their corresponding halogens. -/
def branchPermutation : Equiv.Perm IDs :=
  ((Equiv.swap 1 2).trans (Equiv.swap 5 7)).trans (Equiv.swap 6 8)

private theorem permutation_records : ∀ n : IDs,
    molecule.atoms[(branchPermutation n).val]? = molecule.atoms[n.val]? := by decide
private theorem permutation_bonds : ∀ n m : IDs,
    molecule.bondOrder (branchPermutation n).val (branchPermutation m).val =
      molecule.bondOrder n.val m.val := by decide

def branchAutomorphism (i : Input) (raw : i.molecule = molecule) : GraphMap i i where
  atoms := ((atomEquiv i raw).trans branchPermutation).trans (atomEquiv i raw).symm
  records a := by
    rw [raw]
    exact congrArg (Option.map molecularRecord) (permutation_records (atomEquiv i raw a))
  bonds a b := by
    rw [raw]
    exact permutation_bonds (atomEquiv i raw a) (atomEquiv i raw b)

@[simp] theorem branchAutomorphism_atom (i : Input) (raw : i.molecule = molecule) (n : IDs) :
    (branchAutomorphism i raw).atoms (atom i raw n) = atom i raw (branchPermutation n) := by
  change (atomEquiv i raw).symm (branchPermutation (atomEquiv i raw ((atomEquiv i raw).symm n))) = _
  rw [Equiv.apply_symm_apply]
  rfl

def rootLigand (i : Input) (raw : i.molecule = molecule) (s : Fin 4) : i.certified.Atom :=
  atom i raw (![1,2,3,4] s)

theorem rootLigand_injective (i : Input) (raw : i.molecule = molecule) : Function.Injective (rootLigand i raw) := by
  intro s t eq
  have indices := (atom_injective i raw) eq
  fin_cases s <;> fin_cases t <;> simp_all [rootLigand]

theorem rootLigand_neighbor (i : Input) (raw : i.molecule = molecule) (s : Fin 4) :
    i.certified.moleculeGraph.Adj (rootCenter i raw).val (rootLigand i raw s) := by
  apply (raw_adj i raw 0 _).mpr
  fin_cases s <;> decide

/-- On the four actual neighbors of C0 the automorphism acts by the odd swap of slots 0 and 1. -/
theorem branchAutomorphism_odd_action (i : Input) (raw : i.molecule = molecule) :
    (branchAutomorphism i raw).atoms (rootCenter i raw).val = (rootCenter i raw).val ∧
      (∀ s : Fin 4, (branchAutomorphism i raw).atoms (rootLigand i raw s) =
        rootLigand i raw ((Equiv.swap 0 1) s)) ∧
      Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1) = -1 := by
  constructor
  · exact branchAutomorphism_atom i raw 0
  constructor
  · intro s
    unfold rootLigand
    rw [branchAutomorphism_atom]
    fin_cases s <;> rfl
  · exact Equiv.Perm.sign_swap (by decide)

@[simp] theorem branchAutomorphism_inverse_atom (i : Input) (raw : i.molecule = molecule) (n : IDs) :
    (branchAutomorphism i raw).atoms.symm (atom i raw n) = atom i raw (branchPermutation.symm n) := by
  change (atomEquiv i raw).symm (branchPermutation.symm (atomEquiv i raw ((atomEquiv i raw).symm n))) = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem raw_neighbor_action : ∀ n : IDs, 0 < molecule.bondOrder 0 n.val →
    branchPermutation.symm n = (Equiv.swap 1 2) n := by decide

theorem canonical_odd (i : Input) (raw : i.molecule = molecule) :
    Equiv.Perm.sign ((branchAutomorphism i raw).inverseNeighborPermutation (rootCenter i raw)
      (branchAutomorphism_odd_action i raw).1) = -1 := by
  let u : i.certified.moleculeGraph.Neighbor (rootCenter i raw).val :=
    ⟨atom i raw 1,rootLigand_neighbor i raw 0⟩
  let v : i.certified.moleculeGraph.Neighbor (rootCenter i raw).val :=
    ⟨atom i raw 2,rootLigand_neighbor i raw 1⟩
  apply GraphMap.inverseNeighborPermutation_transposition_odd (branchAutomorphism i raw) (rootCenter i raw)
    (branchAutomorphism_odd_action i raw).1 u v
  · intro eq
    have ids := (atom_injective i raw) (congrArg Subtype.val eq)
    exact (by decide : (1 : IDs) ≠ 2) ids
  · intro n
    let index := atomEquiv i raw n.val
    have positive : 0 < molecule.bondOrder 0 index.val := (raw_adj i raw 0 index).mp (by simpa [index] using n.property)
    change (branchAutomorphism i raw).atoms.symm n.val = Equiv.swap (atom i raw 1) (atom i raw 2) n.val
    rw [← atom_equiv i raw n.val,branchAutomorphism_inverse_atom,raw_neighbor_action _ positive]
    exact ((atom_injective i raw).swap_apply 1 2 index).symm

noncomputable def rawP1 : Fin 3 ≃ {m : IDs // 0 < molecule.bondOrder 1 m.val} :=
  Equiv.ofBijective (fun k => ⟨![5,6,0] k, by fin_cases k <;> decide +kernel⟩) (by decide +kernel)

noncomputable def rawP2 : Fin 3 ≃ {m : IDs // 0 < molecule.bondOrder 2 m.val} :=
  Equiv.ofBijective (fun k => ⟨![7,8,0] k, by fin_cases k <;> decide +kernel⟩) (by decide +kernel)

noncomputable def p1 (i : Input) (raw : i.molecule = molecule) :
    Fin 3 ≃ i.certified.moleculeGraph.Neighbor (atom i raw 1) := rawP1.trans (neighborEquiv i raw 1)
noncomputable def p2 (i : Input) (raw : i.molecule = molecule) :
    Fin 3 ≃ i.certified.moleculeGraph.Neighbor (atom i raw 2) := rawP2.trans (neighborEquiv i raw 2)

@[simp] theorem p1_val (i : Input) (raw : i.molecule = molecule) (k : Fin 3) :
    (p1 i raw k).val = atom i raw (![5,6,0] k) := rfl
@[simp] theorem p2_val (i : Input) (raw : i.molecule = molecule) (k : Fin 3) :
    (p2 i raw k).val = atom i raw (![7,8,0] k) := rfl

theorem selected_phosphorus (i : Input) (raw : i.molecule = molecule)
    (q : RingActivePairs.Site i) (a : i.certified.Atom)
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (which : a = atom i raw 1 ∨ a = atom i raw 2) :
    RingPyramidalPublication.focusP i q = some a := by
  simp [RingPyramidalPublication.focusP,real,current,(phosphorus_ids i raw a).mpr which]

open LocalizedGenericMarkedRecalculation RingSpatialTransport
open RingNumberedHydrogenGeometry RingWrittenPHReadings RingPyramidalChoices

theorem p1_order (i : Input) (raw : i.molecule = molecule) :
    order (phosphorusFrameIds (p1 i raw)) 1 = [5,6,0,1] := rfl

theorem p2_order (i : Input) (raw : i.molecule = molecule) :
    order (phosphorusFrameIds (p2 i raw)) 1 = [7,8,0,2] := rfl

theorem p1_moved (i : Input) (raw : i.molecule = molecule) :
    readback? (geometry (reindexed i i (branchAutomorphism i raw).atoms)) [5,6,0,1] =
    readback? (geometry i.spatial) [7,8,0,2] := by
  rw [←p1_order i raw,←p2_order i raw]
  apply phosphorus_reindexed_order
  intro k
  fin_cases k <;> exact branchAutomorphism_inverse_atom i raw _

theorem p2_moved (i : Input) (raw : i.molecule = molecule) :
    readback? (geometry (reindexed i i (branchAutomorphism i raw).atoms)) [7,8,0,2] =
    readback? (geometry i.spatial) [5,6,0,1] := by
  rw [←p2_order i raw,←p1_order i raw]
  apply phosphorus_reindexed_order
  intro k
  fin_cases k <;> exact branchAutomorphism_inverse_atom i raw _

theorem equal_hands_agreement (i : Input) (raw : i.molecule = molecule)
    (same : readback? (geometry i.spatial) [5,6,0,1] =
      readback? (geometry i.spatial) [7,8,0,2]) :
    BranchAgreement i (rootCenter i raw) (reindexed i i (branchAutomorphism i raw).atoms) := by
  refine ⟨?_,?_⟩
  · intro b other reached noTwins
    exact False.elim (noTwins (all_other_tetra_twins i raw b (fun eq => other (Subtype.ext eq))))
  · intro a hp reached
    rcases (phosphorus_ids i raw a).mp hp with one | two
    · subst a
      apply phosphorus_orders_of_one i.spatial _ _ (p1 i raw) ?_ _ false 1
      rw [p1_order,p1_moved]
      exact same
    · subst a
      apply phosphorus_orders_of_one i.spatial _ _ (p2 i raw) ?_ _ false 1
      rw [p2_order,p2_moved]
      exact same.symm

theorem native_root_refusal (i : Input) (raw : i.molecule = molecule)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (same : readback? (geometry i.spatial) [5,6,0,1] =
      readback? (geometry i.spatial) [7,8,0,2]) :
    RingChemicalGraphProof.root i (rootCenter i raw).val = some none :=
  (branchAutomorphism i raw).odd_branch_refusal admitted (rootCenter i raw)
    (branchAutomorphism_odd_action i raw).1 (canonical_odd i raw) (equal_hands_agreement i raw same)

assert_kernel_only native_root_refusal
assert_kernel_only center_ids
assert_kernel_only phosphorus_ids
assert_kernel_only branchAutomorphism
assert_kernel_only canonical_odd
end TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane

namespace TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.Representatives
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingWrittenPHReadings

def base : List CartesianPoint3 := [
  ⟨0,0,0⟩,⟨2,2,2⟩,⟨-2,-2,2⟩,⟨2,-2,-2⟩,⟨-2,2,-2⟩,
  ⟨4,1,2⟩,⟨2,4,1⟩,⟨-1,-4,2⟩,⟨-4,-2,1⟩,⟨-4,2,-3⟩,⟨-2,4,-3⟩]

def leftPoints : Option RS → CartesianPoint3 × CartesianPoint3
  | some .R => (⟨4,1,2⟩,⟨2,4,1⟩)
  | some .S => (⟨2,4,1⟩,⟨4,1,2⟩)
  | none => (⟨2,4,1⟩,⟨2,4,1⟩)
def rightPoints : Option RS → CartesianPoint3 × CartesianPoint3
  | some .S => (⟨-1,-4,2⟩,⟨-4,-2,1⟩)
  | some .R => (⟨-4,-2,1⟩,⟨-1,-4,2⟩)
  | none => (⟨-4,-2,1⟩,⟨-4,-2,1⟩)

def representative (root : RS) (left right : Option RS) : SpatialConfiguration :=
  let reflect := root == .R
  let l := leftPoints (if reflect then left.map RS.swap else left)
  let r := rightPoints (if reflect then right.map RS.swap else right)
  let points := base.set 5 l.1 |>.set 6 l.2 |>.set 7 r.1 |>.set 8 r.2
  ⟨if reflect then points.map (fun p => {p with x := -p.x}) else points⟩

def hand (g : SpatialConfiguration) (ids : List Nat) : Option RS := readback? (geometry g) ids

theorem representative_checks : ∀ (root : RS) (left right : Option RS),
    (representative root left right).positions.length = 11 ∧
    hand (representative root left right) [1,2,3,4] = some root ∧
    hand (representative root left right) [5,6,0,1] = left ∧
    hand (representative root left right) [7,8,0,2] = right ∧
    (hand (representative root left right) [0,3,9,10]).isSome = true := by
  intro root left right
  cases root <;> cases left with
  | none => cases right with
    | none => decide +kernel
    | some r => cases r <;> decide +kernel
  | some l => cases l <;> cases right with
    | none => decide +kernel
    | some r => cases r <;> decide +kernel
end TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.Representatives
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.Representatives.representative_checks

namespace TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingWrittenPHReadings RingSpatialTransport RingPyramidalChoices
open RingChemicalPriority.ReferenceFrame (readback_all_permutations)
open Representatives (representative hand representative_checks)

private noncomputable def c0Row (i : Input) (raw : i.molecule = molecule) :
    Fin 4 ≃ i.certified.moleculeGraph.Neighbor (atom i raw 0) :=
  (Equiv.ofBijective (fun k : Fin 4 => (⟨![1,2,3,4] k,by fin_cases k <;> decide⟩ :
    {m : IDs // 0 < molecule.bondOrder 0 m.val})) (by decide)).trans (neighborEquiv i raw 0)

private noncomputable def c4Row (i : Input) (raw : i.molecule = molecule) :
    Fin 4 ≃ i.certified.moleculeGraph.Neighbor (atom i raw 4) :=
  (Equiv.ofBijective (fun k : Fin 4 => (⟨![0,3,9,10] k,by fin_cases k <;> decide⟩ :
    {m : IDs // 0 < molecule.bondOrder 4 m.val})) (by decide)).trans (neighborEquiv i raw 4)

private theorem orders_perm {i : Input} {a : i.certified.Atom}
    (d e : Fin 4 ≃ i.certified.moleculeGraph.Neighbor a) :
    (order (fun k => (d k).val.val) 1).Perm (order (fun k => (e k).val.val) 1) := by
  let π : Equiv.Perm (Fin 4) := d.trans e.symm
  have h := π.map_finRange_perm.map (fun k => (e k).val.val)
  simp only [List.map_map,Function.comp_def,π,Equiv.trans_apply,Equiv.apply_symm_apply] at h
  exact h

private theorem center_row {i : Input} (c : i.certified.TetrahedralCenter)
    {a : i.certified.Atom} (atAtom : c.val = a)
    (d : Fin 4 ≃ i.certified.moleculeGraph.Neighbor a) :
    (order (centerIds i c) 1).Perm (order (fun k => (d k).val.val) 1) := by
  subst a
  exact orders_perm (tetraEnumeration i c) d

private def c4Center (i : Input) (raw : i.molecule = molecule) : i.certified.TetrahedralCenter :=
  ⟨atom i raw 4,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr (by
    change Fintype.card (i.certified.moleculeGraph.Neighbor (atom i raw 4)) = 4
    rw [← Fintype.card_congr (neighborEquiv i raw 4)]
    decide)⟩

private theorem isSome_perm {g : Geometry} {a b : List Nat} (p : a.Perm b)
    (nd : b.Nodup) (four : b.length = 4) :
    (readback? g a).isSome = true ↔ (readback? g b).isSome = true :=
  ⟨fun seen => readback_all_permutations (p.nodup_iff.mpr nd) (p.length_eq.trans four) seen b p.symm,
    fun seen => readback_all_permutations nd four seen a p⟩

/-- Admission examines just the two carbon determinants. A flat phosphorus arm
is a possible admitted input and remains a distinct case of the classification. -/
theorem coordinates_iff (i : Input) (raw : i.molecule = molecule) :
    LocalizedChemicalRing.coordinatesAdmitted i = true ↔
      (hand i.spatial [1,2,3,4]).isSome = true ∧ (hand i.spatial [0,3,9,10]).isSome = true := by
  change decide (∀ c, LocalizedChemicalRingPhysicalAdmission.centerAdmitted i.certified c = true) = true ↔ _
  rw [decide_eq_true_eq]
  have c0 (c : i.certified.TetrahedralCenter) (atZero : c.val = atom i raw 0) :
      LocalizedChemicalRingPhysicalAdmission.centerAdmitted i.certified c = true ↔
      (hand i.spatial [1,2,3,4]).isSome = true := by
    rw [centerAdmitted_readback]
    exact isSome_perm (center_row c atZero (c0Row i raw)) (by decide) rfl
  have c4 (c : i.certified.TetrahedralCenter) (atFour : c.val = atom i raw 4) :
      LocalizedChemicalRingPhysicalAdmission.centerAdmitted i.certified c = true ↔
      (hand i.spatial [0,3,9,10]).isSome = true := by
    rw [centerAdmitted_readback]
    exact isSome_perm (center_row c atFour (c4Row i raw)) (by decide) rfl
  constructor
  · intro all
    exact ⟨(c0 (rootCenter i raw) rfl).mp (all _),(c4 (c4Center i raw) rfl).mp (all _)⟩
  · rintro ⟨zero,four⟩ c
    rcases center_ids i raw c with h | h
    · exact (c0 c h).mpr zero
    · exact (c4 c h).mpr four

private theorem other_frames_of_three_hands (i : Input) (raw : i.molecule = molecule)
    (x w : SpatialConfiguration)
    (zero : hand x [1,2,3,4] = hand w [1,2,3,4])
    (one : hand x [5,6,0,1] = hand w [5,6,0,1])
    (two : hand x [7,8,0,2] = hand w [7,8,0,2]) :
    OtherFramesAgree [pairAtFour i raw (c4Center i raw) rfl] x w := by
  let p := pairAtFour i raw (c4Center i raw) rfl
  constructor
  · intro c outside
    rcases center_ids i raw c with atZero | atFour
    · exact LocalizedMarkedMolecularConfiguration.readback_perm_congr [1,2,3,4] _ (by decide) rfl
        (center_row c atZero (c0Row i raw)) zero
    · exact (outside p (by simp [p]) (Subtype.ext atFour.symm)).elim
  · intro a hp
    rcases (phosphorus_ids i raw a).mp hp with rfl | rfl
    · exact phosphorus_orders_of_one x w _ (p1 i raw) one (phosphorusEnumeration i _ hp) false 1
    · exact phosphorus_orders_of_one x w _ (p2 i raw) two (phosphorusEnumeration i _ hp) false 1

/-- The same bijection matches the evaluator's materialized rows at all roots and
all committed sphere prefixes. It fixes all atom IDs except the interchangeable H9/H10. -/
theorem stores_of_three_hands (i : Input) (raw : i.molecule = molecule) (x w : SpatialConfiguration)
    (hx : x.positions.length = size i) (hw : w.positions.length = size i)
    (ax : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true)
    (aw : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true)
    (zero : hand x [1,2,3,4] = hand w [1,2,3,4])
    (one : hand x [5,6,0,1] = hand w [5,6,0,1])
    (two : hand x [7,8,0,2] = hand w [7,8,0,2]) :
    ∃ g : GraphMap i i, PairActions [pairAtFour i raw (c4Center i raw) rfl] g ∧
      ∀ root k, k ≤ RingActiveDistanceSchedule.height (atGeometry i w hw) + 1 →
        ((RingSphereStore.rows (atGeometry i w hw) root k).map fun row =>
          (RingSphereStore.siteMap (g.atTables w x hw hx) row.1,row.2)).Perm
        (RingSphereStore.rows (atGeometry i x hx) (g.atoms root) k) := by
  obtain ⟨g,action,_,hands⟩ := (many_twin_frames_iff _ (by simp) w x hw hx aw ax).mpr
    (other_frames_of_three_hands i raw x w zero one two)
  exact ⟨g,action,RingSphereStore.spelling_rows (g.atTables w x hw hx) aw hands⟩

/-- Every atom request, including repeated or invalid IDs, factors through the
C0 determinant and the two phosphorus determinants on admitted tables. -/
theorem report_of_three_hands (i : Input) (raw : i.molecule = molecule) (x w : SpatialConfiguration)
    (hx : x.positions.length = size i) (hw : w.positions.length = size i)
    (ax : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true)
    (aw : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true)
    (zero : hand x [1,2,3,4] = hand w [1,2,3,4])
    (one : hand x [5,6,0,1] = hand w [5,6,0,1])
    (two : hand x [7,8,0,2] = hand w [7,8,0,2]) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule x ids = RingHydrogenReport.fromRaw? molecule w ids := by
  let p := pairAtFour i raw (c4Center i raw) rfl
  have closed : RingHydrogenCompletion.plan i.molecule = [] := by rw [raw]; decide
  rw [←raw]
  apply many_twin_report [p] (by simp) w x hw hx closed (aw.trans ax.symm) _ ids
  intro _
  exact other_frames_of_three_hands i raw x w zero one two

end TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane

namespace TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
open OneCenter
open LocalizedChemicalRing (Input)
open RingWrittenPHReadings RingSpatialTransport RingHydrogenCompletion
open Representatives (representative hand representative_checks)

private def referencePoints : SpatialConfiguration := representative .S none none
private theorem refExists : (LocalizedChemicalRing.admitRawSpatial? molecule referencePoints).isSome = true := by
  decide +kernel
private def reference : Input := (LocalizedChemicalRing.admitRawSpatial? molecule referencePoints).get refExists
private theorem refRaw : reference.molecule = molecule :=
  (RingChemicalReport.admission_fields (Option.some_get refExists).symm).1
private theorem refSize : size reference = 11 := by decide +kernel
theorem closed : plan molecule = [] := by decide +kernel

/-- A raw report exists exactly on full tables with two nonzero carbon volumes
and in-range atom requests. A zero phosphorus volume is handled by the evaluator. -/
theorem public_domain (x : SpatialConfiguration) (ids : List Nat) :
    (∃ rows, RingHydrogenReport.fromRaw? molecule x ids = some rows) ↔
      x.positions.length = 11 ∧ (hand x [1,2,3,4]).isSome = true ∧
      (hand x [0,3,9,10]).isSome = true ∧ ∀ n ∈ ids, n < 11 := by
  rw [RingHydrogenReport.fromRaw_closed_eq closed]
  by_cases len : x.positions.length = 11
  · let j := atGeometry reference x (len.trans refSize.symm)
    have raw : j.molecule = molecule := refRaw
    have gate := coordinates_iff j raw
    have h := closed_domain j (raw ▸ closed) ids
    change (∃ rows, RingChemicalReport.fromRaw? j.molecule x ids = some rows) ↔ _ at h
    rw [raw,gate] at h
    change (∃ rows, RingChemicalReport.fromRaw? molecule x ids = some rows) ↔
      (∀ n ∈ ids, n < 11) ∧ (hand x [1,2,3,4]).isSome = true ∧ (hand x [0,3,9,10]).isSome = true at h
    constructor
    · intro found
      obtain ⟨bounds,zero,four⟩ := h.mp found
      exact ⟨len,zero,four,bounds⟩
    · rintro ⟨_,zero,four,bounds⟩
      exact h.mpr ⟨bounds,zero,four⟩
  · simp only [len,false_and,iff_false]
    rintro ⟨rows,got⟩
    obtain ⟨_,s,_,found,_⟩ := (RingChemicalReport.fromRaw_domain_iff ..).mp ⟨rows,got⟩
    obtain ⟨raw,pos⟩ := RingChemicalReport.admission_fields found
    apply len
    rw [←pos,full_original]
    exact (s.molecule.toSemanticMolecule?_atomCount _ s.agreement.1).trans (congrArg RawMolecule.atomCount raw)

/-- A single finite classification of all coordinate tables. Failure here is
a source admission failure before any ligand comparison is required. -/
def signature? (x : SpatialConfiguration) : Option (RS × Option RS × Option RS) := do
  guard (x.positions.length = 11 ∧ (hand x [0,3,9,10]).isSome = true)
  let c ← hand x [1,2,3,4]
  return (c,hand x [5,6,0,1],hand x [7,8,0,2])

/-- All rational coordinates and all requested original atom lists reduce to
eighteen fixed raw inputs, including independently flat phosphorus centers. -/
theorem public_normal_form (x : SpatialConfiguration) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule x ids =
      (signature? x).bind fun s => RingHydrogenReport.fromRaw? molecule (representative s.1 s.2.1 s.2.2) ids := by
  have reject (off : ¬ (x.positions.length = 11 ∧ (hand x [1,2,3,4]).isSome = true ∧
      (hand x [0,3,9,10]).isSome = true)) : RingHydrogenReport.fromRaw? molecule x ids = none := by
    cases found : RingHydrogenReport.fromRaw? molecule x ids with
    | none => rfl
    | some rows =>
      obtain ⟨len,zero,four,_⟩ := (public_domain x ids).mp ⟨rows,found⟩
      exact (off ⟨len,zero,four⟩).elim
  by_cases pass : x.positions.length = 11 ∧ (hand x [0,3,9,10]).isSome = true
  · cases root : hand x [1,2,3,4] with
    | none => simp [signature?,pass,root,reject (by simp [root])]
    | some c =>
      let y := representative c (hand x [5,6,0,1]) (hand x [7,8,0,2])
      obtain ⟨lengthY,zeroY,leftY,rightY,fourY⟩ := representative_checks c (hand x [5,6,0,1]) (hand x [7,8,0,2])
      have fx := pass.1.trans refSize.symm
      have fy : y.positions.length = size reference := lengthY.trans refSize.symm
      have ax := (coordinates_iff (atGeometry reference x fx) refRaw).mpr ⟨by change (hand x [1,2,3,4]).isSome = true; rw [root]; rfl,pass.2⟩
      have ay := (coordinates_iff (atGeometry reference y fy) refRaw).mpr ⟨by change (hand y [1,2,3,4]).isSome = true; rw [show hand y [1,2,3,4] = some c from zeroY]; rfl,fourY⟩
      simpa only [signature?,guard,pass,if_true,root,Option.bind_some,pure,Option.pure_def] using
        report_of_three_hands reference refRaw x y fx fy ax ay (root.trans zeroY.symm) leftY.symm rightY.symm ids
  · rw [reject (fun h => pass ⟨h.1,h.2.2⟩)]
    simp [signature?,pass]

end TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane

namespace TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
open OneCenter
open LocalizedChemicalRing (Input)
open RingWrittenPHReadings RingSpatialTransport
open RingNestedActivePair (Labels)
open Representatives (representative hand representative_checks)

/-- Read the requested carbon in the fixed P1, P2, O, C4 frame. -/
def rootLabels (root : RS) (left right : Option RS) : Option Labels :=
  match left,right with
  | none,none => none
  | some _,none => some (.chiral root,.chiral root.swap)
  | none,some _ => some (.chiral root.swap,.chiral root)
  | some l,some r => if l = r then none else
    let h := if l = .R then root else root.swap
    some (.pseudoasymmetric (pseudoRSOfRS h),.pseudoasymmetric (pseudoRSOfRS h))

def labels (root : RS) (left right : Option RS) : Nat → Option Labels
  | 0 => rootLabels root left right
  | 1 => left.map fun h => (.chiral h,.chiral h.swap)
  | 2 => right.map fun h => (.chiral h,.chiral h.swap)
  | _ => none

/-- The finite test uses all eleven original atom IDs, once per representative. -/
def RepresentativeReports : Prop := ∀ (c : RS) (l r : Option RS),
  RingHydrogenReport.fromRaw? molecule (representative c l r) (List.range 11) =
    some ((List.range 11).map fun n => (n,labels c l r n))

def expectedReport (x : SpatialConfiguration) (ids : List Nat) : Option RingGroupedReport.Report := do
  let (c,l,r) ← signature? x
  guard (∀ n ∈ ids, n < 11)
  return ids.map fun n => (n,labels c l r n)

private theorem representative_signature (c : RS) (l r : Option RS) :
    signature? (representative c l r) = some (c,l,r) := by
  obtain ⟨len,zero,left,right,four⟩ := representative_checks c l r
  simp [signature?,len,zero,left,right,four]

/-- Equivalence between eighteen ground evaluations and exact public behavior on
every rational coordinate table and every list of original atom IDs. -/
theorem universal_reports_iff :
    (∀ x ids, RingHydrogenReport.fromRaw? molecule x ids = expectedReport x ids) ↔
      RepresentativeReports := by
  constructor
  · intro all c l r
    have bounds : ∀ n ∈ List.range 11, n < 11 := fun _ => List.mem_range.mp
    simpa only [expectedReport,representative_signature,Option.bind_some,guard,bounds,if_true,
      pure,Option.pure_def] using all (representative c l r) (List.range 11)
  · intro full x ids
    rw [public_normal_form]
    cases hs : signature? x with
    | none => simp [expectedReport,hs]
    | some s =>
      obtain ⟨c,l,r⟩ := s
      let y := representative c l r
      obtain ⟨len,zero,_,_,four⟩ := representative_checks c l r
      by_cases bounds : ∀ n ∈ ids, n < 11
      · let j := atGeometry reference y (len.trans refSize.symm)
        have raw : j.molecule = molecule := refRaw
        have pos : j.spatial = y := rfl
        have count : j.molecule.atomCount = 11 := raw ▸ rfl
        have valid := (coordinates_iff j raw).mpr ⟨by rw [pos]; change (hand (representative c l r) [1,2,3,4]).isSome = true; rw [zero]; rfl,four⟩
        have all := RingPhysicalSignatures.project_full_report j (raw ▸ closed) valid (labels c l r)
          (by rw [count,raw,pos]; exact full c l r) ids (count ▸ bounds)
        rw [raw,pos] at all
        simp only [expectedReport,hs,Option.bind_some,Option.bind_eq_bind,guard,if_pos bounds,pure]
        exact all
      · have absent : RingHydrogenReport.fromRaw? molecule y ids = none := by
          cases got : RingHydrogenReport.fromRaw? molecule y ids with
          | none => rfl
          | some rows => exact (bounds ((public_domain y ids).mp ⟨rows,got⟩).2.2.2).elim
        simpa [expectedReport,hs,bounds,y] using absent
end TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane

assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.public_normal_form
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.universal_reports_iff

assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.stores_of_three_hands
