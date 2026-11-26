import TetraStereo.Engine.RingSphereStore

/-! Whole-branch refusal at C0 of 1-bromo-1-fluorocyclopropane. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingHydrogenSpelling.BranchCoverage
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRawRenumbering (molecularRecord)



def molecule : RawMolecule where
  atoms := [.aliphatic .C,.aliphatic .C,.aliphatic .C,.aliphatic .Br,.aliphatic .F,
    .aliphatic .H,.aliphatic .H,.aliphatic .H,.aliphatic .H]
  bonds := [⟨0,1,.single⟩,⟨0,2,.single⟩,⟨1,2,.single⟩,⟨0,3,.single⟩,⟨0,4,.single⟩,
    ⟨1,5,.single⟩,⟨1,6,.single⟩,⟨2,7,.single⟩,⟨2,8,.single⟩]

abbrev IDs := Fin 9

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
    if n.val < 3 then 4 else 1 := by decide

theorem center_ids (i : Input) (raw : i.molecule = molecule) (c : i.certified.TetrahedralCenter) :
    c.val = atom i raw 0 ∨ c.val = atom i raw 1 ∨ c.val = atom i raw 2 := by
  have degree := (i.certified.moleculeGraph.mem_tetrahedralCenterSet c.val).mp c.property
  change Fintype.card (i.certified.moleculeGraph.Neighbor c.val) = 4 at degree
  let n := atomEquiv i raw c.val
  have same : atom i raw n = c.val := atom_equiv i raw c.val
  rw [←same,← Fintype.card_congr (neighborEquiv i raw n),raw_degrees] at degree
  have low : n.val < 3 := by split at degree <;> omega
  have values : n = 0 ∨ n = 1 ∨ n = 2 := by
    have nv : n.val = 0 ∨ n.val = 1 ∨ n.val = 2 := by omega
    rcases nv with eq | eq | eq
    · exact Or.inl (Fin.ext eq)
    · exact Or.inr (Or.inl (Fin.ext eq))
    · exact Or.inr (Or.inr (Fin.ext eq))
  rcases values with eq | eq | eq <;> simp_all

private theorem pair_rows :
    (∀ a : IDs, molecule.bondOrder 5 a.val = if a = 1 then 1 else 0) ∧
    (∀ a : IDs, molecule.bondOrder 6 a.val = if a = 1 then 1 else 0) ∧
    (∀ a : IDs, molecule.bondOrder 7 a.val = if a = 2 then 1 else 0) ∧
    (∀ a : IDs, molecule.bondOrder 8 a.val = if a = 2 then 1 else 0) := by decide

private theorem leaf_row (i : Input) (raw : i.molecule = molecule) (u parent : IDs)
    (row : ∀ a : IDs, molecule.bondOrder u.val a.val = if a = parent then 1 else 0) :
    ∀ a : i.certified.Atom, i.molecule.bondOrder (atom i raw u).val a.val =
      if a = atom i raw parent then 1 else 0 := by
  intro a
  rw [←atom_equiv i raw a,raw_bond,row]
  simp only [(atom_injective i raw).eq_iff]

def pairAtOne (i : Input) (raw : i.molecule = molecule) (c : i.certified.TetrahedralCenter)
    (center : c.val = atom i raw 1) : TwinPair i where
  c := c
  u := atom i raw 5
  v := atom i raw 6
  distinct := (atom_injective i raw).ne (by decide)
  records := by rw [raw]; rfl
  lu := by rw [center]; exact leaf_row i raw 5 1 pair_rows.1
  lv := by rw [center]; exact leaf_row i raw 6 1 pair_rows.2.1

def pairAtTwo (i : Input) (raw : i.molecule = molecule) (c : i.certified.TetrahedralCenter)
    (center : c.val = atom i raw 2) : TwinPair i where
  c := c
  u := atom i raw 7
  v := atom i raw 8
  distinct := (atom_injective i raw).ne (by decide)
  records := by rw [raw]; rfl
  lu := by rw [center]; exact leaf_row i raw 7 2 pair_rows.2.2.1
  lv := by rw [center]; exact leaf_row i raw 8 2 pair_rows.2.2.2

/-- Every other tetrahedral parent in this cyclic graph has graph-certified identical H leaves. -/
theorem all_other_tetra_twins (i : Input) (raw : i.molecule = molecule)
    (c : i.certified.TetrahedralCenter) (other : c.val ≠ atom i raw 0) : ∃ p : TwinPair i, p.c = c := by
  rcases center_ids i raw c with zero | one | two
  · exact False.elim (other zero)
  · exact ⟨pairAtOne i raw c one,rfl⟩
  · exact ⟨pairAtTwo i raw c two,rfl⟩

theorem no_phosphorus (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) :
    RingPyramidalPublication.phosphorus i a = false := by
  obtain ⟨n,rfl⟩ := (atomEquiv i raw).symm.surjective a
  change RingPyramidalPublication.phosphorus i (atom i raw n) = false
  unfold RingPyramidalPublication.phosphorus
  rw [raw]
  fin_cases n <;> rfl

/-- The source raw graph itself passes endpoint/uniqueness and written-neighbor admission. -/
theorem raw_admissible : molecule.StereochemicalAdmissible :=
  molecule.stereochemicalAdmissible?_eq_true_iff.mp (by decide)

def rootCenter (i : Input) (raw : i.molecule = molecule) : i.certified.TetrahedralCenter :=
  ⟨atom i raw 0,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr (by
    change Fintype.card (i.certified.moleculeGraph.Neighbor (atom i raw 0)) = 4
    rw [← Fintype.card_congr (neighborEquiv i raw 0)]
    decide)⟩

/-- The actual graph symmetry exchanges the two ring arms and their two H pairs. -/
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

theorem rootLigand_neighbor (i : Input) (raw : i.molecule = molecule) (s : Fin 4) :
    i.certified.moleculeGraph.Adj (rootCenter i raw).val (rootLigand i raw s) := by
  apply (raw_adj i raw 0 _).mpr
  fin_cases s <;> decide

theorem root_fixed (i : Input) (raw : i.molecule = molecule) :
    (branchAutomorphism i raw).atoms (rootCenter i raw).val = (rootCenter i raw).val :=
  branchAutomorphism_atom i raw 0

@[simp] theorem branchAutomorphism_inverse_atom (i : Input) (raw : i.molecule = molecule) (n : IDs) :
    (branchAutomorphism i raw).atoms.symm (atom i raw n) = atom i raw (branchPermutation.symm n) := by
  change (atomEquiv i raw).symm (branchPermutation.symm (atomEquiv i raw ((atomEquiv i raw).symm n))) = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem raw_neighbor_action : ∀ n : IDs, 0 < molecule.bondOrder 0 n.val →
    branchPermutation.symm n = (Equiv.swap 1 2) n := by decide

theorem canonical_odd (i : Input) (raw : i.molecule = molecule) :
    Equiv.Perm.sign ((branchAutomorphism i raw).inverseNeighborPermutation (rootCenter i raw)
      (root_fixed i raw)) = -1 := by
  let u : i.certified.moleculeGraph.Neighbor (rootCenter i raw).val :=
    ⟨atom i raw 1,rootLigand_neighbor i raw 0⟩
  let v : i.certified.moleculeGraph.Neighbor (rootCenter i raw).val :=
    ⟨atom i raw 2,rootLigand_neighbor i raw 1⟩
  apply GraphMap.inverseNeighborPermutation_transposition_odd (branchAutomorphism i raw) (rootCenter i raw)
    (root_fixed i raw) u v
  · intro eq
    have ids := (atom_injective i raw) (congrArg Subtype.val eq)
    exact (by decide : (1 : IDs) ≠ 2) ids
  · intro n
    let index := atomEquiv i raw n.val
    have positive : 0 < molecule.bondOrder 0 index.val := (raw_adj i raw 0 index).mp (by simpa [index] using n.property)
    change (branchAutomorphism i raw).atoms.symm n.val = Equiv.swap (atom i raw 1) (atom i raw 2) n.val
    rw [← atom_equiv i raw n.val,branchAutomorphism_inverse_atom,raw_neighbor_action _ positive]
    exact ((atom_injective i raw).swap_apply 1 2 index).symm

theorem covered_branches (i : Input) (raw : i.molecule = molecule) : BranchesWithTwinCenters i (rootCenter i raw) := by
  refine ⟨?_,no_phosphorus i raw⟩
  intro c other
  exact all_other_tetra_twins i raw c (fun eq => other (Subtype.ext eq))

/-- The native molecular evaluator refuses C0 at every independently admitted geometry. -/
theorem native_root_refusal (i : Input) (raw : i.molecule = molecule)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingChemicalGraphProof.root i (rootCenter i raw).val = some none :=
  (branchAutomorphism i raw).graph_only_refusal (rootCenter i raw) (covered_branches i raw)
    (root_fixed i raw) (canonical_odd i raw) admitted

theorem raw_closed : RingHydrogenCompletion.plan molecule = [] := by decide

/-- The actual public closed raw singleton returns a completed refusal, uniformly in all
coordinate tables admitting this nine-atom graph. No evaluator unfolding or pinned result is used. -/
theorem public_root_refusal (i : Input) (raw : i.molecule = molecule)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingHydrogenReport.fromRaw? molecule i.spatial [0] = some [(0,none)] := by
  have closed : RingHydrogenCompletion.plan i.molecule = [] := by rw [raw]; exact raw_closed
  have result := RingWrittenPHReadings.fromRaw_closed_report i closed admitted [(rootCenter i raw).val]
  have native := native_root_refusal i raw admitted
  have report : RingChemicalReport.report? i [(rootCenter i raw).val] = some [(0,none)] := by
    simp only [RingChemicalReport.report?,List.mapM_cons,List.mapM_nil]
    change ((RingChemicalGraphProof.root i (rootCenter i raw).val).map
      (fun labels => ((rootCenter i raw).val.val,labels))).bind (fun row => some [row]) = _
    rw [native]
    rfl
  rw [report] at result
  simpa only [List.map_cons,List.map_nil,rootCenter,atom_val,raw] using result

/-- Every native atom query is a completed refusal: whole-branch symmetry at C0,
identical terminal pairs at C1/C2, and the native ineligible skip at Br/F/H. -/
theorem native_all_refuse (i : Input) (raw : i.molecule = molecule)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) (a : i.certified.Atom) :
    RingChemicalGraphProof.root i a = some none := by
  by_cases four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4
  · let c : i.certified.TetrahedralCenter :=
      ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet a).mpr four⟩
    by_cases zero : c.val = atom i raw 0
    · have same : a = (rootCenter i raw).val := zero
      rw [same]
      exact native_root_refusal i raw admitted
    · obtain ⟨p,center⟩ := all_other_tetra_twins i raw c zero
      have refusal := p.root_refusal admitted
      rw [center] at refusal
      exact refusal
  · let n := atomEquiv i raw a
    have rawDegree := raw_degrees n
    have graphDegree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = if n.val < 3 then 4 else 1 := by
      rw [←atom_equiv i raw a,← Fintype.card_congr (neighborEquiv i raw n)]
      exact rawDegree
    have one : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 1 := by
      split at graphDegree <;> simp_all
    exact LeafAllRequests.root_ineligible i a (LeafAllRequests.terminal_ineligible i a one)

assert_kernel_only canonical_odd
assert_kernel_only native_root_refusal
assert_kernel_only public_root_refusal
assert_kernel_only raw_admissible
assert_kernel_only all_other_tetra_twins
assert_kernel_only no_phosphorus
end TetraStereo.Engine.RingHydrogenSpelling.BranchCoverage

namespace TetraStereo.Engine.RingHydrogenSpelling.BranchSpellings
open OneCenter OrdinaryHydrogenSpellings OrdinaryHydrogenSpellings.Production
open RingHydrogenCompletion RingSpatialTransport RingNumberedHydrogenGeometry
open RingRawRenumbering RingGroupedReport
open LocalizedChemicalRing (Input)

def chosen (mask : Fin 16) : List Nat := (List.range 4).filter fun j => mask.val.testBit j

/-- Bits 0 and 1 retain the two H atoms on C1, and bits 2 and 3 retain those on C2. -/
def source (mask : Fin 16) : RawMolecule := {
  atoms := ([.C,.C,.C,.Br,.F] : List Element).map AtomSpec.aliphatic ++ List.replicate (chosen mask).length (.aliphatic .H)
  bonds := ([(0,1),(0,2),(0,3),(0,4),(1,2)] : List (Nat × Nat)).map (fun ab => ⟨ab.1,ab.2,.single⟩) ++
    (chosen mask).zipIdx.map (fun jk => ⟨1+jk.1/2,5+jk.2,.single⟩) }

def coreAtom (p : Fin 5) : AtomSpec := AtomSpec.aliphatic (([.C,.C,.C,.Br,.F] : List Element).get p)

def coreBond (p q : Fin 5) : Nat := (source 0).bondOrder p.val q.val

def tag (mask : Fin 16) (v : Fin (source mask).atomCount) : Fin 5 ⊕ Fin 5 :=
  if h : v.val < 5 then .inl ⟨v.val,h⟩ else
    .inr ⟨1 + ((chosen mask)[v.val-5]?.getD 0)/2,by
      have bound : ((chosen mask)[v.val-5]?.getD 0) < 4 := by
        cases found : (chosen mask)[v.val-5]? with
        | none => simp
        | some j =>
          have mem := List.mem_of_getElem? found
          have := (List.mem_filter.mp mem).1
          simp only [List.mem_range] at this
          simpa using this
      omega⟩

def completion (mask : Fin 16) : Completion coreAtom coreBond where
  molecule := source mask
  core := {
    toFun := fun p => ⟨p.val,by simp [source,RawMolecule.atomCount]; omega⟩
    inj' := by intro p q h; exact Fin.ext (congrArg (fun z : Fin (source mask).atomCount => z.val) h) }
  tag := tag mask
  core_tag := by intro p; simp [tag,p.isLt]
  core_only := by
    intro v p h
    unfold tag at h
    split at h
    · exact Fin.ext (congrArg (fun z : Fin 5 => z.val) (Sum.inl.inj h))
    · contradiction
  retained := by decide
  records := by fin_cases mask <;> decide
  bonds := by fin_cases mask <;> decide

theorem totals : ∀ mask : Fin 16, ∀ p : Fin 5,
    (completion mask).hydrogenCount p + (addedParents (source mask)).count p.val =
      (completion 15).hydrogenCount p := by decide
/-- Arbitrary-coordinate successful preparation yields the same nine-atom graph,
up to a core-fixing bijection. Only local input tables are reflected. -/
theorem prepared_equivalent (mask : Fin 16) {xyz pos : SpatialConfiguration} {out : RawMolecule}
    (done : prepare? (source mask) xyz = some (out,pos)) :
    ∃ e : Fin out.atomCount ≃ Fin (source 15).atomCount,
      (∀ p : Fin 5, (e ⟨p.val,lt_of_lt_of_le ((completion mask).core p).isLt
        (prepare?_certified done).atomCount_le⟩).val = p.val) ∧
      (∀ v, heavyCore ((source 15).atoms.get (e v)) = heavyCore (out.atoms.get v)) ∧
      (∀ v w, (source 15).bondOrder (e v).val (e w).val = out.bondOrder v.val w.val) := by
  let ca := producedCompletion (a := completion mask) (prepare?_certified done)
  let cb := completion 15
  have counts : ∀ p, ca.hydrogenCount p = cb.hydrogenCount p := by
    intro p
    rw [produced_hydrogenCount]
    exact totals mask p
  refine ⟨Completion.atomEquiv ca cb counts,?_,Completion.atomEquiv_records ca cb counts,
    Completion.atomEquiv_bonds ca cb counts⟩
  intro p
  exact congrArg Fin.val (Completion.atomEquiv_core ca cb counts p)
/-- The reference input supplies the graph. Before evaluating it, the proof installs
the actual placement coordinates via the checked molecular map. -/
private def referencePoints : SpatialConfiguration := ⟨List.replicate 9 ⟨0,0,0⟩⟩
set_option maxRecDepth 100000 in
private theorem reference_exists :
    (LocalizedChemicalRing.admitRawSpatial? BranchCoverage.molecule referencePoints).isSome = true := by decide
private def reference : Input :=
  (LocalizedChemicalRing.admitRawSpatial? BranchCoverage.molecule referencePoints).get reference_exists
private theorem reference_raw : reference.molecule = BranchCoverage.molecule := by
  have found := Option.some_get reference_exists
  exact (RingChemicalReport.admission_fields found.symm).1

theorem canonical_bonds : ∀ a b : Fin 9,
    (source 15).bondOrder a.val b.val = BranchCoverage.molecule.bondOrder a.val b.val := by decide

private def inverse {i j : Input} (g : GraphMap i j) : GraphMap j i where
  atoms := g.atoms.symm
  records a := by simpa using (g.records (g.atoms.symm a)).symm
  bonds a b := by simpa using (g.bonds (g.atoms.symm a) (g.atoms.symm b)).symm

private def compose {i j k : Input} (g : GraphMap i j) (h : GraphMap j k) : GraphMap i k where
  atoms := g.atoms.trans h.atoms
  records a := (h.records _).trans (g.records a)
  bonds a b := (h.bonds _ _).trans (g.bonds a b)

private def centerMap {i j : Input} (g : GraphMap i j) (c : i.certified.TetrahedralCenter) :
    j.certified.TetrahedralCenter :=
  ⟨g.atoms c.val,(j.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr
    ((Fintype.card_congr (RingReportRenumber.neighbors g.atSourceGeometry c.val)).symm.trans
      ((i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp c.property))⟩

private def pairMap {i j : Input} (g : GraphMap i j) (p : TwinPair i) : TwinPair j where
  c := centerMap g p.c
  u := g.atoms p.u
  v := g.atoms p.v
  distinct := g.atoms.injective.ne p.distinct
  records := (g.records _).trans (p.records.trans (g.records _).symm)
  lu a := by
    obtain ⟨a,rfl⟩ := g.atoms.surjective a
    rw [g.bonds,p.lu]
    simp only [centerMap,g.atoms.injective.eq_iff]
  lv a := by
    obtain ⟨a,rfl⟩ := g.atoms.surjective a
    rw [g.bonds,p.lv]
    simp only [centerMap,g.atoms.injective.eq_iff]

/-- Successful materialization keeps each of the five written heavy IDs. -/
def preparedCore {mask : Fin 16} {i : Input} {xyz pos : SpatialConfiguration}
    (done : RingHydrogenCompletion.prepare? (source mask) xyz = some (i.molecule,pos))
    (n : Fin 5) : i.certified.Atom :=
  (rawVertices i rfl).symm ⟨n.val,lt_of_lt_of_le ((completion mask).core n).isLt
    (RingHydrogenCompletion.prepare?_certified done).atomCount_le⟩

@[simp] theorem preparedCore_val {mask : Fin 16} {i : Input} {xyz pos : SpatialConfiguration}
    (done : RingHydrogenCompletion.prepare? (source mask) xyz = some (i.molecule,pos))
    (n : Fin 5) : (preparedCore done n).val = n.val := rfl

private theorem prepared_graph_map (mask : Fin 16) (i : Input) (xyz pos : SpatialConfiguration)
    (done : RingHydrogenCompletion.prepare? (source mask) xyz = some (i.molecule,pos)) :
    ∃ g : GraphMap i reference, ∀ n : Fin 5,
      g.atoms (preparedCore done n) = BranchCoverage.atom reference reference_raw ⟨n.val,by omega⟩ := by
  obtain ⟨e,core,records,bonds⟩ := prepared_equivalent mask done
  let f := ((rawVertices i rfl).trans e).trans (rawVertices reference reference_raw).symm
  have mapped (a : i.certified.Atom) : rawVertices reference reference_raw (f a) = e (rawVertices i rfl a) :=
    (rawVertices reference reference_raw).apply_symm_apply _
  let g : GraphMap i reference := {
    atoms := f
    records := by
      intro a
      rw [record_at_rawVertex reference reference_raw,record_at_rawVertex i rfl,mapped]
      have eq := records (rawVertices i rfl a)
      change RingHydrogenCompletion.heavyCore (BranchCoverage.molecule.atoms.get (e (rawVertices i rfl a))) = _ at eq
      have projected := congrArg molecularRecord eq
      simpa only [molecularRecord,RingHydrogenCompletion.heavyCore] using congrArg some projected
    bonds := by
      intro a b
      rw [rawVertex_bond reference reference_raw,rawVertex_bond i rfl,mapped,mapped]
      rw [← canonical_bonds]
      exact bonds _ _ }
  refine ⟨g,?_⟩
  intro n
  apply Fin.ext
  exact core n

/-- All sixteen explicit/implicit ordinary-H spellings have a real C1/C2
exchange preserving the complete native C0 store at every committed prefix. -/
theorem prepared_branch_store (mask : Fin 16) (i : Input) (xyz pos : SpatialConfiguration)
    (done : RingHydrogenCompletion.prepare? (source mask) xyz = some (i.molecule,pos))
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    ∃ c : i.certified.TetrahedralCenter, ∃ exchange : GraphMap i i,
      c.val = preparedCore done 0 ∧
      exchange.atoms (preparedCore done 1) = preparedCore done 2 ∧
      exchange.atoms (preparedCore done 2) = preparedCore done 1 ∧
      exchange.atoms c.val = c.val ∧
      ∀ k, k ≤ RingActiveDistanceSchedule.height i + 1 →
        ((RingSphereStore.rows i c.val k).map
          (fun row => (RingSphereStore.siteMap exchange row.1,row.2))).Perm
          (RingSphereStore.rows i c.val k) := by
  obtain ⟨g,core⟩ := prepared_graph_map mask i xyz pos done
  let root := BranchCoverage.rootCenter reference reference_raw
  let c := centerMap (inverse g) root
  let exchange := compose (compose g (BranchCoverage.branchAutomorphism reference reference_raw)) (inverse g)
  have center : c.val = preparedCore done 0 := by
    apply g.atoms.injective
    change g.atoms (g.atoms.symm root.val) = _
    rw [g.atoms.apply_symm_apply,core]
    rfl
  have swap (a b : Fin 5) (h : BranchCoverage.branchPermutation ⟨a.val,by omega⟩ = ⟨b.val,by omega⟩) :
      exchange.atoms (preparedCore done a) = preparedCore done b := by
    apply g.atoms.injective
    change g.atoms (g.atoms.symm ((BranchCoverage.branchAutomorphism reference reference_raw).atoms
      (g.atoms (preparedCore done a)))) = _
    rw [g.atoms.apply_symm_apply,core,BranchCoverage.branchAutomorphism_atom,h,core]
  have fixed : exchange.atoms c.val = c.val := by rw [center]; exact swap 0 0 (by decide)
  have covered : BranchesWithTwinCenters i c := by
    refine ⟨?_,?_⟩
    · intro b different
      let b' := centerMap g b
      have diff : b' ≠ root := by
        intro eqn
        apply different
        apply Subtype.ext
        apply g.atoms.injective
        have same := congrArg Subtype.val eqn
        change g.atoms b.val = root.val at same
        simpa [c,centerMap,inverse] using same
      obtain ⟨p,hp⟩ := (BranchCoverage.covered_branches reference reference_raw).other b' diff
      refine ⟨pairMap (inverse g) p,?_⟩
      apply Subtype.ext
      change g.atoms.symm p.c.val = b.val
      rw [hp]
      exact g.atoms.symm_apply_apply b.val
    · intro a
      have off := BranchCoverage.no_phosphorus (withSourceGeometry i reference g.atoms) reference_raw (g.atoms a)
      exact (RingReportRenumber.phosphorus_atom g.atSourceGeometry a).symm.trans off
  refine ⟨c,exchange,center,swap 1 2 (by decide),swap 2 1 (by decide),fixed,?_⟩
  intro k bound
  exact RingSphereStore.branch_rows exchange admitted c fixed (covered.agreement _) k bound

theorem prepared_all_native_refuse (mask : Fin 16) (i : Input) (xyz pos : SpatialConfiguration)
    (done : prepare? (source mask) xyz = some (i.molecule,pos))
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) (a : i.certified.Atom) :
    RingChemicalGraphProof.root i a = some none := by
  obtain ⟨g,_⟩ := prepared_graph_map mask i xyz pos done
  let j := withSourceGeometry i reference g.atoms
  have gj := AtomMap.coordinates g.atSourceGeometry admitted
  have native := BranchCoverage.native_all_refuse j reference_raw gj (g.atoms a)
  exact (RingReportRenumber.chemical_root g.atSourceGeometry admitted a).trans native

/-- Complete raw result for all 16 explicit/implicit ordinary-hydrogen spellings
of 1-bromo-1-fluorocyclopropane, all coordinate tables and all lists of original IDs. -/
theorem public_report_iff (mask : Fin 16) (xyz : SpatialConfiguration) (ids : List Nat) (rows : Report) :
    RingHydrogenReport.fromRaw? (source mask) xyz ids = some rows ↔
      PlacementAdmission (source mask) xyz ids ∧ rows = ids.map (fun n => (n,none)) := by
  apply raw_refusals_iff_admission
  intro out pos done j mol admitted a _
  subst out
  exact prepared_all_native_refuse mask j xyz pos done admitted a

theorem public_reject_iff (mask : Fin 16) (xyz : SpatialConfiguration) (ids : List Nat) :
    RingHydrogenReport.fromRaw? (source mask) xyz ids = none ↔ ¬ PlacementAdmission (source mask) xyz ids := by
  constructor
  · intro rejected gate
    have accepted := (public_report_iff mask xyz ids _).mpr ⟨gate,rfl⟩
    rw [rejected] at accepted
    cases accepted
  · intro failed
    cases computed : RingHydrogenReport.fromRaw? (source mask) xyz ids with
    | none => rfl
    | some rows => exact (failed ((public_report_iff mask xyz ids rows).mp computed).1).elim

assert_kernel_only prepared_equivalent
assert_kernel_only public_report_iff
assert_kernel_only public_reject_iff
end TetraStereo.Engine.RingHydrogenSpelling.BranchSpellings

assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.BranchSpellings.prepared_branch_store
