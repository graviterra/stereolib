import TetraStereo.Engine.RingPyramidalChoices
import TetraStereo.Engine.LocalizedChemicalRingPublic
import TetraStereo.Engine.RingHydrogenCertificate
import TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense
import TetraStereo.Engine.RingPyramidalPublication
set_option autoImplicit false
namespace TetraStereo.Engine.RingPyramidalChoices
open OneCenter RingHydrogenCompletion

/-- A selected appended hydrogen has precisely its selected parent in the raw frame. -/
theorem selected_hydrogen_row {m out : RawMolecule} {g pos : SpatialConfiguration}
    {s : Site} (hs : s ∈ sites m g out pos) :
    out.writtenNeighbors s.hydrogen = [s.parent] := by
  obtain ⟨p, _, v⟩ := sites_valid hs
  obtain ⟨hp, _, _, _, _, _, _, _, _, _, row, _⟩ := v
  simpa [hp] using row

/-- The exact raw view turns the singleton row into an exclusion of every other parent. -/
theorem selected_hydrogen_bond_iff {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : Certified m g out pos) {s : Site} (hs : s ∈ sites m g out pos)
    {q : Nat} (hq : q < out.atomCount) :
    0 < out.bondOrder s.hydrogen q ↔ q = s.parent := by
  obtain ⟨p, _, v⟩ := sites_valid hs
  have hh : s.hydrogen < out.atomCount := by
    rw [← cert.positions_length]
    exact v.hydrogen_lt
  have exactRows := cert.output_admissible.2
  change out.writtenNeighborExact? = true at exactRows
  have er := List.all_eq_true.mp exactRows s.hydrogen (List.mem_range.mpr hh)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at er
  have e := List.all_eq_true.mp er.2 q (List.mem_range.mpr hq)
  have e' : q ∈ out.writtenNeighbors s.hydrogen ↔ 0 < out.bondOrder s.hydrogen q :=
    of_decide_eq_true e
  rw [← e', selected_hydrogen_row hs]
  simp
theorem count_flatMap_replicate (l : List Nat) (f : Nat → Nat) (p : Nat)
    (hn : l.Nodup) :
    (l.flatMap (fun q => List.replicate (f q) q)).count p =
      if p ∈ l then f p else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have na := (List.nodup_cons.mp hn).1
    have nl := (List.nodup_cons.mp hn).2
    rw [List.flatMap_cons, List.count_append, ih nl]
    by_cases eq : a = p
    · subst a
      simp [na]
    · simp [List.count_replicate, eq, Ne.symm eq]

theorem addedParents_count (m : RawMolecule) (p : Nat) (hp : p < m.atomCount) :
    (addedParents m).count p = missing m p := by
  unfold addedParents plan
  rw [RingHydrogenCertificate.flatMap_filterMap_replicate]
  rw [count_flatMap_replicate _ _ _ (List.nodup_range)]
  simp [hp]
theorem getElem?_unique_of_count_one (l : List Nat) (p a b : Nat)
    (hc : l.count p = 1) (ha : l[a]? = some p) (hb : l[b]? = some p) : a = b := by
  induction l generalizing a b with
  | nil => simp at ha
  | cons x l ih =>
    by_cases eq : x = p
    · subst x
      have zero : l.count p = 0 := by simpa using hc
      have absent : p ∉ l := List.count_eq_zero.mp zero
      cases a with
      | zero =>
        cases b with
        | zero => rfl
        | succ b => exact (absent (List.mem_of_getElem? hb)).elim
      | succ a => exact (absent (List.mem_of_getElem? ha)).elim
    · have tail : l.count p = 1 := by simpa [List.count_cons, eq, Ne.symm eq] using hc
      cases a with
      | zero => simp [eq] at ha
      | succ a =>
        cases b with
        | zero => simp [eq] at hb
        | succ b => exact congrArg Nat.succ (ih a b tail ha hb)
/-- A selected parent has exactly one appended leaf, irrespective of other sites. -/
theorem selected_parent_fresh_unique {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : Certified m g out pos) {s : Site} (hs : s ∈ sites m g out pos)
    {q : Nat} (qge : m.atomCount ≤ q) (qlt : q < out.atomCount)
    (row : out.writtenNeighbors q = [s.parent]) : q = s.hydrogen := by
  obtain ⟨p, _, v⟩ := sites_valid hs
  have sh := v.hydrogen_ge
  have ph := v.hydrogen_parent
  obtain ⟨sp, _, miss, _, _, _, _, _, _, _, _, _, _, plt, _⟩ := v
  have count : (addedParents m).count p = 1 := (addedParents_count m p plt).trans miss
  obtain ⟨r, hr, rw⟩ := cert.fresh_row qge qlt
  have rp : r = p := by
    rw [row, sp] at rw
    simpa using rw.symm
  subst r
  have indices := getElem?_unique_of_count_one (addedParents m) p
    (q - m.atomCount) (s.hydrogen - m.atomCount) count hr ph
  omega
theorem selected_parent_neighbors_subset {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : Certified m g out pos) {s : Site} (hs : s ∈ sites m g out pos) :
    out.writtenNeighbors s.parent ⊆ [s.first,s.second,s.hydrogen] := by
  obtain ⟨p, _, v⟩ := sites_valid hs
  have shp := v.hydrogen_parent
  obtain ⟨sp, _, _, old, _, _, _, _, _, _, _, _, _, plt, _⟩ := v
  have po : p < out.atomCount := lt_of_lt_of_le plt cert.atomCount_le
  have clauses := RawMolecule.WrittenNeighborExact.at out cert.output_admissible.2 ⟨p,po⟩
  rw [sp]
  intro q hq
  have qlt := clauses.2.1 q hq
  by_cases qold : q < m.atomCount
  · have filtered : q ∈ (out.writtenNeighbors p).filter (fun j => decide (j < m.atomCount)) := by
      simp [hq,qold]
    have rows := of_decide_eq_true (List.all_eq_true.mp cert.writtenNeighbors_original p
      (List.mem_range.mpr plt))
    rw [rows,old] at filtered
    simpa using List.mem_append_left [s.hydrogen] filtered
  · have qge : m.atomCount ≤ q := by omega
    obtain ⟨r,hr,row⟩ := cert.fresh_row qge qlt
    have adj := (clauses.2.2 ⟨q,qlt⟩).mp hq
    rw [out.bondOrder_symm] at adj
    have qr := RawMolecule.WrittenNeighborExact.at out cert.output_admissible.2 ⟨q,qlt⟩
    have pr := (qr.2.2 ⟨p,po⟩).mpr adj
    rw [row] at pr
    have rp : r = p := (List.mem_singleton.mp pr).symm
    have qs := selected_parent_fresh_unique cert hs qge qlt (by simpa [rp,sp] using row)
    simp [qs]
theorem selected_hydrogen_ne_tetra_ligand {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : Certified m g out pos) {s : Site} (hs : s ∈ sites m g out pos)
    (i : LocalizedChemicalRing.Input) (same : i.molecule = out)
    (c : i.certified.TetrahedralCenter)
    (l : i.certified.moleculeGraph.Neighbor c.val) : l.val.val ≠ s.hydrogen := by
  intro equal
  have rawAdj := LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement
    i.admissible.1.1 i.admissible.1.2 i.supported
  have count := LocalizedChemicalRingPhysicalSense.count i.molecule i.certified i.agreement
  have cb : c.val.val < out.atomCount := by
    rw [← same, ← count]
    exact c.val.isLt
  have positive := (rawAdj c.val l.val).mp l.property
  rw [same, equal, out.bondOrder_symm] at positive
  have cp := (selected_hydrogen_bond_iff cert hs cb).mp positive
  let target := ([s.first,s.second,s.hydrogen] : List Nat).toFinset
  let f : i.certified.moleculeGraph.Neighbor c.val → {x // x ∈ target} := fun n =>
    ⟨n.val.val, by
      have nb : n.val.val < out.atomCount := by
        rw [← same, ← count]
        exact n.val.isLt
      have pp := (rawAdj c.val n.val).mp n.property
      rw [same, cp] at pp
      have pb : s.parent < out.atomCount := cp ▸ cb
      have rows := RawMolecule.WrittenNeighborExact.at out cert.output_admissible.2 ⟨s.parent,pb⟩
      have mem := (rows.2.2 ⟨n.val.val,nb⟩).mpr pp
      exact List.mem_toFinset.mpr (selected_parent_neighbors_subset cert hs mem)⟩
  have inj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg Subtype.val h
  have bound := Fintype.card_le_of_injective f inj
  have three : Fintype.card {x // x ∈ target} ≤ 3 := by
    rw [Fintype.card_coe]
    exact le_trans (List.toFinset_card_le _) (by simp)
  have four := (i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp c.property
  rw [four] at bound
  omega
end TetraStereo.Engine.RingPyramidalChoices
assert_kernel_only TetraStereo.Engine.RingPyramidalChoices.selected_hydrogen_ne_tetra_ligand

namespace TetraStereo.Engine.RingPyramidalChoices
open OneCenter RingHydrogenCompletion

theorem phosphorus_ne_selected_hydrogen {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : Certified m g out pos) {s : Site} (hs : s ∈ sites m g out pos)
    (i : LocalizedChemicalRing.Input) (same : i.molecule = out)
    (a : i.certified.Atom) (ph : RingPyramidalPublication.phosphorus i a = true) :
    a.val ≠ s.hydrogen := by
  intro eq
  obtain ⟨p,_,v⟩ := sites_valid hs
  have ht : s.hydrogen < out.atomCount := by
    rw [← cert.positions_length]
    exact v.hydrogen_lt
  have atom := cert.fresh_atom v.hydrogen_ge ht
  simp [RingPyramidalPublication.phosphorus,same,eq,atom,AtomSpec.aliphatic] at ph

theorem phosphorus_neighbor_selected_parent {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : Certified m g out pos) {s : Site} (hs : s ∈ sites m g out pos)
    (i : LocalizedChemicalRing.Input) (same : i.molecule = out)
    (a : i.certified.Atom) (n : i.certified.moleculeGraph.Neighbor a)
    (eq : n.val.val = s.hydrogen) : a.val = s.parent := by
  have rawAdj := LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement
    i.admissible.1.1 i.admissible.1.2 i.supported
  have count := LocalizedChemicalRingPhysicalSense.count i.molecule i.certified i.agreement
  have ab : a.val < out.atomCount := by
    rw [← same,← count]
    exact a.isLt
  have pp := (rawAdj a n.val).mp n.property
  rw [same,eq,out.bondOrder_symm] at pp
  exact (selected_hydrogen_bond_iff cert hs ab).mp pp
theorem exists_perm_of_injective_range_subset {α : Type} [Finite α]
    (f g : α → Nat) (hf : Function.Injective f)
    (h : ∀ x, ∃ y, f x = g y) :
    ∃ π : Equiv.Perm α, ∀ x, f x = g (π x) := by
  classical
  let r : α → α := fun x => Classical.choose (h x)
  have hr : ∀ x, f x = g (r x) := fun x => Classical.choose_spec (h x)
  have inj : Function.Injective r := by
    intro x y eq
    apply hf
    rw [hr x,hr y,eq]
  exact ⟨Equiv.ofBijective r ⟨inj,Finite.surjective_of_injective inj⟩,hr⟩

/-- Three bonded IDs followed by the center, the determinant convention for P. -/
def phosphorusFrameIds {i : LocalizedChemicalRing.Input} {a : i.certified.Atom}
    (d : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a) : Fin 4 → Nat :=
  ![(d 0).val.val,(d 1).val.val,(d 2).val.val,a.val]

def selectedFrameIds (s : Site) : Fin 4 → Nat :=
  ![s.first,s.second,s.hydrogen,s.parent]

theorem phosphorusFrameIds_injective {i : LocalizedChemicalRing.Input} {a : i.certified.Atom}
    (d : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a) :
    Function.Injective (phosphorusFrameIds d) := by
  have inj : Function.Injective (fun j : Fin 3 => (d j).val.val) := by
    intro x y eq
    apply d.injective
    apply Subtype.ext
    exact Fin.ext eq
  have h01 := inj.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h02 := inj.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := inj.ne (show (1 : Fin 3) ≠ 2 by decide)
  have na : ∀ j, (d j).val.val ≠ a.val := by
    intro j eq
    have same : (d j).val = a := Fin.ext eq
    have bad := (d j).property
    rw [same] at bad
    simp [OneCenter.MoleculeGraph.Adj,i.certified.moleculeGraph.bond_self] at bad
  intro x y eq
  fin_cases x <;> fin_cases y <;> simp_all [phosphorusFrameIds,Ne.symm]

theorem phosphorus_frame_dichotomy {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : Certified m g out pos) (i : LocalizedChemicalRing.Input)
    (same : i.molecule = out) (a : i.certified.Atom)
    (ph : RingPyramidalPublication.phosphorus i a = true)
    (d : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a) :
    (∀ s ∈ sites m g out pos, ∀ j, phosphorusFrameIds d j ≠ s.hydrogen) ∨
    ∃ s ∈ sites m g out pos, ∃ π : Equiv.Perm (Fin 4),
      ∀ j, phosphorusFrameIds d j = selectedFrameIds s (π j) := by
  classical
  by_cases untouched : ∀ s ∈ sites m g out pos, ∀ j, phosphorusFrameIds d j ≠ s.hydrogen
  · exact Or.inl untouched
  · right
    push_neg at untouched
    obtain ⟨s,hs,j,hj⟩ := untouched
    have center : a.val = s.parent := by
      fin_cases j
      · exact phosphorus_neighbor_selected_parent cert hs i same a (d 0) hj
      · exact phosphorus_neighbor_selected_parent cert hs i same a (d 1) hj
      · exact phosphorus_neighbor_selected_parent cert hs i same a (d 2) hj
      · exact (phosphorus_ne_selected_hydrogen cert hs i same a ph hj).elim
    have rawAdj := LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement
      i.admissible.1.1 i.admissible.1.2 i.supported
    have count := LocalizedChemicalRingPhysicalSense.count i.molecule i.certified i.agreement
    have bounds (x : i.certified.Atom) : x.val < out.atomCount := by
      rw [← same,← count]
      exact x.isLt
    have member (k : Fin 3) : (d k).val.val ∈ [s.first,s.second,s.hydrogen] := by
      have pp := (rawAdj a (d k).val).mp (d k).property
      rw [same,center] at pp
      have rows := RawMolecule.WrittenNeighborExact.at out cert.output_admissible.2
        ⟨s.parent,center ▸ bounds a⟩
      exact selected_parent_neighbors_subset cert hs ((rows.2.2 ⟨_,bounds (d k).val⟩).mpr pp)
    have choices (k : Fin 3) : ∃ t : Fin 4, (d k).val.val = selectedFrameIds s t := by
      have mem := member k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with h | h | h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩
    obtain ⟨π,hπ⟩ := exists_perm_of_injective_range_subset (phosphorusFrameIds d)
      (selectedFrameIds s) (phosphorusFrameIds_injective d) (by
        intro k
        fin_cases k
        · exact choices 0
        · exact choices 1
        · exact choices 2
        · exact ⟨3,center⟩)
    exact ⟨s,hs,π,hπ⟩
end TetraStereo.Engine.RingPyramidalChoices

assert_kernel_only TetraStereo.Engine.RingPyramidalChoices.phosphorus_frame_dichotomy
