import TetraStereo.Engine.RingBondRecordOrder
import TetraStereo.Engine.RingHydrogenCompletion

set_option autoImplicit false
namespace TetraStereo.Engine.RingBondRecordOrder
open OneCenter
open LocalizedChemicalRing (Input)
open RingHydrogenCompletion
variable {i j : Input}

theorem raw_atomCount (p : Presentation i j) : i.molecule.atomCount = j.molecule.atomCount :=
  congrArg List.length p.atoms

theorem writtenNeighbors_perm (p : Presentation i j) (n : Nat) (hn : n < i.molecule.atomCount) :
    (i.molecule.writtenNeighbors n).Perm (j.molecule.writtenNeighbors n) := by
  have hn' : n < j.molecule.atomCount := by rw [← raw_atomCount p]; exact hn
  have left := RawMolecule.WrittenNeighborExact.at i.molecule i.admissible.2 ⟨n,hn⟩
  have right := RawMolecule.WrittenNeighborExact.at j.molecule j.admissible.2 ⟨n,hn'⟩
  apply (List.perm_ext_iff_of_nodup left.1 right.1).mpr
  intro v
  constructor
  · intro hv
    have h := left.2.1 v hv
    exact (right.2.2 ⟨v,by rw [← raw_atomCount p]; exact h⟩).mpr
      (by rw [← bondOrder p.bonds]; exact (left.2.2 ⟨v,h⟩).mp hv)
  · intro hv
    have h := right.2.1 v hv
    have h' : v < i.molecule.atomCount := by rw [raw_atomCount p]; exact h
    exact (left.2.2 ⟨v,h'⟩).mpr
      (by rw [bondOrder p.bonds]; exact (right.2.2 ⟨v,h⟩).mp hv)

theorem incidentSum_eq {m n : RawMolecule} (perm : m.bonds.Perm n.bonds) (a : Nat) :
    m.incidentBondOrderSum a = n.incidentBondOrderSum a := by
  unfold RawMolecule.incidentBondOrderSum
  apply perm.foldl_eq'
  intro x hx y hy z
  by_cases h : x.source == a || x.target == a <;>
    by_cases k : y.source == a || y.target == a <;> simp [h,k,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem missing_eq (p : Presentation i j) (n : Nat) : missing i.molecule n = missing j.molecule n := by
  unfold missing RawMolecule.hydrogenCountAt
  have atoms : (closeHydrogenVertices i.molecule).atomAt? n =
      (closeHydrogenVertices j.molecule).atomAt? n := by
    simp [RawMolecule.atomAt?,closeHydrogenVertices,p.atoms]
  rw [atoms]
  have sums : (closeHydrogenVertices i.molecule).incidentBondOrderSum n =
      (closeHydrogenVertices j.molecule).incidentBondOrderSum n := incidentSum_eq p.bonds n
  rw [sums]

theorem plan_eq (p : Presentation i j) : plan i.molecule = plan j.molecule := by
  simp [plan, raw_atomCount p, missing_eq p]

theorem addedParents_eq (p : Presentation i j) : addedParents i.molecule = addedParents j.molecule := by
  rw [addedParents,addedParents,plan_eq p]

theorem neighbors_eq (p : Presentation i j) (n : Nat) (hn : n < i.molecule.atomCount) :
    neighbors i.molecule n = neighbors j.molecule n := by
  simp only [neighbors,raw_atomCount p, (writtenNeighbors_perm p n hn).mem_iff]

end TetraStereo.Engine.RingBondRecordOrder

namespace TetraStereo.Engine.RingBondRecordOrder
open OneCenter
open LocalizedChemicalRing (Input)
open RingHydrogenCompletion
variable {i j : Input}

private theorem expansion_step {m n : RawMolecule} (same : ∀ k, m.hydrogenCountAt k = n.hydrogenCountAt k)
    (s t : RawMolecule.HydrogenExpansionState) (atoms : s.1 = t.1) (bonds : s.2.1.Perm t.2.1) (k : Nat) :
    (m.withExplicitHydrogensStep s k).1 = (n.withExplicitHydrogensStep t k).1 ∧
      (m.withExplicitHydrogensStep s k).2.1.Perm (n.withExplicitHydrogensStep t k).2.1 := by
  unfold RawMolecule.withExplicitHydrogensStep
  rw [same k]
  dsimp only
  split
  · exact ⟨atoms,bonds⟩
  · simp only [atoms]
    exact ⟨trivial, (RawMolecule.spliceHydrogenBondsWithPredecessor_perm _ _ _ _).trans
      ((bonds.append_right _).trans (RawMolecule.spliceHydrogenBondsWithPredecessor_perm _ _ _ _).symm)⟩

private theorem expansion_fold {m n : RawMolecule} (same : ∀ k, m.hydrogenCountAt k = n.hydrogenCountAt k)
    (ks : List Nat) (s t : RawMolecule.HydrogenExpansionState)
    (atoms : s.1 = t.1) (bonds : s.2.1.Perm t.2.1) :
    (ks.foldl (m.withExplicitHydrogensStep) s).1 = (ks.foldl (n.withExplicitHydrogensStep) t).1 ∧
      (ks.foldl (m.withExplicitHydrogensStep) s).2.1.Perm (ks.foldl (n.withExplicitHydrogensStep) t).2.1 := by
  induction ks generalizing s t with
  | nil => exact ⟨atoms,bonds⟩
  | cons k ks ih =>
    have step := expansion_step same s t atoms bonds k
    exact ih _ _ step.1 step.2

/-- Appending implicit hydrogen vertices fixes atom records and only permutes bonds. -/
theorem materialized_records (p : Presentation i j) :
    ((closeHydrogenVertices i.molecule).withExplicitHydrogens).atoms =
        ((closeHydrogenVertices j.molecule).withExplicitHydrogens).atoms ∧
    ((closeHydrogenVertices i.molecule).withExplicitHydrogens).bonds.Perm
        ((closeHydrogenVertices j.molecule).withExplicitHydrogens).bonds := by
  have count : (closeHydrogenVertices i.molecule).atomCount =
      (closeHydrogenVertices j.molecule).atomCount := by
    simp [RawMolecule.atomCount,closeHydrogenVertices,p.atoms]
  have initial : (RawMolecule.initialHydrogenExpansionState (closeHydrogenVertices i.molecule)).1 =
      (RawMolecule.initialHydrogenExpansionState (closeHydrogenVertices j.molecule)).1 := by
    simp [RawMolecule.initialHydrogenExpansionState,closeHydrogenVertices,p.atoms]
  have proof := expansion_fold (fun k => missing_eq p k)
    (List.range (closeHydrogenVertices i.molecule).atomCount) _ _ initial p.bonds
  simpa [RawMolecule.withExplicitHydrogens,RawMolecule.HydrogenExpansionState.toRawMolecule,
    RawMolecule.withExactWrittenNeighbors,count] using proof

end TetraStereo.Engine.RingBondRecordOrder

namespace TetraStereo.Engine.RingBondRecordOrder
open OneCenter
open LocalizedChemicalRing (Input)
open RingHydrogenCompletion
variable {i j : Input}

theorem ordinaryHydrogenVertex_eq (p : Presentation i j) (n : Nat) (hn : n < i.molecule.atomCount) :
    ordinaryHydrogenVertex i.molecule n = ordinaryHydrogenVertex j.molecule n := by
  simp only [ordinaryHydrogenVertex,p.atoms,(writtenNeighbors_perm p n hn).length_eq]

theorem placeAt?_eq (p : Presentation i j) (e : Nat × Nat) (he : e.1 < i.molecule.atomCount) :
    placeAt? i.molecule i.spatial e = placeAt? j.molecule j.spatial e := by
  have any : (i.molecule.writtenNeighbors e.1).any (ordinaryHydrogenVertex i.molecule) =
      (j.molecule.writtenNeighbors e.1).any (ordinaryHydrogenVertex j.molecule) := by
    rw [← (writtenNeighbors_perm p e.1 he).any_eq]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨n,hn,h⟩
      exact ⟨n,hn,(ordinaryHydrogenVertex_eq p n
        ((RawMolecule.WrittenNeighborExact.at i.molecule i.admissible.2 ⟨e.1,he⟩).2.1 n hn)).symm.trans h⟩
    · rintro ⟨n,hn,h⟩
      exact ⟨n,hn,(ordinaryHydrogenVertex_eq p n
        ((RawMolecule.WrittenNeighborExact.at i.molecule i.admissible.2 ⟨e.1,he⟩).2.1 n hn)).trans h⟩
  simp only [placeAt?,p.positions,neighbors_eq p e.1 he,any]

private theorem mapM_eq {α β : Type} (xs : List α) (f g : α → Option β)
    (same : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.mapM_cons, same x (by simp), ih (fun y hy => same y (by simp [hy]))]

theorem addedPositions?_eq (p : Presentation i j) :
    addedPositions? i.molecule i.spatial = addedPositions? j.molecule j.spatial := by
  unfold addedPositions?
  congr 1
  rw [← plan_eq p]
  apply mapM_eq
  intro e he
  apply placeAt?_eq p e
  unfold plan at he
  obtain ⟨n,hn,eq⟩ := List.mem_filterMap.mp he
  split at eq
  · contradiction
  · cases eq
    exact List.mem_range.mp hn

private theorem candidate_of_prepared {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (h : prepare? m xyz = some (out,pos)) : candidate? m xyz = some (out,pos) := by
  unfold prepare? complete? at h
  obtain ⟨r,found,gate⟩ := Option.bind_eq_some_iff.mp h
  have same := (gate_eq_some gate).1
  simpa [same] using found

/-- Successful preparations of bond-permuted source inputs have exactly the same
atom records and coordinates, and permuted bond records, including generated H. -/
theorem prepared_records (p : Presentation i j)
    {out out' : RawMolecule} {pos pos' : SpatialConfiguration}
    (left : prepare? i.molecule i.spatial = some (out,pos))
    (right : prepare? j.molecule j.spatial = some (out',pos')) :
    out.atoms = out'.atoms ∧ out.bonds.Perm out'.bonds ∧ pos.positions = pos'.positions := by
  have l := candidate_of_prepared left
  have r := candidate_of_prepared right
  unfold candidate? at l r
  rw [← plan_eq p] at r
  split at l
  · rename_i empty
    rw [if_pos empty] at r
    cases l
    cases r
    exact ⟨p.atoms,p.bonds,p.positions⟩
  · rename_i nonempty
    rw [if_neg nonempty] at r
    rw [addedPositions?_eq p] at l
    obtain ⟨extra,found,eq⟩ := Option.map_eq_some_iff.mp l
    rw [found] at r
    cases eq
    cases r
    exact ⟨(materialized_records p).1,(materialized_records p).2,by simp [p.positions]⟩

end TetraStereo.Engine.RingBondRecordOrder
assert_kernel_only TetraStereo.Engine.RingBondRecordOrder.prepared_records
