import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceBondGeometry
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceSlots
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileAtomicLabels

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment

def sourceNitrileCarbon (parity : TetrahedralInputParity) (n : Nat) :
    (nitrileSource parity n).AromaticCanonicalAtom :=
  nitrileAtom parity n 2 (by rw [expanded_atomCount]; omega)

def sourceNitrileNitrogen (parity : TetrahedralInputParity) (n : Nat) :
    (nitrileSource parity n).AromaticCanonicalAtom :=
  nitrileAtom parity n 3 (by rw [expanded_atomCount]; omega)

def sourceNitrileRoot (parity : TetrahedralInputParity) (n : Nat) :
    OfficialCIPNode (nitrileSource parity n).AromaticCanonicalAtom :=
  OfficialCIPNode.rootFromEdge (nitrileCenter parity n).1 (sourceNitrileCarbon parity n)

def sourceNitrogenCopy (parity : TetrahedralInputParity) (n copy : Nat) :
    OfficialCIPNode (nitrileSource parity n).AromaticCanonicalAtom :=
  (sourceNitrileRoot parity n).extend (sourceNitrileNitrogen parity n) copy

private theorem source_nitrogen_filter (parity : TetrahedralInputParity) (n : Nat) :
    ((List.finRange (nitrileSource parity n).molecule.atomCount).filter
      (fun atom => decide (atom = sourceNitrileNitrogen parity n))) =
        [sourceNitrileNitrogen parity n] := by
  apply List.Perm.eq_singleton
  apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) (by simp)).mpr
  intro atom
  simp

private theorem source_nitrile_copy_block (parity : TetrahedralInputParity) (n : Nat)
    (neighbor : (nitrileSource parity n).AromaticCanonicalAtom) :
    (((List.range ((nitrileSource parity n).molecule.aromaticCanonicalBondOrder
      2 neighbor.val)).map (fun copy => (neighbor, copy))).filter
        (fun copy => !(copy.1 == (nitrileCenter parity n).1 && copy.2 == 0))) =
      if neighbor = sourceNitrileNitrogen parity n then
        [(neighbor, 0), (neighbor, 1), (neighbor, 2)] else [] := by
  have atCenter : (neighbor == (nitrileCenter parity n).1) = (neighbor.val == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Fin.ext_iff, nitrile_center_index]
  have atNitrogen : neighbor = sourceNitrileNitrogen parity n ↔ neighbor.val = 3 := by
    exact Fin.ext_iff
  rw [source_nitrile_bond_order]
  by_cases zero : neighbor.val = 0
  · simp [zero, atCenter, atNitrogen, List.range_succ]
  · by_cases nitrogen : neighbor.val = 3
    · simp [nitrogen, atCenter, atNitrogen, List.range_succ]
    · simp [zero, nitrogen, atNitrogen]

theorem source_nitrile_child_copies (parity : TetrahedralInputParity) (n : Nat) :
    (nitrileSource parity n).molecule.aromaticCanonicalChildCopiesAt
      (nitrileSource parity n).molecule.atomCount (sourceNitrileRoot parity n) =
        [(sourceNitrileNitrogen parity n, 0), (sourceNitrileNitrogen parity n, 1),
          (sourceNitrileNitrogen parity n, 2)] := by
  have filtered (neighbors : List (nitrileSource parity n).AromaticCanonicalAtom) :
      ((neighbors.flatMap fun neighbor =>
        (List.range ((nitrileSource parity n).molecule.aromaticCanonicalBondOrder
          2 neighbor.val)).map fun copy => (neighbor, copy)).filter
        (fun copy => !(copy.1 == (nitrileCenter parity n).1 && copy.2 == 0))) =
      (neighbors.filter (fun neighbor => decide (neighbor = sourceNitrileNitrogen parity n))).flatMap
        (fun neighbor => [(neighbor, 0), (neighbor, 1), (neighbor, 2)]) := by
    induction neighbors with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.flatMap_cons, List.filter_append, source_nitrile_copy_block, ih,
          List.filter_cons]
        by_cases same : head = sourceNitrileNitrogen parity n <;> simp [same]
  change (((List.finRange (nitrileSource parity n).molecule.atomCount).flatMap fun neighbor =>
    (List.range ((nitrileSource parity n).molecule.aromaticCanonicalBondOrder
      2 neighbor.val)).map fun copy => (neighbor, copy)).filter
        (fun copy => !(copy.1 == (nitrileCenter parity n).1 && copy.2 == 0))) = _
  rw [filtered, source_nitrogen_filter]
  rfl

/-- Literal independent source children: one real nitrogen and the two triple-bond duplicates.
The parent carbon's real copy is removed by the actual source constructor. -/
theorem source_nitrile_children (parity : TetrahedralInputParity) (n : Nat) :
    (nitrileSource parity n).molecule.aromaticCanonicalOfficialCIPChildrenAt
      (nitrileSource parity n).molecule.atomCount (sourceNitrileRoot parity n) =
        [sourceNitrogenCopy parity n 0, sourceNitrogenCopy parity n 1,
          sourceNitrogenCopy parity n 2] := by
  have notLeaf : (sourceNitrileRoot parity n).isDuplicateLeaf = false := rfl
  have current : (sourceNitrileRoot parity n).current? = some (sourceNitrileCarbon parity n) := rfl
  simp only [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt, notLeaf,
    Bool.false_eq_true, ↓reduceIte, source_nitrile_child_copies, current,
    source_no_virtual_duplicate, List.append_nil, List.map_cons, List.map_nil]
  rfl

theorem source_second_nitrogen_provenance (parity : TetrahedralInputParity) (n : Nat) :
    (sourceNitrogenCopy parity n 1).provenance = .multipleBondDuplicate 1 := rfl

private theorem source_triple_not_mancude (parity : TetrahedralInputParity) (n : Nat) :
    ¬(nitrileSource parity n).molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge
      (sourceNitrileCarbon parity n) (sourceNitrileNitrogen parity n) := by
  have order := source_nitrile_bond_order parity n 3
  rw [source_canonical_order_eq_localized] at order
  have triple : (nitrileSource parity n).molecule.toLocalizedMoleculeGraph.bond
      (sourceNitrileCarbon parity n) (sourceNitrileNitrogen parity n) = 3 := by
    change (nitrileSource parity n).molecule.localizedBondOrder 2 3 = 3
    simpa using order
  intro candidate
  have possible := candidate.1.1
  rw [triple] at possible
  rcases possible with impossible | impossible <;> contradiction

theorem source_nitrogen_copy_observation (parity : TetrahedralInputParity) (n copy : Nat) :
    (nitrileSource parity n).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (sourceNitrogenCopy parity n copy) = .ofNat 7 := by
  have z : (nitrileSource parity n).molecule.toLocalizedMoleculeGraph.atomZ
      (sourceNitrileNitrogen parity n) = 7 := by
    rw [converted_atomic_number (expanded parity n) (nitrileSource parity n)
      (expanded_source_annotation_agreement parity n).1]
    exact (expanded_local_atomic_numbers parity n).2.2.2.1
  by_cases zero : copy = 0
  · subst copy
    rw [sourceNitrogenCopy, official_zero_copy_observation, z]
  · have provenance : (sourceNitrogenCopy parity n copy).provenance = .multipleBondDuplicate 1 := by
      simp [sourceNitrogenCopy, OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
        sourceNitrileRoot, OfficialCIPNode.rootFromEdge, OfficialCIPNode.depth, zero]
    have current : (sourceNitrogenCopy parity n copy).current? =
        some (sourceNitrileNitrogen parity n) := rfl
    have parent : (sourceNitrogenCopy parity n copy).parent? =
        some (sourceNitrileCarbon parity n) := rfl
    simp only [MoleculeGraph.exactOfficialRule1aObservation, current, provenance, parent,
      MoleculeGraph.exactRule1aMultipleBond_of_not_localized
        (nitrileSource parity n).molecule.toLocalizedMoleculeGraph
        (source_triple_not_mancude parity n), z]

theorem source_nitrile_observations (parity : TetrahedralInputParity) (n : Nat) :
    (((nitrileSource parity n).molecule.aromaticCanonicalOfficialCIPChildrenAt
      (nitrileSource parity n).molecule.atomCount (sourceNitrileRoot parity n)).map
        (nitrileSource parity n).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation) =
      [.ofNat 7, .ofNat 7, .ofNat 7] := by
  simp only [source_nitrile_children, List.map_cons, List.map_nil, source_nitrogen_copy_observation]

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
