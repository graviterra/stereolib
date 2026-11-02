import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeChildren

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingRuntimeRoot

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.NativeRingRuntimeChildren
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeRingSingleBondChildren

def physicalRoots (n : Nat) (parity : TetrahedralInputParity) : List CanonicalRerootCursor :=
  (recordNeighbors (expanded n parity) 0).map rootCursor

def orderedRoots (n : Nat) : List CanonicalRerootCursor :=
  [rootCursor 1, rootCursor 2, rootCursor (n + 4), rootCursor (n + 5)]

theorem actual_root_children (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).canonicalChildren (canonicalCenterRoot 0) =
      (recordNeighbors (expanded n parity) 0).map (canonicalRoot 0) := by
  have absent : 0 ∉ recordNeighbors (expanded n parity) 0 := by
    intro member
    exact (recordNeighbor_bounds (expanded_stereochemical_admissible n parity).1.1 member).2 rfl
  have copies := actual_child_copies (expanded n parity) (canonicalCenterRoot 0)
    (expanded_record_bond_one n parity 0)
  change (expanded n parity).canonicalChildCopies (canonicalCenterRoot 0) =
    ((recordNeighbors (expanded n parity) 0).erase 0).map (fun other => (other, 0)) at copies
  rw [List.erase_of_not_mem absent] at copies
  unfold canonicalChildren
  rw [show (canonicalCenterRoot 0).forcedLeaf = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte, copies, List.map_map]
  apply List.map_congr_left
  intro other member
  have different := (recordNeighbor_bounds (expanded_stereochemical_admissible n parity).1.1 member).2
  simp [canonicalCenterRoot, canonicalRoot, List.contains_eq_mem, different]

theorem actual_root_cursors (n : Nat) (parity : TetrahedralInputParity) :
    occurrenceLigandCursors (expanded n parity) (canonicalCenterRoot 0) = physicalRoots n parity := by
  have forced : (canonicalCenterRoot 0).forcedLeaf = false := rfl
  have parent : canonicalOriginalParent? (canonicalCenterRoot 0) = none := rfl
  simp only [occurrenceLigandCursors, CanonicalRerootCursor.children,
    CanonicalRerootCursor.neighbors, forced, Bool.false_eq_true, ↓reduceIte,
    parent, Option.toList_none, List.nil_append, actual_root_children,
    List.filterMap_map]
  change List.filterMap (some ∘ rootCursor) (recordNeighbors (expanded n parity) 0) =
    List.map rootCursor (recordNeighbors (expanded n parity) 0)
  exact congrFun List.filterMap_eq_map _

theorem actual_root_ligands (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).ligandsWithLonePair 0 = [n + 5, 1, 2, n + 4] := by
  have observed := expanded_original_atom n parity 0 _ (ringRaw_atomAt_zero n parity)
  unfold ligandsWithLonePair
  rw [observed, expanded_root_written_row]
  rfl

theorem physical_roots_perm (n : Nat) (parity : TetrahedralInputParity) :
    (physicalRoots n parity).Perm
      [rootCursor (n + 5), rootCursor 1, rootCursor 2, rootCursor (n + 4)] :=
  (expanded_root_records n parity).map rootCursor

theorem physical_roots_length (n : Nat) (parity : TetrahedralInputParity) :
    (physicalRoots n parity).length = 4 :=
  (physical_roots_perm n parity).length_eq

theorem actual_root_frame (n : Nat) (parity : TetrahedralInputParity) :
    occurrenceLigandFrame? (expanded n parity) (canonicalCenterRoot 0) =
      some (physicalRoots n parity) := by
  unfold occurrenceLigandFrame?
  change (if ((expanded n parity).ligandsWithLonePair 0).length != 4 then none else _) = _
  rw [actual_root_ligands]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, actual_root_cursors, physical_roots_length,
    beq_self_eq_true]

theorem actual_priority_positions (n : Nat) (parity : TetrahedralInputParity) :
    ((orderedRoots n).mapM fun cursor =>
      (((expanded n parity).ligandsWithLonePair 0).zipIdx.find?
        fun entry => entry.1 == cursor.node.atom).map Prod.snd) = some [1, 2, 3, 0] := by
  rw [actual_root_ligands]
  simp [orderedRoots, rootCursor, awayCursor, pathNode]

theorem actual_priority_odd : permutationIsEven [1, 2, 3, 0] = false := by decide +kernel

end TetraStereo.UniversalProof.NativeRingRuntimeRoot
