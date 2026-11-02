import TetraStereo.UniversalProof.NextFrontier.NativeNitrileAminoChildren
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileOrderedChildren

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge

def nitrileRootCursor (atom : Nat) : CanonicalRerootCursor :=
  ⟨canonicalRoot 0 atom, some (canonicalCenterRoot 0)⟩

theorem actual_center_child_copies (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).canonicalChildCopies (canonicalCenterRoot 0) =
      (recordNeighbors (expanded parity n) 0).map (fun atom => (atom, 0)) := by
  have actual := actual_child_copies (expanded parity n) (canonicalCenterRoot 0)
    (fun other retained => expanded_record_order_one parity n 0 other
      (by decide) (by decide) retained)
  have absent : 0 ∉ recordNeighbors (expanded parity n) 0 := by
    intro retained
    exact (recordNeighbor_bounds (expanded_admissible parity n).1 retained).2 rfl
  simpa only [canonicalCenterRoot, List.erase_of_not_mem absent] using actual

theorem actual_center_children (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).canonicalChildren (canonicalCenterRoot 0) =
      (recordNeighbors (expanded parity n) 0).map (canonicalRoot 0) := by
  have forced : (canonicalCenterRoot 0).forcedLeaf = false := rfl
  unfold canonicalChildren
  rw [forced]
  simp only [Bool.false_eq_true, ↓reduceIte, actual_center_child_copies, List.map_map]
  apply List.map_congr_left
  intro atom retained
  have different := (recordNeighbor_bounds (expanded_admissible parity n).1 retained).2
  simp [canonicalCenterRoot, canonicalRoot, different]

theorem actual_center_cursors (parity : TetrahedralInputParity) (n : Nat) :
    occurrenceLigandCursors (expanded parity n) (canonicalCenterRoot 0) =
      (recordNeighbors (expanded parity n) 0).map nitrileRootCursor := by
  have forced : (canonicalCenterRoot 0).forcedLeaf = false := rfl
  have parent : canonicalOriginalParent? (canonicalCenterRoot 0) = none := rfl
  unfold occurrenceLigandCursors CanonicalRerootCursor.children CanonicalRerootCursor.neighbors
  rw [forced]
  simp only [Bool.false_eq_true, ↓reduceIte, parent, Option.toList_none, List.nil_append,
    actual_center_children, List.filterMap_map]
  change List.filterMap (some ∘ nitrileRootCursor) _ = List.map nitrileRootCursor _
  exact congrFun List.filterMap_eq_map _

theorem actual_center_cursors_permutation (parity : TetrahedralInputParity) (n : Nat) :
    (occurrenceLigandCursors (expanded parity n) (canonicalCenterRoot 0)).Perm
      [nitrileRootCursor (n + 7), nitrileRootCursor 1, nitrileCursor, aminoCursor] := by
  rw [actual_center_cursors]
  exact (expanded_center_records parity n).map nitrileRootCursor

theorem actual_center_ligands (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).ligandsWithLonePair 0 = [n + 7, 1, 2, 4] := by
  unfold ligandsWithLonePair
  rw [expanded_center_row]
  cases (expanded parity n).atomAt? 0 <;> simp

/-- The actual production frame returns its four real occurrence cursors. The triple bond is
below the root and contributes no extra root slot or lone-pair phantom. -/
theorem actual_center_occurrence_frame (parity : TetrahedralInputParity) (n : Nat) :
    occurrenceLigandFrame? (expanded parity n) (canonicalCenterRoot 0) =
      some (occurrenceLigandCursors (expanded parity n) (canonicalCenterRoot 0)) := by
  have count : (occurrenceLigandCursors (expanded parity n) (canonicalCenterRoot 0)).length = 4 :=
    (actual_center_cursors_permutation parity n).length_eq
  have ligandCount :
      ((expanded parity n).ligandsWithLonePair (canonicalCenterRoot 0).atom).length = 4 := by
    change ((expanded parity n).ligandsWithLonePair 0).length = 4
    rw [actual_center_ligands]
    rfl
  simp only [occurrenceLigandFrame?, ligandCount, count]
  rfl

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
