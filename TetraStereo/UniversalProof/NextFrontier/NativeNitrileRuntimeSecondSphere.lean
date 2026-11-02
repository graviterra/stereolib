import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSiblingSorting
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileAminoChildren
import TetraStereo.UniversalProof.NextFrontier.NativeSecondSphereComparisonBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge
open TetraStereo.UniversalProof.NativeSecondSphereComparisonBridge

theorem actual_nitrile_nonterminal (parity : TetrahedralInputParity) (n : Nat) :
    cursorTerminal (expanded parity n) nitrileCursor = false := by
  unfold cursorTerminal
  change (false || (nitrileCursor.children (expanded parity n)).isEmpty) = false
  rw [expanded_nitrile_cursor_children]
  rfl

theorem actual_nitrile_amino_child_labels (parity : TetrahedralInputParity) (n : Nat) :
    ((expanded parity n).compareCanonicalNodeRule? .rule1a
        realNitrileCursor.node (aminoChild 5).node = some .eq ∧
      (expanded parity n).compareCanonicalNodeRuleAuthoritative? .rule1a
        realNitrileCursor.node (aminoChild 5).node = some .eq) ∧
    ((expanded parity n).compareCanonicalNodeRule? .rule1a
        duplicateNitrileCursor.node (aminoChild 6).node = some .gt ∧
      (expanded parity n).compareCanonicalNodeRuleAuthoritative? .rule1a
        duplicateNitrileCursor.node (aminoChild 6).node = some .gt) ∧
    ((expanded parity n).compareCanonicalNodeRule? .rule1a
        (aminoChild 5).node realNitrileCursor.node = some .eq ∧
      (expanded parity n).compareCanonicalNodeRuleAuthoritative? .rule1a
        (aminoChild 5).node realNitrileCursor.node = some .eq) ∧
    ((expanded parity n).compareCanonicalNodeRule? .rule1a
        (aminoChild 6).node duplicateNitrileCursor.node = some .lt ∧
      (expanded parity n).compareCanonicalNodeRuleAuthoritative? .rule1a
        (aminoChild 6).node duplicateNitrileCursor.node = some .lt) := by
  have table := nitrile_sibling_label_table parity n
  rcases expanded_local_atomic_numbers parity n with
    ⟨_, _, _, _, _, nitrogen, carbon, _⟩
  have aminoN : (expanded parity n).canonicalRule1aLabel? (aminoChild 5).node = some ⟨7, 1⟩ := by
    simp [canonicalRule1aLabel?, aminoChild, awayCursor, pathNode, nitrogen]
  have aminoNA : (expanded parity n).canonicalRule1aLabelAuthoritative? (aminoChild 5).node =
      some ⟨7, 1⟩ := by
    simp [canonicalRule1aLabelAuthoritative?, aminoChild, awayCursor, pathNode, nitrogen]
  have aminoC : (expanded parity n).canonicalRule1aLabel? (aminoChild 6).node = some ⟨6, 1⟩ := by
    simp [canonicalRule1aLabel?, aminoChild, awayCursor, pathNode, carbon]
  have aminoCA : (expanded parity n).canonicalRule1aLabelAuthoritative? (aminoChild 6).node =
      some ⟨6, 1⟩ := by
    simp [canonicalRule1aLabelAuthoritative?, aminoChild, awayCursor, pathNode, carbon]
  simp only [compareCanonicalNodeRule?, compareCanonicalNodeRuleAuthoritative?,
    realNitrileCursor, duplicateNitrileCursor, table.1.1, table.1.2,
    table.2.1.1, table.2.1.2, aminoN, aminoNA, aminoC, aminoCA]
  decide

/-- Both production occurrence comparators observe the first N/N tie and the decisive second
N/C pair. The actual sorted left occurrence at that pair is a multiple-bond duplicate. -/
theorem actual_nitrile_amino_comparison (parity : TetrahedralInputParity) (n fuel : Nat)
    (stage : CanonicalRuleStage) :
    compareCursorBranchAt (expanded parity n) (fuel + 2) stage
        nitrileCursor aminoCursor = some .gt ∧
      compareCursorBranchAtAuthoritative? (expanded parity n) (fuel + 2) stage
        nitrileCursor aminoCursor = some .gt ∧
      compareCursorBranchAt (expanded parity n) (fuel + 2) stage
        aminoCursor nitrileCursor = some .lt ∧
      compareCursorBranchAtAuthoritative? (expanded parity n) (fuel + 2) stage
        aminoCursor nitrileCursor = some .lt := by
  have nitrileCount : (nitrileCursor.children (expanded parity n)).length = 3 := by
    rw [expanded_nitrile_cursor_children]
    rfl
  have aminoCount : (aminoCursor.children (expanded parity n)).length = 3 :=
    (actual_amino_children parity n).length_eq
  have nitrileSort := actual_nitrile_sibling_sort parity n fuel stage
  have aminoSort := actual_amino_sibling_sort parity n (fuel + 1) stage
  have leftRank := ranked_fast_of_sort_three _ _ _ _ _ _ nitrileCount nitrileSort.1
  have rightRank := ranked_fast_of_sort_three _ _ _ _ _ _ aminoCount aminoSort.1
  have leftRankA := ranked_authoritative_of_sort_three _ _ _ _ _ _ nitrileCount nitrileSort.2
  have rightRankA := ranked_authoritative_of_sort_three _ _ _ _ _ _ aminoCount aminoSort.2
  have leftLive := actual_nitrile_nonterminal parity n
  have rightLive := actual_amino_nonterminal parity n
  have observations := actual_nitrile_amino_child_labels parity n
  rcases expanded_local_atomic_numbers parity n with ⟨_, _, nitrileZ, _, aminoZ, _⟩
  have sameZ : (expanded parity n).atomZAt nitrileCursor.node.atom =
      (expanded parity n).atomZAt aminoCursor.node.atom := by
    change (expanded parity n).atomZAt 2 = (expanded parity n).atomZAt 4
    rw [nitrileZ, aminoZ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fast_raw_of_ranked_three _ (fuel + 1) stage _ _ _ _ _ _ _ _ .gt
      rfl rfl sameZ leftLive rightLive leftRank rightRank
      (.tie _ _ _ observations.1.1 (.head _ _ _ observations.2.1.1)) (by decide)
  · exact authoritative_raw_of_ranked_three _ (fuel + 1) stage _ _ _ _ _ _ _ _ .gt
      rfl rfl sameZ leftLive rightLive leftRankA rightRankA
      (.tie _ _ _ observations.1.2 (.head _ _ _ observations.2.1.2)) (by decide)
  · exact fast_raw_of_ranked_three _ (fuel + 1) stage _ _ _ _ _ _ _ _ .lt
      rfl rfl sameZ.symm rightLive leftLive rightRank leftRank
      (.tie _ _ _ observations.2.2.1.1 (.head _ _ _ observations.2.2.2.1)) (by decide)
  · exact authoritative_raw_of_ranked_three _ (fuel + 1) stage _ _ _ _ _ _ _ _ .lt
      rfl rfl sameZ.symm rightLive leftLive rightRankA leftRankA
      (.tie _ _ _ observations.2.2.1.2 (.head _ _ _ observations.2.2.2.2)) (by decide)

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
