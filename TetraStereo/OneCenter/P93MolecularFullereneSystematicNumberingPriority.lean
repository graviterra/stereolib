import TetraStereo.OneCenter.P93MolecularFullereneExteriorOrientation
import Mathlib.Data.List.Lex

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

/-!
# IUPAC systematic fullerene-numbering atom and path priority

Rules Fu-3.1.2.1--3, Fu-3.1.4, Fu-3.3.2.1--2, Fu-3.3.4, Fu-3.4.1, and Fu-3.4.2
share one atom-ranking rule.  An atom is ranked by the sizes of the three rings meeting there,
largest first; candidate numbering pathways are then compared sequentially, and the pathway with
the higher-ranking atom at the first point of difference is preferred.

This module derives those atom ranks from the complete molecular face map and proves the executable
path comparator exact against a separate nested lexicographic proposition.  It deliberately does
not yet choose the reference rotation axis or reflection plane, prove helical continuity, or apply
the discontiguous-path rules Fu-3.2.  Those are later filters over the exact priority relation proved
here, not substitutes for it.
-/

/-- Exhaustive finite universe of atom numberings for the canonical cage carrier.  No path is
omitted: every permutation is present before the Fu-3 reference-element and helix filters apply. -/
def molecularFullereneNumberingCandidates
    (input : MolecularFullereneConfigurationInput) : Finset (List ℕ) :=
  input.carrier.toList.permutations.toFinset

/-- Exact candidate-universe theorem: membership is precisely a duplicate-free bijection onto the
cage carrier. -/
theorem mem_molecularFullereneNumberingCandidates_iff
    (input : MolecularFullereneConfigurationInput) (atomsByLocant : List ℕ) :
    atomsByLocant ∈ molecularFullereneNumberingCandidates input ↔
      atomsByLocant.Nodup ∧ atomsByLocant.toFinset = input.carrier := by
  constructor
  · intro present
    have permutation : atomsByLocant.Perm input.carrier.toList :=
      List.mem_permutations.mp
        (List.mem_toFinset.mp (by
          simpa [molecularFullereneNumberingCandidates] using present))
    refine ⟨permutation.nodup_iff.mpr input.carrier.nodup_toList, ?_⟩
    simpa using List.toFinset_eq_of_perm _ _ permutation
  · rintro ⟨nodup, carrierEq⟩
    apply List.mem_toFinset.mpr
    apply List.mem_permutations.mpr
    have permutation : atomsByLocant.Perm atomsByLocant.toFinset.toList :=
      (atomsByLocant.toFinset_toList nodup).symm
    simpa [carrierEq] using permutation

/-- Every numbering accepted by the preexisting molecular evidence judgment belongs to the
exhaustive candidate universe; later preference filters therefore cannot lose it through caller
under-enumeration. -/
theorem MolecularFullereneNumberingEvidenceJudgment.numberingCandidate
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence)
    (judged : MolecularFullereneNumberingEvidenceJudgment input evidence) :
    evidence.atomsByLocant ∈ molecularFullereneNumberingCandidates input :=
  (mem_molecularFullereneNumberingCandidates_iff input evidence.atomsByLocant).mpr
    ⟨judged.1, judged.2.1⟩

/-- Exhaustive systematic-tagged numbering evidence.  Every carrier permutation is paired with
every named face and then filtered by the already independent molecular numbering judgment. -/
noncomputable def molecularFullereneSystematicNumberingEvidenceCandidates
    (input : MolecularFullereneConfigurationInput) :
    List MolecularFullereneNumberingEvidence :=
  (input.carrier.toList.permutations.flatMap fun atomsByLocant =>
    input.faces.map fun startingFace =>
      { numberingKind := .systematic
        atomsByLocant := atomsByLocant
        startingFace := startingFace }).filter fun evidence =>
          decide (MolecularFullereneNumberingEvidenceJudgment input evidence)

/-- Exact no-invention/no-omission theorem for locally valid systematic numbering evidence. -/
theorem mem_molecularFullereneSystematicNumberingEvidenceCandidates_iff
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneNumberingEvidence) :
    evidence ∈ molecularFullereneSystematicNumberingEvidenceCandidates input ↔
      evidence.numberingKind = .systematic ∧
        MolecularFullereneNumberingEvidenceJudgment input evidence := by
  classical
  constructor
  · intro present
    have filtered := List.mem_filter.mp present
    have judged : MolecularFullereneNumberingEvidenceJudgment input evidence :=
      of_decide_eq_true filtered.2
    rcases List.mem_flatMap.mp filtered.1 with
      ⟨atomsByLocant, _atomsPresent, evidencePresent⟩
    rcases List.mem_map.mp evidencePresent with
      ⟨startingFace, _facePresent, evidenceEq⟩
    have kindEq : evidence.numberingKind = .systematic := by
      rw [← evidenceEq]
    exact ⟨kindEq, judged⟩
  · rintro ⟨kindEq, judged⟩
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa only [decide_eq_true_eq] using judged⟩
    apply List.mem_flatMap.mpr
    refine ⟨evidence.atomsByLocant, ?_, ?_⟩
    · have candidate := judged.numberingCandidate input evidence
      exact List.mem_toFinset.mp
        (by simpa [molecularFullereneNumberingCandidates] using candidate)
    · apply List.mem_map.mpr
      refine ⟨evidence.startingFace, judged.2.2.1, ?_⟩
      cases evidence
      simp_all

/-- The exhaustive locally valid evidence universe is nonempty exactly when such systematic
numbering evidence exists. -/
theorem molecularFullereneSystematicNumberingEvidenceCandidates_nonempty_iff
    (input : MolecularFullereneConfigurationInput) :
    molecularFullereneSystematicNumberingEvidenceCandidates input ≠ [] ↔
      ∃ evidence,
        evidence.numberingKind = .systematic ∧
          MolecularFullereneNumberingEvidenceJudgment input evidence := by
  constructor
  · intro nonempty
    obtain ⟨evidence, present⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨evidence,
      (mem_molecularFullereneSystematicNumberingEvidenceCandidates_iff
        input evidence).mp present⟩
  · rintro ⟨evidence, judged⟩
    exact List.ne_nil_of_mem
      ((mem_molecularFullereneSystematicNumberingEvidenceCandidates_iff
        input evidence).mpr judged)

/-- Sizes of all named molecular cage faces incident with one atom. -/
def fullereneIncidentRingSizes
    (input : MolecularFullereneConfigurationInput) (atom : ℕ) : List ℕ :=
  (input.faces.filter fun face => decide (atom ∈ face)).map List.length

/-- Fu-3 atom rank: incident ring sizes sorted from largest to smallest.  On an admitted cubic
fullerene carrier this list has the official three entries. -/
def fullereneAtomRingRank
    (input : MolecularFullereneConfigurationInput) (atom : ℕ) : List ℕ :=
  (fullereneIncidentRingSizes input atom).mergeSort
    (fun left right => decide (right ≤ left))

/-- Rank construction neither invents nor drops an incident ring size. -/
theorem fullereneAtomRingRank_perm_incidentRingSizes
    (input : MolecularFullereneConfigurationInput) (atom : ℕ) :
    (fullereneAtomRingRank input atom).Perm
      (fullereneIncidentRingSizes input atom) := by
  simpa [fullereneAtomRingRank] using
    (List.mergeSort_perm (fullereneIncidentRingSizes input atom)
      (fun left right => decide (right ≤ left)))

/-- Independent Fu-3 meaning of “higher-ranking atom at the first point of difference”. -/
def FullereneRingRankHigherAtFirstDifference
    (left right : List ℕ) : Prop :=
  List.Lex (fun first second : ℕ => first < second) right left

/-- Executable comparison of two descending incident-ring-size ranks. -/
def compareFullereneRingRanks (left right : List ℕ) : Ordering :=
  List.compareLex compare left right

/-- Executable atom-rank comparison is exact against the independent first-difference relation. -/
@[simp] theorem compareFullereneRingRanks_eq_gt_iff
    (left right : List ℕ) :
    compareFullereneRingRanks left right = .gt ↔
      FullereneRingRankHigherAtFirstDifference left right := by
  induction left generalizing right with
  | nil => cases right <;> simp [compareFullereneRingRanks,
      FullereneRingRankHigherAtFirstDifference, List.compareLex]
  | cons leftHead leftTail ih =>
      cases right with
      | nil => simp [compareFullereneRingRanks,
          FullereneRingRankHigherAtFirstDifference, List.compareLex]
      | cons rightHead rightTail =>
          cases compared : compare leftHead rightHead with
          | lt =>
              have lower : leftHead < rightHead := compare_lt_iff_lt.mp compared
              have notHigher : ¬rightHead < leftHead :=
                not_lt_of_ge (Nat.le_of_lt lower)
              have notEqual : rightHead ≠ leftHead :=
                (Nat.ne_of_lt lower).symm
              simp [compareFullereneRingRanks,
                FullereneRingRankHigherAtFirstDifference, List.compareLex, compared,
                List.cons_lex_cons_iff, notHigher, notEqual]
          | eq =>
              have equal : leftHead = rightHead := compare_eq_iff_eq.mp compared
              subst rightHead
              unfold compareFullereneRingRanks
              unfold FullereneRingRankHigherAtFirstDifference
              rw [List.compareLex, compared, List.cons_lex_cons_iff]
              simp only [Nat.lt_irrefl, false_or, true_and]
              simpa only [compareFullereneRingRanks,
                FullereneRingRankHigherAtFirstDifference] using ih rightTail
          | gt =>
              have higher : rightHead < leftHead := compare_gt_iff_gt.mp compared
              simp [compareFullereneRingRanks,
                FullereneRingRankHigherAtFirstDifference, List.compareLex, compared,
                List.cons_lex_cons_iff, higher]

/-- The explicit example in Fu-3.1.2.1: a 6,6,6 atom outranks a 6,6,5 atom. -/
theorem fullereneRingRank_666_higher_665 :
    compareFullereneRingRanks [6, 6, 6] [6, 6, 5] = .gt := by
  decide

/-- Face-derived atom-rank sequence of a proposed locant pathway. -/
def molecularFullereneNumberingPathRingRanks
    (input : MolecularFullereneConfigurationInput) (atomsByLocant : List ℕ) :
    List (List ℕ) :=
  atomsByLocant.map (fullereneAtomRingRank input)

/-- Independent Fu-3.1.4/Fu-3.3.4/Fu-3.4.2 comparison of two proposed numbering paths. -/
def MolecularFullereneNumberingPathHigherAtFirstDifference
    (input : MolecularFullereneConfigurationInput)
    (left right : List ℕ) : Prop :=
  List.Lex
    (fun rightRank leftRank : List ℕ =>
      FullereneRingRankHigherAtFirstDifference leftRank rightRank)
    (molecularFullereneNumberingPathRingRanks input right)
    (molecularFullereneNumberingPathRingRanks input left)

/-- Executable sequential comparison of the face-derived atom ranks of two numbering paths. -/
def compareMolecularFullereneNumberingPathRanks
    (input : MolecularFullereneConfigurationInput)
    (left right : List ℕ) : Ordering :=
  List.compareLex compareFullereneRingRanks
    (molecularFullereneNumberingPathRingRanks input left)
    (molecularFullereneNumberingPathRingRanks input right)

private theorem compareFullereneRingRanks_eq_eq_iff
    (left right : List ℕ) :
    compareFullereneRingRanks left right = .eq ↔ left = right := by
  change List.compareLex compare left right = .eq ↔ left = right
  exact Std.LawfulEqCmp.compare_eq_iff_eq

private theorem compareFullereneRingRankPaths_eq_gt_iff
    (left right : List (List ℕ)) :
    List.compareLex compareFullereneRingRanks left right = .gt ↔
      List.Lex
        (fun rightRank leftRank : List ℕ =>
          FullereneRingRankHigherAtFirstDifference leftRank rightRank)
        right left := by
  induction left generalizing right with
  | nil => cases right <;> simp [List.compareLex]
  | cons leftHead leftTail ih =>
      cases right with
      | nil => simp [List.compareLex]
      | cons rightHead rightTail =>
          cases compared : compareFullereneRingRanks leftHead rightHead with
          | lt =>
              have notHigher :
                  ¬FullereneRingRankHigherAtFirstDifference leftHead rightHead := by
                intro higher
                have contradiction :=
                  (compareFullereneRingRanks_eq_gt_iff leftHead rightHead).mpr higher
                rw [compared] at contradiction
                cases contradiction
              have notEqual : rightHead ≠ leftHead := by
                intro equal
                have comparatorEqual :=
                  (compareFullereneRingRanks_eq_eq_iff leftHead rightHead).mpr equal.symm
                rw [compared] at comparatorEqual
                cases comparatorEqual
              simp [List.compareLex, compared, List.cons_lex_cons_iff,
                notHigher, notEqual]
          | eq =>
              have equal : leftHead = rightHead :=
                (compareFullereneRingRanks_eq_eq_iff leftHead rightHead).mp compared
              subst rightHead
              have notHigher :
                  ¬FullereneRingRankHigherAtFirstDifference leftHead leftHead := by
                intro higher
                have contradiction :=
                  (compareFullereneRingRanks_eq_gt_iff leftHead leftHead).mpr higher
                rw [compared] at contradiction
                cases contradiction
              simpa [List.compareLex, compared, List.cons_lex_cons_iff, notHigher] using
                ih rightTail
          | gt =>
              have higher :
                  FullereneRingRankHigherAtFirstDifference leftHead rightHead :=
                (compareFullereneRingRanks_eq_gt_iff leftHead rightHead).mp compared
              simp [List.compareLex, compared, List.cons_lex_cons_iff, higher]

/-- The path comparator returns `gt` exactly when the left path has the higher face-derived atom
rank at the first point where the two rank sequences differ. -/
@[simp] theorem compareMolecularFullereneNumberingPathRanks_eq_gt_iff
    (input : MolecularFullereneConfigurationInput)
    (left right : List ℕ) :
    compareMolecularFullereneNumberingPathRanks input left right = .gt ↔
      MolecularFullereneNumberingPathHigherAtFirstDifference input left right := by
  change
    compare
        (molecularFullereneNumberingPathRingRanks input left)
        (molecularFullereneNumberingPathRingRanks input right) = .gt ↔
      List.Lex
        (fun rightRank leftRank : List ℕ =>
          List.Lex (fun first second : ℕ => first < second) rightRank leftRank)
        (molecularFullereneNumberingPathRingRanks input right)
        (molecularFullereneNumberingPathRingRanks input left)
  exact compareFullereneRingRankPaths_eq_gt_iff
    (molecularFullereneNumberingPathRingRanks input left)
    (molecularFullereneNumberingPathRingRanks input right)

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
