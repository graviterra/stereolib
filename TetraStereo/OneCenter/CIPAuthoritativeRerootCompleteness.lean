import TetraStereo.OneCenter.CIPAuthoritativeRule6Completeness

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.AuthoritativeCIPRerootCompleteness

/-!
# Width-unbounded constitutional occurrence completeness

This discharges the constitutional part of the ordinary-stage premise exposed by the uncapped
Rule-6 totality theorem.  Recursive support carries only the local five-slot shape; exact uncapped
Rule-1a label availability is stated separately so no failed observation is silently defaulted.
-/

open RawMolecule
open AuthoritativeCIPRule6Completeness

/-- The two authoritative paired-frontier expanders are extensionally identical. -/
theorem nextCursorPairsAuthoritative?_eq_nextOccurrenceDescriptorPairsAuthoritative?
    (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) : ∀ pairs,
    nextCursorPairsAuthoritative? mol before pairs =
      nextOccurrenceDescriptorPairsAuthoritative? mol before before pairs
  | [] => rfl
  | pair :: pairs => by
      have tail := nextCursorPairsAuthoritative?_eq_nextOccurrenceDescriptorPairsAuthoritative?
        mol before pairs
      simp only [nextCursorPairsAuthoritative?,
        nextOccurrenceDescriptorPairsAuthoritative?]
      rw [tail]

/-- Authoritative constitutional node labels are total on a pair of supported observations. -/
theorem compareCanonicalPairLabelsAuthoritative?_exists (mol : RawMolecule)
    (rule : CanonicalRuleStage)
    (labelSupported : ∀ cursor : CanonicalRerootCursor,
      ∃ label, mol.canonicalRule1aLabelAuthoritative? cursor.node = some label) :
    ∀ pairs : List CursorPair,
      ∃ ordering, compareCursorPairLabelsAuthoritative? mol rule pairs = some ordering
  | [] => ⟨.eq, rfl⟩
  | pair :: pairs => by
      have leftLabel := labelSupported pair.1
      have rightLabel := labelSupported pair.2
      rcases leftLabel with ⟨leftLabel, leftEq⟩
      rcases rightLabel with ⟨rightLabel, rightEq⟩
      have nodeTotal : ∃ ordering,
          mol.compareCanonicalNodeRuleAuthoritative? rule pair.1.node pair.2.node = some ordering := by
        cases rule with
        | rule1a =>
            exact ⟨compareCIPAtomicLabel leftLabel rightLabel, by
              simp [RawMolecule.compareCanonicalNodeRuleAuthoritative?, leftEq, rightEq]⟩
        | rule1b => exact ⟨_, rfl⟩
        | rule2 => exact ⟨_, rfl⟩
      rcases nodeTotal with ⟨decision, decisionEq⟩
      cases decision with
      | lt => exact ⟨.lt, by simp [compareCursorPairLabelsAuthoritative?, decisionEq]⟩
      | gt => exact ⟨.gt, by simp [compareCursorPairLabelsAuthoritative?, decisionEq]⟩
      | eq =>
          rcases compareCanonicalPairLabelsAuthoritative?_exists mol rule labelSupported pairs with
            ⟨tailDecision, tailEq⟩
          exact ⟨tailDecision, by
            simp [compareCursorPairLabelsAuthoritative?, decisionEq, tailEq]⟩

/-- Every authoritative constitutional rule-sphere terminates on finite local support, with no
frontier-width premise. -/
theorem compareCursorRuleAuthoritative?_exists (mol : RawMolecule)
    (rankFuel : Nat)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeTotal : ∀ left right,
      CursorSupport mol rankFuel left → CursorSupport mol rankFuel right →
      ∃ ordering, before left right = some ordering)
    (labels : ∀ depth cursor, CursorSupport mol depth cursor →
      ∃ label, mol.canonicalRule1aLabelAuthoritative? cursor.node = some label)
    (rule : CanonicalRuleStage) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 → FrontierSupport mol fuel pairs →
      ∃ ordering, compareCursorRuleAuthoritative? mol before rule fuel pairs = some ordering
  | 0, pairs, _, support => by
      -- State the list proof directly to avoid requiring labels for cursors outside this frontier.
      have labelsExist : ∃ ordering,
          compareCursorPairLabelsAuthoritative? mol rule pairs = some ordering := by
        induction pairs with
        | nil => exact ⟨.eq, rfl⟩
        | cons pair rest inductionHypothesis =>
            have head := support pair (by simp)
            rcases labels 0 pair.1 head.1 with ⟨leftLabel, leftEq⟩
            rcases labels 0 pair.2 head.2 with ⟨rightLabel, rightEq⟩
            have nodeTotal : ∃ ordering,
                mol.compareCanonicalNodeRuleAuthoritative? rule pair.1.node pair.2.node =
                  some ordering := by
              cases rule with
              | rule1a => exact ⟨compareCIPAtomicLabel leftLabel rightLabel, by
                  simp [RawMolecule.compareCanonicalNodeRuleAuthoritative?, leftEq, rightEq]⟩
              | rule1b => exact ⟨_, rfl⟩
              | rule2 => exact ⟨_, rfl⟩
            rcases nodeTotal with ⟨decision, decisionEq⟩
            cases decision with
            | lt => exact ⟨.lt, by simp [compareCursorPairLabelsAuthoritative?, decisionEq]⟩
            | gt => exact ⟨.gt, by simp [compareCursorPairLabelsAuthoritative?, decisionEq]⟩
            | eq =>
                have restSupport : FrontierSupport mol 0 rest := by
                  intro candidate member
                  exact support candidate (by simp [member])
                rcases inductionHypothesis restSupport with ⟨tailDecision, tailEq⟩
                exact ⟨tailDecision, by
                  simp [compareCursorPairLabelsAuthoritative?, decisionEq, tailEq]⟩
      rcases labelsExist with ⟨observed, observedEq⟩
      cases observed with
      | lt => exact ⟨.lt, by simp [compareCursorRuleAuthoritative?, observedEq]⟩
      | gt => exact ⟨.gt, by simp [compareCursorRuleAuthoritative?, observedEq]⟩
      | eq =>
          have nextEq := nextOccurrenceDescriptorPairsAuthoritative?_zero_eq_nil mol before
            before pairs support
          rw [← nextCursorPairsAuthoritative?_eq_nextOccurrenceDescriptorPairsAuthoritative?
            mol before] at nextEq
          exact ⟨.eq, by simp [compareCursorRuleAuthoritative?, observedEq, nextEq]⟩
  | fuel + 1, pairs, fuelLe, support => by
      have lowerLe : fuel ≤ rankFuel := by omega
      have localTotal : ∀ left right,
          CursorSupport mol fuel left → CursorSupport mol fuel right →
          ∃ ordering, before left right = some ordering := by
        intro left right leftSupport rightSupport
        exact beforeTotal left right (leftSupport.mono lowerLe) (rightSupport.mono lowerLe)
      have labelsExist : ∃ ordering,
          compareCursorPairLabelsAuthoritative? mol rule pairs = some ordering := by
        induction pairs with
        | nil => exact ⟨.eq, rfl⟩
        | cons pair rest inductionHypothesis =>
            have head := support pair (by simp)
            rcases labels (fuel + 1) pair.1 head.1 with ⟨leftLabel, leftEq⟩
            rcases labels (fuel + 1) pair.2 head.2 with ⟨rightLabel, rightEq⟩
            have nodeTotal : ∃ ordering,
                mol.compareCanonicalNodeRuleAuthoritative? rule pair.1.node pair.2.node =
                  some ordering := by
              cases rule with
              | rule1a => exact ⟨compareCIPAtomicLabel leftLabel rightLabel, by
                  simp [RawMolecule.compareCanonicalNodeRuleAuthoritative?, leftEq, rightEq]⟩
              | rule1b => exact ⟨_, rfl⟩
              | rule2 => exact ⟨_, rfl⟩
            rcases nodeTotal with ⟨decision, decisionEq⟩
            cases decision with
            | lt => exact ⟨.lt, by simp [compareCursorPairLabelsAuthoritative?, decisionEq]⟩
            | gt => exact ⟨.gt, by simp [compareCursorPairLabelsAuthoritative?, decisionEq]⟩
            | eq =>
                have restSupport : FrontierSupport mol (fuel + 1) rest := by
                  intro candidate member
                  exact support candidate (by simp [member])
                rcases inductionHypothesis restSupport with ⟨tailDecision, tailEq⟩
                exact ⟨tailDecision, by
                  simp [compareCursorPairLabelsAuthoritative?, decisionEq, tailEq]⟩
      rcases labelsExist with ⟨observed, observedEq⟩
      cases observed with
      | lt => exact ⟨.lt, by simp [compareCursorRuleAuthoritative?, observedEq]⟩
      | gt => exact ⟨.gt, by simp [compareCursorRuleAuthoritative?, observedEq]⟩
      | eq =>
          rcases nextOccurrenceDescriptorPairsAuthoritative?_exists_of_support mol before before
              fuel localTotal localTotal pairs support with ⟨next, nextEq, nextSupport⟩
          rw [← nextCursorPairsAuthoritative?_eq_nextOccurrenceDescriptorPairsAuthoritative?
            mol before] at nextEq
          cases next with
          | nil => exact ⟨.eq, by
              simp [compareCursorRuleAuthoritative?, observedEq, nextEq]⟩
          | cons pair rest =>
              rcases compareCursorRuleAuthoritative?_exists mol rankFuel before beforeTotal labels
                  rule fuel (pair :: rest) (by omega) nextSupport with
                ⟨decision, decisionEq⟩
              exact ⟨decision, by
                simp [compareCursorRuleAuthoritative?, observedEq, nextEq, decisionEq]⟩

/-- The complete width-unbounded constitutional Rules-1a--2 comparison is total on every finite
locally supported pair whose uncapped Rule-1a observations exist. -/
theorem compareCursorBranchAtAuthoritative?_exists (mol : RawMolecule)
    (labels : ∀ depth cursor, CursorSupport mol depth cursor →
      ∃ label, mol.canonicalRule1aLabelAuthoritative? cursor.node = some label) :
    ∀ fuel left right,
      CursorSupport mol fuel left → CursorSupport mol fuel right →
      ∃ ordering,
        compareCursorBranchAtAuthoritative? mol fuel .rule2 left right = some ordering
  | 0, left, right, leftSupport, rightSupport => by
      rcases labels 0 left leftSupport with ⟨leftLabel, leftEq⟩
      rcases labels 0 right rightSupport with ⟨rightLabel, rightEq⟩
      simp only [compareCursorBranchAtAuthoritative?,
        RawMolecule.compareCanonicalNodeThroughAuthoritative?,
        RawMolecule.compareCanonicalNodeRuleAuthoritative?, leftEq, rightEq]
      cases rule1aEq : compareCIPAtomicLabel leftLabel rightLabel <;> simp [rule1aEq]
      cases mol.compareCanonicalNodeRule .rule1b left.node right.node <;> simp
  | fuel + 1, left, right, leftSupport, rightSupport => by
      let before := compareCursorBranchAtAuthoritative? mol fuel .rule2
      have beforeTotal : ∀ siblingLeft siblingRight,
          CursorSupport mol fuel siblingLeft → CursorSupport mol fuel siblingRight →
          ∃ ordering, before siblingLeft siblingRight = some ordering := by
        intro siblingLeft siblingRight siblingLeftSupport siblingRightSupport
        exact compareCursorBranchAtAuthoritative?_exists mol labels fuel siblingLeft siblingRight
          siblingLeftSupport siblingRightSupport
      have frontier : FrontierSupport mol (fuel + 1) [(left, right)] := by
        intro pair member
        have pairEq : pair = (left, right) := by simpa using member
        subst pair
        exact ⟨leftSupport, rightSupport⟩
      rcases compareCursorRuleAuthoritative?_exists mol fuel before beforeTotal labels .rule1a
          (fuel + 1) [(left, right)] (by omega) frontier with ⟨rule1a, rule1aEq⟩
      rcases compareCursorRuleAuthoritative?_exists mol fuel before beforeTotal labels .rule1b
          (fuel + 1) [(left, right)] (by omega) frontier with ⟨rule1b, rule1bEq⟩
      rcases compareCursorRuleAuthoritative?_exists mol fuel before beforeTotal labels .rule2
          (fuel + 1) [(left, right)] (by omega) frontier with ⟨rule2, rule2Eq⟩
      cases rule1a <;> cases rule1b <;> cases rule2 <;>
        simp [compareCursorBranchAtAuthoritative?, before, rule1aEq, rule1bEq, rule2Eq]

end TetraStereo.OneCenter.AuthoritativeCIPRerootCompleteness
