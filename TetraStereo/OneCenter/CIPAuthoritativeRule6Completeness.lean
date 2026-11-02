import TetraStereo.OneCenter.CIPAuthoritativeRule6PromotedComparatorLaws
import TetraStereo.OneCenter.ProductionCIPBranchingComparatorCompleteness

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.AuthoritativeCIPRule6Completeness

/-!
# Structural totality of width-unbounded promoted Rule 6

The old branching proof carried a global `3 ^ fuel ≤ defaultBranchWidthCap` certificate.  The
authoritative traversal has no such branch, so its structural support records only the finite
recursive cursor shape and the P-92 bonding-number-six local child bound.  This module proves that
those local facts, together with totality of the strictly earlier comparison on recursively
supported cursors, make every promoted Rule-6 sphere terminate.
-/

open RawMolecule

/-- Finite recursive occurrence shape through a selected comparison depth.  Five forward slots
are the local maximum after removing the incoming occurrence from a bonding-number-six node. -/
inductive CursorSupport (mol : RawMolecule) : Nat → CanonicalRerootCursor → Prop
  | terminal (fuel : Nat) (cursor : CanonicalRerootCursor)
      (isTerminal : cursorTerminal mol cursor = true) : CursorSupport mol fuel cursor
  | branch (fuel : Nat) (cursor : CanonicalRerootCursor)
      (children : List CanonicalRerootCursor)
      (childrenEq : cursor.children mol = children)
      (width : children.length ≤ RawMolecule.authoritativeChildSlots)
      (childrenSupport : ∀ child, child ∈ children → CursorSupport mol fuel child) :
      CursorSupport mol (fuel + 1) cursor

theorem CursorSupport.zero_terminal {mol : RawMolecule} {cursor : CanonicalRerootCursor}
    (support : CursorSupport mol 0 cursor) : cursorTerminal mol cursor = true := by
  cases support with
  | terminal _ _ terminal => exact terminal

theorem CursorSupport.succ {mol : RawMolecule} {fuel : Nat}
    {cursor : CanonicalRerootCursor} (support : CursorSupport mol fuel cursor) :
    CursorSupport mol (fuel + 1) cursor := by
  induction support with
  | terminal fuel cursor terminal => exact .terminal (fuel + 1) cursor terminal
  | branch fuel cursor children childrenEq width childrenSupport inductionHypothesis =>
      exact .branch (fuel + 1) cursor children childrenEq width inductionHypothesis

theorem CursorSupport.mono {mol : RawMolecule} {smaller larger : Nat}
    {cursor : CanonicalRerootCursor} (support : CursorSupport mol smaller cursor)
    (le : smaller ≤ larger) : CursorSupport mol larger cursor := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  clear le
  induction extra with
  | zero => simpa using support
  | succ extra inductionHypothesis =>
      simpa [Nat.add_assoc] using CursorSupport.succ inductionHypothesis

def paddingCursor (mol : RawMolecule) (cursor : CanonicalRerootCursor) :
    CanonicalRerootCursor :=
  { node := mol.canonicalPhantom cursor.node.atom (cursor.node.rule1bRootDistance + 1) }

theorem paddingCursor_support (mol : RawMolecule) (fuel : Nat)
    (cursor : CanonicalRerootCursor) : CursorSupport mol fuel (paddingCursor mol cursor) := by
  apply CursorSupport.terminal
  simp [paddingCursor, cursorTerminal, CanonicalRerootCursor.children,
    RawMolecule.canonicalPhantom, CanonicalBranchNode.forcedLeaf]

/-- Authoritative child ranking succeeds from recursive support and a total earlier-stage
callback.  The result always has exactly five supported slots. -/
theorem rankedCursorChildrenAuthoritative?_exists_of_support (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : Nat) (cursor : CanonicalRerootCursor)
    (support : CursorSupport mol (fuel + 1) cursor)
    (beforeTotal : ∀ left right,
      CursorSupport mol fuel left → CursorSupport mol fuel right →
      ∃ ordering, before left right = some ordering) :
    ∃ ranked,
      rankedCursorChildrenAuthoritative? mol before cursor = some ranked ∧
      ranked.length = RawMolecule.authoritativeChildSlots ∧
      ∀ child, child ∈ ranked → CursorSupport mol fuel child := by
  cases support with
  | terminal _ _ terminal =>
      have childrenNil :=
        AuthoritativeCIPOccurrenceDescriptorComparatorLaws.cursor_children_eq_nil_of_terminal
          mol cursor terminal
      let padding := paddingCursor mol cursor
      refine ⟨List.replicate RawMolecule.authoritativeChildSlots padding, ?_, by simp, ?_⟩
      · simp [rankedCursorChildrenAuthoritative?, childrenNil, padding, paddingCursor,
          sortCursorsBy?]
      · intro child member
        have : child = padding := List.eq_of_mem_replicate member
        subst child
        exact paddingCursor_support mol fuel cursor
  | branch _ _ children childrenEq width childrenSupport =>
      rcases
          ProductionCIPRerootComparatorLaws.sortCursorsBy?_exists_of_supported before
            (CursorSupport mol fuel) beforeTotal children childrenSupport with
        ⟨sorted, sortedEq, sortedSupport, sortedLength⟩
      let padding := paddingCursor mol cursor
      let ranked := sorted ++ List.replicate
        (RawMolecule.authoritativeChildSlots - sorted.length) padding
      have notTooWide : ¬ RawMolecule.authoritativeChildSlots < children.length :=
        Nat.not_lt_of_ge width
      refine ⟨ranked, ?_, ?_, ?_⟩
      · simp [rankedCursorChildrenAuthoritative?, childrenEq, notTooWide, sortedEq, ranked,
          padding, paddingCursor]
      · simp [ranked, sortedLength]
        omega
      · intro child member
        rcases List.mem_append.mp member with sortedMember | paddingMember
        · exact sortedSupport child sortedMember
        · have : child = padding := List.eq_of_mem_replicate paddingMember
          subst child
          exact paddingCursor_support mol fuel cursor

abbrev CursorPair := CanonicalRerootCursor × CanonicalRerootCursor

/-- A complete paired frontier with no cardinality budget. -/
def FrontierSupport (mol : RawMolecule) (fuel : Nat) (pairs : List CursorPair) : Prop :=
  ∀ pair, pair ∈ pairs → CursorSupport mol fuel pair.1 ∧ CursorSupport mol fuel pair.2

/-- At depth zero every supported pair is terminal, so the authoritative next frontier is empty. -/
theorem nextOccurrenceDescriptorPairsAuthoritative?_zero_eq_nil (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    ∀ pairs, FrontierSupport mol 0 pairs →
      nextOccurrenceDescriptorPairsAuthoritative? mol beforeLeft beforeRight pairs = some []
  | [], _ => rfl
  | pair :: pairs, support => by
      have head := support pair (by simp)
      have tail : FrontierSupport mol 0 pairs := by
        intro candidate member
        exact support candidate (by simp [member])
      have tailEq := nextOccurrenceDescriptorPairsAuthoritative?_zero_eq_nil mol beforeLeft
        beforeRight pairs tail
      simp [nextOccurrenceDescriptorPairsAuthoritative?, head.1.zero_terminal,
        head.2.zero_terminal, tailEq]

/-- One authoritative frontier expansion succeeds and lowers recursive support, without producing
or consuming any global width certificate. -/
theorem nextOccurrenceDescriptorPairsAuthoritative?_exists_of_support (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : Nat)
    (beforeLeftTotal : ∀ left right,
      CursorSupport mol fuel left → CursorSupport mol fuel right →
      ∃ ordering, beforeLeft left right = some ordering)
    (beforeRightTotal : ∀ left right,
      CursorSupport mol fuel left → CursorSupport mol fuel right →
      ∃ ordering, beforeRight left right = some ordering) :
    ∀ pairs, FrontierSupport mol (fuel + 1) pairs →
      ∃ next,
        nextOccurrenceDescriptorPairsAuthoritative? mol beforeLeft beforeRight pairs = some next ∧
        FrontierSupport mol fuel next
  | [], _ => ⟨[], rfl, by simp [FrontierSupport]⟩
  | pair :: pairs, support => by
      have head := support pair (by simp)
      have tail : FrontierSupport mol (fuel + 1) pairs := by
        intro candidate member
        exact support candidate (by simp [member])
      rcases nextOccurrenceDescriptorPairsAuthoritative?_exists_of_support mol beforeLeft
          beforeRight fuel beforeLeftTotal beforeRightTotal pairs tail with
        ⟨rest, restEq, restSupport⟩
      by_cases bothTerminal :
          cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true
      · exact ⟨rest, by simp [nextOccurrenceDescriptorPairsAuthoritative?, restEq, bothTerminal],
          restSupport⟩
      · rcases rankedCursorChildrenAuthoritative?_exists_of_support mol beforeLeft fuel pair.1
            head.1 beforeLeftTotal with ⟨left, leftEq, leftLength, leftSupport⟩
        rcases rankedCursorChildrenAuthoritative?_exists_of_support mol beforeRight fuel pair.2
            head.2 beforeRightTotal with ⟨right, rightEq, rightLength, rightSupport⟩
        refine ⟨left.zip right ++ rest, ?_, ?_⟩
        · simp [nextOccurrenceDescriptorPairsAuthoritative?, restEq, bothTerminal, leftEq,
            rightEq]
        · intro candidate member
          rcases List.mem_append.mp member with zipped | tailMember
          · have components := List.of_mem_zip zipped
            exact ⟨leftSupport candidate.1 components.1,
              rightSupport candidate.2 components.2⟩
          · exact restSupport candidate tailMember

/-- The width-unbounded Rule-6 sphere traversal terminates on every recursively supported finite
frontier.  Unlike the bounded theorem, there is no arithmetic envelope and no frontier length in
the statement. -/
theorem compareOccurrenceRule6Authoritative_exists (mol : RawMolecule)
    (rankFuel : Nat)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeTotal : ∀ left right,
      CursorSupport mol rankFuel left → CursorSupport mol rankFuel right →
      ∃ ordering, before left right = some ordering)
    (reference : Nat) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 → FrontierSupport mol fuel pairs →
      ∃ ordering,
        compareOccurrenceRule6Authoritative mol before reference fuel pairs = some ordering
  | 0, pairs, _, support => by
      cases labels : compareOccurrenceRule6PairLabels reference pairs with
      | lt => exact ⟨.lt, by simp [compareOccurrenceRule6Authoritative, labels]⟩
      | gt => exact ⟨.gt, by simp [compareOccurrenceRule6Authoritative, labels]⟩
      | eq =>
          have nextEq := nextOccurrenceDescriptorPairsAuthoritative?_zero_eq_nil mol before
            before pairs support
          exact ⟨.eq, by simp [compareOccurrenceRule6Authoritative, labels, nextEq]⟩
  | fuel + 1, pairs, fuelLe, support => by
      have lowerLe : fuel ≤ rankFuel := by omega
      have localTotal : ∀ left right,
          CursorSupport mol fuel left → CursorSupport mol fuel right →
          ∃ ordering, before left right = some ordering := by
        intro left right leftSupport rightSupport
        exact beforeTotal left right (leftSupport.mono lowerLe) (rightSupport.mono lowerLe)
      cases labels : compareOccurrenceRule6PairLabels reference pairs with
      | lt => exact ⟨.lt, by simp [compareOccurrenceRule6Authoritative, labels]⟩
      | gt => exact ⟨.gt, by simp [compareOccurrenceRule6Authoritative, labels]⟩
      | eq =>
          rcases nextOccurrenceDescriptorPairsAuthoritative?_exists_of_support mol before before
              fuel localTotal localTotal pairs support with ⟨next, nextEq, nextSupport⟩
          cases next with
          | nil =>
              exact ⟨.eq, by simp [compareOccurrenceRule6Authoritative, labels, nextEq]⟩
          | cons pair rest =>
              rcases compareOccurrenceRule6Authoritative_exists mol rankFuel before beforeTotal
                  reference fuel (pair :: rest) (by omega) nextSupport with
                ⟨decision, decisionEq⟩
              exact ⟨decision, by
                simp [compareOccurrenceRule6Authoritative, labels, nextEq, decisionEq]⟩

/-- All structurally supported promoted comparisons terminate once the strictly earlier
width-unbounded Rules-1--5 comparator is total on the same recursive shapes.  This isolates the
remaining ordinary-stage chemistry obligation without reintroducing a global size bound. -/
theorem compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_exists
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (maxFuel : Nat)
    (ordinaryTotal : ∀ depth, depth ≤ maxFuel → ∀ left right,
      CursorSupport mol depth left → CursorSupport mol depth right →
      ∃ comparison,
        compareOccurrenceBranchesUnrestrictedAuthoritative? mol state depth left right =
          some comparison)
    (reference : Nat) : ∀ depth, depth ≤ maxFuel → ∀ left right,
      CursorSupport mol depth left → CursorSupport mol depth right →
      ∃ decision,
        compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference depth
          left right = some decision
  | 0, _, left, right, leftSupport, rightSupport => by
      rcases ordinaryTotal 0 (by omega) left right leftSupport rightSupport with ⟨prior, priorEq⟩
      cases priorOrdering : prior.ordering with
      | lt =>
          exact ⟨{ ordering := .lt, pseudo := false }, by
            simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq,
              priorOrdering]⟩
      | gt =>
          exact ⟨{ ordering := .gt, pseudo := false }, by
            simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq,
              priorOrdering]⟩
      | eq =>
          let ordering := compare
            (if left.node.atom == reference then 1 else 0)
            (if right.node.atom == reference then 1 else 0)
          exact ⟨{ ordering := ordering, pseudo := ordering != Ordering.eq }, by
            simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq,
              priorOrdering, ordering]⟩
  | depth + 1, depthLe, left, right, leftSupport, rightSupport => by
      rcases ordinaryTotal (depth + 1) depthLe left right leftSupport rightSupport with
        ⟨prior, priorEq⟩
      cases priorOrdering : prior.ordering with
      | lt =>
          exact ⟨{ ordering := .lt, pseudo := false }, by
            simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq,
              priorOrdering]⟩
      | gt =>
          exact ⟨{ ordering := .gt, pseudo := false }, by
            simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq,
              priorOrdering]⟩
      | eq =>
          let before := fun a b =>
            (compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference
              depth a b).map Rule6TrackedDecision.ordering
          have beforeTotal : ∀ childLeft childRight,
              CursorSupport mol depth childLeft → CursorSupport mol depth childRight →
              ∃ ordering, before childLeft childRight = some ordering := by
            intro childLeft childRight childLeftSupport childRightSupport
            rcases compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_exists mol
                state maxFuel ordinaryTotal reference depth (by omega) childLeft childRight
                childLeftSupport childRightSupport with ⟨decision, decisionEq⟩
            exact ⟨decision.ordering, by simp [before, decisionEq]⟩
          have frontier : FrontierSupport mol (depth + 1) [(left, right)] := by
            intro pair member
            have pairEq : pair = (left, right) := by simpa using member
            subst pair
            exact ⟨leftSupport, rightSupport⟩
          rcases compareOccurrenceRule6Authoritative_exists mol depth before beforeTotal reference
              (depth + 1) [(left, right)] (by omega) frontier with ⟨ordering, orderingEq⟩
          exact ⟨{ ordering := ordering, pseudo := ordering != Ordering.eq }, by
            simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq,
              priorOrdering, before, orderingEq]⟩

end TetraStereo.OneCenter.AuthoritativeCIPRule6Completeness
