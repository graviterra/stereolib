import TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeSecondSphereComparisonBridge

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery

/-!
Production bridges for a strict Rule-1a difference in the first expanded sphere.

Each application supplies the actual child sort at the recursive callback fuel, real equal-Z
roots, and exact local node comparisons along a tied prefix ending at a strict pair. Child
nodes need not be real: a multiple-bond duplicate must be justified using its actual labeler.
The bridge derives the raw branch result, including production padding. It does not establish
the symmetry guard, certified/public dispatch, source agreement, or a chemical family domain.
-/

/-- Local label observations up to a decisive pair. The comparator is instantiated below with
the production Rule-1a node comparator, never with the desired branch comparison. -/
inductive DecisivePrefix
    (label : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (decision : Ordering) : List (CanonicalRerootCursor × CanonicalRerootCursor) → Prop
  | head (left right : CanonicalRerootCursor)
      (tail : List (CanonicalRerootCursor × CanonicalRerootCursor))
      (observed : label left right = some decision) :
      DecisivePrefix label decision ((left, right) :: tail)
  | tie (left right : CanonicalRerootCursor)
      (tail : List (CanonicalRerootCursor × CanonicalRerootCursor))
      (observed : label left right = some .eq)
      (later : DecisivePrefix label decision tail) :
      DecisivePrefix label decision ((left, right) :: tail)

/-- Two authoritative phantom slots follow three actual children. -/
def paddingCursor (mol : RawMolecule) (cursor : CanonicalRerootCursor) :
    CanonicalRerootCursor :=
  { node := mol.canonicalPhantom cursor.node.atom (cursor.node.rule1bRootDistance + 1) }

theorem ranked_fast_of_sort_three (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (cursor a b c : CanonicalRerootCursor)
    (count : (cursor.children mol).length = 3)
    (sorted : sortCursorsBy? before (cursor.children mol) = some [a, b, c]) :
    rankedCursorChildren? mol before cursor = some [a, b, c] := by
  simp [rankedCursorChildren?, count, sorted]

theorem ranked_authoritative_of_sort_three (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (cursor a b c : CanonicalRerootCursor)
    (count : (cursor.children mol).length = 3)
    (sorted : sortCursorsBy? before (cursor.children mol) = some [a, b, c]) :
    rankedCursorChildrenAuthoritative? mol before cursor =
      some ([a, b, c] ++ List.replicate 2 (paddingCursor mol cursor)) := by
  simp [rankedCursorChildrenAuthoritative?, count, sorted, authoritativeChildSlots,
    paddingCursor]

/-- Trailing child pairs and phantom padding cannot alter a prior strict local decision. -/
theorem labels_fast_of_prefix (mol : RawMolecule) (decision : Ordering)
    (pairs rest : List (CanonicalRerootCursor × CanonicalRerootCursor))
    (decisive : DecisivePrefix
      (fun left right => mol.compareCanonicalNodeRule? .rule1a left.node right.node)
      decision pairs)
    (strict : decision ≠ .eq) :
    compareCursorPairLabels mol .rule1a (pairs ++ rest) = some decision := by
  induction decisive with
  | head left right tail observed =>
      cases decision with
      | eq => exact (strict rfl).elim
      | lt => simp only [List.cons_append, compareCursorPairLabels, observed]
      | gt => simp only [List.cons_append, compareCursorPairLabels, observed]
  | tie left right tail observed later ih =>
      simpa only [List.cons_append, compareCursorPairLabels, observed] using ih

theorem labels_authoritative_of_prefix (mol : RawMolecule) (decision : Ordering)
    (pairs rest : List (CanonicalRerootCursor × CanonicalRerootCursor))
    (decisive : DecisivePrefix
      (fun left right => mol.compareCanonicalNodeRuleAuthoritative? .rule1a left.node right.node)
      decision pairs)
    (strict : decision ≠ .eq) :
    compareCursorPairLabelsAuthoritative? mol .rule1a (pairs ++ rest) = some decision := by
  induction decisive with
  | head left right tail observed =>
      cases decision with
      | eq => exact (strict rfl).elim
      | lt => simp only [List.cons_append, compareCursorPairLabelsAuthoritative?, observed]
      | gt => simp only [List.cons_append, compareCursorPairLabelsAuthoritative?, observed]
  | tie left right tail observed later ih =>
      simpa only [List.cons_append, compareCursorPairLabelsAuthoritative?, observed] using ih

/-- The width-capped production comparator reaches the decisive child pair at every positive
fuel. All ranking premises use its actual recursive callback at the predecessor fuel. -/
theorem fast_raw_of_ranked_three (mol : RawMolecule) (fuel : Nat)
    (stage : CanonicalRuleStage) (left right l₁ l₂ l₃ r₁ r₂ r₃ : CanonicalRerootCursor)
    (decision : Ordering)
    (leftReal : left.node.provenance = .realAtom)
    (rightReal : right.node.provenance = .realAtom)
    (sameZ : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom)
    (leftNonterminal : cursorTerminal mol left = false)
    (rightNonterminal : cursorTerminal mol right = false)
    (rankedLeft : rankedCursorChildren? mol (compareCursorBranchAt mol fuel stage) left =
      some [l₁, l₂, l₃])
    (rankedRight : rankedCursorChildren? mol (compareCursorBranchAt mol fuel stage) right =
      some [r₁, r₂, r₃])
    (decisive : DecisivePrefix
      (fun a b => mol.compareCanonicalNodeRule? .rule1a a.node b.node)
      decision [(l₁, r₁), (l₂, r₂), (l₃, r₃)])
    (strict : decision ≠ .eq) :
    compareCursorBranchAt mol (fuel + 1) stage left right = some decision := by
  have rootTie := compareCanonicalNodeRule?_rule1a_realAtom mol
    left.node right.node leftReal rightReal
  rw [sameZ] at rootTie
  have rootLabels : compareCursorPairLabels mol .rule1a [(left, right)] = some .eq := by
    simp [compareCursorPairLabels, rootTie]
  let pairs := [(l₁, r₁), (l₂, r₂), (l₃, r₃)]
  have expanded : nextCursorPairs? mol (compareCursorBranchAt mol fuel stage)
      [(left, right)] = some pairs := by
    simp [nextCursorPairs?, leftNonterminal, rightNonterminal, rankedLeft, rankedRight,
      pairs, List.zip_cons_cons]
  have labels : compareCursorPairLabels mol .rule1a pairs = some decision := by
    simpa only [List.append_nil] using
      labels_fast_of_prefix mol decision pairs [] decisive strict
  have width : ¬ defaultBranchWidthCap < pairs.length := by
    simp [defaultBranchWidthCap, pairs]
  have second (depth : Nat) :
      compareCursorRule mol (compareCursorBranchAt mol fuel stage) .rule1a depth pairs =
        some decision := by
    cases decision with
    | eq => exact (strict rfl).elim
    | lt => cases depth <;> simp only [compareCursorRule, width, labels, ↓reduceIte]
    | gt => cases depth <;> simp only [compareCursorRule, width, labels, ↓reduceIte]
  have first : compareCursorRule mol (compareCursorBranchAt mol fuel stage) .rule1a
      (fuel + 1) [(left, right)] = some decision := by
    simp only [compareCursorRule]
    simp [rootLabels, expanded, second, defaultBranchWidthCap, pairs]
  cases decision with
  | eq => exact (strict rfl).elim
  | lt => simp only [compareCursorBranchAt, first]
  | gt => simp only [compareCursorBranchAt, first]

/-- The authoritative production comparator retains its two phantom slots. The decisive prefix
is among the three actual children, so no label or ordering premise concerns those phantoms. -/
theorem authoritative_raw_of_ranked_three (mol : RawMolecule) (fuel : Nat)
    (stage : CanonicalRuleStage) (left right l₁ l₂ l₃ r₁ r₂ r₃ : CanonicalRerootCursor)
    (decision : Ordering)
    (leftReal : left.node.provenance = .realAtom)
    (rightReal : right.node.provenance = .realAtom)
    (sameZ : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom)
    (leftNonterminal : cursorTerminal mol left = false)
    (rightNonterminal : cursorTerminal mol right = false)
    (rankedLeft : rankedCursorChildrenAuthoritative? mol
      (compareCursorBranchAtAuthoritative? mol fuel stage) left =
      some ([l₁, l₂, l₃] ++ List.replicate 2 (paddingCursor mol left)))
    (rankedRight : rankedCursorChildrenAuthoritative? mol
      (compareCursorBranchAtAuthoritative? mol fuel stage) right =
      some ([r₁, r₂, r₃] ++ List.replicate 2 (paddingCursor mol right)))
    (decisive : DecisivePrefix
      (fun a b => mol.compareCanonicalNodeRuleAuthoritative? .rule1a a.node b.node)
      decision [(l₁, r₁), (l₂, r₂), (l₃, r₃)])
    (strict : decision ≠ .eq) :
    compareCursorBranchAtAuthoritative? mol (fuel + 1) stage left right = some decision := by
  have rootTie := compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom mol
    left.node right.node leftReal rightReal
  rw [sameZ] at rootTie
  have rootLabels : compareCursorPairLabelsAuthoritative? mol .rule1a [(left, right)] =
      some .eq := by
    simp [compareCursorPairLabelsAuthoritative?, rootTie]
  let pairs := [(l₁, r₁), (l₂, r₂), (l₃, r₃)] ++
    List.replicate 2 (paddingCursor mol left, paddingCursor mol right)
  have expanded : nextCursorPairsAuthoritative? mol
      (compareCursorBranchAtAuthoritative? mol fuel stage) [(left, right)] = some pairs := by
    simp [nextCursorPairsAuthoritative?, leftNonterminal, rightNonterminal, rankedLeft,
      rankedRight, pairs, List.replicate_succ, List.replicate_zero]
  have labels : compareCursorPairLabelsAuthoritative? mol .rule1a pairs = some decision := by
    exact labels_authoritative_of_prefix mol decision _ _ decisive strict
  have second (depth : Nat) : compareCursorRuleAuthoritative? mol
      (compareCursorBranchAtAuthoritative? mol fuel stage) .rule1a depth pairs =
        some decision := by
    cases decision with
    | eq => exact (strict rfl).elim
    | lt => cases depth <;> simp only [compareCursorRuleAuthoritative?, labels]
    | gt => cases depth <;> simp only [compareCursorRuleAuthoritative?, labels]
  have first : compareCursorRuleAuthoritative? mol
      (compareCursorBranchAtAuthoritative? mol fuel stage) .rule1a
      (fuel + 1) [(left, right)] = some decision := by
    simp only [compareCursorRuleAuthoritative?, rootLabels, expanded]
    exact second fuel
  cases decision with
  | eq => exact (strict rfl).elim
  | lt => simp only [compareCursorBranchAtAuthoritative?, first]
  | gt => simp only [compareCursorBranchAtAuthoritative?, first]

end TetraStereo.UniversalProof.NativeSecondSphereComparisonBridge
