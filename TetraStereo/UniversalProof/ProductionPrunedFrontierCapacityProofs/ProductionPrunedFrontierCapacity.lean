import TetraStereo.OneCenter.ProductionCIPBranchingOccurrenceComparatorCompleteness
import TetraStereo.OneCenter.ProductionCIPBranchingSupportReflection
import TetraStereo.UniversalProof.ProductionPrunedFrontierCapacityProofs.ProductionMoleculeBranchingRanking

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ProductionPrunedFrontierCapacityProofs



























































open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.ProductionCIPRerootComparatorLaws
open TetraStereo.OneCenter.ProductionCIPBranchingOccurrenceComparatorCompleteness
open TetraStereo.OneCenter.ProductionCIPLinearOccurrenceComparatorCompleteness
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking

noncomputable section

/-! ## The structural capacity measure -/

/-- Recursive *expansion mass* of a reroot cursor.  Zero at fuel `0`; at a successor fuel it is `0`
at a terminal cursor and otherwise `3 + Σ` of the children masses.  Unlike `3 ^ fuel`, this measure
stays linear on a deep but narrow tree because a spine has a single non-padding child per level. -/
def cursorExpansionMass (mol : RawMolecule) : ℕ → CanonicalRerootCursor → ℕ
  | 0, _ => 0
  | fuel + 1, cursor =>
      if cursorTerminal mol cursor then 0
      else 3 + ((cursor.children mol).map (cursorExpansionMass mol fuel)).sum

/-- Potential of a single pawned frontier pair: `1 + massLeft + massRight`. -/
def pairPotential (mol : RawMolecule) (fuel : ℕ)
    (pair : CanonicalRerootCursor × CanonicalRerootCursor) : ℕ :=
  1 + cursorExpansionMass mol fuel pair.1 + cursorExpansionMass mol fuel pair.2

/-- Sum of pair potentials over a frontier.  This is the quantity kept below `defaultBranchWidthCap`
in place of `length * 3 ^ fuel`. -/
def frontierPotential (mol : RawMolecule) (fuel : ℕ)
    (pairs : List (CanonicalRerootCursor × CanonicalRerootCursor)) : ℕ :=
  (pairs.map (pairPotential mol fuel)).sum

/-- Per-cursor capacity: `1 + 2 * mass ≤ cap`.  This one-level-closed bound is what a sibling
callback needs. It defines an additional sufficient domain incomparable with the global ternary
envelope; neither sufficient domain contains the other. -/
def cursorCapacity (mol : RawMolecule) (fuel : ℕ) (cursor : CanonicalRerootCursor) : Prop :=
  1 + 2 * cursorExpansionMass mol fuel cursor ≤ RawMolecule.defaultBranchWidthCap

/-- A frontier carrying both recursive support and the structural capacity bound. -/
def CapacityFrontierSupport (mol : RawMolecule) (fuel : ℕ)
    (pairs : List (CanonicalRerootCursor × CanonicalRerootCursor)) : Prop :=
  (∀ pair, pair ∈ pairs →
      BranchingCursorSupport mol fuel pair.1 ∧ BranchingCursorSupport mol fuel pair.2) ∧
    frontierPotential mol fuel pairs ≤ RawMolecule.defaultBranchWidthCap

/-! ## Basic mass arithmetic -/

@[simp] theorem cursorExpansionMass_zero (mol : RawMolecule)
    (cursor : CanonicalRerootCursor) : cursorExpansionMass mol 0 cursor = 0 := rfl

theorem cursorExpansionMass_succ_of_terminal (mol : RawMolecule) (fuel : ℕ)
    (cursor : CanonicalRerootCursor) (terminal : cursorTerminal mol cursor = true) :
    cursorExpansionMass mol (fuel + 1) cursor = 0 := by
  simp [cursorExpansionMass, terminal]

theorem cursorExpansionMass_succ_of_not_terminal (mol : RawMolecule) (fuel : ℕ)
    (cursor : CanonicalRerootCursor) (notTerminal : cursorTerminal mol cursor = false) :
    cursorExpansionMass mol (fuel + 1) cursor =
      3 + ((cursor.children mol).map (cursorExpansionMass mol fuel)).sum := by
  simp [cursorExpansionMass, notTerminal]

/-- A terminal cursor has zero mass at every fuel. -/
theorem cursorExpansionMass_eq_zero_of_terminal (mol : RawMolecule) :
    ∀ (fuel : ℕ) (cursor : CanonicalRerootCursor), cursorTerminal mol cursor = true →
      cursorExpansionMass mol fuel cursor = 0
  | 0, _, _ => rfl
  | fuel + 1, _, terminal => cursorExpansionMass_succ_of_terminal mol fuel _ terminal

/-- The padding cursor `{ node := canonicalPhantom parent distance }` is a forced leaf, hence has
zero expansion mass at every fuel. -/
@[simp] theorem cursorExpansionMass_phantom (mol : RawMolecule) (fuel parent distance : ℕ) :
    cursorExpansionMass mol fuel
      ({ node := mol.canonicalPhantom parent distance } : CanonicalRerootCursor) = 0 :=
  cursorExpansionMass_eq_zero_of_terminal mol fuel _
    (by simp [cursorTerminal, CanonicalRerootCursor.children, RawMolecule.canonicalPhantom,
      CanonicalBranchNode.forcedLeaf])

/-- A monote list-sum bound: pointwise `≤` lifts to `≤` of sums.  Reused as the induction engine for
the mass monotonicity of `cursorExpansionMass`. -/
theorem list_sum_map_mono {α : Type*} (values : List α) (f g : α → ℕ)
    (le : ∀ value, value ∈ values → f value ≤ g value) :
    (values.map f).sum ≤ (values.map g).sum := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (le head (by simp))
        (ih (fun value member => le value (by simp [member])))

/-- The expansion mass is monotone in the fuel. -/
theorem cursorExpansionMass_le_succ (mol : RawMolecule) :
    ∀ (fuel : ℕ) (cursor : CanonicalRerootCursor),
      cursorExpansionMass mol fuel cursor ≤ cursorExpansionMass mol (fuel + 1) cursor
  | 0, cursor => by simp [cursorExpansionMass]
  | fuel + 1, cursor => by
      by_cases terminal : cursorTerminal mol cursor = true
      · rw [cursorExpansionMass_succ_of_terminal mol fuel cursor terminal,
            cursorExpansionMass_succ_of_terminal mol (fuel + 1) cursor terminal]
      · have notTerminal : cursorTerminal mol cursor = false :=
          Bool.eq_false_of_not_eq_true terminal
        rw [cursorExpansionMass_succ_of_not_terminal mol fuel cursor notTerminal,
          cursorExpansionMass_succ_of_not_terminal mol (fuel + 1) cursor notTerminal]
        have children := list_sum_map_mono (cursor.children mol)
          (cursorExpansionMass mol fuel) (cursorExpansionMass mol (fuel + 1))
          (fun child _ => cursorExpansionMass_le_succ mol fuel child)
        omega

/-- A cursor's mass is monotone in the fuel across any `≤`. -/
theorem cursorExpansionMass_mono (mol : RawMolecule) (cursor : CanonicalRerootCursor)
    {smaller larger : ℕ} (le : smaller ≤ larger) :
    cursorExpansionMass mol smaller cursor ≤ cursorExpansionMass mol larger cursor := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  clear le
  induction extra with
  | zero => simp
  | succ extra ih =>
      exact le_trans ih (by
        simpa [Nat.add_assoc] using cursorExpansionMass_le_succ mol (smaller + extra) cursor)

/-- A frontier pair with support represents at least one slot, so `length ≤ potential`. -/
theorem list_length_le_frontierPotential (mol : RawMolecule) (fuel : ℕ) :
    ∀ pairs : List (CanonicalRerootCursor × CanonicalRerootCursor),
      pairs.length ≤ frontierPotential mol fuel pairs := by
  intro pairs
  induction pairs with
  | nil => simp [frontierPotential]
  | cons head tail ih =>
      simp only [List.length_cons, frontierPotential, List.map_cons, List.sum_cons] at ih ⊢
      have : 1 ≤ pairPotential mol fuel head := by
        simp only [pairPotential]
        omega
      omega

/-! ## Sorting and padding preserve or bound the mass

The production child ranking `rankedCursorChildren?` (a) discards nothing, and (b) pads to three
slots with a forced-leaf phantom cursor of zero mass.  We record the two consequences the capacity
argument needs: `rankedCursorChildren?` is a permutation-weight-preserving reordering of
`cursor.children` (so the mass sum is preserved), and it contributes exactly the ternary arity. -/

theorem list_perm_sum_map_eq {α : Type*} (f : α → ℕ) {left right : List α}
    (perm : left.Perm right) : (left.map f).sum = (right.map f).sum := by
  induction perm with
  | nil => rfl
  | cons value _ ih => simp [ih]
  | swap first second tail => simp only [List.map_cons, List.sum_cons]; omega
  | trans _ _ ihLeft ihRight => exact ihLeft.trans ihRight

/-- Insertion into a ranked list returns a permutation of the extended input. -/
theorem insertCursorBy?_perm
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (candidate : CanonicalRerootCursor) :
    ∀ (input output : List CanonicalRerootCursor),
      insertCursorBy? before candidate input = some output → output.Perm (candidate :: input)
  | [], output, computed => by
      simp [insertCursorBy?] at computed
      subst output
      exact List.Perm.refl _
  | head :: tail, output, computed => by
      cases ordering : before candidate head with
      | none => simp [insertCursorBy?, ordering] at computed
      | some decision =>
          cases decision with
          | lt =>
              cases inner : insertCursorBy? before candidate tail with
              | none => simp [insertCursorBy?, ordering, inner] at computed
              | some deeper =>
                  have hinner : insertCursorBy? before candidate (head :: tail) =
                      some (head :: deeper) := by
                    simp [insertCursorBy?, ordering, inner]
                  rw [hinner] at computed
                  have hout : output = head :: deeper :=
                    (Option.some.inj computed).symm
                  rw [hout]
                  exact ((insertCursorBy?_perm before candidate tail deeper inner).cons head).trans
                    (List.Perm.swap head candidate tail).symm
          | eq =>
              have hinner : insertCursorBy? before candidate (head :: tail) =
                  some (candidate :: head :: tail) := by
                simp [insertCursorBy?, ordering]
              rw [hinner] at computed
              have hout : output = candidate :: head :: tail :=
                (Option.some.inj computed).symm
              rw [hout]
          | gt =>
              have hinner : insertCursorBy? before candidate (head :: tail) =
                  some (candidate :: head :: tail) := by
                simp [insertCursorBy?, ordering]
              rw [hinner] at computed
              have hout : output = candidate :: head :: tail :=
                (Option.some.inj computed).symm
              rw [hout]

/-- Insertion sort returns a permutation of its input. -/
theorem sortCursorsBy?_perm
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    ∀ (input output : List CanonicalRerootCursor),
      sortCursorsBy? before input = some output → output.Perm input
  | [], output, computed => by
      simp [sortCursorsBy?] at computed
      subst output
      exact List.Perm.refl _
  | node :: nodes, output, computed => by
      cases tailEq : sortCursorsBy? before nodes with
      | none => simp [sortCursorsBy?, tailEq] at computed
      | some sorted =>
          have inner : insertCursorBy? before node sorted = some output := by
            simpa [sortCursorsBy?, tailEq] using computed
          exact (insertCursorBy?_perm before node sorted output inner).trans
            (List.Perm.cons node (sortCursorsBy?_perm before nodes sorted tailEq))

/-- The exact normal form of a successful `rankedCursorChildren?` computation. -/
theorem rankedCursorChildren?_eq_some (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (cursor : CanonicalRerootCursor) (sorted : List CanonicalRerootCursor)
    (small : ¬ 3 < (cursor.children mol).length)
    (sortedEq : sortCursorsBy? before (cursor.children mol) = some sorted) :
    rankedCursorChildren? mol before cursor =
      some (sorted ++ List.replicate (3 - sorted.length)
        ({ node := mol.canonicalPhantom cursor.node.atom
            (cursor.node.rule1bRootDistance + 1) } : CanonicalRerootCursor)) := by
  simp [rankedCursorChildren?, sortedEq, small]

/-- A successful child ranking always returns exactly three slots. -/
theorem rankedCursorChildren?_length (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : ℕ) (cursor : CanonicalRerootCursor) (ranked : List CanonicalRerootCursor)
    (support : BranchingCursorSupport mol (fuel + 1) cursor)
    (beforeTotal : ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, before left right = some ordering)
    (computed : rankedCursorChildren? mol before cursor = some ranked) :
    ranked.length = 3 := by
  rcases rankedCursorChildren?_exists_of_branching_support mol before fuel cursor support
      beforeTotal with ⟨other, otherEq, otherLength, _⟩
  rw [computed] at otherEq
  have hEq : ranked = other := Option.some.inj otherEq
  rw [hEq]
  exact otherLength

/-- The ranked children are a permutation-weight-preserving reordering of the real children: their
mass sum equals the mass sum of `cursor.children`.  Padding contributes nothing because the phantom
cursor is a forced leaf. -/
theorem rankedCursorChildren?_mass_sum (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : ℕ) (cursor : CanonicalRerootCursor) (ranked : List CanonicalRerootCursor)
    (computed : rankedCursorChildren? mol before cursor = some ranked) :
    (ranked.map (cursorExpansionMass mol fuel)).sum
      = ((cursor.children mol).map (cursorExpansionMass mol fuel)).sum := by
  by_cases wide : 3 < (cursor.children mol).length
  · simp [rankedCursorChildren?, wide] at computed
  · cases sortedEq : sortCursorsBy? before (cursor.children mol) with
    | none => simp [rankedCursorChildren?, wide, sortedEq] at computed
    | some sorted =>
        have hsome := rankedCursorChildren?_eq_some mol before cursor sorted wide sortedEq
        rw [computed] at hsome
        have hranked : ranked = sorted ++ List.replicate (3 - sorted.length)
            ({ node := mol.canonicalPhantom cursor.node.atom
                (cursor.node.rule1bRootDistance + 1) } : CanonicalRerootCursor) :=
          Option.some.inj hsome
        rw [hranked, List.map_append, List.sum_append]
        have hperm : sorted.Perm (cursor.children mol) :=
          sortCursorsBy?_perm before (cursor.children mol) sorted sortedEq
        have hsum : (sorted.map (cursorExpansionMass mol fuel)).sum
            = ((cursor.children mol).map (cursorExpansionMass mol fuel)).sum :=
          list_perm_sum_map_eq (cursorExpansionMass mol fuel) hperm
        have hpad : ((List.replicate (3 - sorted.length)
            ({ node := mol.canonicalPhantom cursor.node.atom
                (cursor.node.rule1bRootDistance + 1) } : CanonicalRerootCursor)).map
              (cursorExpansionMass mol fuel)).sum = 0 := by
          simp [List.map_replicate, List.sum_replicate, cursorExpansionMass_phantom]
        rw [hsum, hpad, Nat.add_zero]

/-- The ranked children realise exactly the successor mass: the padded ternary arity replaces the
`3` of the definition.  At a terminal cursor both sides vanish. -/
theorem rankedCursorChildren?_mass_sum_add (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : ℕ) (cursor : CanonicalRerootCursor) (ranked : List CanonicalRerootCursor)
    (computed : rankedCursorChildren? mol before cursor = some ranked) :
    (ranked.map (cursorExpansionMass mol fuel)).sum +
        (if cursorTerminal mol cursor then 0 else 3)
      = cursorExpansionMass mol (fuel + 1) cursor := by
  rw [rankedCursorChildren?_mass_sum mol before fuel cursor ranked computed]
  by_cases terminal : cursorTerminal mol cursor = true
  · have childrenNil := cursor_children_eq_nil_of_terminal mol cursor terminal
    rw [childrenNil, cursorExpansionMass_succ_of_terminal mol fuel cursor terminal]
    simp [terminal]
  · have notTerminal : cursorTerminal mol cursor = false := Bool.eq_false_of_not_eq_true terminal
    rw [cursorExpansionMass_succ_of_not_terminal mol fuel cursor notTerminal]
    simp [notTerminal]
    omega

/-- Potential of a zipped child frontier.  When both child lists have equal length, the pair
potential of the alignment is `length + Σ left masses + Σ right masses`. -/
theorem zip_pairPotential_sum (mol : RawMolecule) (fuel : ℕ) :
    ∀ (left right : List CanonicalRerootCursor), left.length = right.length →
      ((left.zip right).map (pairPotential mol fuel)).sum
        = left.length + (left.map (cursorExpansionMass mol fuel)).sum
            + (right.map (cursorExpansionMass mol fuel)).sum
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | leftHead :: leftTail, rightHead :: rightTail, h => by
      simp only [List.length_cons] at h
      have hTail : leftTail.length = rightTail.length := by omega
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons]
      rw [zip_pairPotential_sum mol fuel leftTail rightTail hTail]
      simp only [pairPotential]
      omega

/-- One expansion of a non-terminal pair does not increase the potential: the zipped child
frontier's potential is bounded by the parent pair's successor potential.  The mixed terminal/
branching cases are what makes the bound true without any ternary envelope. -/
theorem rankedChildren_zip_potential_le (mol : RawMolecule)
    (beforeLeft beforeRight : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : ℕ) (left right : CanonicalRerootCursor)
    (leftKids rightKids : List CanonicalRerootCursor)
    (leftEq : rankedCursorChildren? mol beforeLeft left = some leftKids)
    (rightEq : rankedCursorChildren? mol beforeRight right = some rightKids)
    (leftLen : leftKids.length = 3) (rightLen : rightKids.length = 3)
    (notBothTerminal : ¬ (cursorTerminal mol left = true ∧ cursorTerminal mol right = true)) :
    ((leftKids.zip rightKids).map (pairPotential mol fuel)).sum
      ≤ pairPotential mol (fuel + 1) (left, right) := by
  rw [zip_pairPotential_sum mol fuel leftKids rightKids (by rw [leftLen, rightLen])]
  rw [leftLen]
  have leftMass := rankedCursorChildren?_mass_sum_add mol beforeLeft fuel left leftKids leftEq
  have rightMass := rankedCursorChildren?_mass_sum_add mol beforeRight fuel right rightKids rightEq
  by_cases leftTerminal : cursorTerminal mol left = true
  · by_cases rightTerminal : cursorTerminal mol right = true
    · exact absurd ⟨leftTerminal, rightTerminal⟩ notBothTerminal
    · have rightNot : cursorTerminal mol right = false :=
        Bool.eq_false_of_not_eq_true rightTerminal
      simp only [leftTerminal, rightNot, Bool.false_eq_true, ↓reduceIte] at leftMass rightMass
      simp only [pairPotential]
      omega
  · have leftNot : cursorTerminal mol left = false := Bool.eq_false_of_not_eq_true leftTerminal
    by_cases rightTerminal : cursorTerminal mol right = true
    · simp only [leftNot, rightTerminal, Bool.false_eq_true, ↓reduceIte] at leftMass rightMass
      simp only [pairPotential]
      omega
    · have rightNot : cursorTerminal mol right = false :=
        Bool.eq_false_of_not_eq_true rightTerminal
      simp only [leftNot, rightNot, Bool.false_eq_true, ↓reduceIte] at leftMass rightMass
      simp only [pairPotential]
      omega

@[simp] theorem frontierPotential_nil (mol : RawMolecule) (fuel : ℕ) :
    frontierPotential mol fuel [] = 0 := rfl

theorem frontierPotential_cons (mol : RawMolecule) (fuel : ℕ)
    (pair : CanonicalRerootCursor × CanonicalRerootCursor)
    (pairs : List (CanonicalRerootCursor × CanonicalRerootCursor)) :
    frontierPotential mol fuel (pair :: pairs)
      = pairPotential mol fuel pair + frontierPotential mol fuel pairs := by
  simp [frontierPotential]

theorem frontierPotential_append (mol : RawMolecule) (fuel : ℕ)
    (left right : List (CanonicalRerootCursor × CanonicalRerootCursor)) :
    frontierPotential mol fuel (left ++ right)
      = frontierPotential mol fuel left + frontierPotential mol fuel right := by
  simp [frontierPotential, List.map_append, List.sum_append]

/-! ## Label totality for one recursively supported sphere -/

/-- A single node-rule comparison exists on recursively supported cursors.  Rule 1a uses the label
carried by `BranchingCursorSupport`; rules 1b and 2 are total. -/
theorem compareCanonicalNodeRule?_exists_of_branching_support (mol : RawMolecule)
    (rule : CanonicalRuleStage) {fuel : ℕ} {left right : CanonicalRerootCursor}
    (leftSupport : BranchingCursorSupport mol fuel left)
    (rightSupport : BranchingCursorSupport mol fuel right) :
    ∃ ordering, mol.compareCanonicalNodeRule? rule left.node right.node = some ordering := by
  cases rule with
  | rule1a =>
      rcases leftSupport.label with ⟨leftLabel, leftEq⟩
      rcases rightSupport.label with ⟨rightLabel, rightEq⟩
      exact ⟨compareCIPAtomicLabel leftLabel rightLabel, by
        simp [RawMolecule.compareCanonicalNodeRule?, leftEq, rightEq]⟩
  | rule1b => exact ⟨_, rfl⟩
  | rule2 => exact ⟨_, rfl⟩

/-- The paired sphere labels are total on a recursively supported frontier. -/
theorem compareCursorPairLabels_exists_of_branching_support (mol : RawMolecule)
    (rule : CanonicalRuleStage) (fuel : ℕ) :
    ∀ pairs, (∀ pair, pair ∈ pairs →
        BranchingCursorSupport mol fuel pair.1 ∧ BranchingCursorSupport mol fuel pair.2) →
      ∃ ordering, compareCursorPairLabels mol rule pairs = some ordering
  | [], _ => ⟨.eq, rfl⟩
  | pair :: rest, support => by
      have head := support pair (by simp)
      rcases compareCanonicalNodeRule?_exists_of_branching_support mol rule head.1 head.2 with
        ⟨decision, decisionEq⟩
      cases decision with
      | lt => exact ⟨.lt, by simp [compareCursorPairLabels, decisionEq]⟩
      | gt => exact ⟨.gt, by simp [compareCursorPairLabels, decisionEq]⟩
      | eq =>
          rcases compareCursorPairLabels_exists_of_branching_support mol rule fuel rest
              (fun candidate member => support candidate (by simp [member])) with
            ⟨tailDecision, tailEq⟩
          exact ⟨tailDecision, by simp [compareCursorPairLabels, decisionEq, tailEq]⟩

/-! ## The next-pair capacity invariant

One expansion of a paired frontier preserves recursive support *and* does not increase the frontier
potential.  This is the structural replacement for the global ternary envelope: it needs no power of
three, so a deep narrow tree stays under the operational cap. -/

theorem nextCursorPairs?_potential_exists (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : ℕ)
    (beforeTotal : ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, before left right = some ordering) :
    ∀ pairs,
      (∀ pair, pair ∈ pairs →
        BranchingCursorSupport mol (fuel + 1) pair.1 ∧
        BranchingCursorSupport mol (fuel + 1) pair.2) →
      frontierPotential mol (fuel + 1) pairs ≤ RawMolecule.defaultBranchWidthCap →
      ∃ next,
        nextCursorPairs? mol before pairs = some next ∧
        (∀ pair, pair ∈ next →
          BranchingCursorSupport mol fuel pair.1 ∧
          BranchingCursorSupport mol fuel pair.2) ∧
        frontierPotential mol fuel next ≤ frontierPotential mol (fuel + 1) pairs
  | [], _, _ => ⟨[], rfl, by simp, by simp [frontierPotential]⟩
  | pair :: pairs, support, potential => by
      have headSupport := support pair (by simp)
      have tailSupport : ∀ candidate, candidate ∈ pairs →
          BranchingCursorSupport mol (fuel + 1) candidate.1 ∧
          BranchingCursorSupport mol (fuel + 1) candidate.2 := by
        intro candidate member
        exact support candidate (by simp [member])
      have tailPotential : frontierPotential mol (fuel + 1) pairs ≤
          RawMolecule.defaultBranchWidthCap := by
        have hsplit := frontierPotential_cons mol (fuel + 1) pair pairs
        omega
      rcases nextCursorPairs?_potential_exists mol before fuel beforeTotal pairs tailSupport
          tailPotential with ⟨rest, restEq, restSupport, restBound⟩
      by_cases bothTerminal :
          cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true
      · refine ⟨rest, ?_, restSupport, ?_⟩
        · simp [nextCursorPairs?, restEq, bothTerminal]
        · rw [frontierPotential_cons]
          omega
      · rcases rankedCursorChildren?_exists_of_branching_support mol before fuel pair.1
            headSupport.1 beforeTotal with
          ⟨left, leftEq, leftLen, leftSupport⟩
        rcases rankedCursorChildren?_exists_of_branching_support mol before fuel pair.2
            headSupport.2 beforeTotal with
          ⟨right, rightEq, rightLen, rightSupport⟩
        have headBound : frontierPotential mol fuel (left.zip right) ≤
            pairPotential mol (fuel + 1) pair :=
          rankedChildren_zip_potential_le mol before before fuel pair.1 pair.2 left right
            leftEq rightEq leftLen rightLen bothTerminal
        refine ⟨left.zip right ++ rest, ?_, ?_, ?_⟩
        · simp [nextCursorPairs?, restEq, bothTerminal, leftEq, rightEq]
        · intro candidate member
          rcases List.mem_append.mp member with zipped | tail
          · have components := List.of_mem_zip zipped
            exact ⟨leftSupport candidate.1 components.1,
              rightSupport candidate.2 components.2⟩
          · exact restSupport candidate tail
        · rw [frontierPotential_append, frontierPotential_cons]
          exact Nat.add_le_add headBound restBound

theorem nextOccurrenceDescriptorPairs?_potential_exists (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : ℕ)
    (beforeLeftTotal : ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, beforeLeft left right = some ordering)
    (beforeRightTotal : ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, beforeRight left right = some ordering) :
    ∀ pairs,
      (∀ pair, pair ∈ pairs →
        BranchingCursorSupport mol (fuel + 1) pair.1 ∧
        BranchingCursorSupport mol (fuel + 1) pair.2) →
      frontierPotential mol (fuel + 1) pairs ≤ RawMolecule.defaultBranchWidthCap →
      ∃ next,
        nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs = some next ∧
        (∀ pair, pair ∈ next →
          BranchingCursorSupport mol fuel pair.1 ∧
          BranchingCursorSupport mol fuel pair.2) ∧
        frontierPotential mol fuel next ≤ frontierPotential mol (fuel + 1) pairs
  | [], _, _ => ⟨[], rfl, by simp, by simp [frontierPotential]⟩
  | pair :: pairs, support, potential => by
      have headSupport := support pair (by simp)
      have tailSupport : ∀ candidate, candidate ∈ pairs →
          BranchingCursorSupport mol (fuel + 1) candidate.1 ∧
          BranchingCursorSupport mol (fuel + 1) candidate.2 := by
        intro candidate member
        exact support candidate (by simp [member])
      have tailPotential : frontierPotential mol (fuel + 1) pairs ≤
          RawMolecule.defaultBranchWidthCap := by
        have hsplit := frontierPotential_cons mol (fuel + 1) pair pairs
        omega
      rcases nextOccurrenceDescriptorPairs?_potential_exists mol beforeLeft beforeRight fuel
          beforeLeftTotal beforeRightTotal pairs tailSupport tailPotential with
        ⟨rest, restEq, restSupport, restBound⟩
      by_cases bothTerminal :
          cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true
      · refine ⟨rest, ?_, restSupport, ?_⟩
        · simp [nextOccurrenceDescriptorPairs?, restEq, bothTerminal]
        · rw [frontierPotential_cons]
          omega
      · rcases rankedCursorChildren?_exists_of_branching_support mol beforeLeft fuel pair.1
            headSupport.1 beforeLeftTotal with
          ⟨left, leftEq, leftLen, leftSupport⟩
        rcases rankedCursorChildren?_exists_of_branching_support mol beforeRight fuel pair.2
            headSupport.2 beforeRightTotal with
          ⟨right, rightEq, rightLen, rightSupport⟩
        have headBound : frontierPotential mol fuel (left.zip right) ≤
            pairPotential mol (fuel + 1) pair :=
          rankedChildren_zip_potential_le mol beforeLeft beforeRight fuel pair.1 pair.2 left right
            leftEq rightEq leftLen rightLen bothTerminal
        refine ⟨left.zip right ++ rest, ?_, ?_, ?_⟩
        · simp [nextOccurrenceDescriptorPairs?, restEq, bothTerminal, leftEq, rightEq]
        · intro candidate member
          rcases List.mem_append.mp member with zipped | tail
          · have components := List.of_mem_zip zipped
            exact ⟨leftSupport candidate.1 components.1,
              rightSupport candidate.2 components.2⟩
          · exact restSupport candidate tail
        · rw [frontierPotential_append, frontierPotential_cons]
          exact Nat.add_le_add headBound restBound

/-! ## Generic comparator existence under the structural capacity

These replace the ternary `BranchingFrontierSupport.budget` by the structural capacity
`frontierPotential ≤ cap`.  The recursion is *structural on the fuel*, and the callback totality is
an explicit, fuel-uniform hypothesis (no success trace of the comparison being defined is assumed). -/

theorem compareCursorRule_potential_exists (mol : RawMolecule) (rankFuel : ℕ)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeTotal : ∀ fuel, fuel ≤ rankFuel → ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, before left right = some ordering)
    (rule : CanonicalRuleStage) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 →
      (∀ pair, pair ∈ pairs →
        BranchingCursorSupport mol fuel pair.1 ∧
        BranchingCursorSupport mol fuel pair.2) →
      frontierPotential mol fuel pairs ≤ RawMolecule.defaultBranchWidthCap →
      ∃ ordering, compareCursorRule mol before rule fuel pairs = some ordering
  | 0, pairs, _, support, potential => by
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans (list_length_le_frontierPotential mol 0 pairs) potential
      rcases compareCursorPairLabels_exists_of_branching_support mol rule 0 pairs support with
        ⟨labels, labelsEq⟩
      cases labels with
      | lt => exact ⟨.lt, by simp [compareCursorRule, labelsEq]; omega⟩
      | gt => exact ⟨.gt, by simp [compareCursorRule, labelsEq]; omega⟩
      | eq =>
          have nextEq := nextCursorPairs?_terminal_list_eq_nil mol before pairs (by
            intro pair member
            exact ⟨(support pair member).1.zero_terminal,
              (support pair member).2.zero_terminal⟩)
          exact ⟨.eq, by simp [compareCursorRule, labelsEq, nextEq]; omega⟩
  | fuel + 1, pairs, fuelLe, support, potential => by
      have lowerLe : fuel ≤ rankFuel := by omega
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans (list_length_le_frontierPotential mol (fuel + 1) pairs) potential
      rcases compareCursorPairLabels_exists_of_branching_support mol rule (fuel + 1) pairs
          support with ⟨labels, labelsEq⟩
      cases labels with
      | lt => exact ⟨.lt, by simp [compareCursorRule, labelsEq]; omega⟩
      | gt => exact ⟨.gt, by simp [compareCursorRule, labelsEq]; omega⟩
      | eq =>
          rcases nextCursorPairs?_potential_exists mol before fuel (beforeTotal fuel lowerLe) pairs
              support potential with ⟨next, nextEq, nextSupport, nextBound⟩
          have nextPotential : frontierPotential mol fuel next ≤
              RawMolecule.defaultBranchWidthCap := le_trans nextBound potential
          cases next with
          | nil => exact ⟨.eq, by simp [compareCursorRule, labelsEq, nextEq]; omega⟩
          | cons pair rest =>
              rcases compareCursorRule_potential_exists mol rankFuel before beforeTotal rule fuel
                  (pair :: rest) (by omega) nextSupport nextPotential with ⟨decision, decisionEq⟩
              exact ⟨decision, by simp [compareCursorRule, labelsEq, nextEq, decisionEq]; omega⟩

theorem compareOccurrenceDescriptorRule_potential_exists (mol : RawMolecule) (rankFuel : ℕ)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeLeftTotal : ∀ fuel, fuel ≤ rankFuel → ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, beforeLeft left right = some ordering)
    (beforeRightTotal : ∀ fuel, fuel ≤ rankFuel → ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, beforeRight left right = some ordering)
    (stage : RawDescriptorRuleStage) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 →
      (∀ pair, pair ∈ pairs →
        BranchingCursorSupport mol fuel pair.1 ∧
        BranchingCursorSupport mol fuel pair.2) →
      frontierPotential mol fuel pairs ≤ RawMolecule.defaultBranchWidthCap →
      ∃ ordering,
        compareOccurrenceDescriptorRule mol state beforeLeft beforeRight stage fuel pairs =
          some ordering
  | 0, pairs, _, support, potential => by
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans (list_length_le_frontierPotential mol 0 pairs) potential
      cases labels : compareOccurrenceDescriptorPairLabels state stage pairs with
      | lt => exact ⟨.lt, by simp [compareOccurrenceDescriptorRule, labels]; omega⟩
      | gt => exact ⟨.gt, by simp [compareOccurrenceDescriptorRule, labels]; omega⟩
      | eq =>
          have nextEq := nextOccurrenceDescriptorPairs?_terminal_list_eq_nil mol beforeLeft
            beforeRight pairs (by
              intro pair member
              exact ⟨(support pair member).1.zero_terminal,
                (support pair member).2.zero_terminal⟩)
          exact ⟨.eq, by simp [compareOccurrenceDescriptorRule, labels, nextEq]; omega⟩
  | fuel + 1, pairs, fuelLe, support, potential => by
      have lowerLe : fuel ≤ rankFuel := by omega
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans (list_length_le_frontierPotential mol (fuel + 1) pairs) potential
      cases labels : compareOccurrenceDescriptorPairLabels state stage pairs with
      | lt => exact ⟨.lt, by simp [compareOccurrenceDescriptorRule, labels]; omega⟩
      | gt => exact ⟨.gt, by simp [compareOccurrenceDescriptorRule, labels]; omega⟩
      | eq =>
          rcases nextOccurrenceDescriptorPairs?_potential_exists mol beforeLeft beforeRight fuel
              (beforeLeftTotal fuel lowerLe) (beforeRightTotal fuel lowerLe) pairs support potential
            with ⟨next, nextEq, nextSupport, nextBound⟩
          have nextPotential : frontierPotential mol fuel next ≤
              RawMolecule.defaultBranchWidthCap := le_trans nextBound potential
          cases next with
          | nil => exact ⟨.eq, by simp [compareOccurrenceDescriptorRule, labels, nextEq]; omega⟩
          | cons pair rest =>
              rcases compareOccurrenceDescriptorRule_potential_exists mol rankFuel state beforeLeft
                  beforeRight beforeLeftTotal beforeRightTotal stage fuel (pair :: rest) (by omega)
                  nextSupport nextPotential with ⟨decision, decisionEq⟩
              exact ⟨decision, by
                simp [compareOccurrenceDescriptorRule, labels, nextEq, decisionEq]; omega⟩

/-- Empty-state tie: with the empty auxiliary descriptor state the paired labels are all `.eq`, so
the descriptor rule reduces to a frontier expansion.  Under the structural capacity it returns
`some .eq`. -/
theorem compareOccurrenceDescriptorRule_empty_eq_of_potential (mol : RawMolecule) (rankFuel : ℕ)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeLeftTotal : ∀ fuel, fuel ≤ rankFuel → ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, beforeLeft left right = some ordering)
    (beforeRightTotal : ∀ fuel, fuel ≤ rankFuel → ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, beforeRight left right = some ordering)
    (stage : RawDescriptorRuleStage) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 →
      (∀ pair, pair ∈ pairs →
        BranchingCursorSupport mol fuel pair.1 ∧
        BranchingCursorSupport mol fuel pair.2) →
      frontierPotential mol fuel pairs ≤ RawMolecule.defaultBranchWidthCap →
      compareOccurrenceDescriptorRule mol [] beforeLeft beforeRight stage fuel pairs = some .eq
  | 0, pairs, _, support, potential => by
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans (list_length_le_frontierPotential mol 0 pairs) potential
      have labelsEq := compareOccurrenceDescriptorPairLabels_empty_eq stage pairs
      have nextEq := nextOccurrenceDescriptorPairs?_terminal_list_eq_nil mol beforeLeft beforeRight
        pairs (by
          intro pair member
          exact ⟨(support pair member).1.zero_terminal, (support pair member).2.zero_terminal⟩)
      simp [compareOccurrenceDescriptorRule, labelsEq, nextEq]; omega
  | fuel + 1, pairs, fuelLe, support, potential => by
      have lowerLe : fuel ≤ rankFuel := by omega
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans (list_length_le_frontierPotential mol (fuel + 1) pairs) potential
      have labelsEq := compareOccurrenceDescriptorPairLabels_empty_eq stage pairs
      rcases nextOccurrenceDescriptorPairs?_potential_exists mol beforeLeft beforeRight fuel
          (beforeLeftTotal fuel lowerLe) (beforeRightTotal fuel lowerLe) pairs support potential with
        ⟨next, nextEq, nextSupport, nextBound⟩
      have nextPotential : frontierPotential mol fuel next ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans nextBound potential
      cases next with
      | nil => simp [compareOccurrenceDescriptorRule, labelsEq, nextEq]; omega
      | cons pair rest =>
          have deeper := compareOccurrenceDescriptorRule_empty_eq_of_potential mol rankFuel
            beforeLeft beforeRight beforeLeftTotal beforeRightTotal stage fuel (pair :: rest)
            (by omega) nextSupport nextPotential
          simp [compareOccurrenceDescriptorRule, labelsEq, nextEq, deeper]; omega

/-! ## Concrete branch-at comparisons: everything but the sibling closure is derived

The production `compareCursorBranchAt`/`compareOccurrenceDescriptorBranchAt` capture a *single*
callback at one fuel level and reuse it at every deeper level of the frontier recursion.  Because
the structural capacity is not `mono`-closed (mass grows with fuel), the captured callback's
totality on strictly lower supported pairs is the one genuinely recursive input this module does
*not* discharge.  We expose it as `SiblingCallbackCapacity` and derive the rest: the frontier
capacity bound, the width gate, the recursive support and every rule dispatch. -/

/-- The residual sibling-callback obligation.  `callback` is the function the production code
captures at one depth and reuses deeper; we require it total on recursively supported pairs whose
support lies *strictly below* `bound`.  This is not a success hypothesis on the comparison being
defined at `bound`; it is a lower-level closure hypothesis. -/
def SiblingCallbackCapacity (mol : RawMolecule)
    (callback : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (bound : ℕ) : Prop :=
  ∀ fuel, fuel < bound → ∀ left right,
    BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
    ∃ ordering, callback left right = some ordering

theorem compareCursorBranchAt_zero_potential_exists (mol : RawMolecule)
    (left right : CanonicalRerootCursor)
    (leftSupport : BranchingCursorSupport mol 0 left)
    (rightSupport : BranchingCursorSupport mol 0 right) :
    ∃ ordering, compareCursorBranchAt mol 0 .rule2 left right = some ordering := by
  rcases leftSupport.label with ⟨leftLabel, leftEq⟩
  rcases rightSupport.label with ⟨rightLabel, rightEq⟩
  simp only [compareCursorBranchAt, RawMolecule.compareCanonicalNodeThrough?,
    RawMolecule.compareCanonicalNodeRule?, leftEq, rightEq]
  cases rule1aEq : compareCIPAtomicLabel leftLabel rightLabel <;> simp [rule1aEq]
  cases mol.compareCanonicalNodeRule .rule1b left.node right.node <;> simp

/-- One successor step of the constitutional branch-at, with the captured sibling callback supplied
by `SiblingCallbackCapacity`. -/
theorem compareCursorBranchAt_succ_potential_exists (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor)
    (leftSupport : BranchingCursorSupport mol (fuel + 1) left)
    (rightSupport : BranchingCursorSupport mol (fuel + 1) right)
    (potential : pairPotential mol (fuel + 1) (left, right) ≤ RawMolecule.defaultBranchWidthCap)
    (callbackTotal : SiblingCallbackCapacity mol (compareCursorBranchAt mol fuel .rule2) (fuel + 1)) :
    ∃ ordering, compareCursorBranchAt mol (fuel + 1) .rule2 left right = some ordering := by
  let before := compareCursorBranchAt mol fuel .rule2
  have beforeTotal : ∀ k, k ≤ fuel → ∀ l r,
      BranchingCursorSupport mol k l → BranchingCursorSupport mol k r →
      ∃ ordering, before l r = some ordering :=
    fun k hk l r hl hr => callbackTotal k (by omega) l r hl hr
  have singleSupport : ∀ pair, pair ∈ [(left, right)] →
      BranchingCursorSupport mol (fuel + 1) pair.1 ∧
      BranchingCursorSupport mol (fuel + 1) pair.2 := by
    intro pair member
    have pairEq : pair = (left, right) := by simpa using member
    subst pair
    exact ⟨leftSupport, rightSupport⟩
  have singlePotential : frontierPotential mol (fuel + 1) [(left, right)] ≤
      RawMolecule.defaultBranchWidthCap := by
    simpa [frontierPotential, pairPotential] using potential
  rcases compareCursorRule_potential_exists mol fuel before beforeTotal .rule1a (fuel + 1)
      [(left, right)] (by omega) singleSupport singlePotential with ⟨rule1a, rule1aEq⟩
  rcases compareCursorRule_potential_exists mol fuel before beforeTotal .rule1b (fuel + 1)
      [(left, right)] (by omega) singleSupport singlePotential with ⟨rule1b, rule1bEq⟩
  rcases compareCursorRule_potential_exists mol fuel before beforeTotal .rule2 (fuel + 1)
      [(left, right)] (by omega) singleSupport singlePotential with ⟨rule2, rule2Eq⟩
  exact ⟨(match rule1a with
    | .eq => (match rule1b with | .eq => rule2 | decision => decision)
    | decision => decision), by
    cases rule1a <;> cases rule1b <;> cases rule2 <;>
      simp [compareCursorBranchAt, before, rule1aEq, rule1bEq, rule2Eq]⟩

/-- One successor step of the production occurrence-descriptor branch-at on the empty auxiliary
state.  The three captured callbacks (the raw constitutional one and the two staged descriptor ones)
are the residual sibling obligations; the frontier capacity, the width gate and every rule dispatch
are derived. -/
theorem compareOccurrenceDescriptorBranchAt_succ_potential_exists (mol : RawMolecule)
    (fuel : ℕ) (stage : RawDescriptorRuleStage) (left right : CanonicalRerootCursor)
    (leftSupport : BranchingCursorSupport mol (fuel + 1) left)
    (rightSupport : BranchingCursorSupport mol (fuel + 1) right)
    (potential : pairPotential mol (fuel + 1) (left, right) ≤ RawMolecule.defaultBranchWidthCap)
    (rawCallbackTotal : SiblingCallbackCapacity mol (compareCursorBranchAt mol fuel .rule2) (fuel + 1))
    (beforeLeftTotal : SiblingCallbackCapacity mol
      (compareOccurrenceDescriptorBranchAt mol [] fuel stage.leftInternal) (fuel + 1))
    (beforeRightTotal : SiblingCallbackCapacity mol
      (compareOccurrenceDescriptorBranchAt mol [] fuel stage.rightInternal) (fuel + 1)) :
    ∃ ordering,
      compareOccurrenceDescriptorBranchAt mol [] (fuel + 1) stage left right = some ordering := by
  rcases compareCursorBranchAt_succ_potential_exists mol fuel left right leftSupport rightSupport
      potential rawCallbackTotal with ⟨raw, rawEq⟩
  let beforeLeft := compareOccurrenceDescriptorBranchAt mol [] fuel stage.leftInternal
  let beforeRight := compareOccurrenceDescriptorBranchAt mol [] fuel stage.rightInternal
  have beforeLeftTotal' : ∀ k, k ≤ fuel → ∀ l r,
      BranchingCursorSupport mol k l → BranchingCursorSupport mol k r →
      ∃ ordering, beforeLeft l r = some ordering :=
    fun k hk l r hl hr => beforeLeftTotal k (by omega) l r hl hr
  have beforeRightTotal' : ∀ k, k ≤ fuel → ∀ l r,
      BranchingCursorSupport mol k l → BranchingCursorSupport mol k r →
      ∃ ordering, beforeRight l r = some ordering :=
    fun k hk l r hl hr => beforeRightTotal k (by omega) l r hl hr
  have singleSupport : ∀ pair, pair ∈ [(left, right)] →
      BranchingCursorSupport mol (fuel + 1) pair.1 ∧
      BranchingCursorSupport mol (fuel + 1) pair.2 := by
    intro pair member
    have pairEq : pair = (left, right) := by simpa using member
    subst pair
    exact ⟨leftSupport, rightSupport⟩
  have singlePotential : frontierPotential mol (fuel + 1) [(left, right)] ≤
      RawMolecule.defaultBranchWidthCap := by
    simpa [frontierPotential, pairPotential] using potential
  have compareEq : ∀ selected,
      compareOccurrenceDescriptorRule mol [] beforeLeft beforeRight selected (fuel + 1)
        [(left, right)] = some .eq := by
    intro selected
    exact compareOccurrenceDescriptorRule_empty_eq_of_potential mol fuel beforeLeft beforeRight
      beforeLeftTotal' beforeRightTotal' selected (fuel + 1) [(left, right)] (by omega)
      singleSupport singlePotential
  refine ⟨raw, ?_⟩
  cases raw with
  | lt => simp [compareOccurrenceDescriptorBranchAt, rawEq]
  | gt => simp [compareOccurrenceDescriptorBranchAt, rawEq]
  | eq =>
      cases stage <;>
        simp [compareOccurrenceDescriptorBranchAt, rawEq, beforeLeft, beforeRight, compareEq]

/-! ## Narrow-shape milestones: the capacity reaches beyond the ternary ceiling

The ternary gate `3 ^ fuel ≤ defaultBranchWidthCap` refuses at `fuel = 10` (since `3 ^ 10 = 59049 >
20000`).  We exhibit a genuinely narrow shape whose structural capacity still passes at that depth,
with no capability or success hypothesis: a *spine* cursor (every reachable occurrence is terminal
or has at most one forward child) has mass exactly linear in the fuel. -/

/-- A list-sum bound: pointwise `≤ B` gives `Σ ≤ length * B`. -/
theorem list_sum_map_le_length_mul {α : Type*} (values : List α) (f : α → ℕ) (B : ℕ)
    (bound : ∀ value, value ∈ values → f value ≤ B) :
    (values.map f).sum ≤ values.length * B := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hhead : f head ≤ B := bound head (by simp)
      have htail : (tail.map f).sum ≤ tail.length * B :=
        ih fun value member => bound value (by simp [member])
      calc
        f head + (tail.map f).sum ≤ B + tail.length * B := Nat.add_le_add hhead htail
        _ = (tail.length + 1) * B := by ring

/-- A spine shape: every reachable occurrence down to the support fuel is terminal or has at most one
forward child.  This is a purely structural predicate on the cursor, not a success trace. -/
def SpineShape (mol : RawMolecule) : ℕ → CanonicalRerootCursor → Prop
  | 0, _ => True
  | fuel + 1, cursor =>
      (cursorTerminal mol cursor = true ∨ (cursor.children mol).length ≤ 1) ∧
        ∀ child, child ∈ cursor.children mol → SpineShape mol fuel child

/-- A spine has mass at most `3 * fuel`: the single continuing child advances the mass by three per
level instead of multiplying it.  This is the formal reason the capacity beats the ternary envelope
on narrow trees. -/
theorem cursorExpansionMass_le_three_mul_of_spine (mol : RawMolecule) :
    ∀ (fuel : ℕ) (cursor : CanonicalRerootCursor), SpineShape mol fuel cursor →
      cursorExpansionMass mol fuel cursor ≤ 3 * fuel
  | 0, cursor, _ => by simp [cursorExpansionMass]
  | fuel + 1, cursor, spine => by
      rcases spine with ⟨width, children⟩
      by_cases terminal : cursorTerminal mol cursor = true
      · rw [cursorExpansionMass_succ_of_terminal mol fuel cursor terminal]
        omega
      · have notTerminal : cursorTerminal mol cursor = false := Bool.eq_false_of_not_eq_true terminal
        rw [cursorExpansionMass_succ_of_not_terminal mol fuel cursor notTerminal]
        have hlen : (cursor.children mol).length ≤ 1 := by
          rcases width with h | h
          · exact absurd h terminal
          · exact h
        have childSum : ((cursor.children mol).map (cursorExpansionMass mol fuel)).sum ≤
            (cursor.children mol).length * (3 * fuel) :=
          list_sum_map_le_length_mul (cursor.children mol) (cursorExpansionMass mol fuel) (3 * fuel)
            (fun child member => cursorExpansionMass_le_three_mul_of_spine mol fuel child
              (children child member))
        calc
          3 + ((cursor.children mol).map (cursorExpansionMass mol fuel)).sum
              ≤ 3 + (cursor.children mol).length * (3 * fuel) := Nat.add_le_add_left childSum 3
          _ ≤ 3 + 1 * (3 * fuel) := Nat.add_le_add_left (Nat.mul_le_mul_right (3 * fuel) hlen) 3
          _ = 3 * (fuel + 1) := by ring

/-- A spine cursor whose depth satisfies `6 * fuel ≤ 19999` passes the structural capacity gate. -/
theorem spine_cursorCapacity (mol : RawMolecule) (fuel : ℕ) (cursor : CanonicalRerootCursor)
    (spine : SpineShape mol fuel cursor) (hfuel : 6 * fuel ≤ 19999) :
    cursorCapacity mol fuel cursor := by
  have massLe := cursorExpansionMass_le_three_mul_of_spine mol fuel cursor spine
  simp only [cursorCapacity, RawMolecule.defaultBranchWidthCap]
  omega

/-- The old ternary gate already refuses at depth ten. -/
theorem ternary_gate_refuses_at_ten : ¬ (3 ^ 10 ≤ RawMolecule.defaultBranchWidthCap) := by
  intro envelope
  have := ternary_envelope_depth_le_nine (fuel := 10) envelope
  omega

/-- A spine-shaped cursor of depth ten passes the structural capacity gate even though the ternary
gate refuses at that depth.  No molecular capability, success trace or external approval is used:
the only hypothesis is the purely structural spine shape. -/
theorem spine_cursorCapacity_ten (mol : RawMolecule) (cursor : CanonicalRerootCursor)
    (spine : SpineShape mol 10 cursor) : cursorCapacity mol 10 cursor :=
  spine_cursorCapacity mol 10 cursor spine (by norm_num)

/-! ## Molecule-derived support feeds the capacity unchanged

The molecule-derived branching ranking of `ProductionMoleculeBranchingRanking` (well-formedness,
unique bond records, localized maximum matching, the `≤ 3` ternary width, the molecule-size height)
supplies recursive support; the structural capacity merely replaces the *frontier* gate.  The
max-matching, well-formedness, uniqueness, label, depth and `≤ 3` width hypotheses are preserved
exactly — nothing is weakened and no cap is lifted. -/

/-- A molecule-derived singleton frontier carries the structural capacity and recursive support at
the covered depth, with `WellFormed`, `BondRecordsUnique`, `LocalizedMancudeComponentsMaximum` and
the `≤ 3` `CanonicalCenterBranchingWidth` scope preserved unchanged. -/
theorem moleculeBranchingCapacityFrontier_singleton_of_localizedMaximum
    (mol : RawMolecule) (center : ℕ) (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (branching : CanonicalCenterBranchingWidth mol center)
    (maximum : LocalizedMancudeComponentsMaximum mol)
    (fuel : ℕ) {left right : CanonicalRerootCursor}
    (capacity : 1 + cursorExpansionMass mol fuel left + cursorExpansionMass mol fuel right ≤
      RawMolecule.defaultBranchWidthCap)
    (leftEligible : CanonicalCenterRerootCursor mol center left)
    (rightEligible : CanonicalCenterRerootCursor mol center right)
    (leftCovered : moleculeCursorHeight mol left ≤ fuel)
    (rightCovered : moleculeCursorHeight mol right ≤ fuel) :
    CapacityFrontierSupport mol fuel [(left, right)] :=
  ⟨by
      intro pair member
      have pairEq : pair = (left, right) := by simpa using member
      subst pair
      exact ⟨moleculeBranchingCursorSupport_of_eligible mol center centerBound wellFormed branching
          (productionMancudeRule1aSupported_of_localizedMaximum mol wellFormed unique maximum)
          fuel leftEligible leftCovered,
        moleculeBranchingCursorSupport_of_eligible mol center centerBound wellFormed branching
          (productionMancudeRule1aSupported_of_localizedMaximum mol wellFormed unique maximum)
          fuel rightEligible rightCovered⟩,
    by simpa [frontierPotential, pairPotential] using capacity⟩

/-! ## Mass saturation and the supported mass-bounded domain

The generic certificates above replace the global ternary envelope by the structural capacity, but
they still carry the captured sibling callback (`SiblingCallbackCapacity`) as an opaque hypothesis.
This section discharges that hypothesis from structure alone on a **supported mass-bounded domain**,
using one new fact:

> the expansion mass of a recursively supported cursor *saturates*.

A cursor supported at fuel `k` already describes its whole tree down to `k`, so raising the fuel can
no longer grow its mass.  This is exactly what lets a callback captured at the *highest* fuel be
reused at every strictly lower level with no growth of the capacity budget: the closure is the
induction hypothesis, *lifted* by support monotonicity together with mass saturation, never an
assumed success trace.

The mass bound `M` here is **incomparable** with the old ternary gate `3 ^ fuel ≤ cap`.  A full
ternary tree of depth nine has frontier mass `29523 > 20000` yet satisfies the old gate
`3 ^ 9 = 19683 ≤ 20000`; a deep narrow tree at `fuel = 10` fails the old gate
(`3 ^ 10 = 59049 > 20000`) yet passes the mass gate with `M` linear in the fuel.  Neither gate
implies the other, so this is an *additional* sufficient domain, and the ternary route above is
preserved unchanged. -/

/-- List-sum congruence: pointwise equality lifts to equality of sums. -/
theorem list_sum_map_congr {α : Type*} (values : List α) (f g : α → ℕ) :
    (∀ value, value ∈ values → f value = g value) →
      (values.map f).sum = (values.map g).sum := by
  induction values with
  | nil => intro _; simp
  | cons head tail ih =>
      intro equal
      have htail := ih (fun value member => equal value (by simp [member]))
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, equal head (by simp), htail]

/-- A single member never exceeds the sum of the mapped list. -/
theorem list_le_sum_of_mem {α : Type*} (values : List α) (f : α → ℕ) {value : α} :
    value ∈ values → f value ≤ (values.map f).sum := by
  induction values with
  | nil => intro member; simp at member
  | cons head tail ih =>
      intro member
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp member with rfl | member
      · omega
      · have := ih member
        omega

/-- **Mass saturation, additive form.**  A cursor supported at fuel `k` has the same expansion mass
at `k + extra` for every `extra`: recursive support already captures the whole tree down to `k`, so
the padded ternary mass cannot grow beyond the supporting fuel. -/
theorem cursorExpansionMass_add_eq_of_support (mol : RawMolecule) {k : ℕ}
    {cursor : CanonicalRerootCursor} (support : BranchingCursorSupport mol k cursor) :
    ∀ extra, cursorExpansionMass mol (k + extra) cursor = cursorExpansionMass mol k cursor := by
  induction support with
  | terminal k cursor label terminal =>
      intro extra
      rw [cursorExpansionMass_eq_zero_of_terminal mol (k + extra) cursor terminal,
        cursorExpansionMass_eq_zero_of_terminal mol k cursor terminal]
  | branch j cursor children label childrenEq width childrenSupport ih =>
      intro extra
      have hshift : (j + 1) + extra = j + extra + 1 := by omega
      rw [hshift]
      by_cases terminal : cursorTerminal mol cursor = true
      · rw [cursorExpansionMass_eq_zero_of_terminal mol (j + extra + 1) cursor terminal,
          cursorExpansionMass_eq_zero_of_terminal mol (j + 1) cursor terminal]
      · have notTerminal : cursorTerminal mol cursor = false :=
          Bool.eq_false_of_not_eq_true terminal
        rw [cursorExpansionMass_succ_of_not_terminal mol (j + extra) cursor notTerminal,
          cursorExpansionMass_succ_of_not_terminal mol j cursor notTerminal, childrenEq]
        congr 1
        exact list_sum_map_congr children (cursorExpansionMass mol (j + extra))
          (cursorExpansionMass mol j) (fun child member => ih child member extra)

/-- **Mass saturation.**  If `cursor` carries recursive support at fuel `k`, then at every larger
fuel `f` its expansion mass equals the mass at `k`. -/
theorem cursorExpansionMass_eq_of_support (mol : RawMolecule) {k f : ℕ}
    {cursor : CanonicalRerootCursor} (support : BranchingCursorSupport mol k cursor)
    (le : k ≤ f) :
    cursorExpansionMass mol f cursor = cursorExpansionMass mol k cursor := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  exact cursorExpansionMass_add_eq_of_support mol support extra

/-- The supported mass-bounded domain: recursive branching support at the current fuel together with
an individual expansion mass of at most `M`.  This is the domain on which the captured sibling
callback is total. -/
def MassBoundedSupport (mol : RawMolecule) (fuel M : ℕ) (cursor : CanonicalRerootCursor) : Prop :=
  BranchingCursorSupport mol fuel cursor ∧ cursorExpansionMass mol fuel cursor ≤ M

/-- The mass-bounded domain is monotone in the fuel: support lifts by `mono`, and the mass does not
grow past the supporting fuel by saturation.  This is the exact step that lets a callback captured at
a *higher* fuel be applied to a *lower* supported child without any budget growth. -/
theorem MassBoundedSupport.mono (mol : RawMolecule) {k f M : ℕ} {cursor : CanonicalRerootCursor}
    (le : k ≤ f) (bounded : MassBoundedSupport mol k M cursor) :
    MassBoundedSupport mol f M cursor :=
  ⟨bounded.1.mono le, by
    rw [cursorExpansionMass_eq_of_support mol bounded.1 le]
    exact bounded.2⟩

/-- A real child of a non-terminal cursor carries successor mass no larger than its parent's: the
padded ternary arity already dominates every child mass.  This is the individual-mass preservation
the sorter needs. -/
theorem cursorExpansionMass_child_le_parent (mol : RawMolecule) {fuel : ℕ}
    {cursor child : CanonicalRerootCursor}
    (notTerminal : cursorTerminal mol cursor = false)
    (member : child ∈ cursor.children mol) :
    cursorExpansionMass mol fuel child ≤ cursorExpansionMass mol (fuel + 1) cursor := by
  rw [cursorExpansionMass_succ_of_not_terminal mol fuel cursor notTerminal]
  have := list_le_sum_of_mem (cursor.children mol) (cursorExpansionMass mol fuel) member
  omega

/-- The padding cursor is a forced leaf, hence carries zero mass at every fuel. -/
@[simp] theorem cursorExpansionMass_branchingPaddingCursor (mol : RawMolecule) (fuel : ℕ)
    (cursor : CanonicalRerootCursor) :
    cursorExpansionMass mol fuel (branchingPaddingCursor mol cursor) = 0 := by
  simp [branchingPaddingCursor, linearPaddingCursor]

/-- A callback is total on the mass-bounded domain at every fuel up to `bound`.  This is not a success
hypothesis on any comparison being defined: it is the reusable shape of an induction hypothesis over
the fuel, discharged by `support.mono` plus mass saturation. -/
def MassBoundedCallback (mol : RawMolecule) (M bound : ℕ)
    (callback : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) : Prop :=
  ∀ k, k ≤ bound → ∀ left right,
    MassBoundedSupport mol k M left → MassBoundedSupport mol k M right →
    ∃ ordering, callback left right = some ordering

/-- Ranked children preserve the mass-bounded domain: the produced list has length three, and every
entry is either a real supported child (mass bounded by the parent) or a zero-mass padding leaf. -/
theorem rankedCursorChildren?_exists_of_massBounded (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel M : ℕ) (cursor : CanonicalRerootCursor)
    (support : BranchingCursorSupport mol (fuel + 1) cursor)
    (massBound : cursorExpansionMass mol (fuel + 1) cursor ≤ M)
    (beforeTotal : ∀ left right,
      MassBoundedSupport mol fuel M left → MassBoundedSupport mol fuel M right →
      ∃ ordering, before left right = some ordering) :
    ∃ ranked,
      rankedCursorChildren? mol before cursor = some ranked ∧
      ranked.length = 3 ∧
      ∀ child, child ∈ ranked → MassBoundedSupport mol fuel M child := by
  cases support with
  | terminal _ _ label terminal =>
      let padding := branchingPaddingCursor mol cursor
      refine ⟨List.replicate 3 padding, ?_, by simp, ?_⟩
      · simpa [padding, branchingPaddingCursor, linearPaddingCursor] using
          rankedCursorChildren?_eq_of_linear_terminal mol before cursor terminal
      · intro child member
        have childEq : child = padding := List.eq_of_mem_replicate member
        rw [childEq]
        exact ⟨branchingPaddingCursor_support mol fuel cursor, by
          simp [padding, branchingPaddingCursor, linearPaddingCursor]⟩
  | branch _ _ children label childrenEq width childrenSupport =>
      have sortedPredicate : ∀ child, child ∈ children → MassBoundedSupport mol fuel M child := by
        intro child member
        refine ⟨childrenSupport child member, ?_⟩
        by_cases terminal : cursorTerminal mol cursor = true
        · have childrenNil := cursor_children_eq_nil_of_terminal mol cursor terminal
          rw [childrenEq] at childrenNil
          rw [childrenNil] at member
          simp at member
        · exact le_trans (cursorExpansionMass_child_le_parent mol
            (Bool.eq_false_of_not_eq_true terminal) (by rw [childrenEq]; exact member)) massBound
      rcases sortCursorsBy?_exists_of_supported before (MassBoundedSupport mol fuel M)
          beforeTotal children sortedPredicate with
        ⟨sorted, sortedEq, sortedSupport, sortedLength⟩
      let padding := branchingPaddingCursor mol cursor
      let ranked := sorted ++ List.replicate (3 - sorted.length) padding
      have notTooWide : ¬ 3 < children.length := Nat.not_lt_of_ge width
      refine ⟨ranked, ?_, ?_, ?_⟩
      · simp [rankedCursorChildren?, childrenEq, notTooWide, sortedEq,
          ranked, padding, branchingPaddingCursor, linearPaddingCursor]
      · have rankedLength : ranked.length = sorted.length + (3 - sorted.length) := by
          simp [ranked]
        rw [rankedLength, sortedLength]
        omega
      · intro child member
        rcases List.mem_append.mp member with sortedMember | paddingMember
        · exact sortedSupport child sortedMember
        · have childEq : child = padding := List.eq_of_mem_replicate paddingMember
          rw [childEq]
          exact ⟨branchingPaddingCursor_support mol fuel cursor, by
            simp [padding, branchingPaddingCursor, linearPaddingCursor]⟩

/-- One expansion step preserves the supported mass-bounded domain *and* does not increase the
frontier potential: child masses are bounded by the parent's via the sorter, and the pair-potential
bound is inherited unchanged. -/
theorem nextCursorPairs?_massBounded_exists (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel M : ℕ)
    (beforeTotal : ∀ left right,
      MassBoundedSupport mol fuel M left → MassBoundedSupport mol fuel M right →
      ∃ ordering, before left right = some ordering) :
    ∀ pairs,
      (∀ pair, pair ∈ pairs →
        MassBoundedSupport mol (fuel + 1) M pair.1 ∧
        MassBoundedSupport mol (fuel + 1) M pair.2) →
      frontierPotential mol (fuel + 1) pairs ≤ RawMolecule.defaultBranchWidthCap →
      ∃ next,
        nextCursorPairs? mol before pairs = some next ∧
        (∀ pair, pair ∈ next →
          MassBoundedSupport mol fuel M pair.1 ∧
          MassBoundedSupport mol fuel M pair.2) ∧
        frontierPotential mol fuel next ≤ frontierPotential mol (fuel + 1) pairs
  | [], _, _ => ⟨[], rfl, by simp, by simp [frontierPotential]⟩
  | pair :: pairs, support, potential => by
      have headSupport := support pair (by simp)
      have tailSupport : ∀ candidate, candidate ∈ pairs →
          MassBoundedSupport mol (fuel + 1) M candidate.1 ∧
          MassBoundedSupport mol (fuel + 1) M candidate.2 := by
        intro candidate member
        exact support candidate (by simp [member])
      have tailPotential : frontierPotential mol (fuel + 1) pairs ≤
          RawMolecule.defaultBranchWidthCap := by
        have hsplit := frontierPotential_cons mol (fuel + 1) pair pairs
        omega
      rcases nextCursorPairs?_massBounded_exists mol before fuel M beforeTotal pairs tailSupport
          tailPotential with ⟨rest, restEq, restSupport, restBound⟩
      by_cases bothTerminal :
          cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true
      · refine ⟨rest, ?_, restSupport, ?_⟩
        · simp [nextCursorPairs?, restEq, bothTerminal]
        · rw [frontierPotential_cons]
          omega
      · rcases rankedCursorChildren?_exists_of_massBounded mol before fuel M pair.1
            headSupport.1.1 headSupport.1.2 beforeTotal with ⟨left, leftEq, leftLen, leftBounded⟩
        rcases rankedCursorChildren?_exists_of_massBounded mol before fuel M pair.2
            headSupport.2.1 headSupport.2.2 beforeTotal with
          ⟨right, rightEq, rightLen, rightBounded⟩
        have headBound : frontierPotential mol fuel (left.zip right) ≤
            pairPotential mol (fuel + 1) pair :=
          rankedChildren_zip_potential_le mol before before fuel pair.1 pair.2 left right
            leftEq rightEq leftLen rightLen bothTerminal
        refine ⟨left.zip right ++ rest, ?_, ?_, ?_⟩
        · simp [nextCursorPairs?, restEq, bothTerminal, leftEq, rightEq]
        · intro candidate member
          rcases List.mem_append.mp member with zipped | tail
          · have components := List.of_mem_zip zipped
            exact ⟨leftBounded candidate.1 components.1,
              rightBounded candidate.2 components.2⟩
          · exact restSupport candidate tail
        · rw [frontierPotential_append, frontierPotential_cons]
          exact Nat.add_le_add headBound restBound

/-- The occurrence-descriptor analogue of `nextCursorPairs?_massBounded_exists`: the two staged
callbacks are used on mass-bounded children and the frontier potential is inherited unchanged. -/
theorem nextOccurrenceDescriptorPairs?_massBounded_exists (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel M : ℕ)
    (beforeLeftTotal : ∀ left right,
      MassBoundedSupport mol fuel M left → MassBoundedSupport mol fuel M right →
      ∃ ordering, beforeLeft left right = some ordering)
    (beforeRightTotal : ∀ left right,
      MassBoundedSupport mol fuel M left → MassBoundedSupport mol fuel M right →
      ∃ ordering, beforeRight left right = some ordering) :
    ∀ pairs,
      (∀ pair, pair ∈ pairs →
        MassBoundedSupport mol (fuel + 1) M pair.1 ∧
        MassBoundedSupport mol (fuel + 1) M pair.2) →
      frontierPotential mol (fuel + 1) pairs ≤ RawMolecule.defaultBranchWidthCap →
      ∃ next,
        nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs = some next ∧
        (∀ pair, pair ∈ next →
          MassBoundedSupport mol fuel M pair.1 ∧
          MassBoundedSupport mol fuel M pair.2) ∧
        frontierPotential mol fuel next ≤ frontierPotential mol (fuel + 1) pairs
  | [], _, _ => ⟨[], rfl, by simp, by simp [frontierPotential]⟩
  | pair :: pairs, support, potential => by
      have headSupport := support pair (by simp)
      have tailSupport : ∀ candidate, candidate ∈ pairs →
          MassBoundedSupport mol (fuel + 1) M candidate.1 ∧
          MassBoundedSupport mol (fuel + 1) M candidate.2 := by
        intro candidate member
        exact support candidate (by simp [member])
      have tailPotential : frontierPotential mol (fuel + 1) pairs ≤
          RawMolecule.defaultBranchWidthCap := by
        have hsplit := frontierPotential_cons mol (fuel + 1) pair pairs
        omega
      rcases nextOccurrenceDescriptorPairs?_massBounded_exists mol beforeLeft beforeRight fuel M
          beforeLeftTotal beforeRightTotal pairs tailSupport tailPotential with
        ⟨rest, restEq, restSupport, restBound⟩
      by_cases bothTerminal :
          cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true
      · refine ⟨rest, ?_, restSupport, ?_⟩
        · simp [nextOccurrenceDescriptorPairs?, restEq, bothTerminal]
        · rw [frontierPotential_cons]
          omega
      · rcases rankedCursorChildren?_exists_of_massBounded mol beforeLeft fuel M pair.1
            headSupport.1.1 headSupport.1.2 beforeLeftTotal with ⟨left, leftEq, leftLen, leftBounded⟩
        rcases rankedCursorChildren?_exists_of_massBounded mol beforeRight fuel M pair.2
            headSupport.2.1 headSupport.2.2 beforeRightTotal with
          ⟨right, rightEq, rightLen, rightBounded⟩
        have headBound : frontierPotential mol fuel (left.zip right) ≤
            pairPotential mol (fuel + 1) pair :=
          rankedChildren_zip_potential_le mol beforeLeft beforeRight fuel pair.1 pair.2 left right
            leftEq rightEq leftLen rightLen bothTerminal
        refine ⟨left.zip right ++ rest, ?_, ?_, ?_⟩
        · simp [nextOccurrenceDescriptorPairs?, restEq, bothTerminal, leftEq, rightEq]
        · intro candidate member
          rcases List.mem_append.mp member with zipped | tail
          · have components := List.of_mem_zip zipped
            exact ⟨leftBounded candidate.1 components.1,
              rightBounded candidate.2 components.2⟩
          · exact restSupport candidate tail
        · rw [frontierPotential_append, frontierPotential_cons]
          exact Nat.add_le_add headBound restBound

/-- A frontier admissible for the mass-bounded closure: every pair is mass-bounded at the current
fuel and the whole potential stays under the operational cap. -/
def MassBoundedFrontier (mol : RawMolecule) (fuel M : ℕ)
    (pairs : List (CanonicalRerootCursor × CanonicalRerootCursor)) : Prop :=
  (∀ pair, pair ∈ pairs →
      MassBoundedSupport mol fuel M pair.1 ∧ MassBoundedSupport mol fuel M pair.2) ∧
    frontierPotential mol fuel pairs ≤ RawMolecule.defaultBranchWidthCap

/-- The constitutional rule comparator is total on mass-bounded frontiers, with the captured callback
total on the mass-bounded domain *below* `bound`.  Unlike `compareCursorRule_potential_exists`, the
callback premise is not a fresh obligation: it is discharged from a single-fuel induction hypothesis
by `support.mono` plus mass saturation (see `compareCursorBranchAt_massBounded_exists`). -/
theorem compareCursorRule_massBounded_exists (mol : RawMolecule) (M bound : ℕ)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeTotal : MassBoundedCallback mol M bound before)
    (rule : CanonicalRuleStage) :
    ∀ fuel pairs, fuel ≤ bound + 1 → MassBoundedFrontier mol fuel M pairs →
      ∃ ordering, compareCursorRule mol before rule fuel pairs = some ordering
  | 0, pairs, _, frontier => by
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans (list_length_le_frontierPotential mol 0 pairs) frontier.2
      have pairSupport : ∀ pair, pair ∈ pairs →
          BranchingCursorSupport mol 0 pair.1 ∧ BranchingCursorSupport mol 0 pair.2 :=
        fun pair member => ⟨(frontier.1 pair member).1.1, (frontier.1 pair member).2.1⟩
      rcases compareCursorPairLabels_exists_of_branching_support mol rule 0 pairs pairSupport with
        ⟨labels, labelsEq⟩
      cases labels with
      | lt => exact ⟨.lt, by simp [compareCursorRule, labelsEq]; omega⟩
      | gt => exact ⟨.gt, by simp [compareCursorRule, labelsEq]; omega⟩
      | eq =>
          have nextEq := nextCursorPairs?_terminal_list_eq_nil mol before pairs (by
            intro pair member
            exact ⟨(frontier.1 pair member).1.1.zero_terminal,
              (frontier.1 pair member).2.1.zero_terminal⟩)
          exact ⟨.eq, by simp [compareCursorRule, labelsEq, nextEq]; omega⟩
  | fuel + 1, pairs, fuelLe, frontier => by
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans (list_length_le_frontierPotential mol (fuel + 1) pairs) frontier.2
      have pairSupport : ∀ pair, pair ∈ pairs →
          BranchingCursorSupport mol (fuel + 1) pair.1 ∧
          BranchingCursorSupport mol (fuel + 1) pair.2 :=
        fun pair member => ⟨(frontier.1 pair member).1.1, (frontier.1 pair member).2.1⟩
      rcases compareCursorPairLabels_exists_of_branching_support mol rule (fuel + 1) pairs
          pairSupport with ⟨labels, labelsEq⟩
      cases labels with
      | lt => exact ⟨.lt, by simp [compareCursorRule, labelsEq]; omega⟩
      | gt => exact ⟨.gt, by simp [compareCursorRule, labelsEq]; omega⟩
      | eq =>
          have lowerLe : fuel ≤ bound := by omega
          rcases nextCursorPairs?_massBounded_exists mol before fuel M
              (beforeTotal fuel lowerLe) pairs frontier.1 frontier.2 with
            ⟨next, nextEq, nextBounded, nextBound⟩
          have nextFrontier : MassBoundedFrontier mol fuel M next :=
            ⟨nextBounded, le_trans nextBound frontier.2⟩
          cases next with
          | nil => exact ⟨.eq, by simp [compareCursorRule, labelsEq, nextEq]; omega⟩
          | cons pair rest =>
              rcases compareCursorRule_massBounded_exists mol M bound before beforeTotal rule fuel
                  (pair :: rest) (by omega) nextFrontier with ⟨decision, decisionEq⟩
              exact ⟨decision, by simp [compareCursorRule, labelsEq, nextEq, decisionEq]; omega⟩

/-- The occurrence-descriptor rule comparator is total on mass-bounded frontiers.  The `⇒ fuel ≤ bound`
step is supplied by the caller through `fuel + 1 ≤ bound + 1`. -/
theorem compareOccurrenceDescriptorRule_massBounded_exists (mol : RawMolecule) (M bound : ℕ)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeLeftTotal : MassBoundedCallback mol M bound beforeLeft)
    (beforeRightTotal : MassBoundedCallback mol M bound beforeRight)
    (stage : RawDescriptorRuleStage) :
    ∀ fuel pairs, fuel ≤ bound + 1 → MassBoundedFrontier mol fuel M pairs →
      ∃ ordering,
        compareOccurrenceDescriptorRule mol state beforeLeft beforeRight stage fuel pairs =
          some ordering
  | 0, pairs, _, frontier => by
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans (list_length_le_frontierPotential mol 0 pairs) frontier.2
      cases labels : compareOccurrenceDescriptorPairLabels state stage pairs with
      | lt => exact ⟨.lt, by simp [compareOccurrenceDescriptorRule, labels]; omega⟩
      | gt => exact ⟨.gt, by simp [compareOccurrenceDescriptorRule, labels]; omega⟩
      | eq =>
          have nextEq := nextOccurrenceDescriptorPairs?_terminal_list_eq_nil mol beforeLeft
            beforeRight pairs (by
              intro pair member
              exact ⟨(frontier.1 pair member).1.1.zero_terminal,
                (frontier.1 pair member).2.1.zero_terminal⟩)
          exact ⟨.eq, by simp [compareOccurrenceDescriptorRule, labels, nextEq]; omega⟩
  | fuel + 1, pairs, fuelLe, frontier => by
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans (list_length_le_frontierPotential mol (fuel + 1) pairs) frontier.2
      have lowerLe : fuel ≤ bound := by omega
      cases labels : compareOccurrenceDescriptorPairLabels state stage pairs with
      | lt => exact ⟨.lt, by simp [compareOccurrenceDescriptorRule, labels]; omega⟩
      | gt => exact ⟨.gt, by simp [compareOccurrenceDescriptorRule, labels]; omega⟩
      | eq =>
          rcases nextOccurrenceDescriptorPairs?_massBounded_exists mol beforeLeft beforeRight fuel M
              (beforeLeftTotal fuel lowerLe) (beforeRightTotal fuel lowerLe) pairs frontier.1
              frontier.2 with ⟨next, nextEq, nextBounded, nextBound⟩
          have nextFrontier : MassBoundedFrontier mol fuel M next :=
            ⟨nextBounded, le_trans nextBound frontier.2⟩
          cases next with
          | nil =>
              exact ⟨.eq, by simp [compareOccurrenceDescriptorRule, labels, nextEq]; omega⟩
          | cons pair rest =>
              rcases compareOccurrenceDescriptorRule_massBounded_exists mol M bound state beforeLeft
                  beforeRight beforeLeftTotal beforeRightTotal stage fuel (pair :: rest) (by omega)
                  nextFrontier with ⟨decision, decisionEq⟩
              exact ⟨decision, by
                simp [compareOccurrenceDescriptorRule, labels, nextEq, decisionEq]; omega⟩

/-- Empty-state tie under the mass-bounded capacity: the paired labels are all `.eq`, so the
descriptor rule reduces to a frontier expansion returning `some .eq`. -/
theorem compareOccurrenceDescriptorRule_empty_eq_of_massBounded (mol : RawMolecule) (M bound : ℕ)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeLeftTotal : MassBoundedCallback mol M bound beforeLeft)
    (beforeRightTotal : MassBoundedCallback mol M bound beforeRight)
    (stage : RawDescriptorRuleStage) :
    ∀ fuel pairs, fuel ≤ bound + 1 → MassBoundedFrontier mol fuel M pairs →
      compareOccurrenceDescriptorRule mol [] beforeLeft beforeRight stage fuel pairs = some .eq
  | 0, pairs, _, frontier => by
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans (list_length_le_frontierPotential mol 0 pairs) frontier.2
      have labelsEq := compareOccurrenceDescriptorPairLabels_empty_eq stage pairs
      have nextEq := nextOccurrenceDescriptorPairs?_terminal_list_eq_nil mol beforeLeft beforeRight
        pairs (by
          intro pair member
          exact ⟨(frontier.1 pair member).1.1.zero_terminal,
            (frontier.1 pair member).2.1.zero_terminal⟩)
      simp [compareOccurrenceDescriptorRule, labelsEq, nextEq]; omega
  | fuel + 1, pairs, fuelLe, frontier => by
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap :=
        le_trans (list_length_le_frontierPotential mol (fuel + 1) pairs) frontier.2
      have lowerLe : fuel ≤ bound := by omega
      have labelsEq := compareOccurrenceDescriptorPairLabels_empty_eq stage pairs
      rcases nextOccurrenceDescriptorPairs?_massBounded_exists mol beforeLeft beforeRight fuel M
          (beforeLeftTotal fuel lowerLe) (beforeRightTotal fuel lowerLe) pairs frontier.1 frontier.2
        with ⟨next, nextEq, nextBounded, nextBound⟩
      have nextFrontier : MassBoundedFrontier mol fuel M next :=
        ⟨nextBounded, le_trans nextBound frontier.2⟩
      cases next with
      | nil => simp [compareOccurrenceDescriptorRule, labelsEq, nextEq]; omega
      | cons pair rest =>
          have deeper := compareOccurrenceDescriptorRule_empty_eq_of_massBounded mol M bound
            beforeLeft beforeRight beforeLeftTotal beforeRightTotal stage fuel (pair :: rest)
            (by omega) nextFrontier
          simp [compareOccurrenceDescriptorRule, labelsEq, nextEq, deeper]; omega

/-! ## Actual production wrappers: the callback is *derived*, not assumed

The two wrappers below are the production endpoints.  They establish totality of the actual
`compareCursorBranchAt` / `compareOccurrenceDescriptorBranchAt` on the mass-bounded domain with **no
callback-totality hypothesis**: the captured sibling callback is the strictly lower comparator, whose
totality is the induction hypothesis, and the fuel is lifted by `support.mono` and mass saturation.
The frontier capacity is discharged by the caller's structural bound `1 + 2 * M ≤ cap`. -/

/-- **Actual callback closure (structural branch-at).**  The production `compareCursorBranchAt` is
total on the mass-bounded domain.  Every captured sibling callback call is at a strictly lower fuel
and is discharged by the induction hypothesis; nothing is assumed. -/
theorem compareCursorBranchAt_massBounded_exists (mol : RawMolecule) (M : ℕ)
    (hcap : 1 + 2 * M ≤ RawMolecule.defaultBranchWidthCap) :
    ∀ fuel left right,
      MassBoundedSupport mol fuel M left → MassBoundedSupport mol fuel M right →
      ∃ ordering, compareCursorBranchAt mol fuel .rule2 left right = some ordering := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right leftBounded rightBounded
      rcases leftBounded.1.label with ⟨leftLabel, leftEq⟩
      rcases rightBounded.1.label with ⟨rightLabel, rightEq⟩
      simp only [compareCursorBranchAt, RawMolecule.compareCanonicalNodeThrough?,
        RawMolecule.compareCanonicalNodeRule?, leftEq, rightEq]
      cases rule1aEq : compareCIPAtomicLabel leftLabel rightLabel <;> simp [rule1aEq]
      cases mol.compareCanonicalNodeRule .rule1b left.node right.node <;> simp
  | succ fuel ih =>
      intro left right leftBounded rightBounded
      let before := compareCursorBranchAt mol fuel .rule2
      have beforeTotal : MassBoundedCallback mol M fuel before :=
        fun k hk l r hl hr =>
          ih l r (MassBoundedSupport.mono mol hk hl) (MassBoundedSupport.mono mol hk hr)
      have singleBounded : ∀ pair, pair ∈ [(left, right)] →
          MassBoundedSupport mol (fuel + 1) M pair.1 ∧
          MassBoundedSupport mol (fuel + 1) M pair.2 := by
        intro pair member
        have pairEq : pair = (left, right) := by simpa using member
        rw [pairEq]
        exact ⟨leftBounded, rightBounded⟩
      have singlePotential : frontierPotential mol (fuel + 1) [(left, right)] ≤
          RawMolecule.defaultBranchWidthCap := by
        have hpair : pairPotential mol (fuel + 1) (left, right) ≤
            RawMolecule.defaultBranchWidthCap := by
          show 1 + cursorExpansionMass mol (fuel + 1) left +
            cursorExpansionMass mol (fuel + 1) right ≤ RawMolecule.defaultBranchWidthCap
          have leftMass := leftBounded.2
          have rightMass := rightBounded.2
          omega
        simpa [frontierPotential] using hpair
      have frontier : MassBoundedFrontier mol (fuel + 1) M [(left, right)] :=
        ⟨singleBounded, singlePotential⟩
      rcases compareCursorRule_massBounded_exists mol M fuel before beforeTotal .rule1a (fuel + 1)
          [(left, right)] (by omega) frontier with ⟨rule1a, rule1aEq⟩
      rcases compareCursorRule_massBounded_exists mol M fuel before beforeTotal .rule1b (fuel + 1)
          [(left, right)] (by omega) frontier with ⟨rule1b, rule1bEq⟩
      rcases compareCursorRule_massBounded_exists mol M fuel before beforeTotal .rule2 (fuel + 1)
          [(left, right)] (by omega) frontier with ⟨rule2, rule2Eq⟩
      exact ⟨(match rule1a with
        | .eq => (match rule1b with | .eq => rule2 | decision => decision)
        | decision => decision), by
        cases rule1a <;> cases rule1b <;> cases rule2 <;>
          simp [compareCursorBranchAt, before, rule1aEq, rule1bEq, rule2Eq]⟩

/-- **Actual production closure on the empty auxiliary state.**  `compareOccurrenceDescriptorBranchAt`
is total on the mass-bounded domain with the raw and staged sibling callbacks *derived* from the
induction hypothesis.  The arbitrary auxiliary `OccurrenceAuxState` is out of scope of this wrapper;
it is stated here for the empty state only. -/
theorem compareOccurrenceDescriptorBranchAt_massBounded_exists (mol : RawMolecule) (M : ℕ)
    (hcap : 1 + 2 * M ≤ RawMolecule.defaultBranchWidthCap) :
    ∀ fuel stage left right,
      MassBoundedSupport mol fuel M left → MassBoundedSupport mol fuel M right →
      ∃ ordering,
        compareOccurrenceDescriptorBranchAt mol [] fuel stage left right = some ordering := by
  intro fuel
  induction fuel with
  | zero =>
      intro stage left right leftBounded rightBounded
      rcases compareCursorBranchAt_massBounded_exists mol M hcap 0 left right leftBounded
          rightBounded with ⟨ordering, rawEq⟩
      have throughEq : mol.compareCanonicalNodeThrough? .rule2 left.node right.node = some ordering :=
        rawEq
      refine ⟨ordering, ?_⟩
      cases ordering with
      | lt => simp [compareOccurrenceDescriptorBranchAt, throughEq]
      | gt => simp [compareOccurrenceDescriptorBranchAt, throughEq]
      | eq => cases stage <;>
          simp [compareOccurrenceDescriptorBranchAt, throughEq, occurrenceNodePriority,
            OccurrenceAuxState.factAt?]
  | succ fuel ih =>
      intro stage left right leftBounded rightBounded
      rcases compareCursorBranchAt_massBounded_exists mol M hcap (fuel + 1) left right leftBounded
          rightBounded with ⟨ordering, rawEq⟩
      let beforeLeft := compareOccurrenceDescriptorBranchAt mol [] fuel stage.leftInternal
      let beforeRight := compareOccurrenceDescriptorBranchAt mol [] fuel stage.rightInternal
      have beforeLeftTotal : MassBoundedCallback mol M fuel beforeLeft :=
        fun k hk childLeft childRight childLeftBounded childRightBounded =>
          ih stage.leftInternal childLeft childRight
            (MassBoundedSupport.mono mol hk childLeftBounded)
            (MassBoundedSupport.mono mol hk childRightBounded)
      have beforeRightTotal : MassBoundedCallback mol M fuel beforeRight :=
        fun k hk childLeft childRight childLeftBounded childRightBounded =>
          ih stage.rightInternal childLeft childRight
            (MassBoundedSupport.mono mol hk childLeftBounded)
            (MassBoundedSupport.mono mol hk childRightBounded)
      have singleBounded : ∀ pair, pair ∈ [(left, right)] →
          MassBoundedSupport mol (fuel + 1) M pair.1 ∧
          MassBoundedSupport mol (fuel + 1) M pair.2 := by
        intro pair member
        have pairEq : pair = (left, right) := by simpa using member
        rw [pairEq]
        exact ⟨leftBounded, rightBounded⟩
      have singlePotential : frontierPotential mol (fuel + 1) [(left, right)] ≤
          RawMolecule.defaultBranchWidthCap := by
        have hpair : pairPotential mol (fuel + 1) (left, right) ≤
            RawMolecule.defaultBranchWidthCap := by
          show 1 + cursorExpansionMass mol (fuel + 1) left +
            cursorExpansionMass mol (fuel + 1) right ≤ RawMolecule.defaultBranchWidthCap
          have leftMass := leftBounded.2
          have rightMass := rightBounded.2
          omega
        simpa [frontierPotential] using hpair
      have frontier : MassBoundedFrontier mol (fuel + 1) M [(left, right)] :=
        ⟨singleBounded, singlePotential⟩
      have compareEq : ∀ selected,
          compareOccurrenceDescriptorRule mol [] beforeLeft beforeRight selected (fuel + 1)
            [(left, right)] = some .eq := by
        intro selected
        exact compareOccurrenceDescriptorRule_empty_eq_of_massBounded mol M fuel beforeLeft
          beforeRight beforeLeftTotal beforeRightTotal selected (fuel + 1) [(left, right)]
          (by omega) frontier
      refine ⟨ordering, ?_⟩
      cases ordering with
      | lt => simp [compareOccurrenceDescriptorBranchAt, rawEq]
      | gt => simp [compareOccurrenceDescriptorBranchAt, rawEq]
      | eq => cases stage <;>
          simp [compareOccurrenceDescriptorBranchAt, rawEq, beforeLeft, beforeRight, compareEq]

/-- The mass-bounded closure reaches fuel ten, where the old ternary gate `3 ^ fuel ≤ cap` already
fails.  This is the generic fuel-ten endpoint. The following closed graph fixture discharges its
support and mass hypotheses through a reflected finite check. -/
theorem compareCursorBranchAt_massBounded_ten (mol : RawMolecule) {M : ℕ}
    (hcap : 1 + 2 * M ≤ RawMolecule.defaultBranchWidthCap)
    {left right : CanonicalRerootCursor}
    (leftBounded : MassBoundedSupport mol 10 M left)
    (rightBounded : MassBoundedSupport mol 10 M right) :
    ∃ ordering, compareCursorBranchAt mol 10 .rule2 left right = some ordering :=
  compareCursorBranchAt_massBounded_exists mol M hcap 10 left right leftBounded rightBounded

/-! ## Closed genuinely branching fuel-ten comparison

A thirteen-carbon graph supplies a descending ligand cursor with an actual branch at atom five.
The finite support check accepts fuel ten and refuses fuel nine. Its expansion mass is bounded
by thirty, so the mass theorem derives success of the actual production self-comparison at fuel
ten, where the old global ternary envelope fails. This is a represented graph regression, not a
source-reviewed stereogenic molecule or universal chemical-admission witness. -/

private def fixtureAtom (element : Element) : AtomSpec := { element := element }

private def fixtureBond (source target : ℕ) : RawBond :=
  { source := source, target := target, kind := .single }

/-- A thirteen-carbon chain with a methyl branch at atom five. -/
private def fixtureMolecule : RawMolecule :=
  { atoms :=
      [fixtureAtom .C, fixtureAtom .C, fixtureAtom .C, fixtureAtom .C, fixtureAtom .C,
        fixtureAtom .C, fixtureAtom .C, fixtureAtom .C, fixtureAtom .C, fixtureAtom .C,
        fixtureAtom .C, fixtureAtom .C, fixtureAtom .C],
    bonds :=
      [fixtureBond 0 1, fixtureBond 1 2, fixtureBond 2 3, fixtureBond 3 4, fixtureBond 4 5,
        fixtureBond 5 6, fixtureBond 6 7, fixtureBond 7 8, fixtureBond 8 9, fixtureBond 9 10,
        fixtureBond 10 11, fixtureBond 5 12] }

theorem fixtureMolecule_atomCount : fixtureMolecule.atomCount = 13 := by decide

/-- The real descending ligand occurrence from center zero into atom one. -/
private def fixtureLigandCursor : CanonicalRerootCursor :=
  { node := { atom := 1, parent := 0, history := [1, 0], provenance := .realAtom },
    previous? := some (canonicalCenterRoot 0) }

private def fixtureBranchCursor : CanonicalRerootCursor :=
  { node := { atom := 5, parent := 4, history := [5, 4, 3, 2, 1, 0], provenance := .realAtom },
    previous? := some { atom := 4, parent := 3, history := [4, 3, 2, 1, 0], provenance := .realAtom } }

/-- The represented ligand contains a real two-child branch, not only a linear spine. -/
theorem fixtureBranch_two_children :
    (fixtureBranchCursor.children fixtureMolecule).length = 2 := by decide

theorem fixtureLigand_support_check_ten :
    branchingCursorSupport? fixtureMolecule 10 fixtureLigandCursor = true := by decide

theorem fixtureLigand_support_check_nine_refused :
    branchingCursorSupport? fixtureMolecule 9 fixtureLigandCursor = false := by decide

theorem fixtureLigand_mass_le_thirty :
    cursorExpansionMass fixtureMolecule 10 fixtureLigandCursor ≤ 30 := by decide

theorem fixtureLigand_massBounded_ten :
    MassBoundedSupport fixtureMolecule 10 30 fixtureLigandCursor :=
  ⟨BranchingCursorSupport.of_check fixtureLigand_support_check_ten,
    fixtureLigand_mass_le_thirty⟩

/-- Closed actual comparator success, with all support, mass and callback obligations derived. -/
theorem fixtureLigand_production_ten_exists :
    ∃ ordering, compareCursorBranchAt fixtureMolecule 10 .rule2
      fixtureLigandCursor fixtureLigandCursor = some ordering :=
  compareCursorBranchAt_massBounded_ten fixtureMolecule (M := 30) (by decide)
    fixtureLigand_massBounded_ten fixtureLigand_massBounded_ten

/-- No auxiliary descriptor facts are invented for this closed occurrence comparison. -/
theorem fixtureLigand_production_ten_eq :
    compareCursorBranchAt fixtureMolecule 10 .rule2
      fixtureLigandCursor fixtureLigandCursor = some .eq := by decide

theorem fixtureLigand_occurrence_ten_exists :
    ∃ ordering, compareOccurrenceDescriptorBranchAt fixtureMolecule [] 10 (.rule5 .R .R)
      fixtureLigandCursor fixtureLigandCursor = some ordering :=
  compareOccurrenceDescriptorBranchAt_massBounded_exists fixtureMolecule 30 (by decide)
    10 (.rule5 .R .R) fixtureLigandCursor fixtureLigandCursor
    fixtureLigand_massBounded_ten fixtureLigand_massBounded_ten

end

end TetraStereo.UniversalProof.ProductionPrunedFrontierCapacityProofs
