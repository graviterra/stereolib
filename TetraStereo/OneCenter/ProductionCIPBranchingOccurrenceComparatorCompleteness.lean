import TetraStereo.OneCenter.ProductionCIPBranchingComparatorCompleteness
import TetraStereo.OneCenter.ProductionCIPLinearOccurrenceComparatorCompleteness

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.ProductionCIPBranchingOccurrenceComparatorCompleteness

/-! Structural completeness of the full production Rules-1--5 occurrence comparator on bounded,
acyclic, branching ligand trees with empty auxiliary descriptor state. -/

open RawMolecule
open ProductionCIPRerootComparatorLaws
open ProductionCIPLinearOccurrenceComparatorCompleteness

theorem compareOccurrenceDescriptorPairLabels_empty_eq (stage : RawDescriptorRuleStage) :
    ∀ pairs : List BranchingCursorPair,
      compareOccurrenceDescriptorPairLabels [] stage pairs = .eq
  | [] => rfl
  | _ :: rest => by
      simp [compareOccurrenceDescriptorPairLabels, occurrenceNodePriority,
        OccurrenceAuxState.factAt?, compareOccurrenceDescriptorPairLabels_empty_eq stage rest]

theorem nextOccurrenceDescriptorPairs?_exists_of_branching_support (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : Nat)
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
      ∃ next,
        nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs = some next ∧
        (∀ pair, pair ∈ next →
          BranchingCursorSupport mol fuel pair.1 ∧
          BranchingCursorSupport mol fuel pair.2) ∧
        next.length ≤ 3 * pairs.length
  | [], _ => ⟨[], rfl, by simp, by simp⟩
  | pair :: pairs, support => by
      have headSupport := support pair (by simp)
      have tailSupport : ∀ candidate, candidate ∈ pairs →
          BranchingCursorSupport mol (fuel + 1) candidate.1 ∧
          BranchingCursorSupport mol (fuel + 1) candidate.2 := by
        intro candidate member
        exact support candidate (by simp [member])
      rcases nextOccurrenceDescriptorPairs?_exists_of_branching_support mol
          beforeLeft beforeRight fuel beforeLeftTotal beforeRightTotal pairs tailSupport with
        ⟨rest, restEq, restSupport, restLength⟩
      by_cases bothTerminal :
          cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true
      · refine ⟨rest, ?_, restSupport, ?_⟩
        · simp [nextOccurrenceDescriptorPairs?, restEq, bothTerminal]
        · simp only [List.length_cons]
          omega
      · rcases rankedCursorChildren?_exists_of_branching_support mol beforeLeft fuel pair.1
            headSupport.1 beforeLeftTotal with
          ⟨left, leftEq, leftLength, leftSupport⟩
        rcases rankedCursorChildren?_exists_of_branching_support mol beforeRight fuel pair.2
            headSupport.2 beforeRightTotal with
          ⟨right, rightEq, rightLength, rightSupport⟩
        refine ⟨left.zip right ++ rest, ?_, ?_, ?_⟩
        · simp [nextOccurrenceDescriptorPairs?, restEq, bothTerminal, leftEq, rightEq]
        · intro candidate member
          rcases List.mem_append.mp member with zipped | tail
          · have components := List.of_mem_zip zipped
            exact ⟨leftSupport candidate.1 components.1,
              rightSupport candidate.2 components.2⟩
          · exact restSupport candidate tail
        · simp [List.length_zip, leftLength, rightLength]
          omega

theorem branchingFrontier_nextOccurrence_exists
    {mol : RawMolecule} {fuel rankFuel : Nat} {pairs : List BranchingCursorPair}
    (support : BranchingFrontierSupport mol (fuel + 1) pairs)
    (fuelLe : fuel ≤ rankFuel)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeLeftTotal : ∀ left right,
      BranchingCursorSupport mol rankFuel left → BranchingCursorSupport mol rankFuel right →
      ∃ ordering, beforeLeft left right = some ordering)
    (beforeRightTotal : ∀ left right,
      BranchingCursorSupport mol rankFuel left → BranchingCursorSupport mol rankFuel right →
      ∃ ordering, beforeRight left right = some ordering) :
    ∃ next, nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs = some next ∧
      BranchingFrontierSupport mol fuel next := by
  have localLeftTotal : ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, beforeLeft left right = some ordering := by
    intro left right leftSupport rightSupport
    exact beforeLeftTotal left right (leftSupport.mono fuelLe) (rightSupport.mono fuelLe)
  have localRightTotal : ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, beforeRight left right = some ordering := by
    intro left right leftSupport rightSupport
    exact beforeRightTotal left right (leftSupport.mono fuelLe) (rightSupport.mono fuelLe)
  rcases nextOccurrenceDescriptorPairs?_exists_of_branching_support mol beforeLeft beforeRight
      fuel localLeftTotal localRightTotal pairs support.cursors with
    ⟨next, nextEq, nextSupport, nextLength⟩
  refine ⟨next, nextEq, ⟨nextSupport, ?_⟩⟩
  calc
    next.length * 3 ^ fuel ≤ (3 * pairs.length) * 3 ^ fuel :=
      Nat.mul_le_mul_right (3 ^ fuel) nextLength
    _ = pairs.length * 3 ^ (fuel + 1) := by
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ RawMolecule.defaultBranchWidthCap := support.budget

theorem branchingFrontier_nextOccurrence_zero_eq_nil
    {mol : RawMolecule} {pairs : List BranchingCursorPair}
    (support : BranchingFrontierSupport mol 0 pairs)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs = some [] := by
  exact nextOccurrenceDescriptorPairs?_terminal_list_eq_nil mol beforeLeft beforeRight pairs (by
    intro pair member
    have pairSupport := support.cursors pair member
    exact ⟨pairSupport.1.zero_terminal, pairSupport.2.zero_terminal⟩)

theorem compareOccurrenceDescriptorRule_branching_empty_eq (mol : RawMolecule)
    (rankFuel : Nat)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeLeftTotal : ∀ left right,
      BranchingCursorSupport mol rankFuel left → BranchingCursorSupport mol rankFuel right →
      ∃ ordering, beforeLeft left right = some ordering)
    (beforeRightTotal : ∀ left right,
      BranchingCursorSupport mol rankFuel left → BranchingCursorSupport mol rankFuel right →
      ∃ ordering, beforeRight left right = some ordering)
    (stage : RawDescriptorRuleStage) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 → BranchingFrontierSupport mol fuel pairs →
      compareOccurrenceDescriptorRule mol [] beforeLeft beforeRight stage fuel pairs = some .eq
  | 0, pairs, _, support => by
      have labelsEq := compareOccurrenceDescriptorPairLabels_empty_eq stage pairs
      have nextEq := branchingFrontier_nextOccurrence_zero_eq_nil support beforeLeft beforeRight
      have withinCap := support.length_le_cap
      simp [compareOccurrenceDescriptorRule, labelsEq, nextEq]
      omega
  | fuel + 1, pairs, fuelLe, support => by
      have labelsEq := compareOccurrenceDescriptorPairLabels_empty_eq stage pairs
      have withinCap := support.length_le_cap
      have lowerLe : fuel ≤ rankFuel := by omega
      rcases branchingFrontier_nextOccurrence_exists support lowerLe beforeLeft beforeRight
          beforeLeftTotal beforeRightTotal with ⟨next, nextEq, nextSupport⟩
      cases next with
      | nil =>
          simp [compareOccurrenceDescriptorRule, labelsEq, nextEq]
          omega
      | cons pair rest =>
          have deeper := compareOccurrenceDescriptorRule_branching_empty_eq mol rankFuel
            beforeLeft beforeRight beforeLeftTotal beforeRightTotal stage fuel (pair :: rest)
              (by omega) nextSupport
          simp [compareOccurrenceDescriptorRule, labelsEq, nextEq, deeper]
          omega

theorem compareOccurrenceDescriptorBranchAt_branching_empty_eq_raw (mol : RawMolecule) :
    ∀ fuel stage left right,
      3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap →
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering,
        compareCursorBranchAt mol fuel .rule2 left right = some ordering ∧
        compareOccurrenceDescriptorBranchAt mol [] fuel stage left right = some ordering
  | 0, stage, left, right, width, leftSupport, rightSupport => by
      rcases compareCursorBranchAt_branching_supported_exists mol 0 left right width
          leftSupport rightSupport with ⟨ordering, rawEq⟩
      have throughEq : mol.compareCanonicalNodeThrough? .rule2 left.node right.node =
          some ordering := rawEq
      refine ⟨ordering, rawEq, ?_⟩
      cases ordering with
      | lt => simp [compareOccurrenceDescriptorBranchAt, throughEq]
      | gt => simp [compareOccurrenceDescriptorBranchAt, throughEq]
      | eq =>
          cases stage <;>
            simp [compareOccurrenceDescriptorBranchAt, throughEq, occurrenceNodePriority,
              OccurrenceAuxState.factAt?]
  | fuel + 1, stage, left, right, width, leftSupport, rightSupport => by
      rcases compareCursorBranchAt_branching_supported_exists mol (fuel + 1) left right width
          leftSupport rightSupport with ⟨ordering, rawEq⟩
      have lowerWidth : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap := by
        calc
          3 ^ fuel ≤ 3 ^ (fuel + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          _ ≤ RawMolecule.defaultBranchWidthCap := width
      let beforeLeft := compareOccurrenceDescriptorBranchAt mol [] fuel stage.leftInternal
      let beforeRight := compareOccurrenceDescriptorBranchAt mol [] fuel stage.rightInternal
      have beforeLeftTotal : ∀ childLeft childRight,
          BranchingCursorSupport mol fuel childLeft →
          BranchingCursorSupport mol fuel childRight →
          ∃ decision, beforeLeft childLeft childRight = some decision := by
        intro childLeft childRight childLeftSupport childRightSupport
        rcases compareOccurrenceDescriptorBranchAt_branching_empty_eq_raw mol fuel
            stage.leftInternal childLeft childRight lowerWidth childLeftSupport childRightSupport with
          ⟨decision, _, descriptorEq⟩
        exact ⟨decision, descriptorEq⟩
      have beforeRightTotal : ∀ childLeft childRight,
          BranchingCursorSupport mol fuel childLeft →
          BranchingCursorSupport mol fuel childRight →
          ∃ decision, beforeRight childLeft childRight = some decision := by
        intro childLeft childRight childLeftSupport childRightSupport
        rcases compareOccurrenceDescriptorBranchAt_branching_empty_eq_raw mol fuel
            stage.rightInternal childLeft childRight lowerWidth childLeftSupport childRightSupport
          with ⟨decision, _, descriptorEq⟩
        exact ⟨decision, descriptorEq⟩
      have frontier : BranchingFrontierSupport mol (fuel + 1) [(left, right)] :=
        ⟨by simpa using And.intro leftSupport rightSupport, by simpa using width⟩
      have compareEq : ∀ selected,
          compareOccurrenceDescriptorRule mol [] beforeLeft beforeRight selected (fuel + 1)
            [(left, right)] = some .eq := by
        intro selected
        exact compareOccurrenceDescriptorRule_branching_empty_eq mol fuel beforeLeft beforeRight
          beforeLeftTotal beforeRightTotal selected (fuel + 1) [(left, right)] (by omega) frontier
      refine ⟨ordering, rawEq, ?_⟩
      cases ordering with
      | lt => simp [compareOccurrenceDescriptorBranchAt, rawEq]
      | gt => simp [compareOccurrenceDescriptorBranchAt, rawEq]
      | eq =>
          cases stage <;>
            simp [compareOccurrenceDescriptorBranchAt, rawEq, beforeLeft, beforeRight, compareEq]

theorem compareOccurrenceDescriptorAtTiedRoot?_branching_empty_eq (mol : RawMolecule)
    (fuel : Nat) (stage : RawDescriptorRuleStage)
    (left right : CanonicalRerootCursor)
    (width : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap)
    (leftSupport : BranchingCursorSupport mol fuel left)
    (rightSupport : BranchingCursorSupport mol fuel right) :
    compareOccurrenceDescriptorAtTiedRoot? mol [] fuel stage left right = some .eq := by
  let beforeLeft := compareOccurrenceDescriptorBranchAt mol [] fuel stage.leftInternal
  let beforeRight := compareOccurrenceDescriptorBranchAt mol [] fuel stage.rightInternal
  have beforeLeftTotal : ∀ childLeft childRight,
      BranchingCursorSupport mol fuel childLeft → BranchingCursorSupport mol fuel childRight →
      ∃ decision, beforeLeft childLeft childRight = some decision := by
    intro childLeft childRight childLeftSupport childRightSupport
    rcases compareOccurrenceDescriptorBranchAt_branching_empty_eq_raw mol fuel
        stage.leftInternal childLeft childRight width childLeftSupport childRightSupport with
      ⟨decision, _, descriptorEq⟩
    exact ⟨decision, descriptorEq⟩
  have beforeRightTotal : ∀ childLeft childRight,
      BranchingCursorSupport mol fuel childLeft → BranchingCursorSupport mol fuel childRight →
      ∃ decision, beforeRight childLeft childRight = some decision := by
    intro childLeft childRight childLeftSupport childRightSupport
    rcases compareOccurrenceDescriptorBranchAt_branching_empty_eq_raw mol fuel
        stage.rightInternal childLeft childRight width childLeftSupport childRightSupport with
      ⟨decision, _, descriptorEq⟩
    exact ⟨decision, descriptorEq⟩
  have frontier : BranchingFrontierSupport mol fuel [(left, right)] :=
    ⟨by simpa using And.intro leftSupport rightSupport, by simpa using width⟩
  have compareEq : ∀ selected,
      compareOccurrenceDescriptorRule mol [] beforeLeft beforeRight selected fuel [(left, right)] =
        some .eq := by
    intro selected
    exact compareOccurrenceDescriptorRule_branching_empty_eq mol fuel beforeLeft beforeRight
      beforeLeftTotal beforeRightTotal selected fuel [(left, right)] (by omega) frontier
  cases stage <;>
    simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, compareEq]

inductive BranchingCursorAcyclic (mol : RawMolecule) (cycleFuel : Nat) :
    CanonicalRerootCursor → Prop
  | terminal (cursor : CanonicalRerootCursor)
      (acyclic : mol.atomLiesInCycle cycleFuel cursor.node.atom = false)
      (isTerminal : cursorTerminal mol cursor = true) :
      BranchingCursorAcyclic mol cycleFuel cursor
  | branch (cursor : CanonicalRerootCursor) (children : List CanonicalRerootCursor)
      (acyclic : mol.atomLiesInCycle cycleFuel cursor.node.atom = false)
      (childrenEq : cursor.children mol = children)
      (childrenAcyclic : ∀ child, child ∈ children →
        BranchingCursorAcyclic mol cycleFuel child) :
      BranchingCursorAcyclic mol cycleFuel cursor

theorem BranchingCursorAcyclic.root {mol : RawMolecule} {cycleFuel : Nat}
    {cursor : CanonicalRerootCursor} (acyclic : BranchingCursorAcyclic mol cycleFuel cursor) :
    mol.atomLiesInCycle cycleFuel cursor.node.atom = false := by
  cases acyclic with
  | terminal _ root _ => exact root
  | branch _ _ root _ _ => exact root

theorem LinearCursorAcyclic.toBranching {mol : RawMolecule} {cycleFuel : Nat}
    {cursor : CanonicalRerootCursor} (acyclic : LinearCursorAcyclic mol cycleFuel cursor) :
    BranchingCursorAcyclic mol cycleFuel cursor := by
  induction acyclic with
  | terminal cursor root terminal => exact .terminal cursor root terminal
  | step cursor child root children childAcyclic ih =>
      exact .branch cursor [child] root children (by
        intro candidate member
        simp at member
        subst candidate
        exact ih)

structure AcyclicBranchingCursorSupport (mol : RawMolecule) (fuel : Nat)
    (cursor : CanonicalRerootCursor) : Prop where
  branching : BranchingCursorSupport mol fuel cursor
  acyclic : BranchingCursorAcyclic mol fuel cursor

theorem compareOccurrenceBranches?_acyclic_branching_empty_eq_raw
    (mol : RawMolecule) (fuel : Nat) (left right : CanonicalRerootCursor)
    (width : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap)
    (leftSupport : AcyclicBranchingCursorSupport mol fuel left)
    (rightSupport : AcyclicBranchingCursorSupport mol fuel right) :
    ∃ ordering,
      compareCursorBranchAt mol fuel .rule2 left right = some ordering ∧
      compareOccurrenceBranches? mol [] fuel left right = some { ordering := ordering } := by
  rcases compareCursorBranchAt_branching_supported_exists mol fuel left right width
      leftSupport.branching rightSupport.branching with ⟨ordering, rawEq⟩
  have gateFalse : occurrenceRootsProvedAutomorphic mol fuel left right ordering = false := by
    simp [occurrenceRootsProvedAutomorphic, leftSupport.acyclic.root]
  have constitutionalEq : certifiedConstitutionalStage? mol fuel left right = some ordering := by
    simp [certifiedConstitutionalStage?, rawEq, gateFalse]
  refine ⟨ordering, rawEq, ?_⟩
  cases ordering with
  | lt => simp [compareOccurrenceBranches?, constitutionalEq]
  | gt => simp [compareOccurrenceBranches?, constitutionalEq]
  | eq =>
      have rule4aEq := compareOccurrenceDescriptorAtTiedRoot?_branching_empty_eq
        mol fuel .rule4a left right width leftSupport.branching rightSupport.branching
      have rule5REq := compareOccurrenceDescriptorAtTiedRoot?_branching_empty_eq
        mol fuel (.rule5 .R .R) left right width leftSupport.branching rightSupport.branching
      have rule5SEq := compareOccurrenceDescriptorAtTiedRoot?_branching_empty_eq
        mol fuel (.rule5 .S .S) left right width leftSupport.branching rightSupport.branching
      have rule4bEq : compareOccurrenceRule4b? mol [] fuel left right = some .eq := by
        simp [compareOccurrenceRule4b?, occurrenceRule4bReferences_empty]
      have rule5Eq : compareOccurrenceRule5? mol [] fuel left right =
          some { ordering := .eq, pseudo := false } := by
        simp [compareOccurrenceRule5?, rule5REq, rule5SEq]
      simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq, rule4bEq, rule5Eq]











/-- The production comparator is definitionally partial beyond the width cap: any frontier longer
than `defaultBranchWidthCap` is refused, so a branching "completeness" statement whose frontier can
exceed the cap cannot be completed by this executable. -/
theorem compareOccurrenceDescriptorRule_eq_none_of_cap_lt (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (stage : RawDescriptorRuleStage) :
    ∀ fuel pairs, RawMolecule.defaultBranchWidthCap < pairs.length →
      compareOccurrenceDescriptorRule mol state beforeLeft beforeRight stage fuel pairs = none
  | 0, pairs, large => by
      simp [compareOccurrenceDescriptorRule, if_pos large]
  | fuel + 1, pairs, large => by
      simp [compareOccurrenceDescriptorRule, if_pos large]

/-- The ternary frontier envelope of the branching frames bounds the usable depth by the concrete
constant cap: `3 ^ fuel ≤ 20000` forces `fuel ≤ 9`.  The uniform molecule-size depth
`2 * atomCount + 1` exceeds this ceiling once `atomCount ≥ 5`, so the bounded branching path is not
the arbitrary-finite-graph route. -/
theorem ternary_envelope_depth_le_nine {fuel : Nat}
    (envelope : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap) : fuel ≤ 9 := by
  by_contra h
  have h10 : 10 ≤ fuel := by omega
  have hpow : 3 ^ 10 ≤ 3 ^ fuel := Nat.pow_le_pow_right (by norm_num) h10
  have hcap : 3 ^ 10 ≤ RawMolecule.defaultBranchWidthCap := le_trans hpow envelope
  exact absurd hcap (by norm_num [RawMolecule.defaultBranchWidthCap])

/-- Molecule-level well-founded certificate for the production *branching* (`≤ 3` forward slots)
support.  This is the branching counterpart of the authoritative `CursorTerminationRanking`: it
replaces the previously assumed `BranchingCursorSupport` by finite, decreasing structure.  The
`label` field records the one genuinely partial production observation (`canonicalRule1aLabel?`,
whose `multipleBondDuplicate` branch delegates to the mancude averaging `mancudeRule1aLabel?`). -/
structure BranchingCursorTerminationRanking (mol : RawMolecule) where
  eligible : CanonicalRerootCursor → Prop
  height : CanonicalRerootCursor → Nat
  label : ∀ cursor : CanonicalRerootCursor, eligible cursor →
    ∃ value, mol.canonicalRule1aLabel? cursor.node = some value
  zero_terminal : ∀ cursor : CanonicalRerootCursor,
    eligible cursor → height cursor = 0 → cursorTerminal mol cursor = true
  local_width : ∀ cursor : CanonicalRerootCursor,
    eligible cursor → (cursor.children mol).length ≤ 3
  child_eligible : ∀ cursor child : CanonicalRerootCursor,
    eligible cursor → child ∈ cursor.children mol → eligible child
  child_decreases : ∀ cursor child : CanonicalRerootCursor,
    eligible cursor → child ∈ cursor.children mol → height child < height cursor

namespace BranchingCursorTerminationRanking

/-- A decreasing molecule-level height and the local ternary width construct recursive branching
support at exactly the certified height. -/
theorem branchingSupport {mol : RawMolecule} (ranking : BranchingCursorTerminationRanking mol)
    (cursor : CanonicalRerootCursor) (eligible : ranking.eligible cursor) :
    BranchingCursorSupport mol (ranking.height cursor) cursor := by
  by_cases terminal : cursorTerminal mol cursor = true
  · exact .terminal (ranking.height cursor) cursor (ranking.label cursor eligible) terminal
  · cases heightEq : ranking.height cursor with
    | zero =>
        exact False.elim (terminal (ranking.zero_terminal cursor eligible heightEq))
    | succ height =>
        apply BranchingCursorSupport.branch height cursor (cursor.children mol)
          (ranking.label cursor eligible) rfl (ranking.local_width cursor eligible)
        intro child member
        have childEligible := ranking.child_eligible cursor child eligible member
        have childDecreases := ranking.child_decreases cursor child eligible member
        have childSupport := ranking.branchingSupport child childEligible
        exact childSupport.mono (by omega)
termination_by ranking.height cursor

/-- Any caller fuel covering the certified molecular height supplies recursive branching support. -/
theorem branchingSupport_of_height_le {mol : RawMolecule}
    (ranking : BranchingCursorTerminationRanking mol) (fuel : Nat)
    (cursor : CanonicalRerootCursor) (eligible : ranking.eligible cursor)
    (covered : ranking.height cursor ≤ fuel) :
    BranchingCursorSupport mol fuel cursor :=
  (ranking.branchingSupport cursor eligible).mono covered

end BranchingCursorTerminationRanking

/-- A single supported pair at a depth below the ternary envelope forms a supported frontier.  This
extracts the construction the existing proofs perform inline, so that finite singleton frontier
support is available as a reusable object rather than only alongside a raw comparison. -/
theorem branchingFrontierSupport_singleton (mol : RawMolecule) (fuel : Nat)
    (left right : CanonicalRerootCursor)
    (envelope : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap)
    (leftSupport : BranchingCursorSupport mol fuel left)
    (rightSupport : BranchingCursorSupport mol fuel right) :
    BranchingFrontierSupport mol fuel [(left, right)] where
  cursors := by
    intro pair member
    have pairEq : pair = (left, right) := by simpa using member
    subst pair
    exact ⟨leftSupport, rightSupport⟩
  budget := by
    simpa using envelope

end TetraStereo.OneCenter.ProductionCIPBranchingOccurrenceComparatorCompleteness
