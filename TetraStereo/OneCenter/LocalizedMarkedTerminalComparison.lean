import TetraStereo.OneCenter.LocalizedMarkedTerminalCursor
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Exact unrestricted comparison of terminal ligands on generated promotion states

Real terminal atoms with equal Z, mass and stored comparison depth tie through every ordinary rule. Rule 6 compares
exactly the two promotion bits: it ties unless one of those terminal atoms is the reference.
The generated-state endpoint derives terminal cursors and empty auxiliary reads from the actual
graph and recursion. Real provenance, equal molecular atomic number/mass and equal stored depth remain explicit.
The depth condition matters for the unframed backend, especially at incoming-parent slots.
No comparison success, desired ordering or supplied auxiliary label is assumed.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedTerminalComparison

open LocalizedMarkedOperationEvaluator LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors LocalizedMarkedTerminalReferenceScope
open LocalizedMarkedTerminalCursor
open AuthoritativeCIPOccurrenceDescriptorComparatorLaws
open LocalizedGenericMarkedRecalculation (Geometry)

abbrev Node := RawMolecule.CanonicalBranchNode

def promotionBitsDecision (mark left right : Nat) : Rule6TrackedDecision :=
  let ordering := compare (if left = mark then 1 else 0) (if right = mark then 1 else 0)
  { ordering := ordering, pseudo := ordering != .eq }

theorem constitutional_tie (mol : RawMolecule) (fuel : Nat) (left right : CanonicalRerootCursor)
    (leftTerminal : cursorTerminal mol left = true) (rightTerminal : cursorTerminal mol right = true)
    (leftReal : left.node.provenance = .realAtom) (rightReal : right.node.provenance = .realAtom)
    (sameZ : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom)
    (sameDepth : left.node.depth = right.node.depth)
    (sameMass : mol.atomMassAt left.node.atom = mol.atomMassAt right.node.atom) :
    compareCursorBranchAtAuthoritative? mol fuel .rule2 left right = some .eq := by
  have leftChildren := cursor_children_eq_nil_of_terminal mol left leftTerminal
  have rightChildren := cursor_children_eq_nil_of_terminal mol right rightTerminal
  cases fuel <;>
    simp [compareCursorBranchAtAuthoritative?, RawMolecule.compareCanonicalNodeThroughAuthoritative?,
      RawMolecule.compareCanonicalNodeRuleAuthoritative?, RawMolecule.canonicalRule1aLabelAuthoritative?,
      RawMolecule.compareCanonicalNodeRule, RawMolecule.CanonicalBranchNode.rule1bRootDistance,
      compareCursorRuleAuthoritative?, compareCursorPairLabelsAuthoritative?,
      nextCursorPairsAuthoritative?, cursorTerminal, leftChildren, rightChildren,
      leftReal, rightReal, sameZ, sameDepth, sameMass]

theorem ordinary_tie (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor)
    (leftTerminal : cursorTerminal mol left = true) (rightTerminal : cursorTerminal mol right = true)
    (leftReal : left.node.provenance = .realAtom) (rightReal : right.node.provenance = .realAtom)
    (sameZ : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom)
    (sameDepth : left.node.depth = right.node.depth)
    (sameMass : mol.atomMassAt left.node.atom = mol.atomMassAt right.node.atom)
    (leftSilent : state.factAt? left.node = none) (rightSilent : state.factAt? right.node = none) :
    compareOccurrenceBranchesUnrestrictedAuthoritative? mol state fuel left right =
      some { ordering := .eq } := by
  have constitutional := constitutional_tie mol fuel left right leftTerminal rightTerminal
    leftReal rightReal sameZ sameDepth sameMass
  have stage := fun s => compareOccurrenceDescriptorAtTiedRootAuthoritative?_terminal_silent_eq
    mol state fuel s left right leftTerminal rightTerminal leftSilent rightSilent
  have referencesL := occurrenceRule4bReferences_terminal_silent_eq_nil mol state fuel left
    leftTerminal leftSilent
  have referencesR := occurrenceRule4bReferences_terminal_silent_eq_nil mol state fuel right
    rightTerminal rightSilent
  have c := compareOccurrenceRule4cWithWitnessAuthoritative?_terminal_silent_eq mol state fuel
    (compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel .rule4c)
    left right leftTerminal rightTerminal leftSilent rightSilent
  cases lower : state.any (fun fact => !fact.uppercase) <;>
    simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, constitutional, stage,
      compareOccurrenceRule4bUnrestrictedAuthoritative?, referencesL, referencesR,
      lower, c, compareOccurrenceRule5Authoritative?]

/-- Exact promotion-bit result, also covering promotion of either terminal ligand itself. -/
theorem promoted_bits (mol : RawMolecule) (state : OccurrenceAuxState) (fuel mark : Nat)
    (left right : CanonicalRerootCursor)
    (leftTerminal : cursorTerminal mol left = true) (rightTerminal : cursorTerminal mol right = true)
    (leftReal : left.node.provenance = .realAtom) (rightReal : right.node.provenance = .realAtom)
    (sameZ : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom)
    (sameDepth : left.node.depth = right.node.depth)
    (sameMass : mol.atomMassAt left.node.atom = mol.atomMassAt right.node.atom)
    (leftSilent : state.factAt? left.node = none) (rightSilent : state.factAt? right.node = none) :
    compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state mark fuel left right =
      some (promotionBitsDecision mark left.node.atom right.node.atom) := by
  have ordinary := fun n => ordinary_tie mol state n left right leftTerminal rightTerminal
    leftReal rightReal sameZ sameDepth sameMass leftSilent rightSilent
  have lc := cursor_children_eq_nil_of_terminal mol left leftTerminal
  have rc := cursor_children_eq_nil_of_terminal mol right rightTerminal
  cases fuel <;> by_cases l : left.node.atom = mark <;> by_cases r : right.node.atom = mark <;>
    simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, ordinary,
      compareOccurrenceRule6Authoritative, compareOccurrenceRule6PairLabels,
      nextOccurrenceDescriptorPairsAuthoritative?, cursorTerminal, lc, rc, l, r,
      promotionBitsDecision]

/-- The complete actual comparison on generated snapshots reduces to promotion bits. -/
theorem generated_promoted_bits (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (depth fuel : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (source target : Node) (sourceReached : Reached mol source) (targetReached : Reached mol target)
    (mark : Nat) (left right : CanonicalRerootCursor)
    (leftSlot : left ∈ occurrenceLigandCursors mol target)
    (rightSlot : right ∈ occurrenceLigandCursors mol target)
    (leftTerminal : TerminalNeighbor mol target.atom left.node.atom)
    (rightTerminal : TerminalNeighbor mol target.atom right.node.atom)
    (leftReal : left.node.provenance = .realAtom) (rightReal : right.node.provenance = .realAtom)
    (sameZ : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom)
    (sameDepth : left.node.depth = right.node.depth)
    (sameMass : mol.atomMassAt left.node.atom = mol.atomMassAt right.node.atom) :
    compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol
      (underWith mol ops geom state source (facts mol ops depth) mark) mark fuel left right =
      some (promotionBitsDecision mark left.node.atom right.node.atom) := by
  obtain ⟨lr, lt⟩ := ligand_terminal mol wellFormed single unique target targetReached
    left leftSlot target.atom leftTerminal
  obtain ⟨rr, rt⟩ := ligand_terminal mol wellFormed single unique target targetReached
    right rightSlot target.atom rightTerminal
  exact promoted_bits mol _ fuel mark left right lt rt leftReal rightReal sameZ sameDepth sameMass
    (snapshot_factAt_terminal_none mol ops wellFormed single unique depth geom state source
      sourceReached mark left.node lr target.atom leftTerminal)
    (snapshot_factAt_terminal_none mol ops wellFormed single unique depth geom state source
      sourceReached mark right.node rr target.atom rightTerminal)

theorem outward_depth_eq (mol : RawMolecule) (target : Node) (left right : CanonicalRerootCursor)
    (leftChild : left.node ∈ mol.canonicalChildren target)
    (rightChild : right.node ∈ mol.canonicalChildren target) :
    left.node.depth = right.node.depth := by
  simp only [RawMolecule.CanonicalBranchNode.depth,
    mol.canonicalChildren_history target left.node leftChild,
    mol.canonicalChildren_history target right.node rightChild, List.length_cons]

/-- An inherited reference cannot split an actual outward terminal-twin pair in the full
uncapped comparison. Stored-depth agreement, empty reads and the promotion-bit tie are derived. -/
theorem carried_outward_terminal_tie (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (depth fuel : Nat) (geom : Geometry)
    (source target : Node) (sourceReached : Reached mol source)
    (path : StrictDescendant mol source target)
    (atoms : List Nat) (frame : LocalizedGenericMarkedRecalculation.frameAtoms? mol source = some atoms)
    (mark : Nat) (selected : mark ∈ atoms) (left right : CanonicalRerootCursor)
    (leftSlot : left ∈ occurrenceLigandCursors mol target)
    (rightSlot : right ∈ occurrenceLigandCursors mol target)
    (leftChild : left.node ∈ mol.canonicalChildren target)
    (rightChild : right.node ∈ mol.canonicalChildren target)
    (leftTerminal : TerminalNeighbor mol target.atom left.node.atom)
    (rightTerminal : TerminalNeighbor mol target.atom right.node.atom)
    (leftReal : left.node.provenance = .realAtom) (rightReal : right.node.provenance = .realAtom)
    (sameZ : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom)
    (sameMass : mol.atomMassAt left.node.atom = mol.atomMassAt right.node.atom) :
    ((LocalizedGenericMarkedRecalculation.appendFacts? []
      (underWith mol ops geom [] target (facts mol ops depth) mark)).bind fun temporary =>
        compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol temporary
          mark fuel left right) =
        some { ordering := .eq, pseudo := false } := by
  have targetReached : Reached mol target := by
    obtain ⟨child, edge, rest⟩ := path
    exact descendant_reached (reached_child mol source child sourceReached edge) rest
  have real : target.forcedLeaf = false := by
    cases leaf : target.forcedLeaf with
    | false => rfl
    | true => simp [occurrenceLigandCursors, CanonicalRerootCursor.children, leaf] at leftSlot
  have exclude := carried_not_terminal mol wellFormed single source target sourceReached path
    real atoms frame mark selected
  have leftOther : left.node.atom ≠ mark := fun same => exclude (same ▸ leftTerminal)
  have rightOther : right.node.atom ≠ mark := fun same => exclude (same ▸ rightTerminal)
  rw [LocalizedMarkedGeneratedFactUniqueness.generated_extension_succeeds mol ops wellFormed
    single unique depth geom target mark]
  simp only [Option.bind_some]
  rw [generated_promoted_bits mol ops wellFormed single unique depth fuel geom [] target target
    targetReached targetReached mark left right leftSlot rightSlot leftTerminal rightTerminal
    leftReal rightReal sameZ (outward_depth_eq mol target left right leftChild rightChild) sameMass]
  simp [promotionBitsDecision, leftOther, rightOther]

end TetraStereo.OneCenter.LocalizedMarkedTerminalComparison

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalComparison.constitutional_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalComparison.ordinary_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalComparison.promoted_bits
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalComparison.generated_promoted_bits
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalComparison.carried_outward_terminal_tie
