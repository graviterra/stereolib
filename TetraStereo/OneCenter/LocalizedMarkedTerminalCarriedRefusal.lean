import TetraStereo.OneCenter.LocalizedMarkedOrdinaryStrictness
import TetraStereo.OneCenter.LocalizedMarkedTerminalMarkedRefusal

set_option autoImplicit false

/-!
# Complete inherited-context refusal at terminal-twin occurrences

The ordinary fast path cannot separate a terminal-twin pair. In a valid inherited
promotion context the marked path also refuses on its actual generated snapshot.
Thus the raw evaluator and its mirror-derived descriptor refuse, independently of
coordinates. The fallback to locally selected references is a separate obligation.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedTerminalCarriedRefusal

open LocalizedMarkedOperationEvaluator LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors LocalizedMarkedTerminalReferenceScope
open LocalizedMarkedTerminalCursor LocalizedMarkedTerminalComparison
open LocalizedMarkedTerminalMarkedRefusal LocalizedMarkedOrdinaryStrictness
open LocalizedMarkedUncappedEvaluator (operations)
open LocalizedGenericMarkedRecalculation (Geometry frameAtomsOf)

abbrev Node := RawMolecule.CanonicalBranchNode

theorem outward_ordinary_not_strict (mol : RawMolecule)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (target : Node) (targetReached : Reached mol target)
    (roots : List CanonicalRerootCursor) (frame : occurrenceLigandFrame? mol target = some roots)
    (left right : CanonicalRerootCursor)
    (leftSlot : left ∈ occurrenceLigandCursors mol target)
    (rightSlot : right ∈ occurrenceLigandCursors mol target) (distinct : left ≠ right)
    (leftChild : left.node ∈ mol.canonicalChildren target)
    (rightChild : right.node ∈ mol.canonicalChildren target)
    (leftTerminal : TerminalNeighbor mol target.atom left.node.atom)
    (rightTerminal : TerminalNeighbor mol target.atom right.node.atom)
    (leftReal : left.node.provenance = .realAtom) (rightReal : right.node.provenance = .realAtom)
    (sameZ : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom)
    (sameMass : mol.atomMassAt left.node.atom = mol.atomMassAt right.node.atom)
    (sorted : List Nat) (adjacent : List (Option Ordering))
    (computed : LocalizedMarkedUncappedOperations.ordinary? mol [] target = some (sorted, adjacent)) :
    LocalizedGenericMarkedRecalculation.strict adjacent = false := by
  have lt := (ligand_terminal mol wellFormed single unique target targetReached left leftSlot
    target.atom leftTerminal).2
  have rt := (ligand_terminal mol wellFormed single unique target targetReached right rightSlot
    target.atom rightTerminal).2
  have tied := ordinary_tie mol [] (LocalizedMarkedUncappedOperations.comparisonFuel mol)
    left right lt rt leftReal rightReal sameZ
    (outward_depth_eq mol target left right leftChild rightChild) sameMass rfl rfl
  exact ordinary_not_strict_of_tie mol [] target roots frame left right
    (physical_slots_mem_frame mol target roots frame left leftSlot)
    (physical_slots_mem_frame mol target roots frame right rightSlot)
    distinct _ tied rfl sorted adjacent computed

theorem carried_outward_raw_none (mol : RawMolecule)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (depth : Nat) (geom : Geometry) (source target : Node) (sourceReached : Reached mol source)
    (path : StrictDescendant mol source target)
    (sourceAtoms : List Nat)
    (sourceFrame : LocalizedGenericMarkedRecalculation.frameAtoms? mol source = some sourceAtoms)
    (mark : Nat) (sourceSelected : mark ∈ sourceAtoms)
    (targetAtoms : List Nat)
    (targetFrame : LocalizedGenericMarkedRecalculation.frameAtoms? mol target = some targetAtoms)
    (targetSelected : mark ∈ targetAtoms)
    (left right : CanonicalRerootCursor)
    (leftSlot : left ∈ occurrenceLigandCursors mol target)
    (rightSlot : right ∈ occurrenceLigandCursors mol target) (distinct : left ≠ right)
    (leftChild : left.node ∈ mol.canonicalChildren target)
    (rightChild : right.node ∈ mol.canonicalChildren target)
    (leftTerminal : TerminalNeighbor mol target.atom left.node.atom)
    (rightTerminal : TerminalNeighbor mol target.atom right.node.atom)
    (leftReal : left.node.provenance = .realAtom) (rightReal : right.node.provenance = .realAtom)
    (sameZ : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom)
    (sameMass : mol.atomMassAt left.node.atom = mol.atomMassAt right.node.atom) :
    rawWith? mol (operations mol) geom [] (some mark) target (facts mol (operations mol) depth) =
      none := by
  have targetReached : Reached mol target := by
    obtain ⟨child, edge, rest⟩ := path
    exact descendant_reached (reached_child mol source child sourceReached edge) rest
  have markedNone := carried_outward_markedReading_none mol wellFormed single unique depth geom
    source target sourceReached path sourceAtoms sourceFrame mark sourceSelected left right
    leftSlot rightSlot distinct leftChild rightChild leftTerminal rightTerminal leftReal rightReal
    sameZ sameMass
  cases frame : occurrenceLigandFrame? mol target with
  | none => simp [LocalizedGenericMarkedRecalculation.frameAtoms?, frame] at targetFrame
  | some roots =>
      cases ordinary : LocalizedMarkedUncappedOperations.ordinary? mol [] target with
      | none => simp [rawWith?, rawStep?, targetFrame, operations, ordinary]
      | some data =>
          obtain ⟨sorted, adjacent⟩ := data
          have nonstrict := outward_ordinary_not_strict mol wellFormed single unique target
            targetReached roots frame left right leftSlot rightSlot distinct leftChild rightChild
            leftTerminal rightTerminal leftReal rightReal sameZ sameMass sorted adjacent ordinary
          have ordinaryOps : (operations mol).ordinary [] target = some (sorted, adjacent) := ordinary
          by_cases invalid : ¬ targetAtoms.Nodup ∨
              LocalizedGenericMarkedRecalculation.consistent adjacent = false
          · simp [rawWith?, rawStep?, targetFrame, ordinaryOps, invalid]
          · simpa [rawWith?, rawStep?, targetFrame, ordinaryOps, invalid, nonstrict, targetSelected]
              using markedNone

/-- The actual cased auxiliary descriptor is absent in every valid carried context at these
terminal-twin occurrences. Neither raw execution nor its case is assumed. -/
theorem carried_outward_descriptor_none (mol : RawMolecule)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (depth : Nat) (geom : Geometry) (source target : Node) (sourceReached : Reached mol source)
    (path : StrictDescendant mol source target)
    (sourceAtoms : List Nat)
    (sourceFrame : LocalizedGenericMarkedRecalculation.frameAtoms? mol source = some sourceAtoms)
    (mark : Nat) (sourceSelected : mark ∈ sourceAtoms)
    (targetAtoms : List Nat)
    (targetFrame : LocalizedGenericMarkedRecalculation.frameAtoms? mol target = some targetAtoms)
    (targetSelected : mark ∈ targetAtoms)
    (left right : CanonicalRerootCursor)
    (leftSlot : left ∈ occurrenceLigandCursors mol target)
    (rightSlot : right ∈ occurrenceLigandCursors mol target) (distinct : left ≠ right)
    (leftChild : left.node ∈ mol.canonicalChildren target)
    (rightChild : right.node ∈ mol.canonicalChildren target)
    (leftTerminal : TerminalNeighbor mol target.atom left.node.atom)
    (rightTerminal : TerminalNeighbor mol target.atom right.node.atom)
    (leftReal : left.node.provenance = .realAtom) (rightReal : right.node.provenance = .realAtom)
    (sameZ : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom)
    (sameMass : mol.atomMassAt left.node.atom = mol.atomMassAt right.node.atom) :
    descriptor? mol (operations mol) depth geom [] (some mark) target = none := by
  have raw := carried_outward_raw_none mol wellFormed single unique depth geom source target
    sourceReached path sourceAtoms sourceFrame mark sourceSelected targetAtoms targetFrame
    targetSelected left right leftSlot rightSlot distinct leftChild rightChild leftTerminal
    rightTerminal leftReal rightReal sameZ sameMass
  simp [descriptor?, descriptorWith?, raw, LocalizedGenericMarkedRecalculation.caseFromMirror?]

end TetraStereo.OneCenter.LocalizedMarkedTerminalCarriedRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalCarriedRefusal.outward_ordinary_not_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalCarriedRefusal.carried_outward_raw_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalCarriedRefusal.carried_outward_descriptor_none
