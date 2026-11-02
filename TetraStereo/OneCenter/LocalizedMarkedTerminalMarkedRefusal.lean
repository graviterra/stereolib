import TetraStereo.OneCenter.LocalizedMarkedUncappedRankingLaws
import TetraStereo.OneCenter.LocalizedMarkedTerminalComparison
import TetraStereo.OneCenter.LocalizedMarkedUncappedEvaluator

set_option autoImplicit false

/-!
# Terminal-twin refusal of inherited marked readback

The actual generated descendant snapshot yields a tied pair; the actual uncapped
tracked ranking must therefore be nonunique, and geometric readback refuses for
every geometry. No nondegeneracy condition is imposed at a terminal-twin center.
This closes the carried-reference marked branch. The ordinary fast branch, local
reference consensus, and the certified physical-domain adapter are separate obligations.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedTerminalMarkedRefusal

open LocalizedMarkedOperationEvaluator LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors LocalizedMarkedTerminalReferenceScope
open LocalizedMarkedUncappedRankingLaws LocalizedMarkedTerminalComparison
open LocalizedMarkedUncappedEvaluator (operations)
open LocalizedGenericMarkedRecalculation (Geometry frameAtomsOf)
open AuthoritativeCIPRule6ReferenceFamily AuthoritativeCIPRule6P92Enumeration

abbrev Node := RawMolecule.CanonicalBranchNode

theorem physical_slots_mem_frame (mol : RawMolecule) (node : Node)
    (roots : List CanonicalRerootCursor) (frame : occurrenceLigandFrame? mol node = some roots)
    (cursor : CanonicalRerootCursor) (member : cursor ∈ occurrenceLigandCursors mol node) :
    cursor ∈ roots := by
  unfold occurrenceLigandFrame? at frame
  dsimp only at frame
  split at frame
  · simp at frame
  · split at frame
    · simp only [Option.some.injEq] at frame
      subst roots
      exact member
    · split at frame
      · simp only [Option.some.injEq] at frame
        subst roots
        exact List.mem_append_left _ member
      · simp at frame

/-- A tied pair of actual physical slots prevents marked geometric readback, even when
the frame or ranking cannot be built. -/
theorem markedReading_none_of_slot_tie (mol : RawMolecule) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (mark : Nat)
    (left right : CanonicalRerootCursor)
    (leftSlot : left ∈ occurrenceLigandCursors mol node)
    (rightSlot : right ∈ occurrenceLigandCursors mol node) (distinct : left ≠ right)
    (decision : Rule6TrackedDecision)
    (compared : compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state mark
      (LocalizedMarkedUncappedOperations.comparisonFuel mol) left right = some decision)
    (tied : decision.ordering = .eq) :
    markedReading? mol (operations mol) geom state node mark = none := by
  cases frame : occurrenceLigandFrame? mol node with
  | none => simp [markedReading?, LocalizedGenericMarkedRecalculation.frameAtoms?, frame]
  | some roots =>
      by_cases member : mark ∈ frameAtomsOf roots
      · have bound : (frameAtomsOf roots).idxOf mark < (frameAtomsOf roots).length :=
          List.idxOf_lt_length_iff.mpr member
        have lookup : ((frameAtomsOf roots)[(frameAtomsOf roots).idxOf mark]?).getD 0 = mark := by
          simp [List.getElem?_idxOf member]
        cases ranked : LocalizedMarkedUncappedOperations.marked? mol state node mark with
        | none => simp [markedReading?, operations, ranked,
            LocalizedGenericMarkedRecalculation.frameAtoms?, frame]
        | some ranking =>
            have computed : rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?
                mol state mark (LocalizedMarkedUncappedOperations.comparisonFuel mol) roots =
                some ranking := by
              simpa [LocalizedMarkedUncappedOperations.marked?, frame, Nat.not_le_of_lt bound,
                authoritativeOccurrenceRule6PositionRankingBackend,
                authoritativeOccurrenceRule6RankingBackend, lookup] using ranked
            have notUnique := ranking_not_unique_of_tie mol state mark _ roots left right
              (physical_slots_mem_frame mol node roots frame left leftSlot)
              (physical_slots_mem_frame mol node roots frame right rightSlot)
              distinct decision compared tied ranking computed
            simp [markedReading?, operations, LocalizedGenericMarkedRecalculation.frameAtoms?,
              frame, ranked, LocalizedGenericMarkedRecalculation.rankedAtoms?, notUnique]
      · have outside : (frameAtomsOf roots).length ≤ (frameAtomsOf roots).idxOf mark :=
          Nat.le_of_not_gt (fun h => member (List.idxOf_lt_length_iff.mp h))
        simp [markedReading?, operations, LocalizedGenericMarkedRecalculation.frameAtoms?, frame,
          LocalizedMarkedUncappedOperations.marked?, outside]

/-- Actual generated facts, full uncapped marked ranking, and geometric refusal are connected
for a terminal-twin pair below the occurrence that selected the carried reference. -/
theorem carried_outward_markedReading_none (mol : RawMolecule)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (depth : Nat) (geom : Geometry) (source target : Node) (sourceReached : Reached mol source)
    (path : StrictDescendant mol source target)
    (atoms : List Nat) (frame : LocalizedGenericMarkedRecalculation.frameAtoms? mol source = some atoms)
    (mark : Nat) (selected : mark ∈ atoms) (left right : CanonicalRerootCursor)
    (leftSlot : left ∈ occurrenceLigandCursors mol target)
    (rightSlot : right ∈ occurrenceLigandCursors mol target)
    (distinct : left ≠ right)
    (leftChild : left.node ∈ mol.canonicalChildren target)
    (rightChild : right.node ∈ mol.canonicalChildren target)
    (leftTerminal : TerminalNeighbor mol target.atom left.node.atom)
    (rightTerminal : TerminalNeighbor mol target.atom right.node.atom)
    (leftReal : left.node.provenance = .realAtom) (rightReal : right.node.provenance = .realAtom)
    (sameZ : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom)
    (sameMass : mol.atomMassAt left.node.atom = mol.atomMassAt right.node.atom) :
    ((LocalizedGenericMarkedRecalculation.appendFacts? []
      (underWith mol (operations mol) geom [] target (facts mol (operations mol) depth) mark)).bind
      fun temporary => markedReading? mol (operations mol) geom temporary target mark) = none := by
  have extension := LocalizedMarkedGeneratedFactUniqueness.generated_extension_succeeds mol
    (operations mol) wellFormed single unique depth geom target mark
  have comparison := carried_outward_terminal_tie mol (operations mol) wellFormed single unique
    depth (LocalizedMarkedUncappedOperations.comparisonFuel mol) geom source target sourceReached
    path atoms frame mark selected left right leftSlot rightSlot leftChild rightChild
    leftTerminal rightTerminal leftReal rightReal sameZ sameMass
  rw [extension] at comparison ⊢
  simp only [Option.bind_some] at comparison ⊢
  exact markedReading_none_of_slot_tie mol geom _ target mark left right leftSlot rightSlot
    distinct _ comparison rfl

end TetraStereo.OneCenter.LocalizedMarkedTerminalMarkedRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalMarkedRefusal.physical_slots_mem_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalMarkedRefusal.markedReading_none_of_slot_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalMarkedRefusal.carried_outward_markedReading_none
