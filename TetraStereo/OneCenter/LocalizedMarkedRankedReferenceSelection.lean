import TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader
import TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularSelection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Executable ranked Rule-4b reference selection from a raw auxiliary state

`LocalizedMarkedReferenceSelectionBoundary` shows that the raw whole-frontier selector
`occurrenceRule4bReferences` disagrees with ranked selection. This module supplies the ranked
selector the marked recursion should consult instead: the actual executable Rule-4a cumulative
builder `buildRuleMajorCumulativeWithReadExec?` run on the retained cyclic occurrence expansion,
reading the raw state through `rawStateReader`, followed by the existing ranked population reading
`localizedRule4bReferencesFromRankedLabels`.

At every executable child of a carrier target of a simple-bonded certified input, the result is
`some` and equals the independent `retainedReferenceSelection` of the raw-state descriptor map on
the realized arm graph. Success and the selected population are conclusions; no key, selection or
sorting is assumed. Rings and their terminal ring-duplicate leaves are included. The raw state is
arbitrary; its chemical meaning is not asserted here.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRankedReferenceSelection

open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree Rule4aTableBridge
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedMolecularSelection

variable (input : CertifiedLocalizedCIPInput)

/-- Actual ranked Rule-4b reference population of one ligand cursor under a raw state: the
executable Rule-4a cumulative key at twice the carrier budget, read by the raw-state reader, then
the ranked population reading. -/
def rankedReferences? (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (cursor : input.LocalizedRerootCursor (retainedCarrierFuel input)) : Option (List RS) :=
  (input.buildRuleMajorCumulativeWithReadExec? .rule4a (rawStateReader input state target)
    (2 * (retainedCarrierFuel input + 1)) cursor).map fun key =>
      localizedRule4bReferencesFromRankedLabels key.rankedLabels

/-- **The executable ranked selector computes the independent retained reference selection** of
the raw-state descriptor map at every executable child of a simple-bonded carrier target. -/
theorem rankedReferences?_eq_retainedSelection (singleBonded : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState)
    (target : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (rootChild : cursor ∈ input.executableLocalizedRerootChildren target) :
    ∃ tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input),
      tree.source = cursor ∧
      rankedReferences? input state target.occurrence cursor =
        some (toReferenceList (retainedReferenceSelection input.moleculeGraph
          (rawStateDescriptorMap input state) unit (ruleMajorTreeGraph tree))) := by
  obtain ⟨tree, key, source, built, references⟩ :=
    exists_retainedMolecularContextTree_references_eq_selection
      (rawStateDescriptorMap input state) (rawStateDescriptorMap_tetrahedral input state)
      singleBonded target unit targetUnit cursor rootChild
  refine ⟨tree, source, ?_⟩
  have built' : input.buildRuleMajorCumulativeWithReadExec? .rule4a
      (input.molecularReader (rawStateDescriptorMap input state) target.occurrence)
      (2 * (retainedCarrierFuel input + 1)) cursor = some key := built
  unfold rankedReferences?
  rw [rawStateReader_eq_molecularReader, built', Option.map_some, references]

/-- Success of the executable ranked selector is a conclusion at every executable child. -/
theorem rankedReferences?_isSome (singleBonded : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState)
    (target : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (rootChild : cursor ∈ input.executableLocalizedRerootChildren target) :
    (rankedReferences? input state target.occurrence cursor).isSome = true := by
  obtain ⟨_, _, computed⟩ := rankedReferences?_eq_retainedSelection input singleBonded state
    target unit targetUnit cursor rootChild
  rw [computed]
  rfl

end TetraStereo.OneCenter.LocalizedMarkedRankedReferenceSelection

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRankedReferenceSelection.rankedReferences?_eq_retainedSelection
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRankedReferenceSelection.rankedReferences?_isSome
