import TetraStereo.OneCenter.LocalizedActualReferenceMolecularEvidence
import TetraStereo.OneCenter.LocalizedOrderedReferencePipeline
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Molecular descriptor map from the ordered runtime's own reference state

The independent multireference problem reads auxiliary descriptors through a `DescriptorMap` on
detected molecular occurrences.  This adapter builds that map from the callable ordered runtime's
generated reference state.  It deliberately makes no claim that the ordered and production states
agree globally; locality lemmas establish the exact agreements needed by a root proof.
-/

namespace TetraStereo.OneCenter

open DeclarativeCIP
open CertifiedLocalizedCIPInput

noncomputable section
open scoped Classical

/-- The actual ordered descriptor map: at a detected unit, read the ordered runtime state at the
actual carrier occurrence that carries that molecular root-and-path unit. -/
def actualOrderedReferenceDescriptorMap
    (input : LocalizedOrderedReference.Input) :
    DescriptorMap (DetectedOccurrence input.certified.moleculeGraph) :=
  fun unit =>
    (actualReferenceOccurrenceOf input unit.1).bind fun occurrence =>
      (LocalizedOrderedReference.referenceState input occurrence).map
        localizedAuxiliaryDescriptor

/-- Reading the ordered map back through the localized descriptor projection returns the ordered
state at the actual carrier occurrence. -/
theorem actualOrderedReferenceDescriptorMap_readback
    (input : LocalizedOrderedReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (occurrence : LocalizedOrderedReference.Occurrence input)
    (unitEq : input.certified.molecularFrameUnit occurrence.1 = unit.1) :
    (actualOrderedReferenceDescriptorMap input unit).bind Descriptor.toLocalizedLabel =
      LocalizedOrderedReference.referenceState input occurrence := by
  have hsome : actualReferenceOccurrenceOf input unit.1 = some occurrence :=
    (actualReferenceOccurrenceOf_eq_some_iff input singleBonded acyclic unit.1 occurrence).mpr
      unitEq
  unfold actualOrderedReferenceDescriptorMap
  rw [hsome]
  exact option_map_localizedAuxiliaryDescriptor_bind _

/-- At a unit carried by a specified occurrence, equality of the ordered and production states at
that occurrence gives equality of their molecular descriptor maps.  This is intentionally
occurrence-local; the state equality is an explicit argument. -/
theorem actualOrderedReferenceDescriptorMap_eq_actualReferenceDescriptorMap_of_stateEq
    (input : LocalizedOrderedReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (occurrence : LocalizedOrderedReference.Occurrence input)
    (unitEq : input.certified.molecularFrameUnit occurrence.1 = unit.1)
    (stateEq : LocalizedOrderedReference.referenceState input occurrence =
      LocalizedUniversalReference.referenceState input occurrence) :
    actualOrderedReferenceDescriptorMap input unit = actualReferenceDescriptorMap input unit := by
  have hsome : actualReferenceOccurrenceOf input unit.1 = some occurrence :=
    (actualReferenceOccurrenceOf_eq_some_iff input singleBonded acyclic unit.1 occurrence).mpr
      unitEq
  unfold actualOrderedReferenceDescriptorMap actualReferenceDescriptorMap
  rw [hsome]
  exact congrArg (fun state : Option LocalizedAuxiliaryLabel =>
    state.map localizedAuxiliaryDescriptor) stateEq

/-- The callable pipeline state is pointwise the ordered fixed point used by the P1 preservation
theorems. -/
theorem orderedReferenceStateAt_eq_pipelineState
    (input : LocalizedOrderedReference.Input)
    (occurrence : LocalizedOrderedReference.Occurrence input) :
    input.certified.orderedReferenceState (LocalizedOrderedReference.carrierFuel input)
        occurrence = LocalizedOrderedReference.referenceState input occurrence := by
  exact (congrFun
    (LocalizedOrderedReference.referenceState_eq_orderedReferenceState input) occurrence).symm

end

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.actualOrderedReferenceDescriptorMap
assert_kernel_only TetraStereo.OneCenter.actualOrderedReferenceDescriptorMap_readback
assert_kernel_only
  TetraStereo.OneCenter.actualOrderedReferenceDescriptorMap_eq_actualReferenceDescriptorMap_of_stateEq
assert_kernel_only TetraStereo.OneCenter.orderedReferenceStateAt_eq_pipelineState
