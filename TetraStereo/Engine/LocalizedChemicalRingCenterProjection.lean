import TetraStereo.Engine.LocalizedChemicalRingPublic
import TetraStereo.OneCenter.LocalizedChemicalRingPartitionTable

set_option autoImplicit false

namespace TetraStereo.Engine.LocalizedChemicalRing

open OneCenter CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation (structuralDepth frameAtoms?)
open LocalizedChemicalRingPreparedContextRecursion (rawStepPrepared? preparedAssignCenter?)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)

def frameNodes (mol : RawMolecule) : Nat → RawMolecule.CanonicalBranchNode →
    List RawMolecule.CanonicalBranchNode
  | 0, _ => []
  | fuel+1, n =>
    (if (frameAtoms? mol n).isSome then [n] else []) ++
      (mol.canonicalChildren n).flatMap (frameNodes mol fuel)

/-- Evaluate one detected candidate with the two proved caches. Missing table entries
are computed on demand, so the supplied list affects only evaluation cost. -/
def centerOutcome (input : Input) (c : input.certified.detectedMultiCenterMolecule.Center)
    (contexts : List (List Nat)) : Option LocalizedAuxiliaryLabel :=
  let mol := input.molecule
  let full := input.certified.localizedRerootCarrierCache (retainedCarrierFuel input.certified)
  let slice := localizedRerootRootSliceCache full c.1
  let n := canonicalCenterRoot c.1.val
  let depth := structuralDepth mol n
  let ops := LocalizedChemicalRingPartitionTable.operations input.certified slice.reader mol
    (frameNodes mol (depth+1) n) contexts
  LocalizedChemicalRingPartitionTable.descriptor (rawStepPrepared? ops) mol
    (inputGeometry input.certified) [] contexts depth [] n

theorem centerOutcome_mem_iff (profile : Profile) (input : Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) (contexts : List (List Nat))
    (outcome : Option LocalizedAuxiliaryLabel) :
    (c.1.val, outcome) ∈ analyze profile input ↔ centerOutcome input c contexts = outcome := by
  rw [analyze_eq_prepared, LocalizedChemicalRingJointPreparedReport.mem_analyze_at_center_iff]
  simp only [centerOutcome, LocalizedChemicalRingPartitionTable.descriptor_eq,
    LocalizedChemicalRingPartitionTable.operations_eq, LocalizedChemicalRingJointCachedExecutable.operations_eq,
    LocalizedChemicalRingJointExecutable.operations_eq, preparedAssignCenter?]

end TetraStereo.Engine.LocalizedChemicalRing
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.centerOutcome_mem_iff
