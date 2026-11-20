import TetraStereo.OneCenter.LocalizedChemicalRingRootPhysicalKeyClasses
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact independent physical interpretation of the evaluator's one-mark root fallback.
A fallback regenerates descendants under its extended reference context and then demands an
immediate strict root reading. Its obstruction is motion in the promoted point's stabilizer,
which can be even (for example, a three-cycle). No global descriptor success, chirality
completeness or source-policy claim follows from per-fallback resolution alone. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRootFallbackPhysicalObstruction

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRootPhysicalKeyClasses (PhysicalTransport keys_injective_iff_no_physicalTransport)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt observedGeometry)
open LocalizedChemicalRingJointPreparedExecution (fallback fallback_none_iff)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

/-- An independent molecular residual symmetry moves some root ligand while fixing the promoted
atom, the root and all older references, and remaining proper at every other center. -/
def MarkedRootMotion (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (c : input.detectedMultiCenterMolecule.Center) (references : List input.Atom)
    (marked : input.Atom) : Prop :=
  ∃ left right : Fin 4, left ≠ right ∧
    PhysicalTransport input cfg c (references ++ [marked]) left right


/-- The promoted point's physical stabilizer acts trivially on all four root ligands.
Internal molecular automorphisms acting trivially on those ligands are allowed. -/
def FreeAt (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (c : input.detectedMultiCenterMolecule.Center) (references : List input.Atom)
    (marked : input.Atom) : Prop :=
  ∀ left right : Fin 4,
    PhysicalTransport input cfg c (references ++ [marked]) left right → left = right

/-- The independent point-stabilizer criterion is exactly absence of residual root motion. -/
theorem freeAt_iff_not_markedRootMotion (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (c : input.detectedMultiCenterMolecule.Center) (references : List input.Atom)
    (marked : input.Atom) :
    FreeAt input cfg c references marked ↔ ¬ MarkedRootMotion input cfg c references marked := by
  constructor
  · intro free motion
    obtain ⟨left, right, different, transported⟩ := motion
    exact different (free left right transported)
  · intro noMotion left right transported
    by_contra different
    exact noMotion ⟨left, right, different, transported⟩

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported single charge calibrated in
/-- Failure of the actual fallback is exactly nontrivial action of the independent marked
point stabilizer. It is not equivalent to an odd symmetry: a residual C3 also causes failure. -/
theorem fallback_none_iff_markedRootMotion
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool) (slot : Fin 4) :
    fallback input mol c node data (structuralDepth mol node)
      (observedGeometry input reflected) references slot = none ↔
    MarkedRootMotion input cfg c references (referenceAt input mol c node data slot) := by
  rw [fallback_none_iff input mol agreement admissible supported single c node data
    (structuralDepth mol node) references cfg (calibrated c) reflected slot]
  rw [keys_injective_iff_no_physicalTransport input mol agreement admissible supported single
    charge cfg calibrated c node data reached current rootAddress
    (references ++ [referenceAt input mol c node data slot]) reflected]
  push_neg
  constructor
  · rintro ⟨left, right, distinct, transported⟩
    exact ⟨data.ligandOf left, data.ligandOf right,
      fun same => distinct (data.ligandOf.injective same), transported⟩
  · rintro ⟨left, right, distinct, transported⟩
    refine ⟨data.ligandOf.symm left, data.ligandOf.symm right, ?_, ?_⟩
    · intro same
      exact distinct (by simpa using congrArg data.ligandOf same)
    · simpa using transported


include agreement admissible supported single charge calibrated in
/-- Resolution of one actual root fallback is equivalent to the independent promoted-point
stabilizer criterion. This says nothing about agreement of different key-class readings. -/
theorem fallback_ne_none_iff_freeAt
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool) (slot : Fin 4) :
    fallback input mol c node data (structuralDepth mol node)
      (observedGeometry input reflected) references slot ≠ none ↔
    FreeAt input cfg c references (referenceAt input mol c node data slot) := by
  rw [freeAt_iff_not_markedRootMotion]
  exact not_congr (fallback_none_iff_markedRootMotion input mol agreement admissible supported
    single charge cfg calibrated c node data reached current rootAddress references reflected slot)

end
end TetraStereo.OneCenter.LocalizedChemicalRingRootFallbackPhysicalObstruction

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootFallbackPhysicalObstruction.fallback_none_iff_markedRootMotion

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootFallbackPhysicalObstruction.freeAt_iff_not_markedRootMotion
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootFallbackPhysicalObstruction.fallback_ne_none_iff_freeAt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootFallbackPhysicalObstruction.MarkedRootMotion
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootFallbackPhysicalObstruction.FreeAt
