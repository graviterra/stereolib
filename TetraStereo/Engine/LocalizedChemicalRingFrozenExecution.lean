import TetraStereo.Engine.LocalizedChemicalRingCenterProjection

set_option autoImplicit false

namespace TetraStereo.Engine.LocalizedChemicalRing

open OneCenter CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation (Geometry mirror structuralDepth)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)

/-- Freeze only the auxiliary observations. The promotion still reaches the full
underlying ligand comparator at its newly selected reference. -/
def freezeChildren (step : PreparedStep) : PreparedStep := fun mol g st refs n under =>
  let prepared := under refs
  step mol g st refs n (fun _ => prepared)

private theorem frozen_descriptor_congr (s t : PreparedStep) (mol : RawMolecule)
    (refs : MarkContext) (same : ∀ g st n saved,
      s mol g st refs n (fun _ => saved) = t mol g st refs n (fun _ => saved))
    (depth : Nat) (g : Geometry) (st : OccurrenceAuxState) (n : Node)
    (ih : ∀ geo state child, factsOfStep (freezeChildren s) mol depth geo state refs child =
      factsOfStep (freezeChildren t) mol depth geo state refs child) :
    descriptorOfStep (freezeChildren s) mol depth g st refs n =
      descriptorOfStep (freezeChildren t) mol depth g st refs n := by
  have lower (geo : Geometry) : childrenUnder mol (factsOfStep (freezeChildren s) mol depth)
      geo st n refs = childrenUnder mol (factsOfStep (freezeChildren t) mol depth) geo st n refs := by
    simp only [childrenUnder]
    exact congrArg (fun f => (mol.canonicalChildren n).flatMap f) (funext (ih geo st))
  simp only [descriptorOfStep,descriptorWithPrepared,freezeChildren,lower,same]

/-- Changes to the step at other contexts are observationally irrelevant everywhere
below an occurrence when auxiliary observations are frozen. No chemical hypotheses
are needed, and both sides generate all descendants independently. -/
theorem frozen_facts_congr (s t : PreparedStep) (mol : RawMolecule) (refs : MarkContext)
    (same : ∀ g st n saved,
      s mol g st refs n (fun _ => saved) = t mol g st refs n (fun _ => saved)) (depth : Nat) :
    ∀ g st n, factsOfStep (freezeChildren s) mol depth g st refs n =
      factsOfStep (freezeChildren t) mol depth g st refs n := by
  induction depth with
  | zero => intro g st n; rfl
  | succ depth ih =>
    intro g st n
    simp only [factsOfStep_succ, frozen_descriptor_congr s t mol refs same depth g st n ih]
    rw [show factsOfStep (freezeChildren s) mol depth g st refs =
      factsOfStep (freezeChildren t) mol depth g st refs from funext (ih g st)]

theorem frozen_outcome_congr (s t : PreparedStep) (mol : RawMolecule) (refs : MarkContext)
    (same : ∀ g st n saved,
      s mol g st refs n (fun _ => saved) = t mol g st refs n (fun _ => saved))
    (depth : Nat) (g : Geometry) (st : OccurrenceAuxState) (n : Node) :
    descriptorOfStep (freezeChildren s) mol depth g st refs n =
      descriptorOfStep (freezeChildren t) mol depth g st refs n :=
  frozen_descriptor_congr s t mol refs same depth g st n (frozen_facts_congr s t mol refs same depth)

/-- Frozen chronological control with precisely the public evaluator's frame discovery,
joint comparator, eligibility, consensus, geometry and readback. -/
def frozenCenterOutcome (input : Input) (c : input.certified.detectedMultiCenterMolecule.Center) :=
  let mol := input.molecule
  let full := input.certified.localizedRerootCarrierCache (retainedCarrierFuel input.certified)
  let slice := localizedRerootRootSliceCache full c.1
  let n := canonicalCenterRoot c.1.val
  let depth := structuralDepth mol n
  let ids := List.range mol.atoms.length
  let cs := [] :: ids.map (fun i => [i])
  let ops := LocalizedChemicalRingPartitionTable.operations input.certified slice.reader mol
    (frameNodes mol (depth+1) n) cs
  LocalizedChemicalRingPartitionTable.descriptor (freezeChildren (rawStepPrepared? ops)) mol
    (inputGeometry input.certified) [] [[]] depth [] n

/-- The executable frozen projection uses the same canonical joint operation as
the regenerated public report, at the same root and structural depth. -/
theorem frozenCenterOutcome_eq (input : Input) (c : input.certified.detectedMultiCenterMolecule.Center) :
    frozenCenterOutcome input c =
      let n := canonicalCenterRoot c.1.val
      descriptorOfStep (freezeChildren (rawStepPrepared?
        (LocalizedChemicalRingJointMarkerOperations.jointOperations input.certified input.molecule)))
        input.molecule (structuralDepth input.molecule n) (inputGeometry input.certified) [] [] n := by
  simp only [frozenCenterOutcome, LocalizedChemicalRingPartitionTable.descriptor_eq,
    LocalizedChemicalRingPartitionTable.operations_eq, LocalizedChemicalRingJointCachedExecutable.operations_eq,
    LocalizedChemicalRingJointExecutable.operations_eq]

end TetraStereo.Engine.LocalizedChemicalRing
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.frozen_facts_congr
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.frozen_outcome_congr
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.frozenCenterOutcome_eq
