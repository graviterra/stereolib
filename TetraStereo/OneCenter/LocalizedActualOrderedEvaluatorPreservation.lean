import TetraStereo.OneCenter.LocalizedActualOrderedEvaluatorAgreement
import TetraStereo.OneCenter.LocalizedActualRule4bPhysicalSlotArms
import TetraStereo.OneCenter.LocalizedPhysicalGuardedRule5Closure
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# P1: the ordered bare Rule-4/5 evaluator preserves the generated reference state

The ordered bare Rule-4/5 descriptor (`localizedOccurrenceRule45DescriptorOrdered?`) is packaged
as an auxiliary rule semantics with the trivial declarative reading and iterated to its own fixed
point `orderedReferenceState` by the production ranked iteration.  On the general rigid /
terminal-twin physical domain:

* `orderedReferenceState_eq_referenceState_of_dependency` — at every actual strict dependency of
  the final occurrence of the root, the ordered fixed point equals the generated reference state
  (well-founded induction along `LocalizedDepthDependency`, using the per-occurrence agreement
  of `LocalizedActualOrderedEvaluatorAgreement` on the generated state's view);
* `orderedReferenceState_eq_referenceState_final` — at the final occurrence itself, when every
  frame slot carries at most one Rule-4b reference (which `physical_priorReferences_length_le_one`
  derives from the physical branch domain of each slot,
  `orderedReferenceState_eq_referenceState_final_of_branchDomain`).

So the accepted endpoint of the physical chain, the generated label at the final occurrence, is
unchanged by ordering the alternatives before comparing: the ordered and the production bare
evaluators compute the same label there and at everything it depends on.  The study note's
earlier reading, that singleton references at the root alone establish this, is replaced by the
dependency induction: the deeper auxiliary outputs agree by rigidity or terminal-twin refusal, not
by any reference count.
-/

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open AcyclicCutBranchAutomorphism
open Rule4aTableBridge

noncomputable section

namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput) (fuel : Nat)

/-- The ordered bare Rule-4/5 evaluator as an auxiliary rule semantics.  Its declarative reading is
the executable rule itself: the content of the semantics is in the ordered builder's independent
meaning (`DeclarativeLocalizedRerootCompoundRule45KeyOrdered`), not restated here. -/
def localizedOccurrenceRule45OrderedAuxiliarySemantics : input.LocalizedAuxiliaryRuleSemantics fuel where
  DeclarativeDerivation state target outcome :=
    input.localizedOccurrenceRule45DescriptorOrdered? target
      (input.localizedDependencyView state target) = outcome
  executableRule := fun target view => input.localizedOccurrenceRule45DescriptorOrdered? target view
  derivation_executable_iff := fun _ _ _ => Iff.rfl

/-- The fixed point of the ordered bare evaluator under the production ranked iteration. -/
def orderedReferenceState : input.LocalizedAuxiliaryState fuel :=
  input.evaluateLocalizedOccurrences fuel
    (input.localizedOccurrenceRule45OrderedAuxiliarySemantics fuel).executableRule

/-- The ordered fixed point is fixed by the ordered evaluator. -/
theorem orderedReferenceState_fixed (target : input.LocalizedCIPOccurrence fuel) :
    input.localizedOccurrenceRule45DescriptorOrdered? target
        (input.localizedDependencyView (input.orderedReferenceState fuel) target) =
      input.orderedReferenceState fuel target :=
  input.cipModel_evaluateLocalizedOccurrences fuel
    (input.localizedOccurrenceRule45OrderedAuxiliarySemantics fuel) target

/-- The number of alternatives of a reference population of at most one reference. -/
theorem localizedRule4bcReferenceAlternatives_length_le_one (references : List RS)
    (h : references.length ≤ 1) : (localizedRule4bcReferenceAlternatives references).length ≤ 1 := by
  match references, h with
  | [], _ => simp [localizedRule4bcReferenceAlternatives]
  | [_], _ => simp [localizedRule4bcReferenceAlternatives]

/-- One Rules-4b/4c reading per alternative. -/
theorem buildLocalizedRerootRule4bcReadings?_length {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel' : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ (alternatives : List (Option RS)) {readings : List input.LocalizedRerootRule4bcReading},
      input.buildLocalizedRerootRule4bcReadings? target view fuel' cursor alternatives =
        some readings → readings.length = alternatives.length
  | [], readings, h => by
      simp [buildLocalizedRerootRule4bcReadings?] at h
      subst h
      rfl
  | alternative :: alternatives, readings, h => by
      unfold buildLocalizedRerootRule4bcReadings? at h
      cases hr : input.buildLocalizedRerootRule4bcReading? target view fuel' cursor alternative with
      | none => simp [hr] at h
      | some reading =>
          cases hrest : input.buildLocalizedRerootRule4bcReadings? target view fuel' cursor
              alternatives with
          | none => simp [hr, hrest] at h
          | some rest =>
              simp [hr, hrest] at h
              subst h
              simp [buildLocalizedRerootRule4bcReadings?_length target view fuel' cursor
                alternatives hrest]

/-- A built compound prior with at most one reference has at most one alternative. -/
theorem readings_length_le_one_of_references {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel' : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    {prior : input.LocalizedRerootCompoundRule4bcKey}
    (built : input.buildLocalizedRerootCompoundRule4bcKey? target view fuel' cursor = some prior)
    (short : prior.references.length ≤ 1) : prior.readings.length ≤ 1 := by
  obtain ⟨_, _, _, hreadings⟩ := compound_built_components target view fuel' cursor built
  rw [input.buildLocalizedRerootRule4bcReadings?_length target view fuel' cursor _ hreadings]
  exact localizedRule4bcReferenceAlternatives_length_le_one _ short

end CertifiedLocalizedCIPInput

/-! ## Transfer along the depth order -/

section Transfer

variable (input : LocalizedUniversalReference.Input)

/-- **P1 at the strict dependencies.**  On the general rigid / terminal-twin physical domain, the
ordered fixed point equals the generated reference state at every actual strict dependency of the
final occurrence of the root. -/
theorem orderedReferenceState_eq_referenceState_of_dependency
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.TetrahedralCenter)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg root)
    (topCenter : input.certified.TetrahedralCenter)
    (topAt : topCenter.1 = root.1) :
    ∀ target : LocalizedUniversalReference.Occurrence input,
      input.certified.LocalizedDepthDependency target
        (input.certified.localizedFinalOccurrence
          (LocalizedUniversalReference.carrierFuel input) topCenter) →
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input) target =
        LocalizedUniversalReference.referenceState input target := by
  intro target
  induction target using
    (input.certified.localizedDepthDependency_wellFounded
      (LocalizedUniversalReference.carrierFuel input)).induction with
  | _ target ih =>
      intro dependency
      rw [← input.certified.orderedReferenceState_fixed, ←
        localizedOccurrenceRule45Descriptor?_referenceState input noDouble target]
      have step :
          input.certified.localizedOccurrenceRule45DescriptorOrdered? target
              (input.certified.localizedDependencyView
                (input.certified.orderedReferenceState
                  (LocalizedUniversalReference.carrierFuel input)) target) =
            input.certified.localizedOccurrenceRule45DescriptorOrdered? target
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input) target) :=
        input.certified.localizedExecutableStep_eq_of_depthAgree
          (input.certified.localizedOccurrenceRule45OrderedAuxiliarySemantics
            (LocalizedUniversalReference.carrierFuel input)).executableRule
          _ _ target fun source hs =>
            ih source hs (input.certified.localizedDepthDependency_trans hs dependency)
      rw [step]
      exact orderedDescriptor_eq_descriptor_of_strictDependency input singleBonded acyclic hcharge
        noDouble cfg root domain topCenter topAt target dependency

/-- **P1 at the final occurrence.**  With at most one Rule-4b reference per frame slot of the final
occurrence, the ordered fixed point equals the generated reference state there. -/
theorem orderedReferenceState_eq_referenceState_final
    (S : ActualCentrePhysicalSetup input)
    (short : ∀ slot : Fin 4,
      (actualSlotCompoundKey input S.c S.frame S.frameComputed slot).prior.references.length ≤ 1) :
    input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
        (ActualReaderPhysicalBranchInverse.topTarget input S.c) =
      LocalizedUniversalReference.referenceState input
        (ActualReaderPhysicalBranchInverse.topTarget input S.c) := by
  have deps := orderedReferenceState_eq_referenceState_of_dependency input S.singleBonded S.acyclic
    S.hcharge S.noDouble (input.certified.canonicalReindexConfiguration S.cfg) S.c
    (S.slotSetup 0).globalDomain ⟨S.c.1, S.c.2⟩ rfl
  rw [← input.certified.orderedReferenceState_fixed, ←
    localizedOccurrenceRule45Descriptor?_referenceState input S.noDouble]
  have step :
      input.certified.localizedOccurrenceRule45DescriptorOrdered?
          (ActualReaderPhysicalBranchInverse.topTarget input S.c)
          (input.certified.localizedDependencyView
            (input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input))
            (ActualReaderPhysicalBranchInverse.topTarget input S.c)) =
        input.certified.localizedOccurrenceRule45DescriptorOrdered?
          (ActualReaderPhysicalBranchInverse.topTarget input S.c)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (ActualReaderPhysicalBranchInverse.topTarget input S.c)) :=
    input.certified.localizedExecutableStep_eq_of_depthAgree
      (input.certified.localizedOccurrenceRule45OrderedAuxiliarySemantics
        (LocalizedUniversalReference.carrierFuel input)).executableRule
      _ _ _ fun source hs => deps source hs
  rw [step]
  refine input.certified.localizedOccurrenceRule45DescriptorOrdered?_eq_of_short _ _ S.frame
    (actualSlotDerived input S.c S.frame S.frameComputed) S.frameComputed ?_
  intro slot
  exact input.certified.readings_length_le_one_of_references _ _ _ _
    (actualSlotPriorBuilt input S.c S.frame S.frameComputed slot) (short slot)

/-- The one-reference bound of every slot from the physical branch domain of every ligand. -/
theorem actualSlotCompoundKey_references_length_le_one_of_branchDomain
    (S : ActualCentrePhysicalSetup input)
    (branchDomain : ∀ index : Fin 4,
      PhysicalBranchDomain input (S.slotSetup index).root (S.slotSetup index).oAtom)
    (slot : Fin 4) :
    (actualSlotCompoundKey input S.c S.frame S.frameComputed slot).prior.references.length ≤ 1 := by
  obtain ⟨index, hindex⟩ := S.slot_bijective.2 slot
  have := physical_priorReferences_length_le_one (S.slotSetup index) (branchDomain index)
  simpa [ActualSlotPhysicalSetup.key, ActualCentrePhysicalSetup.slotSetup, hindex] using this

/-- **P1.**  On the general rigid / terminal-twin physical domain with the physical branch domain at
every ligand of the root, the ordered bare evaluator's fixed point agrees with the generated
reference state at the final occurrence of the root and at all of its strict dependencies. -/
theorem orderedReferenceState_eq_referenceState_final_of_branchDomain
    (S : ActualCentrePhysicalSetup input)
    (branchDomain : ∀ index : Fin 4,
      PhysicalBranchDomain input (S.slotSetup index).root (S.slotSetup index).oAtom) :
    input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
        (ActualReaderPhysicalBranchInverse.topTarget input S.c) =
      LocalizedUniversalReference.referenceState input
        (ActualReaderPhysicalBranchInverse.topTarget input S.c) :=
  orderedReferenceState_eq_referenceState_final input S
    (actualSlotCompoundKey_references_length_le_one_of_branchDomain input S branchDomain)

end Transfer

end
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.orderedReferenceState_fixed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.readings_length_le_one_of_references
assert_kernel_only TetraStereo.OneCenter.orderedReferenceState_eq_referenceState_of_dependency
assert_kernel_only TetraStereo.OneCenter.orderedReferenceState_eq_referenceState_final
assert_kernel_only TetraStereo.OneCenter.actualSlotCompoundKey_references_length_le_one_of_branchDomain
assert_kernel_only TetraStereo.OneCenter.orderedReferenceState_eq_referenceState_final_of_branchDomain
