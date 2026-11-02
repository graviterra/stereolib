import TetraStereo.OneCenter.IUPACProvisionSemantics

set_option autoImplicit false

/-!
# Bulk projection of provision-compiler refinement

The proof unit is the whole compiler, not an editable list of provision families.  Once the seven
semantic-family obligations have produced one `ProvisionCompilerCorrect`, extensional
production/reference equality follows for every provision and every admitted input.  Downstream
certificate code may then project that single theorem into a generated 2,452-row terminal ledger.

This module deliberately contains no maturity manifest, hand-maintained conformant batch, or
caller-authored terminal status.  Those early project-management intermediates were superseded by
the compiler disposition and the root `ProvisionTerminalLedger`.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

namespace ProvisionInterpreter

/-- The actual production relation, viewed extensionally as the emitted observation set. -/
def productionAssignments {corpus : FrozenProvisionCorpus}
    (interpreter : ProvisionInterpreter corpus)
    (provision : IUPACNormativeProvision)
    (input : AuthoritativeChemicalInput) :
    Set (corpus.reference provision).Observation :=
  { observation | interpreter.Produces provision input observation }

end ProvisionInterpreter

namespace FrozenProvisionCorpus

/-- The independently reviewed reference relation, viewed as the expected observation set. -/
def referenceAssignments (corpus : FrozenProvisionCorpus)
    (provision : IUPACNormativeProvision)
    (input : AuthoritativeChemicalInput) :
    Set (corpus.reference provision).Observation :=
  { observation |
    (corpus.reference provision).Applicable input ∧
      (corpus.reference provision).Judges input observation }

end FrozenProvisionCorpus

namespace ProvisionCompilerCorrect

/-- One compiler-wide refinement proof yields the requested production/reference equation for
every one of the 2,452 provisions.  No row-specific ledger theorem is needed. -/
theorem pipeline_eq_reference
    {corpus : FrozenProvisionCorpus}
    {compiler : ProvisionCompiler corpus}
    {interpreter : ProvisionInterpreter corpus}
    (correct : ProvisionCompilerCorrect compiler interpreter)
    (provision : IUPACNormativeProvision)
    (input : AuthoritativeChemicalInput)
    (admitted : corpus.ChemicallyAdmitted input) :
    interpreter.productionAssignments provision input =
      corpus.referenceAssignments provision input := by
  apply Set.ext
  intro observation
  exact correct.every_provision_correct provision input admitted observation

/-- Pointwise form used by generated ledger projections and fixed production joins. -/
theorem production_iff_reference
    {corpus : FrozenProvisionCorpus}
    {compiler : ProvisionCompiler corpus}
    {interpreter : ProvisionInterpreter corpus}
    (correct : ProvisionCompilerCorrect compiler interpreter)
    (provision : IUPACNormativeProvision)
    (input : AuthoritativeChemicalInput)
    (admitted : corpus.ChemicallyAdmitted input)
    (observation : (corpus.reference provision).Observation) :
    interpreter.Produces provision input observation ↔
      (corpus.reference provision).Applicable input ∧
        (corpus.reference provision).Judges input observation :=
  correct.every_provision_correct provision input admitted observation

end ProvisionCompilerCorrect

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionCompilerCorrect.pipeline_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionCompilerCorrect.production_iff_reference
