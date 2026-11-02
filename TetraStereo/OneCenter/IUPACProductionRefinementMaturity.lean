import TetraStereo.OneCenter.IUPACProvisionSemantics

set_option autoImplicit false

/-!
# Production soundness and completeness decomposition

`ProvisionCorrect` contains two distinct mathematical obligations: production soundness and
reverse realization of every applicable reviewed judgment.  The next-54 foundational adapter uses
this decomposition to prove existing rows without confusing soundness with totality.

Earlier unused global and scoped seven-family wrapper structures have been removed.  The global
compiler already exposes `ProvisionCompilerCorrect` directly, so duplicating its entire shape for
both halves added API surface without a consumer.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def ProvisionSound (corpus : FrozenProvisionCorpus)
    (interpreter : ProvisionInterpreter corpus)
    (provision : IUPACNormativeProvision) : Prop :=
  ∀ input,
    corpus.ChemicallyAdmitted input →
      ∀ observation,
        interpreter.Produces provision input observation →
          (corpus.reference provision).Applicable input ∧
            (corpus.reference provision).Judges input observation

def ProvisionComplete (corpus : FrozenProvisionCorpus)
    (interpreter : ProvisionInterpreter corpus)
    (provision : IUPACNormativeProvision) : Prop :=
  ∀ input,
    corpus.ChemicallyAdmitted input →
      ∀ observation,
        (corpus.reference provision).Applicable input ∧
          (corpus.reference provision).Judges input observation →
            interpreter.Produces provision input observation

theorem provisionCorrect_iff_sound_and_complete
    {corpus : FrozenProvisionCorpus}
    {interpreter : ProvisionInterpreter corpus}
    {provision : IUPACNormativeProvision} :
    ProvisionCorrect corpus interpreter provision ↔
      ProvisionSound corpus interpreter provision ∧
        ProvisionComplete corpus interpreter provision := by
  constructor
  · intro correct
    refine ⟨?_, ?_⟩
    · intro input admitted observation produced
      exact (correct input admitted observation).mp produced
    · intro input admitted observation judged
      exact (correct input admitted observation).mpr judged
  · rintro ⟨sound, complete⟩ input admitted observation
    exact ⟨sound input admitted observation, complete input admitted observation⟩

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.provisionCorrect_iff_sound_and_complete
