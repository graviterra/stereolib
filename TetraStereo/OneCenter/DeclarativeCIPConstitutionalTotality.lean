import TetraStereo.OneCenter.DeclarativeCIPCanonicalAddressing
import TetraStereo.OneCenter.DeclarativeCIPFaithfulExpansionBisimulation

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

universe u

/-!
# Total declarative constitutional rule outcomes

With the canonical addressing family, canonical outcomes exist and are unique for every pair of
addressed hierarchies (`withCanonicalAddressing_canonicalOutcome_existsUnique`).  Existing results
then finish the argument: any two faithful exact expansions of a ligand are isomorphic
(`faithfulExactExpansion_unique_up_to_iso`), and canonical outcomes are representation-invariant
(`canonicalOutcome_transport_iff`).  Hence `Problem.RuleOutcome`, which quantifies over every
admissible expansion of both ligands, holds for exactly one outcome.

Existence of a faithful expansion is a hypothesis here.  It is supplied for `Fin atomCount`
molecules by `semanticOfficialFaithfulExactExpansion_exists`.
-/

namespace ConstitutionalProblemData

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Admissible expansions are faithful exact expansions of the unit's ligands. -/
def ExpansionsFaithful (data : ConstitutionalProblemData Atom Unit) : Prop :=
  ∀ unit ligand graph, data.admissibleExpansion unit ligand graph →
    RootedDigraph.FaithfulExactExpansion data.molecule (data.centerAtom unit)
      (data.ligandAtom unit ligand) graph

/-- **Totality of declarative Rules 1a, 1b, and 2.** -/
theorem withCanonicalAddressing_ruleOutcome_existsUnique
    (data : ConstitutionalProblemData Atom Unit) (hfaithful : data.ExpansionsFaithful)
    (hexpansion : ∀ unit ligand, ∃ graph, data.admissibleExpansion unit ligand graph)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : ConstitutionalRule)
    (leftLigand rightLigand : Fin 4) :
    ∃! outcome, data.withCanonicalAddressing.toProblem.RuleOutcome descriptorMap
      rule.toSequenceRule unit leftLigand rightLigand outcome := by
  obtain ⟨left₀, hleft₀⟩ := hexpansion unit leftLigand
  obtain ⟨right₀, hright₀⟩ := hexpansion unit rightLigand
  obtain ⟨_, leftAddressing, _⟩ := (hfaithful _ _ _ hleft₀).1
  obtain ⟨_, rightAddressing, _⟩ := (hfaithful _ _ _ hright₀).1
  obtain ⟨outcome, houtcome, hunique⟩ :=
    data.withCanonicalAddressing_canonicalOutcome_existsUnique descriptorMap unit rule
      leftAddressing rightAddressing
  have hcanonical : ∀ {left right : RootedDigraph Atom} {o : Ordering},
      data.withCanonicalAddressing.toProblem.OutcomeOnGraphs descriptorMap rule.toSequenceRule
          unit left right o ↔
        data.withCanonicalAddressing.CanonicalOutcome descriptorMap unit rule left right o := by
    intro left right o
    cases rule <;> rfl
  refine ⟨outcome, fun left right hleft hright => ?_, fun other hother =>
    hunique other (hcanonical.1 (hother left₀ right₀ hleft₀ hright₀))⟩
  obtain ⟨leftIso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso _ _ _ _ _
    (hfaithful _ _ _ hleft₀) (hfaithful _ _ _ hleft)
  obtain ⟨rightIso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso _ _ _ _ _
    (hfaithful _ _ _ hright₀) (hfaithful _ _ _ hright)
  rw [hcanonical]
  exact (data.withCanonicalAddressing.canonicalOutcome_transport_iff descriptorMap unit rule
    leftIso rightIso outcome).1 houtcome

end ConstitutionalProblemData

end DeclarativeCIP
end OneCenter
end TetraStereo
