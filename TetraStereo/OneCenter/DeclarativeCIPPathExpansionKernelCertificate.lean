import TetraStereo.OneCenter.DeclarativeCIPPathExpansion
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP
namespace PathExpansionKernelCertificate

/-! A non-vacuity witness: bromochlorofluoromethane with atoms `0 = C, 1 = H, 2 = F, 3 = Cl,
4 = Br`.  The universal theorem applies with no further hypothesis. -/

def chbrclf : MoleculeGraph (Fin 5) where
  atomZ := fun atom => [6, 1, 9, 17, 35].getD atom.val 0
  bond := fun first second =>
    if (first = 0 ∧ second ≠ 0) ∨ (second = 0 ∧ first ≠ 0) then 1 else 0
  bond_symm := by decide
  bond_self := by decide

/-- One tetrahedral unit at carbon; later rules are left empty. -/
def chbrclfData : ConstitutionalProblemData (Fin 5) Unit where
  molecule := chbrclf
  centerAtom := fun _ => 0
  ligandAtom := fun _ ligand => ligand.succ
  admissibleExpansion := fun _ _ _ => False
  expansion_sound := fun _ _ _ h => h.elim
  admissibleAddressing := fun _ _ _ _ => True
  addressing_invariant := fun _ _ _ _ _ _ => Iff.rfl
  laterRuleJudgment := fun _ _ _ _ _ _ => False
  admissibleRule6Reference := fun _ _ _ => False
  rule6Judgment := fun _ _ _ _ _ _ => False
  dependsOn := fun _ _ _ => False
  orientationJudgment := fun _ _ _ => False

theorem chbrclf_bonded (center : Unit) (ligand : Fin 4) :
    chbrclf.Adj (chbrclfData.centerAtom center) (chbrclfData.ligandAtom center ligand) := by
  cases center
  revert ligand
  decide

/-- Rule 1a has exactly one declarative outcome for every pair of CHBrClF ligands. -/
theorem chbrclf_rule1a_existsUnique (descriptorMap : DescriptorMap Unit) (left right : Fin 4) :
    ∃! outcome, chbrclfData.withFaithfulExpansions.withCanonicalAddressing.toProblem.RuleOutcome
      descriptorMap ConstitutionalRule.rule1aAtomicNumber.toSequenceRule () left right outcome :=
  chbrclfData.withFaithfulExpansions_ruleOutcome_existsUnique chbrclf_bonded descriptorMap ()
    ConstitutionalRule.rule1aAtomicNumber left right

end PathExpansionKernelCertificate
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.exists_addressing_of_unique_parent
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.pathExpansion_multiplicities
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.pathExpansion_duplicateDistances
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.pathExpansion_faithful
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.exists_faithfulExactExpansion
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.ConstitutionalProblemData.withFaithfulExpansions_ruleOutcome_existsUnique
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.PathExpansionKernelCertificate.chbrclf_rule1a_existsUnique
