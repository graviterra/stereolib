import TetraStereo.Certificate.Dependency
import TetraStereo.KernelOnly

assert_kernel_only TetraStereo.Certificate.Dependency.lookup_none_of_not_mem
assert_kernel_only TetraStereo.Certificate.Dependency.lookup_certified
assert_kernel_only TetraStereo.Certificate.Dependency.referenced_certified
assert_kernel_only TetraStereo.Certificate.Dependency.validNode_certificate
assert_kernel_only TetraStereo.Certificate.Dependency.checkFrom_certified
assert_kernel_only TetraStereo.Certificate.Dependency.check_sound
assert_kernel_only TetraStereo.Certificate.Dependency.checked_outcome_eq_solution
assert_kernel_only TetraStereo.Certificate.Dependency.checked_outcome_declarative

namespace TetraStereo.Certificate.Dependency.Tests

open TetraStereo.OneCenter.DeclarativeCIP

/-- Small dependency fixture, not a chemical interpretation or source-approval claim. -/
def system : OccurrenceSystem (Fin 3) (Fin 3) Bool where
  finalOccurrence := id
  descriptorOf := fun label => if label then .R else .S
  DeclarativeDerivation := fun state target outcome =>
    if target = 0 then outcome = some true
    else if target = 1 then outcome = some false
    else (outcome = some true ∧ state 0 = some true ∧ state 1 = some false) ∨
      (outcome = none ∧ ¬ (state 0 = some true ∧ state 1 = some false))
  executableStep := fun state target =>
    if target = 0 then some true
    else if target = 1 then some false
    else if state 0 = some true ∧ state 1 = some false then some true else none

def dependencies (target : Fin 3) : List (Fin 3) := if target = 2 then [0, 1] else []

def nodes : List (Node (Fin 3) Bool) :=
  [⟨0, some true, []⟩, ⟨1, some false, []⟩, ⟨2, some true, [0, 1]⟩]

theorem accepted : check system dependencies nodes =
    some [(0, some true), (1, some false), (2, some true)] := by decide +kernel

theorem missing_dependency_rejected :
    check system dependencies
      [⟨0, some true, []⟩, ⟨1, some false, []⟩, ⟨2, some true, [0]⟩] = none := by decide +kernel

theorem forward_reference_rejected :
    check system dependencies
      [⟨0, some true, []⟩, ⟨2, some true, [0, 2]⟩, ⟨1, some false, []⟩] = none := by decide +kernel

theorem wrong_identity_rejected :
    check system dependencies
      [⟨0, some true, []⟩, ⟨1, some false, []⟩, ⟨2, some true, [1, 0]⟩] = none := by decide +kernel

theorem duplicate_reference_rejected :
    check system dependencies
      [⟨0, some true, []⟩, ⟨1, some false, []⟩, ⟨2, some true, [0, 0]⟩] = none := by decide +kernel

theorem wrong_outcome_rejected :
    check system dependencies
      [⟨0, some true, []⟩, ⟨1, some false, []⟩, ⟨2, none, [0, 1]⟩] = none := by decide +kernel

theorem unearned_leaf_rejected :
    check system dependencies
      [⟨0, some false, []⟩, ⟨1, some false, []⟩, ⟨2, some true, [0, 1]⟩] = none := by decide +kernel

end TetraStereo.Certificate.Dependency.Tests

assert_kernel_only TetraStereo.Certificate.Dependency.Tests.accepted
assert_kernel_only TetraStereo.Certificate.Dependency.Tests.missing_dependency_rejected
assert_kernel_only TetraStereo.Certificate.Dependency.Tests.forward_reference_rejected
assert_kernel_only TetraStereo.Certificate.Dependency.Tests.wrong_identity_rejected
assert_kernel_only TetraStereo.Certificate.Dependency.Tests.duplicate_reference_rejected
assert_kernel_only TetraStereo.Certificate.Dependency.Tests.wrong_outcome_rejected
assert_kernel_only TetraStereo.Certificate.Dependency.Tests.unearned_leaf_rejected
