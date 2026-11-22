import TetraStereo.Engine.CertificateExporter
import TetraStereo.Examples.Rule6CageAuxiliaries

set_option autoImplicit false
namespace TetraStereo.Engine
open OneCenter RingChemicalPriority Examples.Rule6CageAuxiliaries

/-- The recursive assignment and the four-way ring refusal carried by the
exported artifact. Both molecular graphs are explicit. -/
def recursiveRingClaim : Prop :=
  Promotion.Justified twins twinGeometry [0] ⟨.R,.R⟩ ∧
  ∃ e : Promotion.Experiment spiroPentane [0], ∃ ts : List Promotion.Trial,
    (∀ a ∈ e.arms, a.facts = []) ∧ e.trials? = some ts ∧ ts.map (·.mark) = [1,2,3,4] ∧
    ∀ g, Promotion.result g ts = some none

theorem recursiveRingProof : recursiveRingClaim :=
  ⟨twin_chemical_proof,spiroPentane_no_descriptor⟩

def recursiveRingArtifact : LeanCertificateArtifact where
  kind := .stereoClaim
  title := "Recursive Rule 6 auxiliary assignment and complete four-way ring refusal"
  claim := recursiveRingClaim
  proof := recursiveRingProof
  theoremExport := {
    imports := ["TetraStereo.Examples.Rule6CageAuxiliaries"]
    options := ["set_option autoImplicit false",
      "open TetraStereo.Engine.RingChemicalPriority TetraStereo.Examples.Rule6CageAuxiliaries"]
    namespacePath := ["TetraStereo","Generated"]
    theoremName := "recursiveRingAssignmentAndRefusal"
    statement := joinLines [
      "Promotion.Justified twins twinGeometry [0] ⟨.R,.R⟩ ∧",
      "    ∃ e : Promotion.Experiment spiroPentane [0], ∃ ts : List Promotion.Trial,",
      "      (∀ a ∈ e.arms, a.facts = []) ∧ e.trials? = some ts ∧ ts.map (·.mark) = [1,2,3,4] ∧",
      "      ∀ g, Promotion.result g ts = some none"]
    proofTerm := "  exact ⟨twin_chemical_proof,spiroPentane_no_descriptor⟩" }

def recursiveRingExportEntry : CertificateExportEntry where
  artifact := recursiveRingArtifact
  key := "recursive-rule6-ring"
  description := recursiveRingArtifact.title
  fileName := "RecursiveRingAssignmentAndRefusal.lean"
  source := recursiveRingArtifact.source

end TetraStereo.Engine
assert_kernel_only TetraStereo.Engine.recursiveRingProof
assert_kernel_only TetraStereo.Engine.recursiveRingExportEntry
