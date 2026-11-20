import TetraStereo.OneCenter.LocalizedChemicalRingColoredReconstruction
import TetraStereo.OneCenter.LocalizedActualBoundaryPathRealization
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# From joint source observations to one reference-fixing molecular automorphism

The residual path equivalence is constructed by the existing boundary-path realization theorem.
Matching reference bits at its common source-tree addresses then prove terminal-color
preservation for that same equivalence. Component reconstruction produces one molecular
automorphism fixing the reference. No desired path map or automorphism is supplied.

The source trees must have the same constitutional/provenance observations and reference
observations in their chosen order. The promoted-address readback and source readdressing
modules supply the ingredients for deriving those premises from actual keys.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferencePathReconstruction

open LocalizedActualBoundaryPathRealization LocalizedChemicalRingColoredReconstruction
open RetainedCoherentSymmetry RetainedRingSymmetryReconstruction
open scoped Classical
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {B : List input.Atom} {a b : input.Atom}
  {left right : OfficialCIPSourceTree input.Atom}

def referenceAt (tree : OfficialCIPSourceTree input.Atom) (reference : input.Atom)
    (address : List Nat) : Nat :=
  ((tree.sourceAtAddress? address).map
    (fun node => if node.current? = some reference then 1 else 0)).getD 0

theorem residual_reference_preserved (pair : ObservedTreePair input B B a b left right)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (parentL : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj a z)
    (parentR : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj b z)
    (reference : input.Atom)
    (same : ∀ address, referenceAt left reference address = referenceAt right reference address) :
    TerminalColorPreserved
      (residualPathTreeEquivOfSameObservations pair charge rfl parentL parentR)
      (referenceColor reference) := by
  intro path
  obtain ⟨address, lookupL, lookupR⟩ :=
    residualPathTreeEquivOfSameObservations_correspond pair charge rfl parentL parentR path
  have equalBits := same address
  simp only [referenceAt, lookupL, lookupR, Option.map_some, Option.getD_some,
    boundaryNode_current?] at equalBits
  simpa only [referenceColor, pathTerminal, List.getLast?_eq_some_getLast path.2.nonempty,
    List.getLast?_eq_some_getLast
      ((residualPathTreeEquivOfSameObservations pair charge rfl parentL parentR).toEquiv path).2.nonempty,
    Option.some.injEq] using equalBits.symm

/-- The joint observations construct one molecular automorphism with the selected reference fixed. -/
theorem exists_reference_fixed_aut (pair : ObservedTreePair input B B a b left right)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (parentL : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj a z)
    (parentR : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj b z)
    (reference : input.Atom)
    (same : ∀ address, referenceAt left reference address = referenceAt right reference address) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      (∀ z ∈ B, π z = z) ∧ π a = b ∧ π reference = reference := by
  have outside : a ∉ B := not_mem_of_nodup_append_singleton pair.rooted₁.nodup
  obtain ⟨π, aut, fixed, entry, ref, _, _⟩ := exists_reference_fixed_automorphism
    (residualPathTreeEquivOfSameObservations pair charge rfl parentL parentR) outside reference
    (residual_reference_preserved pair charge parentL parentR reference same)
  exact ⟨π, aut, fixed, entry, ref⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferencePathReconstruction

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePathReconstruction.residual_reference_preserved
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePathReconstruction.exists_reference_fixed_aut
