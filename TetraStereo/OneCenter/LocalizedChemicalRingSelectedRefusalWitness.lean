import TetraStereo.OneCenter.LocalizedChemicalRingInheritedReferenceTie
import TetraStereo.OneCenter.LocalizedChemicalRingOutwardKeyWitness
import TetraStereo.OneCenter.LocalizedChemicalRingSelectedOutwardTie
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
An actual inherited-context refusal inside a Rule-1a-tied root arm supplies
matched generated labels under the ORIGINAL inherited reference. The refused comparison,
real outward siblings, default marker coverage, and matching automorphism are all derived.
The root-arm executions and Rule-1a tie describe the carrier branch in question;
they do not assume any auxiliary label or refined comparison result. Membership in
the evaluator's selected recursive calls is not asserted by this broader interface.

This is a structural/refusal endpoint, not a physical properness theorem. In particular,
its inherited reference may be distant, so local oddness does not follow automatically.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSelectedRefusalWitness

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedPromotedRanking LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedCanonicalFrame LocalizedCumulativeDecoratedTree
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingInheritedReferenceTie
open LocalizedChemicalRingOutwardKeyWitness LocalizedChemicalRingSelectedOutwardTie
open LocalizedChemicalRingWitnessLabelMatch LocalizedChemicalRingBoundaryWitnessFactMatch
open LocalizedChemicalRingWitnessFactMatch RetainedCoherentSymmetry
open LocalizedChemicalRingPhysicalSense
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

/-- Evidence of a carrier branch, retaining the two real Rule-4a builds and
their Rule-1a tie. No assumption about the target's marked keys is included. -/
structure TiedRootBranch (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input)) where
  rootCursor : input.LocalizedRerootCursor (retainedCarrierFuel input)
  rootAddress : rootCursor.occurrence.1.address = []
  arm : input.LocalizedRerootCursor (retainedCarrierFuel input)
  arm' : input.LocalizedRerootCursor (retainedCarrierFuel input)
  member : arm ∈ input.executableLocalizedRerootChildren rootCursor
  member' : arm' ∈ input.executableLocalizedRerootChildren rootCursor
  different : arm.occurrence ≠ arm'.occurrence
  real : arm.occurrence.1.node.provenance = .realAtom
  real' : arm'.occurrence.1.node.provenance = .realAtom
  read : input.LocalizedRerootCursor (retainedCarrierFuel input) → Option LocalizedAuxiliaryLabel
  read' : input.LocalizedRerootCursor (retainedCarrierFuel input) → Option LocalizedAuxiliaryLabel
  fuel : Nat
  fuel' : Nat
  key : input.LocalizedRerootCumulativeRule45Key
  key' : input.LocalizedRerootCumulativeRule45Key
  built : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel arm = some key
  built' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read' fuel' arm' = some key'
  tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
    key.constitutional.rule1a key'.constitutional.rule1a = .eq
  inside : input.RootBranchContains arm.occurrence target
  nonroot : target.1.address ≠ []

/-- The same symmetry carries every field; in particular the fact matches are not
attached to an independently chosen isomorphism. -/
structure MatchedSymmetry (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = .realAtom)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (reference : input.Atom) (left right : Fin 4) (a b : input.Atom) where
  leftCurrent : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a
  rightCurrent : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b
  leftReal : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.provenance = .realAtom
  rightReal : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.provenance = .realAtom
  symmetry : input.detectedMultiCenterMolecule.Aut
  rank : input.Atom → Nat
  fixedHistory : ∀ atom ∈ target.1.node.history, (symmetry : Equiv.Perm input.Atom) atom = atom
  entry : (symmetry : Equiv.Perm input.Atom) a = b
  fixedReference : (symmetry : Equiv.Perm input.Atom) reference = reference
  support : ∀ z, ¬ InComponent input.moleculeGraph target.1.node.history.reverse a z →
    ¬ InComponent input.moleculeGraph target.1.node.history.reverse b z →
    (symmetry : Equiv.Perm input.Atom) z = z
  matched : ∀ c : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph target.1.node.history.reverse a c.1 →
    ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph target.1.node.history.reverse a p},
      pathTerminal p.1 p.2.nonempty = c.1 ∧
      PathLabelsAgree
        (slotTree input single state target real unit targetUnit left)
        (slotTree input single state target real unit targetUnit right)
        (rawStateReader input state target) (rawStateReader input state target)
        target.1.node.history.reverse p.1 (p.1.map (symmetry : Equiv.Perm input.Atom)) ∧
      (state.factAt? (rawPathNode target.1.root (boundaryPath target p.1))).map factLabel =
        (state.factAt? (rawPathNode target.1.root
          (boundaryPath target (p.1.map (symmetry : Equiv.Perm input.Atom))))).map factLabel ∧
      (∀ y ∈ p.1.dropLast, rank y < rank c.1) ∧
      ∀ y, InComponent input.moleculeGraph (target.1.node.history.reverse ++ p.1.dropLast) c.1 y →
        y ≠ c.1 → rank c.1 < rank y

variable (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (c : input.detectedMultiCenterMolecule.Center)
  (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
  (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)

include agreement admissible supported calibrated in
/-- From actual descriptor refusal to exact optional generated-label matches. Both the
geometry side and the tied real outward slots are produced, not assumed. -/
theorem selected_refusal_matched_symmetry
    (branch : TiedRootBranch input data.target) (depth : Nat) (reference : input.Atom)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (refused : LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
      depth (inputGeometry input) [] (some reference.val) node = none) :
    ∃ (reflected : Bool) (left right : Fin 4) (a b : input.Atom),
      left ≠ right ∧ a ≠ b ∧
      Nonempty (MatchedSymmetry input single
        (generated input mol node depth reflected reference.val) data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl reference left right a b) := by
  obtain ⟨side, left, right, _, distinct, tie⟩ := descriptor_none_original_reference_tie
    input mol agreement admissible supported single cfg c calibrated node data depth reference refused
  let state := generated input mol node depth side reference.val
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  change refinedKey input single state data.target data.real unit rfl reference
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left =
    refinedKey input single state data.target data.real unit rfl reference
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) right at tie
  obtain ⟨center, current⟩ := input.localizedRerootCursor_current_exists
    (⟨data.target, none⟩ : input.LocalizedRerootCursor (retainedCarrierFuel input))
  obtain ⟨_, pair, a, b, _, _, _, targetEq, leftEq, rightEq, different,
      currentL, currentR, realL, realR⟩ := selected_refined_tie_real_outward input single
    branch.rootCursor branch.rootAddress branch.arm branch.arm' branch.member branch.member'
    branch.different branch.real branch.real' branch.read branch.read' branch.key branch.key'
    branch.built branch.built' branch.tie state data.target data.real branch.inside branch.nonroot
    center current unit rfl reference (retainedCarrierFuel input)
    (2 * (retainedCarrierFuel input + 1)) left right distinct tie
  have rootL := pair.leftRoot
  have rootR := pair.rightRoot
  have addressL := pair.leftAddress
  have addressR := pair.rightAddress
  rw [targetEq, leftEq] at rootL addressL
  rw [targetEq, rightEq] at rootR addressR
  rw [leftEq] at currentL realL
  rw [rightEq] at currentR realR
  obtain ⟨e, rank, fixed, entry, ref, support, matched⟩ := actual_outward_default_tie_witness
    input single state data.target data.real unit rfl reference left right a b currentL currentR
    realL realR rootL rootR pair.leftSlot pair.rightSlot addressL addressR tie charge
  exact ⟨side, left, right, a, b, distinct, different,
    ⟨⟨currentL, currentR, realL, realR, e, rank, fixed, entry, ref, support, matched⟩⟩⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingSelectedRefusalWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedRefusalWitness.selected_refusal_matched_symmetry
