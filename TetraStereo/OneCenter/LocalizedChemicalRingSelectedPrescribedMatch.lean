import TetraStereo.OneCenter.LocalizedChemicalRingSelectedRefusalWitness
import TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathFactMatch
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
The actual inherited-fallback refusal supplies the generated state and tied outward
comparison keys consumed by prescribed-path reconstruction. No key tie, slot-address
equations, path realization, or label match is supplied by the caller.

For each prescribed path there is one molecular automorphism matching all its prefixes.
The geometry side is produced by the refusal diagnosis. Optional facts can both be absent;
this does not establish a successful observation or an orientation-preserving map.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSelectedPrescribedMatch

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingInheritedReferenceTie
open LocalizedChemicalRingSelectedRefusalWitness LocalizedChemicalRingSelectedOutwardTie
open LocalizedChemicalRingPrescribedPathFactMatch LocalizedChemicalRingWitnessLabelMatch
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingBoundaryWitnessFactMatch
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingPhysicalSense
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (c : input.detectedMultiCenterMolecule.Center)
  (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
  (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)

include agreement admissible supported calibrated in
/-- Operational entry point: actual refusal yields prescribed-path and prefix matches
under the actual generated state, retaining its original reference, depth and geometry side.
The tied carrier branch and physical occurrence premises remain explicit. -/
theorem selected_refusal_prescribed_prefixes
    (branch : TiedRootBranch input data.target) (depth : Nat) (reference : input.Atom)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (refused : LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
      depth (inputGeometry input) [] (some reference.val) node = none) :
    ∃ (reflected : Bool) (left right : Fin 4) (a b : input.Atom),
      let state := generated input mol node depth reflected reference.val
      let unit : DetectedOccurrence input.moleculeGraph :=
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩
      left ≠ right ∧ a ≠ b ∧
      ((frames input single state data.target data.real unit rfl).frame.cursorAt left).occurrence.1.node.current? = some a ∧
      ((frames input single state data.target data.real unit rfl).frame.cursorAt right).occurrence.1.node.current? = some b ∧
      ((frames input single state data.target data.real unit rfl).frame.cursorAt left).occurrence.1.node.provenance = .realAtom ∧
      ((frames input single state data.target data.real unit rfl).frame.cursorAt right).occurrence.1.node.provenance = .realAtom ∧
      ∃ e : ResidualPathTreeEquiv input.moleculeGraph
          data.target.1.node.history.reverse data.target.1.node.history.reverse a b,
        ∀ p : {p : List input.Atom //
            ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p},
          ∃ π : Equiv.Perm input.Atom,
            input.moleculeGraph.IsAutomorphism π ∧
            (∀ atom ∈ data.target.1.node.history, π atom = atom) ∧
            π a = b ∧ π reference = reference ∧
            (∀ z, ¬ InComponent input.moleculeGraph data.target.1.node.history.reverse a z →
              ¬ InComponent input.moleculeGraph data.target.1.node.history.reverse b z → π z = z) ∧
            (e.toEquiv p).1 = p.1.map π ∧
            ∀ k (positive : 0 < k) (bounded : k ≤ p.1.length),
              PathLabelsAgree
                (slotTree input single state data.target data.real unit rfl left)
                (slotTree input single state data.target data.real unit rfl right)
                (rawStateReader input state data.target) (rawStateReader input state data.target)
                data.target.1.node.history.reverse (p.1.take k) ((p.1.take k).map π) ∧
              (IsDetectedCenter input.moleculeGraph
                  (pathTerminal (p.1.take k) (obs_take input.moleculeGraph p.2 bounded positive).nonempty) →
                IsDetectedCenter input.moleculeGraph
                  (π (pathTerminal (p.1.take k) (obs_take input.moleculeGraph p.2 bounded positive).nonempty)) ∧
                (state.factAt? (rawPathNode data.target.1.root
                  (boundaryPath data.target (p.1.take k)))).map factLabel =
                  (state.factAt? (rawPathNode data.target.1.root
                    (boundaryPath data.target ((p.1.take k).map π)))).map factLabel) := by
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
  refine ⟨side, left, right, a, b, distinct, different, currentL, currentR, realL, realR, ?_⟩
  exact actual_outward_default_tie_prescribed_prefixes input single state data.target data.real
    unit rfl reference left right a b currentL currentR realL realR rootL rootR pair.leftSlot
    pair.rightSlot addressL addressR tie charge

end
end TetraStereo.OneCenter.LocalizedChemicalRingSelectedPrescribedMatch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedPrescribedMatch.selected_refusal_prescribed_prefixes
