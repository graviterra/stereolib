import TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathMirrorOrientation
import TetraStereo.OneCenter.LocalizedChemicalRingRootPrescribedFactMatch
import TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Actual reflected root keys cannot tie when a successful reflected covering
observation ends at a center reversed by every possible marked branch exchange.
The physical sign is decoded through the invertible spatial-mirror descriptor identity;
no original/reflected snapshot equality or desired comparison is assumed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathMirrorKeySeparation

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingRootPrescribedFactMatch
open LocalizedChemicalRingCoveredPathMirrorOrientation LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingBoundaryWitnessExecution
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel LocalizedChemicalRingSenseTransport
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedGenericMarkedRecalculation (mirror)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section

theorem actual_root_mirror_keys_ne_of_covered_observation
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = .realAtom)
    (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (rootAddress : target.1.address = []) (reference : input.Atom)
    (depth : Nat) (source : RawMolecule.CanonicalBranchNode) (sourceReached : Reached mol source)
    (left right : Fin 4) (a b : input.Atom)
    (path : List input.Atom) (valid : ResidualObsPath input.moleculeGraph [target.1.root] a path)
    (d : input.detectedMultiCenterMolecule.Center) (terminal : pathTerminal path valid.nonempty = d.1)
    (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (covered : ∀ c : input.detectedMultiCenterMolecule.Center,
      c.1.val ∈ (rawPathNode target.1.root (boundaryPath target path)).history)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (reverses : ∀ e : input.detectedMultiCenterMolecule.Aut,
      (e : Equiv.Perm input.Atom) target.1.root = target.1.root →
      (e : Equiv.Perm input.Atom) a = b → (e : Equiv.Perm input.Atom) reference = reference →
      input.detectedMultiCenterMolecule.centerPerm e d = d ∧
        relativeSign input.detectedMultiCenterMolecule cfg e d = -1) :
    let state := snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol depth
      (mirror (inputGeometry input)) source reference.val
    ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a →
    ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b →
    (state.factAt? (rawPathNode target.1.root (boundaryPath target path))).map factLabel ≠ none →
    refinedKey input single state target real unit targetUnit reference
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left ≠
      refinedKey input single state target real unit targetUnit reference
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) right := by
  dsimp only
  intro currentL currentR present tie
  let state := snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol depth
    (mirror (inputGeometry input)) source reference.val
  have detected : IsDetectedCenter input.moleculeGraph (pathTerminal path valid.nonempty) := by
    rw [terminal]
    exact (input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mp
      ((input.moleculeGraph.mem_tetrahedralCenterSet _).mp d.2)
  obtain ⟨π, graphAut, rootFixed, entry, refFixed, matched⟩ :=
    actual_root_tie_prescribed_fact_match input single state target real unit targetUnit
      rootAddress reference left right a b currentL currentR tie charge path valid detected
  let e : input.detectedMultiCenterMolecule.Aut :=
    input.moleculeGraph.detectedMultiCenterAutOfGraphAut ⟨π, graphAut⟩
  obtain ⟨centerFixed, negative⟩ := reverses e rootFixed entry refFixed
  have imageCalibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule
      cfg (input.detectedMultiCenterMolecule.centerPerm e d) := by
    rw [centerFixed]
    exact calibrated
  have targetNode : target.1.node = OfficialCIPNode.root target.1.root := by
    have eq := input.declarativeLocalizedOccurrence_eq_root_of_address_nil
      ((input.mem_localizedOccurrences_iff _ _).mp target.2) rootAddress
    simpa using congrArg (fun occurrence => occurrence.node) eq
  have history : target.1.node.history.reverse = [target.1.root] := by rw [targetNode]; rfl
  have boundaryFixed : ∀ atom ∈ target.1.node.history.reverse, (e : Equiv.Perm input.Atom) atom = atom := by
    intro atom member
    rw [history, List.mem_singleton] at member
    simpa only [member] using rootFixed
  have valid' : ResidualObsPath input.moleculeGraph target.1.node.history.reverse a path := by
    rw [history]
    exact valid
  cases observed : (state.factAt? (rawPathNode target.1.root (boundaryPath target path))).map factLabel with
  | none => exact present observed
  | some label =>
      have sym := LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut
        input mol agreement admissible supported e
      have cov := LocalizedChemicalRingSemanticSymmetry.actual_covariant
        input mol agreement admissible supported single e
      have stepMap := LocalizedChemicalRingInheritedFallback.stepMap sym admissible.1.1 admissible.1.2
        (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single) cov
      have proper := relativeSign_of_covered_mirror_snapshot input mol agreement admissible supported single
        cfg e LocalizedChemicalRingInheritedFallback.rawStep? stepMap
        (LocalizedChemicalRingInheritedFallback.stepCongr mol (sparseOperations input mol))
        (LocalizedChemicalRingInheritedFallback.stepFlip mol (sparseOperations input mol)) target
        reference a boundaryFixed refFixed path valid' d terminal calibrated imageCalibrated covered
        depth source sourceReached matched label observed
      rw [negative] at proper
      norm_num at proper

end
end TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathMirrorKeySeparation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathMirrorKeySeparation.actual_root_mirror_keys_ne_of_covered_observation
