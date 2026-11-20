import TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathFactMatch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Original-root facade for prescribed-path reconstruction. Root source generation and
the actual default key bounds are derived from the computed frame. A key tie supplies
one root/reference-fixing molecular automorphism and exact generated fact equality at
any prescribed detected-terminal path; no outward-address premises are supplied. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRootPrescribedFactMatch

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingActualReferenceFixing
open LocalizedChemicalRingDefaultMarkerLayout LocalizedChemicalRingPrescribedPathLabels
open LocalizedChemicalRingPrescribedPathReconstruction LocalizedChemicalRingColoredReconstruction
open LocalizedChemicalRingWitnessLabelMatch LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingBoundaryWitnessFactMatch

noncomputable section
open scoped Classical

theorem actual_root_tie_prescribed_fact_match
    (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = .realAtom)
    (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (rootAddress : target.1.address = []) (reference : input.Atom) (left right : Fin 4)
    (a b : input.Atom)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    (tie : refinedKey input single state target real unit targetUnit reference
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left =
      refinedKey input single state target real unit targetUnit reference
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) right)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (path : List input.Atom) (valid : ResidualObsPath input.moleculeGraph [target.1.root] a path)
    (detected : IsDetectedCenter input.moleculeGraph (pathTerminal path valid.nonempty)) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      π target.1.root = target.1.root ∧ π a = b ∧ π reference = reference ∧
      (state.factAt? (rawPathNode target.1.root (boundaryPath target path))).map factLabel =
        (state.factAt? (rawPathNode target.1.root (boundaryPath target (path.map π)))).map factLabel := by
  obtain ⟨widthL, heightL⟩ := actual_root_slot_bounds input single state target real unit targetUnit
    rootAddress left
  obtain ⟨widthR, heightR⟩ := actual_root_slot_bounds input single state target real unit targetUnit
    rootAddress right
  let frame := frames input single state target real unit targetUnit
  obtain ⟨rootedL, adjacentL⟩ := root_slot_boundary single (rawStateDescriptorMap input state)
    target frame rootAddress left a currentL
  obtain ⟨rootedR, adjacentR⟩ := root_slot_boundary single (rawStateDescriptorMap input state)
    target frame rootAddress right b currentR
  have parentL : ∀ z, ([target.1.root] : List input.Atom).getLast? = some z →
      input.moleculeGraph.Adj a z := by
    intro z eq
    have same : target.1.root = z := by simpa using eq
    simpa only [same] using adjacentL
  have parentR : ∀ z, ([target.1.root] : List input.Atom).getLast? = some z →
      input.moleculeGraph.Adj b z := by
    intro z eq
    have same : target.1.root = z := by simpa using eq
    simpa only [same] using adjacentR
  obtain ⟨e, colors, matched⟩ := actual_tie_path_equivalence input single state target real unit
    targetUnit reference (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
    (frame.retainedKeys unit left) left right widthL heightL widthR heightR tie
    [target.1.root] a b rootedL rootedR charge parentL parentR
  have outside : a ∉ [target.1.root] :=
    valid.outside a (List.mem_of_head?_eq_some valid.head)
  obtain ⟨π, aut, fixed, entry, preserved, _, image⟩ :=
    exists_forced_color_preserving_aut e outside (referenceColor reference) colors ⟨path, valid⟩
  have referenceFixed : π reference = reference := by
    have eq := preserved reference
    by_contra different
    simp [referenceColor, different] at eq
  have targetNode : target.1.node = OfficialCIPNode.root target.1.root := by
    have eq := input.declarativeLocalizedOccurrence_eq_root_of_address_nil
      ((input.mem_localizedOccurrences_iff _ _).mp target.2) rootAddress
    simpa using congrArg (fun occurrence => occurrence.node) eq
  have history : target.1.node.history.reverse = [target.1.root] := by
    rw [targetNode]
    rfl
  have labels : PathLabelsAgree
      (slotTree input single state target real unit targetUnit left)
      (slotTree input single state target real unit targetUnit right)
      (rawStateReader input state target) (rawStateReader input state target)
      target.1.node.history.reverse path (path.map π) := by
    simpa only [history, image] using matched ⟨path, valid⟩
  have mappedNonempty : path.map π ≠ [] := by simpa using valid.nonempty
  let graphAut : input.moleculeGraph.Aut := ⟨π, aut⟩
  have imageDetected : IsDetectedCenter input.moleculeGraph
      (pathTerminal (path.map π) mappedNonempty) := by
    simp only [pathTerminal, List.getLast_map]
    exact (input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mp
      ((input.moleculeGraph.isTetrahedralCenter_apply_aut_iff graphAut _).mpr
        ((input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mpr detected))
  exact ⟨π, aut, fixed _ (by simp), entry, referenceFixed,
    fact_labels_eq_of_boundary_pathLabelsAgree single state target _ _ path (path.map π)
      valid.nonempty mappedNonempty detected imageDetected labels⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingRootPrescribedFactMatch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootPrescribedFactMatch.actual_root_tie_prescribed_fact_match
