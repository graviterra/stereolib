import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootAssignment
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! An original root starts without inherited references. Its actual joint marker is empty,
so its ordering is exactly the independently specified ordinary Rules-1--5 key ordering.
This result concerns arbitrary supplied auxiliary states, including actual generated states.
Empty inherited marks do not require empty Rule-4b reference populations inside the branches. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootEmptyContext

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingJointMarkerKey LocalizedChemicalRingJointMarkerRanking
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedOrdinaryRanking
open LocalizedChemicalRingCompletenessMarked (slotAt slotPerm)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData rank)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

theorem built_markers_nil {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (W D fuel : Nat)
    (cursor : input.LocalizedRerootCursor carrierFuel) (key : JointPromotedKey input)
    (built : buildJoint? input target view [] W D fuel cursor = some key) :
    key.markers = [] := by
  cases fuel <;>
    simp only [buildJoint?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
  · obtain ⟨prior, _, children, _, rest⟩ := built
    split at rest
    · cases Option.some.inj rest
      rfl
    · cases rest
  · obtain ⟨prior, _, children, _, keys, _, same⟩ := built
    cases Option.some.inj same
    rfl

variable (single : input.moleculeGraph.SimpleBonded) (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = .realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1) (W D : Nat)

theorem refinedKey_nil (slot : Fin 4) :
    refinedKey input single state target real unit targetUnit [] W D slot =
      toLex (rawStateKeys input single state target real unit targetUnit slot, ([] : JointMarker)) := by
  unfold refinedKey
  rw [built_markers_nil input target (rawStateView input state target) W D _ _ _
    (compiled_built input single state target real unit targetUnit [] W D slot)]

theorem keyOrder_nil (entries : List (Fin 4)) :
    keyOrder (refinedKey input single state target real unit targetUnit [] W D) entries =
      keyOrder (rawStateKeys input single state target real unit targetUnit) entries := by
  unfold keyOrder
  congr 1
  funext a b
  apply propext
  rw [refinedKey_nil, refinedKey_nil]
  simp only [Prod.Lex.toLex_le_toLex]
  exact ⟨fun h => h.elim le_of_lt (fun h => le_of_eq h.1),
    fun h => (lt_or_eq_of_le h).elim Or.inl (fun h => Or.inr ⟨h, le_rfl⟩)⟩

theorem slotPerm_nil :
    slotPerm (refinedKey input single state target real unit targetUnit [] W D) =
      slotPerm (rawStateKeys input single state target real unit targetUnit) := by
  apply Equiv.ext
  intro slot
  change slotAt _ slot = slotAt _ slot
  simp only [slotAt, keyOrder_nil]

/-- The root priority uses the independent ordinary signatures on its actually generated
auxiliary evidence; no runtime marker table occurs in this definition. -/
def ordinaryGeometryRank (mol : RawMolecule) (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)
    (reflected : Bool) : Equiv.Perm (Fin 4) :=
  rank input mol c node data (rawStateKeys input single
    (LocalizedChemicalRingJointPreparedCorrectionWitness.sideState input mol node
      (LocalizedChemicalRingPhysicalSense.inputGeometry input) [] reflected)
    data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl)

theorem geometryRank_nil (mol : RawMolecule) (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)
    (reflected : Bool) :
    LocalizedChemicalRingJointPreparedRootAssignment.geometryRank input mol single c node data
        [] reflected = ordinaryGeometryRank input single mol c node data reflected := by
  unfold LocalizedChemicalRingJointPreparedRootAssignment.geometryRank ordinaryGeometryRank rank
  rw [slotPerm_nil]

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootEmptyContext

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootEmptyContext.built_markers_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootEmptyContext.refinedKey_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootEmptyContext.keyOrder_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootEmptyContext.slotPerm_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootEmptyContext.geometryRank_nil
