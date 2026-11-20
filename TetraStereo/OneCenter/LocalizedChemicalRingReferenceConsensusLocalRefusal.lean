import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCrossGeometry
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAnyReferenceObservation
import TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

/-!
**A local test of the shape of a correction lemma, on the 46-atom input.**

At the actual occurrence `q = [0,30,34,26,1,2]` with inherited reference 28:
* the actual descriptor refuses, at every depth;
* no automorphism fixes the history of `q` and the reference while being negative at center 2:
  every such automorphism is a power of the spoke rotation;
* an automorphism negative at center 2 and fixing the history does exist, but it moves 28.

So "an actual refusal at a reached occurrence gives a history- and reference-fixing correction
negative there" is false as an unrestricted statement, and the reference-moving odd map is unavoidable
at this occurrence. The same center and reference do carry a label on the covering path.

LOGICAL BOUNDARY: `q` is not shown to be a maximal bad witness of an actual key tie, and this input
has no actual root prior tie. Nothing here refutes a correction lemma stated under those hypotheses.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusLocalRefusal

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitAllCalibration
open LocalizedChemicalRingReferenceOrbitRootMirrorCriterion (root_aut_normal_form)
open LocalizedChemicalRingReferenceOrbitCoveringSymmetry (candidate)
open LocalizedChemicalRingReferenceOrbitArmSymmetry (armSwap physicalAut physicalAut_square)
open LocalizedChemicalRingReferenceOrbitOtherArmSymmetry (otherArmSwap)
open LocalizedChemicalRingReferenceConsensusSymmetry LocalizedChemicalRingReferenceConsensusStabilizer
open LocalizedChemicalRingReferenceConsensusCrossGeometry (center3_proper)
open LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingSelectedParentEligibility (eligible_iff_other)
open LocalizedChemicalRingMovedSlotEligibility (actual_slot_key_action)
open LocalizedChemicalRingResidualReadingTransport (candidate_reading_transport)
open LocalizedChemicalRingRankedCorrectionTransport (relativeSign_mul)
open LocalizedChemicalRingComponentExchangeProperness (relativeSign_one)
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingSenseTransport
open LocalizedMarkedReachableConfigurations (Reached reached_root reached_child)
open LocalizedMarkedTerminalReferenceScope (Descends descendant_reached)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedDetectedFrames (detected_frame)
open LocalizedMarkedOperationEvaluator (underWith)
open BoundaryComponentReconstruction
open LocalizedMarkedReachedFrameNeighbors (frame_atoms_perm_neighbors)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedGenericMarkedRecalculation (frameAtoms? frameAtomsOf caseFromMirror?)

noncomputable section
open scoped Classical

/-- The tested occurrence. -/
def qNode : RawMolecule.CanonicalBranchNode := nodeOf [0, 30, 34, 26, 1, 2]

private def qRoute (n : Nat) := nodeOf (([0, 30, 34, 26, 1, 2] : List Nat).take (n + 1))

private theorem q_edges (i : Fin 5) : qRoute (i.val + 1) ∈ mol.canonicalChildren (qRoute i.val) := by
  fin_cases i <;> decide +kernel

theorem q_reached : Reached mol qNode := by
  have all : ∀ n, n ≤ 5 → Reached mol (qRoute n) := by
    intro n
    induction n with
    | zero => intro _; exact reached_root mol 0 (by decide)
    | succ n ih =>
        intro bound
        exact reached_child mol _ _ (ih (by omega)) (q_edges ⟨n, by omega⟩)
  exact all 5 (by omega)

private theorem q_data : Nonempty (OccurrenceData certified mol current qNode) :=
  occurrenceData_exists certified mol structure_agreement admissible supported single_bonded
    current qNode q_reached rfl rfl

private theorem relabel_fixed (e : physical.Aut) (value : Nat) (fixed : fixesNat e.val value = true) :
    relabelOf certified e.val value = value := by
  by_cases bound : value < 46
  · have direct := relabelOf_val certified e.val (⟨value, bound⟩ : Fin 46)
    have same : e.val ⟨value, bound⟩ = ⟨value, bound⟩ := by
      unfold fixesNat at fixed
      rw [dif_pos bound] at fixed
      exact of_decide_eq_true fixed
    change relabelOf certified e.val value = (e.val ⟨value, bound⟩).val at direct
    rw [same] at direct
    exact direct
  · exact relabelOf_outside certified _ _ (Nat.le_of_not_lt bound)

private theorem rho_history : ∀ value ∈ qNode.history, fixesNat rho value = true := by decide +kernel

private theorem armSwap_history : ∀ value ∈ qNode.history, fixesNat armSwap value = true := by
  decide +kernel

private def center (a : Fin 46) (member : a ∈ graph.tetrahedralCenterSet) : physical.Center :=
  ⟨a, member⟩

private theorem mem3 : (3 : Fin 46) ∈ graph.tetrahedralCenterSet := by
  rw [detected_inventory]
  decide

private theorem mem4 : (4 : Fin 46) ∈ graph.tetrahedralCenterSet := by
  rw [detected_inventory]
  decide

private theorem proper3 : relativeSign physical cfg physicalAut (center 3 mem3) = 1 :=
  center3_proper physicalAut rfl

private theorem proper4 : relativeSign physical cfg physicalAut (center 4 mem4) = 1 := by
  have product := relativeSign_mul physical cfg physicalAut physicalAut (center 3 mem3)
  have image : physical.centerPerm physicalAut (center 3 mem3) = center 4 mem4 := Subtype.ext rfl
  rw [physicalAut_square, relativeSign_one, proper3, image, mul_one] at product
  exact product.symm

private theorem negative2 : relativeSign physical cfg physicalAut current = -1 := by
  obtain ⟨fixed, odd⟩ := LocalizedChemicalRingTwoFixedNeighbors.local_odd_of_two_fixed_neighbors
    physical physicalAut current rfl (1 : Fin 46) (5 : Fin 46) (by decide) (by decide +kernel)
    (by decide +kernel) rfl rfl ⟨(6 : Fin 46), by decide +kernel, by decide⟩
  rw [relativeSign_of_fixed cfg physicalAut current fixed, odd]

private theorem center_cases (c : physical.Center) :
    c.1 = (0 : Fin 46) ∨ c.1 = (2 : Fin 46) ∨ c.1 = (3 : Fin 46) ∨ c.1 = (4 : Fin 46) ∨
      c.1 = (26 : Fin 46) := by
  obtain ⟨a, member⟩ := c
  change a ∈ graph.tetrahedralCenterSet at member
  rw [detected_inventory] at member
  simpa only [Finset.mem_insert, Finset.mem_singleton] using member

/-- The fallback reading at the reference 5 refuses: the transposition of 6 and 7 fixes it, is
negative at center 2 and proper on the residual component. -/
theorem reading5_none (depth : Nat) (reflected : Bool) :
    LocalizedPhysicalMarkedDistantReference.inheritedRead? mol (sparseOperations certified mol)
      (observedGeometry certified reflected) [] qNode (generated certified mol qNode depth reflected)
      (5 : Fin 46).val = none := by
  have transported := candidate_reading_transport certified mol structure_agreement admissible
    supported single_bonded cfg physicalAut all_calibrated current qNode q_reached rfl rfl
    (fun value member => relabel_fixed physicalAut value (armSwap_history value member))
    ([0, 30, 34, 26, 1] : List (Fin 46)) (by decide) (by decide +kernel)
    (by
      intro d member different
      have outside : d.1 ∉ ([0, 30, 34, 26, 1] : List (Fin 46)) := inComponent_not_mem graph member
      rcases center_cases d with h | h | h | h | h
      · exact absurd (by rw [h]; decide) outside
      · exact absurd h different
      · rw [show d = center 3 mem3 from Subtype.ext h]
        exact proper3
      · rw [show d = center 4 mem4 from Subtype.ext h]
        exact proper4
      · exact absurd (by rw [h]; decide) outside)
    depth reflected (5 : Fin 46)
  have fixed5 : physicalAut.val (5 : Fin 46) = (5 : Fin 46) := rfl
  rw [fixed5, negative2, if_neg (by norm_num)] at transported
  cases found : LocalizedPhysicalMarkedDistantReference.inheritedRead? mol
      (sparseOperations certified mol) (observedGeometry certified reflected) [] qNode
      (generated certified mol qNode depth reflected) (5 : Fin 46).val with
  | none => rfl
  | some value =>
      rw [found, Option.map_some, Option.some.injEq] at transported
      cases value <;> cases transported

private theorem rotation_moves_five : ∃ atom ∈ frameAtomsOf (occurrenceLigandCursors mol qNode),
    relabelOf certified rhoAut.val atom ≠ atom := by
  have frame := detected_frame mol certified structure_agreement admissible supported single_bonded
    current qNode q_reached rfl rfl
  have rawSingle := raw_single mol certified structure_agreement admissible.1.1 admissible.1.2
    supported single_bonded
  have degree := LocalizedMarkedDetectedFrames.detected_raw_degree mol certified structure_agreement
    admissible.1.1 admissible.1.2 supported current
  have perm : (frameAtomsOf (occurrenceLigandCursors mol qNode)).Perm
      (mol.canonicalIncidentNeighbors qNode.atom) := by
    rcases frame_atoms_perm_neighbors mol admissible.1.1 rawSingle qNode q_reached _ frame with
      ⟨_, perm⟩ | ⟨three, _⟩
    · exact perm
    · change (mol.canonicalIncidentNeighbors (current.1.val)).length = 3 at three
      rw [degree] at three
      cases three
  refine ⟨(5 : Fin 46).val, perm.mem_iff.mpr (by decide +kernel), ?_⟩
  rw [relabelOf_val]
  exact fun same => absurd (Fin.ext same) (by decide)

/-- The inherited reference 28 refuses: the rotation fixes it, the history and is proper. -/
theorem reading28_none (depth : Nat) (reflected : Bool) :
    LocalizedPhysicalMarkedDistantReference.inheritedRead? mol (sparseOperations certified mol)
      (observedGeometry certified reflected) [] qNode (generated certified mol qNode depth reflected)
      (28 : Fin 46).val = none :=
  LocalizedChemicalRingInheritedFixedReferenceRefusal.inheritedReading_none certified mol
    structure_agreement admissible supported single_bonded cfg rhoAut all_calibrated
    (rho_relativeSign cfg) current qNode q_reached rfl rfl
    (fun value member => relabel_fixed rhoAut value (rho_history value member)) (28 : Fin 46) rfl
    rotation_moves_five depth reflected

private theorem distant_eq_none (mol : RawMolecule)
    (ops : LocalizedMarkedOperationEvaluator.Operations)
    (geom : LocalizedGenericMarkedRecalculation.Geometry) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (under : Nat → OccurrenceAuxState)
    (atoms : List Nat) (mark : Nat) (frame : frameAtoms? mol node = some atoms)
    (absent : mark ∉ atoms)
    (refused : LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops geom state node under mark = none) :
    LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state (some mark) node under =
      LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under := by
  simp [LocalizedPhysicalMarkedDistantReference.rawStep?, frame,
    LocalizedPhysicalMarkedDistantReference.chooseInherited, absent, refused]

/-- **The actual step refuses at `q` under the inherited reference 28**, on either geometry. -/
theorem q_step_none (depth : Nat) (reflected : Bool) :
    LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations certified mol)
      (observedGeometry certified reflected) [] (some (28 : Fin 46).val) qNode
      (generated certified mol qNode depth reflected) = none := by
  obtain ⟨data⟩ := q_data
  obtain ⟨p, atoms, keys⟩ := actual_slot_key_action certified mol structure_agreement admissible
    supported single_bonded rhoAut current qNode data q_reached
    (fun value member => relabel_fixed rhoAut value (rho_history value member))
  obtain ⟨i, atFive⟩ := physical.ligandAtomAt_surjective current (5 : Fin 46) (by decide +kernel)
  let slot := data.ligandOf.symm i
  have atSlot : referenceAt certified mol current qNode data slot = (5 : Fin 46) := by
    simp only [referenceAt, slot, Equiv.apply_symm_apply, atFive]
  have changed : p slot ≠ slot := by
    intro same
    have image := atoms slot
    rw [same, atSlot] at image
    exact absurd image (by decide)
  have member : slot ∈ eligibleSlots certified mol single_bonded current qNode data :=
    (eligible_iff_other certified mol single_bonded current qNode data slot).mpr
      ⟨p slot, changed, keys slot⟩
  have notInjective : ¬ Function.Injective (ordinaryKeys certified mol single_bonded current qNode data) :=
    fun injective => changed (injective (keys slot))
  have refused : generatedReading certified mol current qNode data depth reflected slot = none := by
    unfold generatedReading LocalizedChemicalRingInheritedRefusalCases.reading
    rw [atSlot]
    exact reading5_none depth reflected
  obtain ⟨left, right, different, tied⟩ := (generatedReading_none_iff certified mol single_bonded cfg
    current (all_calibrated current) qNode data structure_agreement admissible supported depth
    reflected slot).mp refused
  have noContext := (noContext_none_iff certified mol single_bonded cfg current (all_calibrated current)
    qNode data structure_agreement admissible supported depth reflected).mpr
    ⟨notInjective, Or.inl ⟨slot, member, left, right, different, tied⟩⟩
  have frame := detected_frame mol certified structure_agreement admissible supported single_bonded
    current qNode q_reached rfl rfl
  have absent : (28 : Fin 46).val ∉ frameAtomsOf (occurrenceLigandCursors mol qNode) := by
    have rawSingle := raw_single mol certified structure_agreement admissible.1.1 admissible.1.2
      supported single_bonded
    have degree := LocalizedMarkedDetectedFrames.detected_raw_degree mol certified structure_agreement
      admissible.1.1 admissible.1.2 supported current
    rcases frame_atoms_perm_neighbors mol admissible.1.1 rawSingle qNode q_reached _ frame with
      ⟨_, perm⟩ | ⟨three, _⟩
    · rw [perm.mem_iff]
      decide +kernel
    · change (mol.canonicalIncidentNeighbors (current.1.val)).length = 3 at three
      rw [degree] at three
      cases three
  have inherited := distant_eq_none mol (sparseOperations certified mol)
    (observedGeometry certified reflected) [] qNode
    (generated certified mol qNode depth reflected) _ (28 : Fin 46).val frame absent
    (reading28_none depth reflected)
  cases found : LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations certified mol)
      (observedGeometry certified reflected) [] (some (28 : Fin 46).val) qNode
      (generated certified mol qNode depth reflected) with
  | none => rfl
  | some value =>
      rcases (LocalizedChemicalRingInheritedFallback.rawStep_eq_some_iff mol _ _ _ _ _ _ value).mp found with
        first | ⟨_, second⟩
      · rw [inherited, noContext] at first
        cases first
      · rw [noContext] at second
        cases second

/-- **The actual descriptor at `q` under the inherited reference 28 refuses, at every depth.** -/
theorem q_descriptor_none (depth : Nat) :
    LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol) depth
      (inputGeometry certified) [] (some (28 : Fin 46).val) qNode = none := by
  unfold LocalizedChemicalRingInheritedFallback.descriptor? descriptorWith
  have step := q_step_none depth false
  change LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations certified mol)
    (inputGeometry certified) [] (some (28 : Fin 46).val) qNode
    (underWith mol (sparseOperations certified mol) (inputGeometry certified) [] qNode
      (factsWith LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations certified mol)
        depth)) = none at step
  rw [step]
  rfl

private theorem forms_fixing (k : Fin 3) (a r : Bool)
    (fixed28 : (candidate k * (if a then armSwap else 1) * (if r then otherArmSwap else 1)) 28 = 28)
    (fixed30 : (candidate k * (if a then armSwap else 1) * (if r then otherArmSwap else 1)) 30 = 30) :
    candidate k * (if a then armSwap else 1) * (if r then otherArmSwap else 1) = 1 ∨
      candidate k * (if a then armSwap else 1) * (if r then otherArmSwap else 1) = rho ∨
      candidate k * (if a then armSwap else 1) * (if r then otherArmSwap else 1) = rho * rho := by
  revert fixed28 fixed30
  fin_cases k <;> cases a <;> cases r <;> simp only [Fin.isValue] <;> first
    | (intro first second; exact absurd first (by decide +kernel))
    | (intro first second; exact absurd second (by decide +kernel))
    | (intro _ _; left; apply Equiv.ext; decide +kernel)
    | (intro _ _; right; left; apply Equiv.ext; decide +kernel)
    | (intro _ _; right; right; apply Equiv.ext; decide +kernel)

/-- **No correction at `q` both fixes the reference 28 and is negative at center 2.** Fixing the
root, 28 and 30 leaves only powers of the spoke rotation, proper at every center. -/
theorem no_reference_fixing_odd (e : physical.Aut) (root : e.val (0 : Fin 46) = (0 : Fin 46))
    (fixed28 : e.val (28 : Fin 46) = (28 : Fin 46)) (fixed30 : e.val (30 : Fin 46) = (30 : Fin 46)) :
    relativeSign physical cfg e current = 1 := by
  obtain ⟨k, a, r, same⟩ := root_aut_normal_form ⟨e.val, e.2.1⟩ root
  have form : e.val = candidate k * (if a then armSwap else 1) * (if r then otherArmSwap else 1) := same
  have cases := forms_fixing k a r (by rw [← form]; exact fixed28) (by rw [← form]; exact fixed30)
  rw [← form] at cases
  have rhoProper := rho_relativeSign cfg
  rcases cases with one | single | double
  · rw [show e = 1 from Subtype.ext one]
    exact relativeSign_one physical cfg current
  · rw [show e = rhoAut from Subtype.ext single]
    exact rhoProper current
  · rw [show e = rhoAut * rhoAut from Subtype.ext double, relativeSign_mul, rhoProper, rhoProper]
    norm_num

/-- The reference-moving odd map does exist at `q`: it fixes the history, moves 28 and is negative. -/
theorem odd_moves_reference :
    (∀ value ∈ qNode.history, relabelOf certified physicalAut.val value = value) ∧
      physicalAut.val (28 : Fin 46) ≠ (28 : Fin 46) ∧ relativeSign physical cfg physicalAut current = -1 :=
  ⟨fun value member => relabel_fixed physicalAut value (armSwap_history value member),
    by decide, negative2⟩

/-- The same center and the same reference carry a label on the covering path. -/
theorem covering_contrast (depth : Nat) :
    ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
      depth (inputGeometry certified) [] (some (28 : Fin 46).val)
      LocalizedChemicalRingReferenceOrbitCoveringPath.coveringNode = some value :=
  LocalizedChemicalRingReferenceOrbitAnyReferenceObservation.covering_descriptor_exists_at 28 depth

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusLocalRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusLocalRefusal.reading5_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusLocalRefusal.reading28_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusLocalRefusal.q_step_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusLocalRefusal.q_descriptor_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusLocalRefusal.no_reference_fixing_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusLocalRefusal.odd_moves_reference
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusLocalRefusal.covering_contrast
