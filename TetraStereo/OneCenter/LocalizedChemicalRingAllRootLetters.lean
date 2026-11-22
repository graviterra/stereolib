import TetraStereo.OneCenter.LocalizedChemicalRingTwoPairReport
import TetraStereo.OneCenter.CIPTetrahedralArbitraryFrameSourceConformance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace TetraStereo.OneCenter.LocalizedChemicalRingAllRootLetters

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingPairingParity (matchingEven handedness_eq_matching)
open LocalizedChemicalRingTwoPairReport (RootSuccess sideLetter)
open LocalizedChemicalRingRootPhysicalKeyClasses
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData rank ranked_eq referenceAt observedGeometry)
open LocalizedChemicalRingJointPreparedExecution (step keys generated fallback)
open LocalizedChemicalRingJointPreparedSourceStep
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence (finalQuery)
open LocalizedChemicalRingJointPreparedReport (analyze mem_analyze_at_center_iff)
open LocalizedChemicalRingJointPreparedRootInput (root_data root_reached)
open LocalizedChemicalRingCompletenessMarked (enumeration readback_enum)
open LocalizedChemicalRingPhysicalSense (inputGeometry letterOfSign)
open LocalizedChemicalRingJointMarkerRanking (RefinedKey)
open LocalizedGenericMarkedRecalculation (structuralDepth caseFromMirror? readback_mirror)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (c : input.detectedMultiCenterMolecule.Center)

set_option quotPrecheck false
local notation "root" => canonicalCenterRoot c.1.val
variable (data : OccurrenceData input mol c (canonicalCenterRoot c.1.val))
  (addr : data.target.1.address = [])
  (p : Profile input mol) (model : SourceModel input mol single p)

/-- Use the unmarked frame when all physical classes are singletons. Otherwise any member of
any moving class can serve as the common reference on both geometry sides. -/
def Eligible : Option (Fin 4) → Prop
  | none => ∀ i j, i ≠ j → ¬ PhysicalTransport input cfg c [] i j
  | some i => ∃ j, i ≠ j ∧ PhysicalTransport input cfg c [] i j

theorem exists_eligible : ∃ m, Eligible input cfg c m := by
  by_cases moves : ∃ i j, i ≠ j ∧ PhysicalTransport input cfg c [] i j
  · obtain ⟨i,j,h⟩ := moves
    exact ⟨some i, j, h⟩
  · exact ⟨none, fun i j ne h => moves ⟨i,j,ne,h⟩⟩

/-- Descending priority order using the indicated geometry and source reference. -/
def priorityFrame (m : Option (Fin 4)) (side : Bool) : Equiv.Perm (Fin 4) :=
  rank input mol c root data
    (sourceKeysAt input single
      (profileFamily input mol p (finalQuery input mol agreement c)) data.target data.frame
      (observedGeometry input side) (m.map (input.detectedMultiCenterMolecule.ligandAtomAt c)).toList)

/-- Parity of the source priority frame on the indicated geometry. -/
def orientation (m : Option (Fin 4)) (side : Bool) : Bool :=
  matchingEven (priorityFrame input mol agreement single c data p m side)

/-- The same ranking parity under reflection gives uppercase. A reversal gives lowercase.
The absolute letter uses the original configuration and original ranking parity. -/
def orientedLabel (base : ℝ) (original reflected : Bool) : LocalizedAuxiliaryLabel :=
  let raw := sideLetter base false original
  if original = reflected then .chiral raw else .pseudoasymmetric (pseudoRSOfRS raw)

private theorem mirror_label (base : ℝ) (unit : base = 1 ∨ base = -1) (a b : Bool) :
    caseFromMirror? (some (sideLetter base false a)) (some (sideLetter base true b)) =
      some (orientedLabel base a b) := by
  rcases unit with rfl | rfl <;> cases a <;> cases b <;>
    norm_num [caseFromMirror?, orientedLabel, sideLetter, letterOfSign, RS.swap] <;> decide

include calibrated in
private theorem source_read (side : Bool) (k : Fin 4 → RefinedKey) :
    sourceReading input (observedGeometry input side) data.frame k =
      some (sideLetter (input.detectedMultiCenterMolecule.configurationSign cfg c) side
        (matchingEven (rank input mol c root data k))) := by
  have atoms := ranked_eq input mol c root data k
  rw [data.read.atoms] at atoms
  unfold sourceReading
  rw [atoms]
  cases side <;> simp [observedGeometry, readback_mirror, readback_enum input cfg c
    (calibrated c), handedness_eq_matching, sideLetter]

include agreement admissible supported charge calibrated addr model in
private theorem side_of_success (m : Option (Fin 4)) (eligible : Eligible input cfg c m)
    (side : Bool) (v : RS)
    (success : step input mol root (structuralDepth mol root) (observedGeometry input side) [] = some v) :
    some v = some (sideLetter (input.detectedMultiCenterMolecule.configurationSign cfg c) side
      (orientation input mol agreement single c data p m side)) := by
  let geom := observedGeometry input side
  let depth := structuralDepth mol root
  let family := profileFamily input mol p (finalQuery input mol agreement c)
  let source := sourceKeysAt input single family data.target data.frame geom []
  let actual := keys input mol single c root data depth geom []
  have fam := LocalizedChemicalRingSourcePromotionCancellation.sourceModel_family_eq_generated
    input single mol agreement admissible supported model (finalQuery input mol agreement c)
  change family = generatedFamily input mol depth root at fam
  have sourceEq (i j : Fin 4) : actual i = actual j ↔ source i = source j := by
    change _ ↔ sourceKeysAt _ _ family _ _ _ _ _ = sourceKeysAt _ _ family _ _ _ _ _
    rw [fam, ← LocalizedChemicalRingJointMarkerRanking.refined_compare_eq_iff,
      ← LocalizedChemicalRingJointMarkerRanking.refined_compare_eq_iff (sourceKeysAt _ _ _ _ _ _ _ i)]
    exact (congrArg (· = Ordering.eq) (keys_compare_eq input mol single c root data depth geom [] i j)).to_iff
  have sourceRun : sourceStep input single family data.target data.frame geom [] = some v := by
    rw [fam, ← step_eq_source input mol single c root data depth agreement admissible supported]
    exact success
  cases m with
  | none =>
    have strict : Function.Injective source := by
      intro i j tie
      by_contra ne
      have transport := (keys_eq_iff_physicalTransport input mol agreement admissible supported
        single charge cfg calibrated c root data (root_reached input mol agreement c) rfl addr []
        side i j ne).mp ((sourceEq i j).mpr tie)
      exact eligible _ _ (fun h => ne (data.ligandOf.injective h)) transport
    rw [sourceStep_eq_strict _ _ _ _ _ _ _ strict] at sourceRun
    exact sourceRun.symm.trans (source_read input mol cfg calibrated c data side source)
  | some i =>
    obtain ⟨j, ne, moves⟩ := eligible
    let a := data.ligandOf.symm i
    let b := data.ligandOf.symm j
    have ab : a ≠ b := fun h => ne (data.ligandOf.symm.injective h)
    have tied : source a = source b := (sourceEq a b).mp
      ((keys_eq_iff_physicalTransport input mol agreement admissible supported single charge cfg
        calibrated c root data (root_reached input mol agreement c) rfl addr [] side a b ab).mpr
          (by simpa [a,b] using moves))
    have member := (sourceSelectedSlots_mem_iff source a).mpr
      ⟨List.mem_finRange _, b, List.mem_finRange _, Ne.symm ab, tied.symm⟩
    rw [sourceStep_eq_consensus _ _ _ _ _ _ _ (fun inj => ab (inj tied))] at sourceRun
    have found := ((LocalizedChemicalRingSenseTransport.consensus_eq_some_iff _ _).mp sourceRun).2
      _ (List.mem_map_of_mem member)
    rw [sourceFallback_eq_some _ _ _ _ _ _ _ _ _ (frameAtom_eq_referenceAt input mol c root data a)] at found
    split at found
    · have atom : referenceAt input mol c root data a =
          input.detectedMultiCenterMolecule.ligandAtomAt c i := by simp [referenceAt,a]
      rw [atom] at found
      exact found.symm.trans (source_read input mol cfg calibrated c data side _)
    · cases found

include agreement admissible supported charge calibrated addr model in
/-- Exact public-facing meaning for each eligible physical frame of every class. -/
theorem exact_entry (m : Option (Fin 4)) (eligible : Eligible input cfg c m)
    (outcome : Option LocalizedAuxiliaryLabel) :
    (c.1.val, outcome) ∈ analyze input mol ↔
      (if RootSuccess input mol agreement single cfg c data p then
        let parity := orientation input mol agreement single c data p m
        some (orientedLabel (input.detectedMultiCenterMolecule.configurationSign cfg c)
          (parity false) (parity true)) else none) = outcome := by
  have classifies := LocalizedChemicalRingTwoPairReport.allRoot_success_refusal_iff input mol
    agreement admissible supported single charge cfg calibrated c data addr p model
  rw [mem_analyze_at_center_iff]
  by_cases ok : RootSuccess input mol agreement single cfg c data p
  · rw [if_pos ok]
    obtain ⟨label, found⟩ := classifies.1.mpr ok
    rw [mem_analyze_at_center_iff] at found
    let read := fun side => step input mol root (structuralDepth mol root) (observedGeometry input side) []
    change caseFromMirror? (read false) (read true) = some label at found
    change caseFromMirror? (read false) (read true) = outcome ↔ _
    cases orig : read false with
    | none => simp [orig, caseFromMirror?] at found
    | some a =>
      cases mir : read true with
      | none => simp [orig, mir, caseFromMirror?] at found
      | some b =>
        have result := mirror_label _ (LocalizedChemicalRingPhysicalSense.configurationSign_unit input cfg c)
          (orientation input mol agreement single c data p m false)
          (orientation input mol agreement single c data p m true)
        rw [side_of_success input mol agreement admissible supported single charge cfg
          calibrated c data addr p model m eligible false a orig,
          side_of_success input mol agreement admissible supported single charge cfg calibrated
          c data addr p model m eligible true b mir, result]
  · rw [if_neg ok, (mem_analyze_at_center_iff _ _ _ _).mp (classifies.2.mpr ok)]

/-- The input supplies the four ordered points. The explicit positive-determinant
normalization places the fourth ligand behind the first three for the viewing test. -/
def ViewedLetter (atoms : List Nat) (raw : RS) : Prop :=
  ∃ a b d e : CartesianPoint3,
    atoms.mapM (inputGeometry input) = some [a,b,d,e] ∧
    let transform := CIPTetrahedralArbitraryFrameSourceConformance.normalizationT a b d e
    0 < transform.determinant ∧ CIPTetrahedralViewingCalibration.SourceCalibratedDescriptor
      ([a,b,d,e].map transform.applyPoint) raw

include agreement admissible supported charge calibrated addr model in
theorem viewed_entry (m : Option (Fin 4)) (eligible : Eligible input cfg c m)
    (label : LocalizedAuxiliaryLabel) (entry : (c.1.val, some label) ∈ analyze input mol) :
    let frame := priorityFrame input mol agreement single c data p m
    ∃ raw, ViewedLetter input (enumeration input c (frame false)) raw ∧
      label = (if matchingEven (frame false) = matchingEven (frame true) then
        .chiral raw else .pseudoasymmetric (pseudoRSOfRS raw)) := by
  let frame := priorityFrame input mol agreement single c data p m
  let base := input.detectedMultiCenterMolecule.configurationSign cfg c
  let raw := sideLetter base false (matchingEven (frame false))
  have output := (exact_entry input mol agreement admissible supported single charge cfg
    calibrated c data addr p model m eligible (some label)).mp entry
  split at output
  · refine ⟨raw, ?_, (Option.some.inj output).symm⟩
    have read := readback_enum input cfg c (calibrated c) (frame false)
    rw [handedness_eq_matching] at read
    change ((enumeration input c (frame false)).mapM (inputGeometry input)).bind
      descriptorOfPriorityOrderedPoints? = some raw at read
    cases pointsEq : (enumeration input c (frame false)).mapM (inputGeometry input) with
    | none => simp [pointsEq] at read
    | some points =>
      rw [pointsEq] at read
      change descriptorOfPriorityOrderedPoints? points = some raw at read
      obtain ⟨a,b,d,e,listEq,sign⟩ := (descriptorOfPriorityOrderedPoints?_eq_some_iff _ _).mp read
      subst points
      have nonzero : TetrahedralAffineViewingNormalization.frameVolume a b d e ≠ 0 := by
        unfold TetrahedralAffineViewingNormalization.frameVolume
        cases which : raw with
        | R => exact ne_of_lt (by simpa only [which] using sign)
        | S => exact ne_of_gt (by simpa only [which] using sign)
      exact ⟨a,b,d,e,pointsEq,
        TetrahedralAffineViewingNormalization.viewingTransform_determinant_pos _ _ _ _ nonzero,
        (CIPTetrahedralArbitraryFrameSourceConformance.descriptorOfPriorityOrderedPoints?_eq_some_iff_source_of_normalized
          a b d e raw nonzero).mp read⟩
  · cases output

end
end TetraStereo.OneCenter.LocalizedChemicalRingAllRootLetters

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAllRootLetters.exists_eligible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAllRootLetters.exact_entry
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAllRootLetters.viewed_entry
