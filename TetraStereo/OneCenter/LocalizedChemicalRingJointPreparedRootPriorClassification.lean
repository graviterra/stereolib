import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSuccess
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReflection
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusReflection
import TetraStereo.OneCenter.LocalizedRetainedRule5ClassBound
import TetraStereo.OneCenter.LocalizedFourSlotReflectionParity
import TetraStereo.OneCenter.LocalizedPseudoasymmetricClassification
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Lowercase classification of the actual prepared root from the independent prior key count

The actual root descriptor is already known to be the mirror-case classification of the two
ordinary rank signs on the actually generated original and reflected states.  This module
identifies the remaining lowercase mechanism with the independent retained prior-key pair count
of the actual generated state.  The argument is comparison-theoretic: the reflected generated
state has the same generated graph family up to the actual generated mirror, so its full retained
key comparisons agree with the same-graph reflected-key comparisons.  On a prior tie the full comparison reverses and otherwise
it is unchanged.  Four-slot reflection parity then gives the rank handedness ratio as
`(-1) ^ completeRule5PairCount`.  Injective full keys bound that count by two, so the only
lowercase count is one.

No mirror rank, desired label, sorting success, or pseudoasymmetry premise is introduced.  The
source is the actual `ordinaryGeometryRank` and the actual `rawStateKeys` of the generated states.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPriorClassification

open CertifiedLocalizedCIPInput
open MultiCenterMolecule (PairwiseProperDistinguishable)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt rank observedGeometry)
open LocalizedChemicalRingJointPreparedOccurrenceCorrection (SourceProper)
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingJointPreparedExecution (keys)
open LocalizedChemicalRingJointPreparedRootInput (root_reached root_data)
open LocalizedChemicalRingJointPreparedRootEmptyContext
  (ordinaryGeometryRank geometryRank_nil refinedKey_nil)
open LocalizedChemicalRingPhysicalSense (inputGeometry letterOfSign)
open LocalizedChemicalRingPreparedContextRecursion (preparedAssignCenter? preparedDescriptor?)
open LocalizedGenericMarkedRecalculation (structuralDepth caseFromMirror?)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedChemicalRingJointMarkerKey (JointMarker)
open LocalizedChemicalRingJointMarkerRanking
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedOrdinaryRanking
  (rawStateKeys rawStateFrames RetainedExecutionFrame keyOrder keyOrder_pairwise)
open LocalizedMarkedRetainedStateReader (rawStateDescriptorMap)
open LocalizedChemicalRingReferenceConsensusReflection
  (mirrorFact rawStateKeys_mirror_compare slotPerm_eq_of_compare)
open LocalizedRetainedDescriptorTransport
  (retainedCompleteLigandPriorKeyAt_reflect retainedPairCompare_reflect)
open LocalizedFourSlotReflectionParity
  (slotKey priorTieCount priorTieCount_completeRule5PairCount FourSlotReflection
    descendingReflection_sign)
open LocalizedRetainedRule5ClassBound
  (retainedPriorClass_atMostTwo completeRule5PairCount_le_two_of_injective
    completeRule5PairCount_even_or_one_of_injective)
open LocalizedChemicalRingCompletenessMarked
  (slotPerm slotAt keyOrder_eq_slots keyOrder_length mul_unit letterOfSign_neg swap_swap)
open DeclarativeCIP
open Certificate.CanonicalSphereKey (Key)

noncomputable section
open scoped Classical

section Generic

/-- Composition order for permutations: `e.trans f` acts as `f` after `e`. -/
private theorem equiv_trans_eq_mul {α : Type*} (e f : Equiv.Perm α) :
    e.trans f = f * e := by
  ext x
  simp [Equiv.trans_apply]

/-- `slotPerm` is a strictly descending permutation of an injective four-slot key family. -/
theorem slotPerm_strict_desc {α : Type} [LinearOrder α]
    (keys : Fin 4 → α) (injective : Function.Injective keys) :
    ∀ p q : Fin 4, p < q → keys (slotPerm keys q) < keys (slotPerm keys p) := by
  intro p q hpq
  have hpair := List.pairwise_iff_get.mp (keyOrder_pairwise keys (List.finRange 4))
  have hle0 :
      keys ((keyOrder keys (List.finRange 4)).get
        ⟨q.val, by rw [keyOrder_length keys]; exact q.isLt⟩) ≤
      keys ((keyOrder keys (List.finRange 4)).get
        ⟨p.val, by rw [keyOrder_length keys]; exact p.isLt⟩) :=
    hpair ⟨p.val, by rw [keyOrder_length keys]; exact p.isLt⟩
      ⟨q.val, by rw [keyOrder_length keys]; exact q.isLt⟩ (by simpa using hpq)
  have hle : keys (slotPerm keys q) ≤ keys (slotPerm keys p) := by
    fin_cases p <;> fin_cases q <;> simp_all [keyOrder_eq_slots keys]
  have hne : keys (slotPerm keys q) ≠ keys (slotPerm keys p) := by
    intro equal
    have hσ : slotPerm keys q = slotPerm keys p := injective equal
    exact (ne_of_lt hpq) ((slotPerm keys).injective hσ).symm
  exact lt_of_le_of_ne hle hne

/-- A unit times a unit has product one only in the equal case. -/
private theorem eq_of_mul_eq_one_of_unit {a b : ℝ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (h : a * b = 1) : b = a := by
  rcases ha with rfl | rfl
  all_goals rcases hb with rfl | rfl
  all_goals norm_num at *

/-- A unit times a unit has product minus one exactly in the opposite case. -/
private theorem eq_neg_of_mul_eq_neg_one_of_unit {a b : ℝ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (h : a * b = -1) : b = -a := by
  rcases ha with rfl | rfl
  all_goals rcases hb with rfl | rfl
  all_goals norm_num at *

/-- A unit sign's letter is never its own swap. -/
private theorem letterOfSign_swap_ne_self (s : ℝ) : (letterOfSign s).swap ≠ letterOfSign s := by
  cases letterOfSign s <;> simp [RS.swap]

/-- The single `caseFromMirror?` calculation used by the root bridge.  The product hypothesis is
the independent parity statement; only the unit classification and the prior count interval are
needed after it. -/
theorem caseFromMirror_classification_of_unit_product (s t : ℝ) (count : ℕ)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (hcount : count = 0 ∨ count = 1 ∨ count = 2)
    (hproduct : s * t = (-1 : ℝ) ^ count) :
    caseFromMirror? (some (letterOfSign s)) (some (letterOfSign t).swap) =
      some (classifyTetrahedralRSPseudo (letterOfSign s) count) := by
  rcases hcount with rfl | rfl | rfl
  · have hsame : t = s :=
      eq_of_mul_eq_one_of_unit hs ht (by simpa using hproduct)
    have hne : (letterOfSign t).swap ≠ letterOfSign s := by
      simpa [hsame] using letterOfSign_swap_ne_self s
    simp [caseFromMirror?, classifyTetrahedralRSPseudo, hne]
  · have hneg : t = -s :=
      eq_neg_of_mul_eq_neg_one_of_unit hs ht (by simpa using hproduct)
    have heq : (letterOfSign t).swap = letterOfSign s := by
      rw [hneg, letterOfSign_neg s hs, swap_swap]
    simp [caseFromMirror?, classifyTetrahedralRSPseudo, heq]
  · have hsame : t = s :=
      eq_of_mul_eq_one_of_unit hs ht (by simpa using hproduct)
    have hne : (letterOfSign t).swap ≠ letterOfSign s := by
      simpa [hsame] using letterOfSign_swap_ne_self s
    simp [caseFromMirror?, classifyTetrahedralRSPseudo, hne]

end Generic

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

section RankAlgebra

variable (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)

/-- The actual rank permutation is the ligand frame permutation followed by the key order. -/
theorem rank_eq_ligand_mul_slotPerm {K : Type} [LinearOrder K] (keys : Fin 4 → K) :
    rank input mol c node data keys = data.ligandOf * slotPerm keys := by
  unfold rank
  exact equiv_trans_eq_mul (slotPerm keys) data.ligandOf

end RankAlgebra

include agreement admissible supported charge calibrated in
/-- The actual root descriptor is classified by the independent prior-key pair count of the
actually generated original state.  The reflected actual rank is not assumed; its comparison and
handedness are derived from the actual generated mirror state. -/
theorem root_descriptor_eq_prior_classification
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (rootAddress : data.target.1.address = []) (current : node.atom = c.1.val)
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg c) :
    preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] [] node =
      some (classifyTetrahedralRSPseudo
        (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c *
          permHandedness (ordinaryGeometryRank input single mol c node data false)))
        (completeRule5PairCount
          (rawStateKeys input single
            (sideState input mol node (inputGeometry input) [] false)
            data.target data.real
            ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl))) := by
  let state0 : OccurrenceAuxState :=
    sideState input mol node (inputGeometry input) [] false
  let state1 : OccurrenceAuxState :=
    sideState input mol node (inputGeometry input) [] true
  let unit : DetectedOccurrence input.moleculeGraph := ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  let frames0 := rawStateFrames input single state0 data.target data.real unit rfl
  let frames1 := rawStateFrames input single state1 data.target data.real unit rfl
  let K0 : Fin 4 → CompleteLigandRule5Key :=
    rawStateKeys input single state0 data.target data.real unit rfl
  let K1 : Fin 4 → CompleteLigandRule5Key :=
    rawStateKeys input single state1 data.target data.real unit rfl
  let map0 := rawStateDescriptorMap input state0
  let graphs0 := frames0.actualArmGraphs
  let W0 : ℕ := frames0.W
  let D0 : ℕ := frames0.D
  let K0at : Fin 4 → CompleteLigandRule5Key := fun slot =>
    retainedCompleteLigandRule5KeyAt input.moleculeGraph map0 unit (graphs0 slot) W0 D0
  let Kr : Fin 4 → CompleteLigandRule5Key := fun slot =>
    retainedCompleteLigandRule5KeyAt input.moleculeGraph map0.reflect unit (graphs0 slot) W0 D0

  have hstate1 : state1 = state0.map mirrorFact := by
    simpa [state0, state1, LocalizedChemicalRingJointPreparedCorrectionWitness.sideState] using
      (LocalizedChemicalRingJointPreparedReflection.generated_mirror input mol
        (structuralDepth mol node) (inputGeometry input) node [])

  have hroot := LocalizedChemicalRingJointPreparedRootSuccess.root_descriptor_eq_ordinary_signs
    input mol agreement admissible supported single charge cfg calibrated c node data reached
    rootAddress current properDistinct

  have hsource : Function.Injective
      (LocalizedChemicalRingJointPreparedExecution.keys input mol single c node data
        (structuralDepth mol node) (observedGeometry input false) []) :=
    LocalizedChemicalRingJointPreparedRootAssignment.keys_injective input mol single cfg c node data rootAddress current properDistinct []
      (LocalizedChemicalRingJointPreparedRootSuccess.root_tie_sourceProper input mol agreement
        admissible supported single charge cfg calibrated c node data reached rootAddress [])
      false
  have hkeys0 : Function.Injective (fun slot =>
      refinedKey input single state0 data.target data.real unit rfl []
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) slot) := by
    simpa [LocalizedChemicalRingJointPreparedExecution.keys,
      LocalizedChemicalRingJointPreparedCorrectionWitness.sideState,
      LocalizedChemicalRingInheritedRefusalCases.observedGeometry,
      LocalizedChemicalRingJointMarkerFrameExecution.slotKeys] using hsource

  have K0inj : Function.Injective K0 := by
    intro left right equal
    apply hkeys0
    have hfull : refinedKey input single state0 data.target data.real unit rfl []
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left =
        refinedKey input single state0 data.target data.real unit rfl []
          (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) right := by
      rw [refinedKey_nil, refinedKey_nil]
      simpa [K0] using congrArg (fun key => toLex (key, ([] : JointMarker))) equal
    exact hfull

  have hK0at : K0 = K0at := by
    funext slot
    rfl

  have K0atInj : Function.Injective K0at := by
    rw [← hK0at]
    exact K0inj

  have hK0prior : ∀ slot, (ofLex (K0 slot)).1 =
      retainedCompleteLigandPriorKeyAt input.moleculeGraph map0 unit (graphs0 slot) W0 D0 := by
    intro slot
    rw [hK0at]
    rfl

  have hKrPrior : ∀ slot, (ofLex (Kr slot)).1 = (ofLex (K0 slot)).1 := by
    intro slot
    rw [hK0prior slot]
    simpa [Kr] using
      (retainedCompleteLigandPriorKeyAt_reflect input.moleculeGraph map0 unit
        (graphs0 slot) W0 D0)

  have hKrCompare : ∀ left right, compare (Kr left) (Kr right) =
      if retainedCompleteLigandPriorKeyAt input.moleculeGraph map0 unit (graphs0 left) W0 D0 =
          retainedCompleteLigandPriorKeyAt input.moleculeGraph map0 unit (graphs0 right) W0 D0 then
        (compare (K0 left) (K0 right)).swap
      else compare (K0 left) (K0 right) := by
    intro left right
    rw [show compare (Kr left) (Kr right) =
        compare
          (retainedCompleteLigandRule5KeyAt input.moleculeGraph map0.reflect unit
            (graphs0 left) W0 D0)
          (retainedCompleteLigandRule5KeyAt input.moleculeGraph map0.reflect unit
            (graphs0 right) W0 D0) from rfl]
    rw [retainedPairCompare_reflect input.moleculeGraph map0 unit
      (graphs0 left) (graphs0 right) W0 D0]
    rfl

  have Krinj : Function.Injective Kr := by
    intro left right equal
    have hcmp : compare (Kr left) (Kr right) = Ordering.eq :=
      (completeLigandRule5Key_compare_eq_iff _ _).2 equal
    rw [hKrCompare left right] at hcmp
    by_cases hp : retainedCompleteLigandPriorKeyAt input.moleculeGraph map0 unit
        (graphs0 left) W0 D0 =
        retainedCompleteLigandPriorKeyAt input.moleculeGraph map0 unit (graphs0 right) W0 D0
    · rw [if_pos hp] at hcmp
      have h0 : compare (K0 left) (K0 right) = Ordering.eq := by
        simpa using congrArg Ordering.swap hcmp
      exact K0inj ((completeLigandRule5Key_compare_eq_iff _ _).1 h0)
    · rw [if_neg hp] at hcmp
      exact K0inj ((completeLigandRule5Key_compare_eq_iff _ _).1 hcmp)

  have hMirrorCompare : ∀ left right, compare (K1 left) (K1 right) =
      if (ofLex (K0 left)).1 = (ofLex (K0 right)).1 then
        (compare (K0 left) (K0 right)).swap
      else compare (K0 left) (K0 right) := by
    intro left right
    have h := rawStateKeys_mirror_compare input single state0 data.target data.real unit rfl
      left right
    rw [← hstate1] at h
    simpa [K0, K1] using h

  have hcompActualKr : ∀ left right, compare (K1 left) (K1 right) =
      compare (Kr left) (Kr right) := by
    intro left right
    rw [hMirrorCompare left right, hKrCompare left right]
    rw [← hK0prior left, ← hK0prior right]

  have hK1perm : slotPerm K1 = slotPerm Kr :=
    slotPerm_eq_of_compare (K := Kr) (K' := K1) Krinj hcompActualKr

  let prior : Fin 4 → CompleteLigandPriorKey := fun slot => (ofLex (K0 slot)).1
  let later : Fin 4 → List (Key StereoLabel) := fun slot => (ofLex (K0 slot)).2
  let laterReflect : Fin 4 → List (Key StereoLabel) := fun slot => (ofLex (Kr slot)).2

  have hslotK0 : slotKey prior later = K0 := by
    funext slot
    simp [slotKey, prior, later]
  have hslotKr : slotKey prior laterReflect = Kr := by
    funext slot
    simp only [slotKey, prior, laterReflect, ← hKrPrior slot]
    rfl

  let dataR : FourSlotReflection CompleteLigandPriorKey (List (Key StereoLabel)) := {
    prior := prior
    later := later
    laterReflect := laterReflect
    keyInjective := by
      rw [hslotK0]
      exact K0inj
    reflectInjective := by
      rw [hslotKr]
      exact Krinj
    classAtMostTwo := by
      intro i j k hij hik
      have hij' : retainedCompleteLigandPriorKeyAt input.moleculeGraph map0 unit
          (graphs0 i) W0 D0 =
          retainedCompleteLigandPriorKeyAt input.moleculeGraph map0 unit (graphs0 j) W0 D0 := by
        change (ofLex (K0 i)).1 = (ofLex (K0 j)).1
        rw [hK0prior i, hK0prior j]
        exact hij
      have hik' : retainedCompleteLigandPriorKeyAt input.moleculeGraph map0 unit
          (graphs0 i) W0 D0 =
          retainedCompleteLigandPriorKeyAt input.moleculeGraph map0 unit (graphs0 k) W0 D0 := by
        change (ofLex (K0 i)).1 = (ofLex (K0 k)).1
        rw [hK0prior i, hK0prior k]
        exact hik
      rcases retainedPriorClass_atMostTwo input.moleculeGraph map0 unit graphs0 W0 D0 K0atInj
          i j k hij' hik' with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)
    tieReverses := by
      intro i j distinct tied
      have tied' : retainedCompleteLigandPriorKeyAt input.moleculeGraph map0 unit
          (graphs0 i) W0 D0 =
          retainedCompleteLigandPriorKeyAt input.moleculeGraph map0 unit (graphs0 j) W0 D0 := by
        change (ofLex (K0 i)).1 = (ofLex (K0 j)).1
        rw [hK0prior i, hK0prior j]
        exact tied
      have hcmp := hKrCompare i j
      rw [if_pos tied'] at hcmp
      rw [show slotKey prior later i = K0 i from congrFun hslotK0 i,
        show slotKey prior later j = K0 j from congrFun hslotK0 j,
        show slotKey prior laterReflect j = Kr j from congrFun hslotKr j,
        show slotKey prior laterReflect i = Kr i from congrFun hslotKr i]
      constructor
      · intro hlt
        have h0 : compare (K0 i) (K0 j) = Ordering.lt :=
          (completeLigandRule5Key_compare_lt_iff _ _).2 hlt
        have h1 : compare (Kr i) (Kr j) = Ordering.gt := by
          rw [hcmp, h0]
          rfl
        exact (completeLigandRule5Key_compare_gt_iff _ _).1 h1
      · intro hlt
        have h1 : compare (Kr i) (Kr j) = Ordering.gt :=
          (completeLigandRule5Key_compare_gt_iff _ _).2 hlt
        have hswap : (compare (K0 i) (K0 j)).swap = Ordering.gt := by
          rw [← hcmp]
          exact h1
        have h0 : compare (K0 i) (K0 j) = Ordering.lt := by
          have := congrArg Ordering.swap hswap
          simpa using this
        exact (completeLigandRule5Key_compare_lt_iff _ _).1 h0
  }

  let σ0 : Equiv.Perm (Fin 4) := slotPerm K0
  let σr : Equiv.Perm (Fin 4) := slotPerm Kr
  have hσ0 : ∀ p q, p < q → slotKey prior later (σ0 q) < slotKey prior later (σ0 p) := by
    intro p q hpq
    simpa [σ0, hslotK0] using slotPerm_strict_desc K0 K0inj p q hpq
  have hσr : ∀ p q, p < q →
      slotKey prior laterReflect (σr q) < slotKey prior laterReflect (σr p) := by
    intro p q hpq
    simpa [σr, hslotKr] using slotPerm_strict_desc Kr Krinj p q hpq

  have hdesc := descendingReflection_sign dataR σ0 σr hσ0 hσr
  have htieCount : priorTieCount prior = completeRule5PairCount K0 := by
    simpa [prior] using priorTieCount_completeRule5PairCount K0
  have hratio : permHandedness (σ0⁻¹ * σr) = (-1 : ℝ) ^ completeRule5PairCount K0 := by
    simpa only [dataR, htieCount] using hdesc.2.2

  have hcountEq : completeRule5PairCount K0 = completeRule5PairCount K0at := by
    rw [hK0at]
  have hle : completeRule5PairCount K0 ≤ 2 := by
    rw [hcountEq]
    exact completeRule5PairCount_le_two_of_injective input.moleculeGraph map0 unit graphs0 W0 D0
      K0atInj
  have heven : Even (completeRule5PairCount K0) ∨ completeRule5PairCount K0 = 1 := by
    rw [hcountEq]
    exact completeRule5PairCount_even_or_one_of_injective input.moleculeGraph map0 unit graphs0 W0 D0
      K0atInj
  have hcount : completeRule5PairCount K0 = 0 ∨ completeRule5PairCount K0 = 1 ∨
      completeRule5PairCount K0 = 2 := by
    rcases heven with ⟨k, hk⟩ | hone
    · have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · left
        omega
      · right
        right
        omega
    · exact Or.inr (Or.inl hone)

  have hr0 : ordinaryGeometryRank input single mol c node data false =
      data.ligandOf * σ0 := by
    unfold ordinaryGeometryRank
    rw [rank_eq_ligand_mul_slotPerm]
  have hr1 : ordinaryGeometryRank input single mol c node data true =
      data.ligandOf * σr := by
    unfold ordinaryGeometryRank
    rw [rank_eq_ligand_mul_slotPerm]
    change data.ligandOf * slotPerm K1 = data.ligandOf * σr
    rw [hK1perm]

  have hratioActual : permHandedness
      ((ordinaryGeometryRank input single mol c node data false)⁻¹ *
        ordinaryGeometryRank input single mol c node data true) =
      (-1 : ℝ) ^ completeRule5PairCount K0 := by
    rw [hr0, hr1]
    have hgroup : (data.ligandOf * σ0)⁻¹ * (data.ligandOf * σr) = σ0⁻¹ * σr := by
      rw [mul_inv_rev]
      simp [mul_assoc]
    rw [hgroup]
    exact hratio

  have hproduct : permHandedness (ordinaryGeometryRank input single mol c node data false) *
      permHandedness (ordinaryGeometryRank input single mol c node data true) =
      (-1 : ℝ) ^ completeRule5PairCount K0 := by
    simpa [permHandedness_mul, permHandedness_inv] using hratioActual

  let cs : ℝ := input.detectedMultiCenterMolecule.configurationSign cfg c
  let h0 : ℝ := permHandedness (ordinaryGeometryRank input single mol c node data false)
  let h1 : ℝ := permHandedness (ordinaryGeometryRank input single mol c node data true)
  let s : ℝ := cs * h0
  let t : ℝ := cs * h1
  let count : ℕ := completeRule5PairCount K0

  have hcs : cs = 1 ∨ cs = -1 := by
    dsimp [cs]
    simpa [MultiCenterMolecule.configurationSign] using
      (permHandedness_eq_one_or_eq_neg_one (cfg c))
  have hcs2 : cs * cs = 1 := by
    dsimp [cs]
    simpa [MultiCenterMolecule.configurationSign] using
      (permHandedness_mul_self (cfg c))
  have hh0 : h0 = 1 ∨ h0 = -1 := by
    dsimp [h0]
    exact permHandedness_eq_one_or_eq_neg_one _
  have hh1 : h1 = 1 ∨ h1 = -1 := by
    dsimp [h1]
    exact permHandedness_eq_one_or_eq_neg_one _
  have hs : s = 1 ∨ s = -1 := by
    dsimp [s]
    exact mul_unit hcs hh0
  have ht : t = 1 ∨ t = -1 := by
    dsimp [t]
    exact mul_unit hcs hh1
  have hprod : s * t = (-1 : ℝ) ^ count := by
    calc
      s * t = (cs * h0) * (cs * h1) := rfl
      _ = (cs * cs) * (h0 * h1) := by ring
      _ = h0 * h1 := by rw [hcs2, one_mul]
      _ = (-1 : ℝ) ^ count := by
        dsimp [h0, h1, count]
        exact hproduct

  have hclass := caseFromMirror_classification_of_unit_product s t count hs ht hcount hprod

  rw [hroot]
  change caseFromMirror? (some (letterOfSign s)) (some (letterOfSign t).swap) =
    some (classifyTetrahedralRSPseudo (letterOfSign s) count)
  exact hclass

include agreement admissible supported charge calibrated in
/-- The actual assignment at a properly distinguishable detected root is the independent
prior-key classification of its actual ordinary original rank. -/
theorem assignCenter_eq_prior_classification
    (c : input.detectedMultiCenterMolecule.Center)
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg c) :
    ∃ (data : OccurrenceData input mol c (canonicalCenterRoot c.1.val))
      (_rootAddress : data.target.1.address = []),
      preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) c.1.val =
        some (classifyTetrahedralRSPseudo
          (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c *
            permHandedness (ordinaryGeometryRank input single mol c
              (canonicalCenterRoot c.1.val) data false)))
          (completeRule5PairCount
            (rawStateKeys input single
              (sideState input mol (canonicalCenterRoot c.1.val) (inputGeometry input) [] false)
              data.target data.real
              ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl))) := by
  obtain ⟨data, rootAddress⟩ :=
    root_data input mol agreement admissible supported single c
  have h := root_descriptor_eq_prior_classification input mol agreement admissible supported single
    charge cfg calibrated c (canonicalCenterRoot c.1.val) data
    (root_reached input mol agreement c) rootAddress rfl properDistinct
  change preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) c.1.val = _ at h
  exact ⟨data, rootAddress, h⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPriorClassification

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPriorClassification.slotPerm_strict_desc
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPriorClassification.rank_eq_ligand_mul_slotPerm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPriorClassification.caseFromMirror_classification_of_unit_product
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPriorClassification.root_descriptor_eq_prior_classification
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPriorClassification.assignCenter_eq_prior_classification
