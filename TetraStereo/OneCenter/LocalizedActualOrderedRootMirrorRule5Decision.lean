import TetraStereo.OneCenter.LocalizedActualOrderedRootMirrorPriorTie
import TetraStereo.OneCenter.LocalizedActualOrderedRootRule5Seniority
import TetraStereo.KernelOnly

set_option autoImplicit false


































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open RootedTetrahedralBranchSymmetry

namespace CertifiedLocalizedCIPInput

/-- After a prior tie the pulled-back compound comparison is the common-`R` reading-list
comparison. -/
theorem compoundKeyComparison_eq_rule5_of_priorTie (input : CertifiedLocalizedCIPInput)
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key) {i j : Fin 4}
    (htie : priorKeyTie input keys i j) :
    compoundKeyComparison input keys i j =
      input.compareLocalizedRerootCompoundRule5Readings .R
        (keys i).rule5Readings (keys j).rule5Readings := by
  have tied : Ordering.byKey (fun key => key.prior) input.compareLocalizedRerootCompoundRule4bcKeys
      (keys i) (keys j) = .eq := htie
  show compareLex _ _ (keys i) (keys j) = _
  rw [localizedCompareLex_eq_right_of_eq tied]
  rfl

/-- A reading-list comparison with a decisive head is the head comparison. -/
theorem compareLocalizedRerootCompoundRule5Readings_cons_of_ne (input : CertifiedLocalizedCIPInput)
    (commonReference : RS) (u v : input.LocalizedRerootRule5Reading)
    (tailU tailV : List input.LocalizedRerootRule5Reading)
    (decisive : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (input.localizedRerootRule5Descriptor commonReference u)
      (input.localizedRerootRule5Descriptor commonReference v) ≠ .eq) :
    input.compareLocalizedRerootCompoundRule5Readings commonReference (u :: tailU) (v :: tailV) =
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.localizedRerootRule5Descriptor commonReference u)
        (input.localizedRerootRule5Descriptor commonReference v) := by
  unfold compareLocalizedRerootCompoundRule5Readings
  rw [List.compareLex_cons_cons]
  simp only [Ordering.byKey]
  cases h : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (input.localizedRerootRule5Descriptor commonReference u)
      (input.localizedRerootRule5Descriptor commonReference v)
  · rfl
  · exact absurd h decisive
  · rfl

/-- The cumulative priority comparator decides equality of tables. -/
theorem compareSparseLayers_priority_eq_iff
    (left right : List (List (OfficialSparseEntry (List Nat)))) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority left right =
        .eq ↔ left = right :=
  CompilerProjectionFidelity.compareSparseLayers_eq_eq_iff compareLocalizedCumulativeRule45Priority
    (fun v => (CompilerProjectionFidelity.list_compareLex_eq_eq_iff OfficialRuleMajorKey.compareNat
      CompilerProjectionFidelity.compareNat_self
      (fun l r h => (CompilerProjectionFidelity.compareNat_eq_eq_iff l r).1 h) v v).2 rfl)
    (fun v w hvw => (CompilerProjectionFidelity.list_compareLex_eq_eq_iff
      OfficialRuleMajorKey.compareNat CompilerProjectionFidelity.compareNat_self
      (fun l r h => (CompilerProjectionFidelity.compareNat_eq_eq_iff l r).1 h) v w).1 hvw)
    left right

end CertifiedLocalizedCIPInput

namespace Rule4aTableBridge
namespace ActualCentrePhysicalSetup

open DeclarativeCIP
open CertifiedLocalizedCIPInput.OriginalRootArm

variable {input : LocalizedUniversalReference.Input} (S : ActualCentrePhysicalSetup input)

/-- The production evaluation fuel. -/
local notation "evalFuel" =>
  localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input)

/-! ## Stage-`.rule4b ρ` arms of the ligands -/

/-- A chosen stage-`.rule4b ρ` original-root arm of ligand `ℓ`. -/
noncomputable def arm4b (ℓ : Fin 4) (ρ : RS) :
    input.certified.OriginalRootArm S.center ℓ (.rule4b ρ) S.read :=
  Classical.choice (input.certified.exists_originalRootArm S.center ℓ (.rule4b ρ) S.read)

/-- The frame cursor of slot `i` is reachable from the slot setup's tree source. -/
theorem reachable_frameSlot (i : Fin 4) :
    input.certified.ActualChildReachable (S.frameSlotSetup i).tree.source (S.frame.cursorAt i) := by
  rw [ActualSlotPhysicalSetup.tree_source]
  exact Relation.ReflTransGen.refl

/-- The Rule-4b key of a referenced Rule-5 reading of slot `i` is the stage-`.rule4b ρ` arm key
of its ligand. -/
theorem rule4bKey_eq_arm4b {i : Fin 4} {u : input.certified.LocalizedRerootRule5Reading}
    (hu : u ∈ (S.frameKey i).rule5Readings) {ρ : RS} (hρ : u.prior.reference? = some ρ) :
    u.prior.rule4bKey = (S.arm4b (S.slotEquiv.symm i) ρ).key := by
  obtain ⟨hmem, _⟩ := (S.frameKey_readings i).2 u hu
  obtain ⟨_, hbuild⟩ := S.frameKey_priorReadings i u.prior hmem
  rw [hρ] at hbuild
  obtain ⟨b4b, _, _⟩ := reading_some_built S.top S.referenceView evalFuel _ ρ hbuild
  have harm := S.arm_production_built (S.arm4b (S.slotEquiv.symm i) ρ)
  rw [S.slot_slotEquiv_symm] at harm
  exact Option.some.inj (b4b.symm.trans harm)

/-- The Rule-4b build of a referenced reading of slot `i`, in the slot-setup form. -/
theorem rule4bKey_built {i : Fin 4} {u : input.certified.LocalizedRerootRule5Reading}
    (hu : u ∈ (S.frameKey i).rule5Readings) {ρ : RS} (hρ : u.prior.reference? = some ρ) :
    input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4b ρ)
        (ActualReaderPhysicalBranchInverse.topTarget input S.c)
        (referenceDependencyView input S.c) evalFuel (S.frame.cursorAt i) =
      some u.prior.rule4bKey := by
  obtain ⟨hmem, _⟩ := (S.frameKey_readings i).2 u hu
  obtain ⟨_, hbuild⟩ := S.frameKey_priorReadings i u.prior hmem
  rw [hρ] at hbuild
  exact (reading_some_built S.top S.referenceView evalFuel _ ρ hbuild).1



theorem commonR_eq_extend {i : Fin 4} {u : input.certified.LocalizedRerootRule5Reading}
    (hu : u ∈ (S.frameKey i).rule5Readings) {ρ : RS} (hρ : u.prior.reference? = some ρ) :
    u.commonR = input.certified.extendLocalizedRerootCumulativeRule45Key
      (extendLocalizedRule4bPriorityToRule5 ρ .R) u.prior.rule4bKey := by
  obtain ⟨_, hbuild5⟩ := (S.frameKey_readings i).2 u hu
  obtain ⟨cR, _⟩ := rule5Reading_built S.top S.referenceView evalFuel _ hbuild5
  rw [hρ] at cR
  have succ := physical_rule5_success (S.frameSlotSetup i) ρ .R evalFuel (S.frame.cursorAt i)
    (S.reachable_frameSlot i) _ (S.rule4bKey_built hu hρ)
  exact Option.some.inj (cR.symm.trans succ)

/-- The Rule-4b table of a referenced reading is in the no-pseudo stage image. -/
theorem rule4bKey_image {i : Fin 4} {u : input.certified.LocalizedRerootRule5Reading}
    (hu : u ∈ (S.frameKey i).rule5Readings) {ρ : RS} (hρ : u.prior.reference? = some ρ) :
    LocalizedStageDescriptorImage (.rule4b ρ) LocalizedNoPseudoLabel
      u.prior.rule4bKey.descriptor :=
  physical_descriptorImage (S.frameSlotSetup i) (.rule4b ρ) evalFuel (S.frame.cursorAt i)
    (S.reachable_frameSlot i) _ (S.rule4bKey_built hu hρ)

/-! ## The decision at a matched head pair -/

section Distinct

variable (distinct : ∀ i j : Fin 4, i ≠ j →
  ¬ ProperTransport input.certified.detectedMultiCenterMolecule S.cfg S.c i j)
include distinct

/-- The head readings of a distinct ordered-prior-tied pair are matched: complete prior tie,
opposite references, and the same Rule-4b table. -/
theorem head_matched {i j : Fin 4} (hij : i ≠ j)
    (tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) i j)
    {u : input.certified.LocalizedRerootRule5Reading} {tailU}
    (hu : (orderedKeys input.certified S.frameKey i).rule5Readings = u :: tailU)
    {v : input.certified.LocalizedRerootRule5Reading} {tailV}
    (hv : (orderedKeys input.certified S.frameKey j).rule5Readings = v :: tailV)
    {ρ : RS} (hρ : u.prior.reference? = some ρ) :
    u ∈ (S.frameKey i).rule5Readings ∧ v ∈ (S.frameKey j).rule5Readings ∧
      v.prior.reference? = some (RS.swap ρ) ∧
      u.prior.rule4bKey.descriptor = v.prior.rule4bKey.descriptor := by
  obtain ⟨_, _, matched⟩ := input.certified.orderedPriorTie_matched _ _ tie
    (S.frameKey_readings i).1 (S.frameKey_readings j).1
  have matched' : List.Forall₂ (fun u v : input.certified.LocalizedRerootRule5Reading =>
      input.certified.compareRule4bcReadingsComplete u.prior v.prior = .eq)
      (orderedKeys input.certified S.frameKey i).rule5Readings
      (orderedKeys input.certified S.frameKey j).rule5Readings := matched
  rw [hu, hv] at matched'
  have hcomplete := (List.forall₂_cons.1 matched').1
  have memU : u ∈ (S.frameKey i).rule5Readings :=
    input.certified.mem_of_mem_rankRule5Readings (by
      rw [show input.certified.rankRule5Readings (S.frameKey i).rule5Readings = u :: tailU from hu]
      exact List.mem_cons_self)
  have memV : v ∈ (S.frameKey j).rule5Readings :=
    input.certified.mem_of_mem_rankRule5Readings (by
      rw [show input.certified.rankRule5Readings (S.frameKey j).rule5Readings = v :: tailV from hv]
      exact List.mem_cons_self)
  obtain ⟨ρ₁, ρ₂, hρ₁, hρ₂, hne, _, _⟩ :=
    S.matched_classification distinct hij tie memU memV hcomplete
  rw [hρ] at hρ₁
  cases hρ₁
  have hswap : ρ₂ = RS.swap ρ := by
    cases ρ <;> cases ρ₂ <;> simp_all [RS.swap]
  subst hswap
  refine ⟨memU, memV, hρ₂, ?_⟩
  exact (compareSparseLayers_priority_eq_iff _ _).1 (rule4b_tie_of_complete hcomplete)

/-- **The common-`R` decision at a matched head pair, in production form.**  Slot `i` is senior
exactly when the first chiral address of its Rule-4b key, in the sphere-major order, carries the
actual descriptor `R`. -/
theorem commonR_decision_gt_iff {i j : Fin 4} (hij : i ≠ j)
    (tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) i j)
    {u : input.certified.LocalizedRerootRule5Reading} {tailU}
    (hu : (orderedKeys input.certified S.frameKey i).rule5Readings = u :: tailU)
    {v : input.certified.LocalizedRerootRule5Reading} {tailV}
    (hv : (orderedKeys input.certified S.frameKey j).rule5Readings = v :: tailV)
    {ρ : RS} (hρ : u.prior.reference? = some ρ) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        u.commonR.descriptor v.commonR.descriptor = .gt ↔
      ∃ path,
        SparsePhysicalFirstDifference.tableValue (scalar4a (S.arm4b (S.slotEquiv.symm i) ρ).key)
            path = 2 ∧
        descriptorOfBit ρ (SparsePhysicalFirstDifference.tableValue
          (scalar4b (S.arm4b (S.slotEquiv.symm i) ρ).key) path) = RS.R ∧
        ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
          SparsePhysicalFirstDifference.tableValue
            (scalar4a (S.arm4b (S.slotEquiv.symm i) ρ).key) earlier ≠ 2 := by
  obtain ⟨memU, memV, hσ, sameTable⟩ := S.head_matched distinct hij tie hu hv hρ
  have uR := S.commonR_eq_extend memU hρ
  have vR := S.commonR_eq_extend memV hσ
  have image := S.rule4bKey_image memU hρ
  have keyEq := S.rule4bKey_eq_arm4b memU hρ
  rw [uR, vR, extendLocalizedRerootCumulativeRule45Key_descriptor,
    extendLocalizedRerootCumulativeRule45Key_descriptor, ← sameTable,
    ← extendLocalizedRerootCumulativeRule45Key_descriptor,
    ← extendLocalizedRerootCumulativeRule45Key_descriptor]
  rw [keyEq] at image ⊢
  exact compare_extend5_gt_iff (S.arm4b (S.slotEquiv.symm i) ρ).tableMatch
    (S.arm4b (S.slotEquiv.symm i) ρ).realizes image

/-- **The common-`R` decision at a matched head pair, read on the independent reading.**  Slot
`i` is senior exactly when the independent reading of its ligand under its own selected sense, at
its first chiral address, is the like code of `R`: `like` when the own reference is `R`,
`unlike` when it is `S`. -/
theorem commonR_decision_gt_iff_reading {i j : Fin 4} (hij : i ≠ j)
    (tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) i j)
    {u : input.certified.LocalizedRerootRule5Reading} {tailU}
    (hu : (orderedKeys input.certified S.frameKey i).rule5Readings = u :: tailU)
    {v : input.certified.LocalizedRerootRule5Reading} {tailV}
    (hv : (orderedKeys input.certified S.frameKey j).rule5Readings = v :: tailV)
    {ρ : RS} (hρ : u.prior.reference? = some ρ) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        u.commonR.descriptor v.commonR.descriptor = .gt ↔
      ∃ path,
        Certificate.CanonicalSphereKey.pathObservationOf
            (armGraph (S.arm4b (S.slotEquiv.symm i) ρ)).width
            (armGraph (S.arm4b (S.slotEquiv.symm i) ρ)).height
            (reading input.certified.moleculeGraph (actualReferenceDescriptorMap input)
              (input.certified.topUnit S.center) (armGraph (S.arm4b (S.slotEquiv.symm i) ρ))
              (senseOf ρ)) path =
          (((code (if ρ = RS.R then 1 else 0) : DeclarativeCIP.StereoCode) :
            DeclarativeCIP.StereoLabel) : WithBot DeclarativeCIP.StereoLabel) ∧
        ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
          ∀ b : Nat, Certificate.CanonicalSphereKey.pathObservationOf
            (armGraph (S.arm4b (S.slotEquiv.symm i) ρ)).width
            (armGraph (S.arm4b (S.slotEquiv.symm i) ρ)).height
            (reading input.certified.moleculeGraph (actualReferenceDescriptorMap input)
              (input.certified.topUnit S.center) (armGraph (S.arm4b (S.slotEquiv.symm i) ρ))
              (senseOf ρ)) earlier ≠
            (((code b : DeclarativeCIP.StereoCode) : DeclarativeCIP.StereoLabel) :
              WithBot DeclarativeCIP.StereoLabel) := by
  obtain ⟨memU, memV, hσ, sameTable⟩ := S.head_matched distinct hij tie hu hv hρ
  have uR := S.commonR_eq_extend memU hρ
  have vR := S.commonR_eq_extend memV hσ
  have image := S.rule4bKey_image memU hρ
  have keyEq := S.rule4bKey_eq_arm4b memU hρ
  rw [uR, vR, extendLocalizedRerootCumulativeRule45Key_descriptor,
    extendLocalizedRerootCumulativeRule45Key_descriptor, ← sameTable,
    ← extendLocalizedRerootCumulativeRule45Key_descriptor,
    ← extendLocalizedRerootCumulativeRule45Key_descriptor]
  rw [keyEq] at image ⊢
  exact compare_extend5_gt_iff_represented (S.arm4b (S.slotEquiv.symm i) ρ).tableMatch
    (S.arm4b (S.slotEquiv.symm i) ρ).realizes image
    (arm_root_represents4b (S.arm4b (S.slotEquiv.symm i) ρ)
      (S.armReadback4b (S.arm4b (S.slotEquiv.symm i) ρ)))

/-! ## The root consequence: the sort places the senior slot first -/

/-- The head common-`R` decision of a distinct ordered-prior-tied pair is strict. -/
theorem head_commonR_ne_eq {i j : Fin 4} (hij : i ≠ j)
    (tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) i j)
    {u : input.certified.LocalizedRerootRule5Reading} {tailU}
    (hu : (orderedKeys input.certified S.frameKey i).rule5Readings = u :: tailU)
    {v : input.certified.LocalizedRerootRule5Reading} {tailV}
    (hv : (orderedKeys input.certified S.frameKey j).rule5Readings = v :: tailV) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      u.commonR.descriptor v.commonR.descriptor ≠ .eq := by
  intro heq
  obtain ⟨rule4aTie, _, _⟩ := input.certified.orderedPriorTie_matched _ _ tie
    (S.frameKey_readings i).1 (S.frameKey_readings j).1
  have memU : u ∈ (S.frameKey i).rule5Readings :=
    input.certified.mem_of_mem_rankRule5Readings (by
      rw [show input.certified.rankRule5Readings (S.frameKey i).rule5Readings = u :: tailU from hu]
      exact List.mem_cons_self)
  have memV : v ∈ (S.frameKey j).rule5Readings :=
    input.certified.mem_of_mem_rankRule5Readings (by
      rw [show input.certified.rankRule5Readings (S.frameKey j).rule5Readings = v :: tailV from hv]
      exact List.mem_cons_self)
  exact distinct (S.alpha i) (S.alpha j) (fun h => hij (S.alpha.injective h))
    (S.properTransport_of_commonR_eq hij memU memV rule4aTie
      ((compareSparseLayers_priority_eq_iff _ _).1 heq))

/-- **Within an ordered-prior-tied pair, the ordered rank order is the head common-`R`
decision.** -/
theorem rank_lt_iff_commonR_gt {i j : Fin 4} (hij : i ≠ j)
    (tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) i j)
    {u : input.certified.LocalizedRerootRule5Reading} {tailU}
    (hu : (orderedKeys input.certified S.frameKey i).rule5Readings = u :: tailU)
    {v : input.certified.LocalizedRerootRule5Reading} {tailV}
    (hv : (orderedKeys input.certified S.frameKey j).rule5Readings = v :: tailV) :
    input.certified.compoundKeyRank (orderedKeys input.certified S.frameKey) j <
        input.certified.compoundKeyRank (orderedKeys input.certified S.frameKey) i ↔
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        u.commonR.descriptor v.commonR.descriptor = .gt := by
  rw [← compare_gt_iff_gt, ← input.certified.compoundKeyComparison_eq_compare_rank _
    (S.orderedKeys_offDiagonalStrict distinct) i j,
    input.certified.compoundKeyComparison_eq_rule5_of_priorTie _ tie, hu, hv,
    input.certified.compareLocalizedRerootCompoundRule5Readings_cons_of_ne .R u v tailU tailV
      (S.head_commonR_ne_eq distinct hij tie hu hv)]
  exact Iff.rfl

/-- **The sorted order inside every mirror pair is the Rule-5 decision.**  Along a rank-sorted slot
list, whenever an earlier and a later slot form a distinct ordered-prior-tied pair, the earlier
slot's head reading is senior under the common reference `R`. -/
theorem highestFirst_pairwise_rule5 (tracked : TrackedLocalizedLigandOrder)
    (sorted : SortedByRank
      (input.certified.compoundKeyRank (orderedKeys input.certified S.frameKey))
      tracked.highestFirst.reverse) :
    tracked.highestFirst.Pairwise fun i j =>
      compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey) i j →
        ∀ (u : input.certified.LocalizedRerootRule5Reading) tailU
          (v : input.certified.LocalizedRerootRule5Reading) tailV,
          (orderedKeys input.certified S.frameKey i).rule5Readings = u :: tailU →
          (orderedKeys input.certified S.frameKey j).rule5Readings = v :: tailV →
          OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
            u.commonR.descriptor v.commonR.descriptor = .gt := by
  refine (List.pairwise_reverse.mp sorted).imp ?_
  intro i j hrank htie u tailU v tailV hu hv
  exact (S.rank_lt_iff_commonR_gt distinct htie.1 htie.2 hu hv).1 hrank

/-- **The ordered Rule-5 root theorem with the inside-pair decision.**  The R3 headline together
with the pairwise Rule-5 statement on the sorted order: the final letter is read from the actual
coordinates in a slot order that is descending in the independent keys wherever they differ and,
inside every enantiomorphic pair, places the slot whose head reading is senior under the common
reference `R` first. -/
theorem orderedReferenceState_top_eq_classify_physical_rule5
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨S.c.1, S.c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ (tracked : TrackedLocalizedLigandOrder) (normalizedRS : RS)
      (pointsAt : Fin 4 → CartesianPoint3),
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input) S.top =
        some (classifyTetrahedralRSPseudo normalizedRS
          (physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule
            S.cfg S.c)) ∧
      (∀ index : Fin 4,
        input.certified.localizedRerootCursorSpatialPoint? (S.frame.cursorAt index) =
          some (pointsAt index)) ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      RationalTetrahedralDescriptor (tracked.highestFirst.map pointsAt) normalizedRS ∧
      ((classifyTetrahedralRSPseudo normalizedRS
          (physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule
            S.cfg S.c)).IsLowercase ↔
        physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule
          S.cfg S.c = 1) ∧
      (∀ i j : Fin 4,
        compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey) i j ↔
          Enantiomorphic input.certified.detectedMultiCenterMolecule S.cfg S.c
            (S.alpha i) (S.alpha j)) ∧
      (tracked.highestFirst.map S.slotEquiv.symm).Pairwise (fun ℓ m =>
        S.independentKey ℓ ≠ S.independentKey m → S.independentKey m < S.independentKey ℓ) ∧
      tracked.highestFirst.Pairwise (fun i j =>
        compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey) i j →
          ∀ (u : input.certified.LocalizedRerootRule5Reading) tailU
            (v : input.certified.LocalizedRerootRule5Reading) tailV,
            (orderedKeys input.certified S.frameKey i).rule5Readings = u :: tailU →
            (orderedKeys input.certified S.frameKey j).rule5Readings = v :: tailV →
            OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
              u.commonR.descriptor v.commonR.descriptor = .gt) := by
  obtain ⟨tracked, normalizedRS, pointsAt, stateEq, spatial, perm, sorted, rational, lowercase,
    bridge, keys⟩ := S.orderedReferenceState_top_eq_classify_physical distinct coordinates
  exact ⟨tracked, normalizedRS, pointsAt, stateEq, spatial, perm, rational, lowercase, bridge,
    keys, S.highestFirst_pairwise_rule5 distinct tracked sorted⟩

end Distinct

end ActualCentrePhysicalSetup
end Rule4aTableBridge

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compoundKeyComparison_eq_rule5_of_priorTie
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.commonR_eq_extend
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.head_matched
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.commonR_decision_gt_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.commonR_decision_gt_iff_reading
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.rank_lt_iff_commonR_gt
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.highestFirst_pairwise_rule5
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedReferenceState_top_eq_classify_physical_rule5
