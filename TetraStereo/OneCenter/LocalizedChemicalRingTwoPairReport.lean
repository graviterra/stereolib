import TetraStereo.OneCenter.LocalizedChemicalRingPairingParity
import TetraStereo.OneCenter.LocalizedChemicalRingRootTwoMovingPairs
import TetraStereo.OneCenter.LocalizedChemicalRingAllRootCancellationReport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace TetraStereo.OneCenter.LocalizedChemicalRingTwoPairReport

open CertifiedLocalizedCIPInput LocalizedChemicalRingPairingParity
open LocalizedChemicalRingRootPhysicalKeyClasses (PhysicalTransport keys_eq_iff_physicalTransport)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData rank referenceAt observedGeometry)
open LocalizedChemicalRingJointPreparedExecution (keys generated fallback step)
open LocalizedChemicalRingJointMarkerFrameExecution (selectedSlots)
open LocalizedChemicalRingJointPreparedRefusalCharacterization (OddBoundarySymmetry)
open LocalizedChemicalRingJointPreparedRootInput (root_data root_reached)
open LocalizedChemicalRingJointPreparedSourceStep
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence (finalQuery)
open LocalizedChemicalRingJointPreparedReport (analyze mem_analyze_at_center_iff)
open LocalizedChemicalRingCompletenessMarked (slotPerm keyOrder_eq_slots enumeration readback_enum)
open LocalizedChemicalRingPhysicalSense (inputGeometry letterOfSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedGenericMarkedRecalculation (structuralDepth consensus caseFromMirror? readback_mirror)
open LocalizedChemicalRingJointMarkerRanking (RefinedKey)
open LocalizedMarkedRetainedOrdinaryRanking (keyOrder)
open scoped Classical
noncomputable section

/-- Reflection reverses the geometric orientation for a fixed priority order. -/
def sideLetter (base : ℝ) (side even : Bool) : RS :=
  let raw := letterOfSign (base * (if even then 1 else -1))
  if side then raw.swap else raw

private theorem rank_congr {k l : Fin 4 → RefinedKey}
    (same : keyOrder k (List.finRange 4) = keyOrder l (List.finRange 4)) :
    slotPerm k = slotPerm l := by
  rw [keyOrder_eq_slots, keyOrder_eq_slots] at same
  simp only [List.cons.injEq, and_true] at same
  apply Equiv.ext
  intro i
  fin_cases i
  · exact same.1
  · exact same.2.1
  · exact same.2.2.1
  · exact same.2.2.2

private theorem consensus_two {α : Type} (xs : List α) (f : α → Option RS)
    (a b : α) (ha : a ∈ xs) (hb : b ∈ xs) (u v : RS)
    (hu : f a = some u) (hv : f b = some v)
    (cover : ∀ i ∈ xs, f i = f a ∨ f i = f b) :
    consensus (xs.map f) = if u = v then some u else none := by
  by_cases eq : u = v
  · subst v
    rw [if_pos rfl, LocalizedChemicalRingSenseTransport.consensus_eq_some_iff]
    refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem ha), ?_⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact (cover i hi).elim (·.trans hu) (·.trans hv)
  · rw [if_neg eq]
    cases h : consensus (xs.map f) with
    | none => rfl
    | some w =>
      have all := ((LocalizedChemicalRingSenseTransport.consensus_eq_some_iff _ _).mp h).2
      exact False.elim (eq (Option.some.inj (hu.symm.trans ((all _ (List.mem_map_of_mem ha)).trans
        ((all _ (List.mem_map_of_mem hb)).symm.trans hv)))))

private theorem four_cover : ∀ a b c d : Fin 4,
    [a,b,c,d].Pairwise (· ≠ ·) → ∀ i, i = a ∨ i = b ∨ i = c ∨ i = d := by decide +kernel

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (center : input.detectedMultiCenterMolecule.Center)

set_option quotPrecheck false
local notation "root" => canonicalCenterRoot center.1.val
local notation "query" => finalQuery input mol agreement center
variable (data : OccurrenceData input mol center (canonicalCenterRoot center.1.val))
  (rootAddress : data.target.1.address = [])
  (candidate : Profile input mol) (model : SourceModel input mol single candidate)

/-- The parity of the three physical pairings in the source priority order after marking a
native ligand. Each geometry and mark queries its own contextual descendant descriptors. -/
def promotedMatchingEven (side : Bool) (ligand : Fin 4) : Bool :=
  matchingEven (rank input mol center root data
    (sourceKeysAt input single (profileFamily input mol candidate query) data.target data.frame
      (observedGeometry input side) [input.detectedMultiCenterMolecule.ligandAtomAt center ligand]))

include agreement admissible supported model calibrated in
private theorem promoted_reading (side : Bool) (ligand : Fin 4)
    (resolved : fallback input mol center root data (structuralDepth mol root)
      (observedGeometry input side) [] (data.ligandOf.symm ligand) ≠ none) :
    fallback input mol center root data (structuralDepth mol root)
        (observedGeometry input side) [] (data.ligandOf.symm ligand) =
      some (sideLetter (input.detectedMultiCenterMolecule.configurationSign cfg center) side
        (promotedMatchingEven input mol agreement single center data candidate side ligand)) := by
  let ctx := [input.detectedMultiCenterMolecule.ligandAtomAt center ligand]
  let geom := observedGeometry input side
  have atom : referenceAt input mol center root data (data.ligandOf.symm ligand) =
      input.detectedMultiCenterMolecule.ligandAtomAt center ligand := by simp [referenceAt]
  have eqn := LocalizedChemicalRingJointPreparedExecution.fallback_eq input mol agreement admissible
    supported single center root data (structuralDepth mol root) geom [] (data.ligandOf.symm ligand)
  simp only [List.nil_append] at eqn
  rw [atom] at eqn
  rw [eqn] at resolved ⊢
  split at resolved <;> rename_i strict
  · rw [if_pos strict]
    unfold promotedMatchingEven
    rw [LocalizedChemicalRingSourcePromotionCancellation.sourceModel_family_eq_generated
      input single mol agreement admissible supported model query]
    have order := rank_congr (keyOrder_source_eq input mol single center root data
      (structuralDepth mol root) geom ctx)
    have ranks := congrArg (fun p : Equiv.Perm (Fin 4) => p.trans data.ligandOf) order
    change rank input mol center root data _ = rank input mol center root data _ at ranks
    change _ = some (sideLetter _ side (matchingEven (rank input mol center root data
      (sourceKeysAt input single (generatedFamily input mol (structuralDepth mol root) root)
        data.target data.frame geom ctx))))
    rw [ranks]
    have read (r : Bool) (p : Equiv.Perm (Fin 4)) :
        LocalizedGenericMarkedRecalculation.readback? (observedGeometry input r) (enumeration input center p) =
          some (sideLetter (input.detectedMultiCenterMolecule.configurationSign cfg center) r (matchingEven p)) := by
      cases r <;> simp [observedGeometry, readback_mirror, readback_enum input cfg center
        (calibrated center), handedness_eq_matching, sideLetter]
    exact read side _
  · exact False.elim (resolved rfl)

include agreement admissible supported charge calibrated rootAddress model in
/-- One geometry succeeds precisely when the two representative matching orders have equal
parity. Every selected mark resolves, and every native ligand occurs in one of the two pairs. -/
theorem twoPair_step (a a' b b' : Fin 4) (distinct : [a,a',b,b'].Pairwise (· ≠ ·))
    (moveA : PhysicalTransport input cfg center [] a a')
    (moveB : PhysicalTransport input cfg center [] b b')
    (apart : ¬ PhysicalTransport input cfg center [] a b)
    (noOdd : ¬ OddBoundarySymmetry input cfg center [] []) (side : Bool) :
    step input mol root (structuralDepth mol root) (observedGeometry input side) [] =
      let even := promotedMatchingEven input mol agreement single center data candidate side
      if even a = even b then some (sideLetter
        (input.detectedMultiCenterMolecule.configurationSign cfg center) side (even a)) else none := by
  let slot := data.ligandOf.symm
  let depth := structuralDepth mol root
  let geom := observedGeometry input side
  let key := keys input mol single center root data depth geom []
  let state := generated input mol depth geom root []
  let population := selectedSlots input mol single center root data state []
  let read := fallback input mol center root data depth geom []
  have reaches := root_reached input mol agreement center
  have corr (i j : Fin 4) (neq : i ≠ j) :
      key (slot i) = key (slot j) ↔ PhysicalTransport input cfg center [] i j := by
    simpa only [slot, Equiv.apply_symm_apply] using
      keys_eq_iff_physicalTransport input mol agreement admissible supported single charge cfg
        calibrated center root data reaches rfl rootAddress [] side (slot i) (slot j)
        (fun h => neq (data.ligandOf.symm.injective h))
  have aa : a ≠ a' := (List.pairwise_cons.mp distinct).1 a' (by simp)
  have ab : a ≠ b := (List.pairwise_cons.mp distinct).1 b (by simp)
  have bb : b ≠ b' := (List.pairwise_cons.mp (List.pairwise_cons.mp
    (List.pairwise_cons.mp distinct).2).2).1 b' (by simp)
  have ka := (corr a a' aa).mpr moveA
  have kb := (corr b b' bb).mpr moveB
  have nonconstant : ¬ ∀ i, key i = key 0 := fun h =>
    apart ((corr a b ab).mp ((h _).trans (h _).symm))
  have tied : ¬ Function.Injective key := fun h => aa (slot.injective (h ka))
  have pairSelected (i j : Fin 4) (neq : i ≠ j) (tie : key i = key j) : i ∈ population := by
    apply (LocalizedChemicalRingOrderingTransport.tied_sorted_mem compare
      LocalizedChemicalRingJointMarkerRanking.refined_compare_eq_iff key (List.finRange 4)
      (List.nodup_finRange 4) i).mpr
    exact ⟨List.mem_finRange _, j, List.mem_finRange _, Ne.symm neq, tie.symm⟩
  have ma := pairSelected _ _ (fun h => aa (slot.injective h)) ka
  have mb := pairSelected _ _ (fun h => bb (slot.injective h)) kb
  have resolves (i : Fin 4) (hi : i ∈ population) : read i ≠ none :=
    LocalizedChemicalRingJointPreparedRootSelectedResolution.selected_fallback_resolves
      input mol agreement admissible supported single charge cfg calibrated center root data
      reaches rfl rootAddress [] side noOdd nonconstant i hi
  have within (i j : Fin 4) (tie : key i = key j) : read i = read j :=
    LocalizedChemicalRingJointPreparedRootClassReadings.fallback_eq_of_root_key_eq
      input mol agreement admissible supported single charge cfg calibrated center root data
      reaches rfl rootAddress [] side noOdd i j tie
  have covered (i : Fin 4) (_ : i ∈ population) : read i = read (slot a) ∨ read i = read (slot b) := by
    have h := four_cover _ _ _ _ distinct (data.ligandOf i)
    rcases h with h | h | h | h
    · exact Or.inl (congrArg read ((data.ligandOf.symm_apply_eq.mpr h.symm).symm))
    · exact Or.inl ((congrArg read ((data.ligandOf.symm_apply_eq.mpr h.symm).symm)).trans
        (within _ _ ka.symm))
    · exact Or.inr (congrArg read ((data.ligandOf.symm_apply_eq.mpr h.symm).symm))
    · exact Or.inr ((congrArg read ((data.ligandOf.symm_apply_eq.mpr h.symm).symm)).trans
        (within _ _ kb.symm))
  have left := promoted_reading input mol agreement admissible supported single cfg calibrated
    center data candidate model side a (resolves _ ma)
  have right := promoted_reading input mol agreement admissible supported single cfg calibrated
    center data candidate model side b (resolves _ mb)
  rw [LocalizedChemicalRingJointPreparedExecution.step_eq input mol agreement admissible supported
    single center root data depth geom [], if_neg tied]
  rw [consensus_two population read _ _ ma mb _ _ left right covered]
  dsimp only
  congr 1
  apply propext
  have unit := LocalizedChemicalRingPhysicalSense.configurationSign_unit input cfg center
  generalize promotedMatchingEven input mol agreement single center data candidate side a = u
  generalize promotedMatchingEven input mol agreement single center data candidate side b = v
  rcases unit with h | h <;> cases side <;> cases u <;> cases v <;>
    norm_num [sideLetter, letterOfSign, h, RS.swap] <;> decide


/-- On coherent sides the original matching parity fixes the letter. Changing that parity
under reflection preserves the geometric letter and therefore gives lowercase. -/
def pairingDescriptor (base : ℝ) (originalA originalB mirrorA mirrorB : Bool) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  if originalA = originalB ∧ mirrorA = mirrorB then
    let raw := sideLetter base false originalA
    some (if originalA = mirrorA then .chiral raw else .pseudoasymmetric (pseudoRSOfRS raw))
  else none

private theorem case_eq_pairingDescriptor (base : ℝ) (unit : base = 1 ∨ base = -1)
    (a b c d : Bool) :
    caseFromMirror? (if a = b then some (sideLetter base false a) else none)
      (if c = d then some (sideLetter base true c) else none) = pairingDescriptor base a b c d := by
  rcases unit with rfl | rfl <;> cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [caseFromMirror?, pairingDescriptor, sideLetter, letterOfSign, RS.swap] <;> decide

include agreement admissible supported charge calibrated rootAddress model in
/-- For any representatives of the two physical pairs the formula gives the exact entry,
including odd-boundary refusals. No strict order or successful promotion is a premise. -/
theorem report_iff_pairingDescriptor (a a' b b' : Fin 4) (distinct : [a,a',b,b'].Pairwise (· ≠ ·))
    (moveA : PhysicalTransport input cfg center [] a a')
    (moveB : PhysicalTransport input cfg center [] b b')
    (apart : ¬ PhysicalTransport input cfg center [] a b)
    (outcome : Option LocalizedAuxiliaryLabel) :
    (center.1.val, outcome) ∈ analyze input mol ↔
      (if OddBoundarySymmetry input cfg center [] [] then none else
        let even := promotedMatchingEven input mol agreement single center data candidate
        pairingDescriptor (input.detectedMultiCenterMolecule.configurationSign cfg center)
          (even false a) (even false b) (even true a) (even true b)) = outcome := by
  rw [mem_analyze_at_center_iff]
  by_cases odd : OddBoundarySymmetry input cfg center [] []
  · rw [if_pos odd]
    have history := LocalizedChemicalRingJointPreparedRootPhysicalTransport.root_history input mol
      center root data rootAddress rfl
    have refused := LocalizedChemicalRingJointPreparedRefusalCharacterization.refusal_of_oddBoundary
      input mol agreement admissible supported single cfg calibrated center root data
      (root_reached input mol agreement center) rfl [] [] (by simp [history]) (by simp) odd
    change _ = outcome ↔ none = outcome
    exact iff_of_eq (congrArg (· = outcome) refused)
  · rw [if_neg odd]
    have sides := twoPair_step input mol agreement admissible supported single charge cfg calibrated
      center data rootAddress candidate model a a' b b' distinct moveA moveB apart odd
    change caseFromMirror? (step input mol root (structuralDepth mol root) (observedGeometry input false) [])
      (step input mol root (structuralDepth mol root) (observedGeometry input true) []) = outcome ↔ _
    rw [sides false, sides true]
    dsimp only
    rw [case_eq_pairingDescriptor _ (LocalizedChemicalRingPhysicalSense.configurationSign_unit input cfg center)]

include agreement admissible supported single charge calibrated in
/-- Starting solely from the physical two-pair hypothesis, there is a molecular root frame
and a unique source profile whose matching-parity formula classifies every possible entry. -/
theorem twoMovingPairs_exact_report
    (pairs : LocalizedChemicalRingRootTwoMovingPairs.TwoMovingPairs input cfg center []) :
    ∃ (data : OccurrenceData input mol center root), data.target.1.address = [] ∧
    ∃ a a' b b' : Fin 4, [a,a',b,b'].Pairwise (· ≠ ·) ∧
      PhysicalTransport input cfg center [] a a' ∧ PhysicalTransport input cfg center [] b b' ∧
      ¬ PhysicalTransport input cfg center [] a b ∧
      ∃! candidate : Profile input mol, SourceModel input mol single candidate ∧
        ∀ outcome, (center.1.val, outcome) ∈ analyze input mol ↔
          (if OddBoundarySymmetry input cfg center [] [] then none else
            let even := promotedMatchingEven input mol agreement single center data candidate
            pairingDescriptor (input.detectedMultiCenterMolecule.configurationSign cfg center)
              (even false a) (even false b) (even true a) (even true b)) = outcome := by
  obtain ⟨data, addr⟩ := root_data input mol agreement admissible supported single center
  obtain ⟨a, a', b, b', ds, ma, mb, apart⟩ := pairs
  obtain ⟨p, hp, unique⟩ := LocalizedChemicalRingJointPreparedSourceModelExistence.existsUnique_sourceModel
    input mol agreement admissible supported single
  exact ⟨data, addr, a, a', b, b', ds, ma, mb, apart, p, ⟨hp,
    report_iff_pairingDescriptor input mol agreement admissible supported single charge cfg calibrated
      center data addr p hp a a' b b' ds ma mb apart⟩, fun q h => unique q h.1⟩

open LocalizedChemicalRingRootTransitiveClassification (PhysicalTransitive)
open LocalizedChemicalRingRootTransitiveReport (TransitiveSuccess)
open LocalizedChemicalRingRootSingleMovingClass (SingleMovingClass)

/-- Exhaustive final-root success criterion for CURRENT. Only the two-pair case needs
cross-class comparisons of orders obtained from the independent contextual source profile. -/
def RootSuccess : Prop :=
  if PhysicalTransitive input cfg center [] then TransitiveSuccess input cfg center
  else if SingleMovingClass input cfg center [] then ¬ OddBoundarySymmetry input cfg center [] []
  else ¬ OddBoundarySymmetry input cfg center [] [] ∧
    ∃ a a' b b' : Fin 4, [a,a',b,b'].Pairwise (· ≠ ·) ∧
      PhysicalTransport input cfg center [] a a' ∧ PhysicalTransport input cfg center [] b b' ∧
      ¬ PhysicalTransport input cfg center [] a b ∧
      ∀ side, promotedMatchingEven input mol agreement single center data candidate side a =
        promotedMatchingEven input mol agreement single center data candidate side b

private theorem pairingDescriptor_success (base : ℝ) (u v w z : Bool) :
    (∃ label, pairingDescriptor base u v w z = some label) ↔ u = v ∧ w = z := by
  unfold pairingDescriptor
  split <;> simp_all

include agreement admissible supported charge calibrated rootAddress model in
/-- Exact outcome classification of every detected center, without a distinguishability
premise. Both success and refusal refer to membership of the actual whole-molecule report. -/
theorem allRoot_success_refusal_iff :
    ((∃ label, (center.1.val, some label) ∈ analyze input mol) ↔
      RootSuccess input mol agreement single cfg center data candidate) ∧
    ((center.1.val, none) ∈ analyze input mol ↔
      ¬ RootSuccess input mol agreement single cfg center data candidate) := by
  classical
  by_cases transitive : PhysicalTransitive input cfg center []
  · simpa only [RootSuccess, if_pos transitive] using
      LocalizedChemicalRingRootTransitiveReport.detected_report_success_refusal_iff input mol
        agreement admissible supported single charge cfg calibrated center transitive
  by_cases oneClass : SingleMovingClass input cfg center []
  · simpa only [RootSuccess, if_neg transitive, if_pos oneClass, not_not] using
      LocalizedChemicalRingRootSingleMovingClass.detected_report_success_refusal_iff input mol
        agreement admissible supported single charge cfg calibrated center oneClass transitive
  obtain ⟨a,a',b,b',ds,ma,mb,apart⟩ :=
    (LocalizedChemicalRingRootTwoMovingPairs.not_singleMovingClass_iff_twoMovingPairs input mol
      agreement admissible supported single charge cfg calibrated center root data
      (root_reached input mol agreement center) rfl rootAddress [] false).mp oneClass
  have formula := report_iff_pairingDescriptor input mol agreement admissible supported single
    charge cfg calibrated center data rootAddress candidate model
  have success : (∃ label, (center.1.val, some label) ∈ analyze input mol) ↔
      RootSuccess input mol agreement single cfg center data candidate := by
    simp only [RootSuccess, if_neg transitive, if_neg oneClass]
    constructor
    · rintro ⟨label, member⟩
      have found := (formula a a' b b' ds ma mb apart _).mp member
      split at found <;> rename_i h
      · cases found
      · have agree := (pairingDescriptor_success _ _ _ _ _).mp ⟨_, found⟩
        exact ⟨h, a, a', b, b', ds, ma, mb, apart, fun side => by
          cases side <;> first | exact agree.1 | exact agree.2⟩
    · rintro ⟨noOdd, i, i', j, j', distinct, mi, mj, separated, agree⟩
      obtain ⟨label, result⟩ := (pairingDescriptor_success
        (input.detectedMultiCenterMolecule.configurationSign cfg center) _ _ _ _).mpr
          ⟨agree false, agree true⟩
      exact ⟨label, (formula i i' j j' distinct mi mj separated _).mpr (by
        rw [if_neg noOdd]; exact result)⟩
  refine ⟨success, ?_⟩
  rw [← success]
  simp only [mem_analyze_at_center_iff]
  cases LocalizedChemicalRingPreparedContextRecursion.preparedAssignCenter? mol
    (LocalizedChemicalRingJointMarkerOperations.jointOperations input mol) (inputGeometry input)
    center.1.val <;> simp

include agreement admissible supported single charge calibrated in
/-- One and the same independently specified source profile classifies all detected centers.
The required molecular root frames and their canonical addresses are derived. -/
theorem existsUnique_allRoot_outcomes :
    ∃! candidate : Profile input mol, SourceModel input mol single candidate ∧
      ∀ c : input.detectedMultiCenterMolecule.Center,
        ∃ data : OccurrenceData input mol c (canonicalCenterRoot c.1.val),
          data.target.1.address = [] ∧
          ((∃ label, (c.1.val, some label) ∈ analyze input mol) ↔
            RootSuccess input mol agreement single cfg c data candidate) ∧
          ((c.1.val, none) ∈ analyze input mol ↔
            ¬ RootSuccess input mol agreement single cfg c data candidate) := by
  obtain ⟨p, hp, unique⟩ := LocalizedChemicalRingJointPreparedSourceModelExistence.existsUnique_sourceModel
    input mol agreement admissible supported single
  refine ⟨p, ⟨hp, ?_⟩, fun q h => unique q h.1⟩
  intro c
  obtain ⟨frame, addr⟩ := root_data input mol agreement admissible supported single c
  exact ⟨frame, addr, allRoot_success_refusal_iff input mol agreement admissible supported single
    charge cfg calibrated c frame addr p hp⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingTwoPairReport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoPairReport.twoPair_step
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoPairReport.report_iff_pairingDescriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoPairReport.twoMovingPairs_exact_report
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoPairReport.allRoot_success_refusal_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoPairReport.existsUnique_allRoot_outcomes
