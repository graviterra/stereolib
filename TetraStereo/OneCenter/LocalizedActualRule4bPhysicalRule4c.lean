import TetraStereo.OneCenter.LocalizedActualRule4bPhysicalComparison
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000






















namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open DeclarativeCIP

noncomputable section
open scoped Classical

/-! ## Vector-level transport of the Rule-4c extension -/

theorem compare_extend4c_two (u v : List Nat) (hu : u.length = 2) (hv : v.length = 2) :
    compareLocalizedCumulativeRule45Priority (extendLocalizedRule4bPriorityToRule4c u)
        (extendLocalizedRule4bPriorityToRule4c v) =
      compareLocalizedCumulativeRule45Priority u v := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hu
  obtain ⟨c, d, rfl⟩ := List.length_eq_two.1 hv
  simp only [extendLocalizedRule4bPriorityToRule4c, compareLocalizedCumulativeRule45Priority,
    List.compareLex_cons_cons, List.compareLex_nil_nil, CompilerProjectionFidelity.compareNat_self]
  rfl

theorem length_two_of_image {ρ : RS} {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {v : List Nat} (h : LocalizedStagePriorityImage (.rule4b ρ) admitted v) : v.length = 2 := by
  obtain ⟨label, _, rfl⟩ := h
  rfl

theorem compareSparseEntry_extend4c_two (left right : OfficialSparseEntry (List Nat))
    (hl : left.2.length = 2) (hr : right.2.length = 2) :
    OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority
        (extendLocalizedPriorityEntry extendLocalizedRule4bPriorityToRule4c left)
        (extendLocalizedPriorityEntry extendLocalizedRule4bPriorityToRule4c right) =
      OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority left right := by
  unfold OfficialRuleMajorKey.compareSparseEntry
  simp only [compareLex, Ordering.byKey, extendLocalizedPriorityEntry_fst,
    extendLocalizedPriorityEntry_snd]
  rw [compare_extend4c_two _ _ hl hr]

theorem compareSparseLayer_extend4c_two :
    ∀ (left right : List (OfficialSparseEntry (List Nat))),
      (∀ entry ∈ left, entry.2.length = 2) → (∀ entry ∈ right, entry.2.length = 2) →
      OfficialRuleMajorKey.compareSparseLayer compareLocalizedCumulativeRule45Priority
          (left.map (extendLocalizedPriorityEntry extendLocalizedRule4bPriorityToRule4c))
          (right.map (extendLocalizedPriorityEntry extendLocalizedRule4bPriorityToRule4c)) =
        OfficialRuleMajorKey.compareSparseLayer compareLocalizedCumulativeRule45Priority left right
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | head :: tail, otherHead :: otherTail, hl, hr => by
      unfold OfficialRuleMajorKey.compareSparseLayer
      simp only [List.map_cons, List.compareLex_cons_cons]
      rw [compareSparseEntry_extend4c_two head otherHead (hl head (by simp))
        (hr otherHead (by simp))]
      have tailStep := compareSparseLayer_extend4c_two tail otherTail
        (fun entry present => hl entry (by simp [present]))
        (fun entry present => hr entry (by simp [present]))
      unfold OfficialRuleMajorKey.compareSparseLayer at tailStep
      rw [tailStep]

theorem compareSparseLayers_extend4c_two :
    ∀ (left right : List (List (OfficialSparseEntry (List Nat)))),
      (∀ layer ∈ left, ∀ entry ∈ layer, entry.2.length = 2) →
      (∀ layer ∈ right, ∀ entry ∈ layer, entry.2.length = 2) →
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          (extendLocalizedPriorityLayers extendLocalizedRule4bPriorityToRule4c left)
          (extendLocalizedPriorityLayers extendLocalizedRule4bPriorityToRule4c right) =
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority left right
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | head :: tail, otherHead :: otherTail, hl, hr => by
      unfold OfficialRuleMajorKey.compareSparseLayers extendLocalizedPriorityLayers
      simp only [List.map_cons, List.compareLex_cons_cons]
      rw [show extendLocalizedPriorityLayer extendLocalizedRule4bPriorityToRule4c head =
          head.map (extendLocalizedPriorityEntry extendLocalizedRule4bPriorityToRule4c) from rfl,
        show extendLocalizedPriorityLayer extendLocalizedRule4bPriorityToRule4c otherHead =
          otherHead.map (extendLocalizedPriorityEntry extendLocalizedRule4bPriorityToRule4c) from rfl,
        compareSparseLayer_extend4c_two head otherHead (hl head (by simp)) (hr otherHead (by simp))]
      have tailStep := compareSparseLayers_extend4c_two tail otherTail
        (fun layer present => hl layer (by simp [present]))
        (fun layer present => hr layer (by simp [present]))
      unfold OfficialRuleMajorKey.compareSparseLayers extendLocalizedPriorityLayers at tailStep
      rw [tailStep]

theorem length_two_of_descriptorImage {ρ : RS} {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {descriptor : List (List (OfficialSparseEntry (List Nat)))}
    (image : LocalizedStageDescriptorImage (.rule4b ρ) admitted descriptor) :
    ∀ layer ∈ descriptor, ∀ entry ∈ layer, entry.2.length = 2 :=
  fun layer hlayer entry hentry => length_two_of_image (image layer hlayer entry hentry)

/-! ## The no-reference extension under the physical admission -/

theorem compare_extendNoRef_one (k k' : Nat) :
    compareLocalizedCumulativeRule45Priority
        (extendLocalizedRule4aPriorityToRule4cNoReference [k])
        (extendLocalizedRule4aPriorityToRule4cNoReference [k']) =
      compareLocalizedCumulativeRule45Priority [k] [k'] := by
  simp only [extendLocalizedRule4aPriorityToRule4cNoReference,
    compareLocalizedCumulativeRule45Priority, List.compareLex_cons_cons, List.compareLex_nil_nil,
    CompilerProjectionFidelity.compareNat_self]
  rfl

theorem priority_rule4a_extend_noRef_of_noPseudo (label : Option LocalizedAuxiliaryLabel)
    (h : LocalizedNoPseudoLabel label) :
    extendLocalizedRule4aPriorityToRule4cNoReference
        (localizedCumulativeRule45Priority .rule4a label) =
      localizedCumulativeRule45Priority .rule4cNoReference label := by
  cases label with
  | none => rfl
  | some aux =>
      cases aux with
      | chiral _ => rfl
      | pseudoasymmetric _ => simp [LocalizedNoPseudoLabel] at h

/-! ## Per-reading build equations -/

section Builders

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
  (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)

/-- The Rule-4b stage of an alternative. -/
def rule4bStageOf : Option RS → LocalizedCumulativeRule45Stage
  | none => .rule4a
  | some ρ => .rule4b ρ

/-- The Rule-4c stage of an alternative. -/
def rule4cStageOf : Option RS → LocalizedCumulativeRule45Stage
  | none => .rule4cNoReference
  | some ρ => .rule4c ρ

theorem reading_built (a : Option RS) {r : input.LocalizedRerootRule4bcReading}
    (h : input.buildLocalizedRerootRule4bcReading? target view fuel cursor a = some r) :
    r.reference? = a ∧
      input.buildLocalizedRerootCumulativeRule45Key? (rule4bStageOf a) target view fuel cursor =
        some r.rule4bKey ∧
      input.buildLocalizedRerootCumulativeRule45Key? (rule4cStageOf a) target view fuel cursor =
        some r.rule4cKey := by
  cases a with
  | none =>
      show r.reference? = none ∧
        input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor =
          some r.rule4bKey ∧
        input.buildLocalizedRerootCumulativeRule45Key? .rule4cNoReference target view fuel cursor =
          some r.rule4cKey
      unfold buildLocalizedRerootRule4bcReading? at h
      cases h4b : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor with
      | none => simp [h4b] at h
      | some k4b =>
          cases h4c : input.buildLocalizedRerootCumulativeRule45Key? .rule4cNoReference target view
              fuel cursor with
          | none => simp [h4b, h4c] at h
          | some k4c =>
              simp [h4b, h4c] at h
              subst h
              exact ⟨rfl, rfl, rfl⟩
  | some ρ =>
      obtain ⟨hb, hc, href⟩ := reading_some_built target view fuel cursor ρ h
      exact ⟨href, hb, hc⟩

theorem readings_mem_built :
    ∀ (alternatives : List (Option RS)) {readings : List input.LocalizedRerootRule4bcReading},
      input.buildLocalizedRerootRule4bcReadings? target view fuel cursor alternatives =
        some readings →
      ∀ r ∈ readings, ∃ a ∈ alternatives,
        input.buildLocalizedRerootRule4bcReading? target view fuel cursor a = some r
  | [], readings, h => by
      simp [buildLocalizedRerootRule4bcReadings?] at h
      subst h
      intro r hr
      simp at hr
  | a :: alternatives, readings, h => by
      unfold buildLocalizedRerootRule4bcReadings? at h
      cases hr : input.buildLocalizedRerootRule4bcReading? target view fuel cursor a with
      | none => simp [hr] at h
      | some r₀ =>
          cases hrest : input.buildLocalizedRerootRule4bcReadings? target view fuel cursor
              alternatives with
          | none => simp [hr, hrest] at h
          | some rest =>
              simp [hr, hrest] at h
              subst h
              intro r hmem
              rcases List.mem_cons.1 hmem with rfl | hmem
              · exact ⟨a, by simp, hr⟩
              · obtain ⟨b, hb, hbuilt⟩ :=
                  readings_mem_built alternatives hrest r hmem
                exact ⟨b, List.mem_cons_of_mem _ hb, hbuilt⟩

end Builders

/-- Equal reference-count priorities force the same reference kind. -/
theorem kind_of_count_eq (selI selJ : ReferenceSelection)
    (h : constitutionalRule4bReferenceCountPriority (toReferenceList selI) =
      constitutionalRule4bReferenceCountPriority (toReferenceList selJ)) :
    (selI != .empty) = (selJ != .empty) := by
  cases selI with
  | empty =>
      cases selJ with
      | empty => rfl
      | one t => cases t <;> exact absurd h (by decide)
      | both => exact absurd h (by decide)
  | one s =>
      cases selJ with
      | empty => cases s <;> exact absurd h (by decide)
      | one t => rfl
      | both => cases s <;> exact absurd h (by decide)
  | both =>
      cases selJ with
      | empty => exact absurd h (by decide)
      | one t => cases t <;> exact absurd h (by decide)
      | both => rfl

/-! ## Physical identification of the Rule-4c keys -/

namespace ActualCentrePhysicalSetup

variable {input : LocalizedUniversalReference.Input} (S : ActualCentrePhysicalSetup input)

theorem reachable_slot (index : Fin 4) :
    input.certified.ActualChildReachable (S.slotSetup index).tree.source
      (S.frame.cursorAt (S.slot index)) := by
  rw [ActualSlotPhysicalSetup.tree_source]
  exact Relation.ReflTransGen.refl

/-- Every reading of a slot carries the Rule-4b and Rule-4c production builds of its alternative. -/
theorem readings_built (index : Fin 4) :
    ∀ r ∈ (S.slotKey index).prior.readings,
      input.certified.buildLocalizedRerootCumulativeRule45Key? (rule4bStageOf r.reference?)
          (ActualReaderPhysicalBranchInverse.topTarget input S.c)
          (referenceDependencyView input S.c)
          (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
          (S.frame.cursorAt (S.slot index)) = some r.rule4bKey ∧
        input.certified.buildLocalizedRerootCumulativeRule45Key? (rule4cStageOf r.reference?)
          (ActualReaderPhysicalBranchInverse.topTarget input S.c)
          (referenceDependencyView input S.c)
          (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
          (S.frame.cursorAt (S.slot index)) = some r.rule4cKey := by
  obtain ⟨_, _, _, hreadings⟩ := compound_built_components _ _ _ _ (S.prior_built index)
  intro r hr
  obtain ⟨a, _, hbuilt⟩ := readings_mem_built _ _ _ _ _ hreadings r hr
  obtain ⟨href, hb, hc⟩ := reading_built _ _ _ _ a hbuilt
  subst href
  exact ⟨hb, hc⟩

/-- The no-reference Rule-4c build is the extended Rule-4a build (physical admission). -/
theorem noReference_extension (index : Fin 4) (fuel : Nat) :
    input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4cNoReference
        (ActualReaderPhysicalBranchInverse.topTarget input S.c)
        (referenceDependencyView input S.c) fuel (S.frame.cursorAt (S.slot index)) =
      Option.map
        (input.certified.extendLocalizedRerootCumulativeRule45Key
          extendLocalizedRule4aPriorityToRule4cNoReference)
        (input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4a
          (ActualReaderPhysicalBranchInverse.topTarget input S.c)
          (referenceDependencyView input S.c) fuel (S.frame.cursorAt (S.slot index))) := by
  show input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4cNoReference
      (ActualReaderPhysicalBranchInverse.topTarget input (S.slotSetup index).c)
      (referenceDependencyView input (S.slotSetup index).c) fuel
      ((S.slotSetup index).frame.cursorAt (S.slotSetup index).slot) =
    Option.map
      (input.certified.extendLocalizedRerootCumulativeRule45Key
        extendLocalizedRule4aPriorityToRule4cNoReference)
      (input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4a
        (ActualReaderPhysicalBranchInverse.topTarget input (S.slotSetup index).c)
        (referenceDependencyView input (S.slotSetup index).c) fuel
        ((S.slotSetup index).frame.cursorAt (S.slotSetup index).slot))
  rw [← buildWithRead_dependencyReader_eq_build (S.slotSetup index) .rule4cNoReference fuel _,
    ← buildWithRead_dependencyReader_eq_build (S.slotSetup index) .rule4a fuel _]
  refine buildLocalizedRerootCumulativeRule45KeyWithRead?_extend
    (admitted := LocalizedNoPseudoLabel) input.certified
    (nodewise := ?_) (priorityExtend := priority_rule4a_extend_noRef_of_noPseudo)
    (ActualReaderPhysicalBranchInverse.dependencyReader input S.c) (S.slotSetup index).tree.source
    (physicalReader_noPseudo (S.slotSetup index)) fuel _ (S.reachable_slot index)
  intro first second hfirst hsecond
  obtain ⟨labelF, _, rfl⟩ := hfirst
  obtain ⟨labelS, _, rfl⟩ := hsecond
  exact compare_extendNoRef_one _ _

/-- **Rule-4c neutrality, pointwise.**  Two readings of two Rule-4a-tied slots with the same
reference kind compare by Rule 4c exactly as they compare by Rule 4b. -/
theorem cmp4c_eq_cmp4b {i j : Fin 4}
    (hobs : input.certified.localizedRerootCumulativeRule45Observable (S.slotKey i).prior.rule4aKey =
      input.certified.localizedRerootCumulativeRule45Observable (S.slotKey j).prior.rule4aKey)
    {rI rJ : input.certified.LocalizedRerootRule4bcReading}
    (hI : rI ∈ (S.slotKey i).prior.readings) (hJ : rJ ∈ (S.slotKey j).prior.readings)
    (kind : rI.reference?.isSome = rJ.reference?.isSome) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        rI.rule4cKey.descriptor rJ.rule4cKey.descriptor =
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        rI.rule4bKey.descriptor rJ.rule4bKey.descriptor := by
  obtain ⟨hbI, hcI⟩ := S.readings_built i rI hI
  obtain ⟨hbJ, hcJ⟩ := S.readings_built j rJ hJ
  have hij := congrArg LocalizedCumulativeRule45Observable.descriptor hobs
  simp only [localizedRerootCumulativeRule45Observable] at hij
  cases hrefI : rI.reference? with
  | none =>
      cases hrefJ : rJ.reference? with
      | some _ => simp [hrefI, hrefJ] at kind
      | none =>
          rw [hrefI] at hbI hcI
          rw [hrefJ] at hbJ hcJ
          simp only [rule4bStageOf, rule4cStageOf] at hbI hcI hbJ hcJ
          have kI : rI.rule4bKey = (S.slotKey i).prior.rule4aKey :=
            Option.some.inj (hbI.symm.trans (S.slotSetup i).rule4aBuilt)
          have kJ : rJ.rule4bKey = (S.slotKey j).prior.rule4aKey :=
            Option.some.inj (hbJ.symm.trans (S.slotSetup j).rule4aBuilt)
          have cI : rI.rule4cKey = input.certified.extendLocalizedRerootCumulativeRule45Key
              extendLocalizedRule4aPriorityToRule4cNoReference (S.slotKey i).prior.rule4aKey := by
            apply Option.some.inj
            rw [← hcI, S.noReference_extension i, hbI, kI]
            rfl
          have cJ : rJ.rule4cKey = input.certified.extendLocalizedRerootCumulativeRule45Key
              extendLocalizedRule4aPriorityToRule4cNoReference (S.slotKey j).prior.rule4aKey := by
            apply Option.some.inj
            rw [← hcJ, S.noReference_extension j, hbJ, kJ]
            rfl
          have refl4 : ∀ v, compareLocalizedCumulativeRule45Priority v v = .eq := fun v =>
            CompilerProjectionFidelity.list_compareLex_self _
              CompilerProjectionFidelity.compareNat_self v
          rw [kI, kJ, cI, cJ, extendLocalizedRerootCumulativeRule45Key_descriptor,
            extendLocalizedRerootCumulativeRule45Key_descriptor, hij]
          exact (CompilerProjectionFidelity.compareSparseLayers_self _ refl4 _).trans
            (CompilerProjectionFidelity.compareSparseLayers_self _ refl4 _).symm
  | some ρ =>
      cases hrefJ : rJ.reference? with
      | none => simp [hrefI, hrefJ] at kind
      | some σ =>
          rw [hrefI] at hbI hcI
          rw [hrefJ] at hbJ hcJ
          simp only [rule4bStageOf, rule4cStageOf] at hbI hcI hbJ hcJ
          have cI : rI.rule4cKey = input.certified.extendLocalizedRerootCumulativeRule45Key
              extendLocalizedRule4bPriorityToRule4c rI.rule4bKey :=
            Option.some.inj (hcI.symm.trans
              (physical_rule4c_success (S.slotSetup i) ρ _ _ (S.reachable_slot i) _ hbI))
          have cJ : rJ.rule4cKey = input.certified.extendLocalizedRerootCumulativeRule45Key
              extendLocalizedRule4bPriorityToRule4c rJ.rule4bKey :=
            Option.some.inj (hcJ.symm.trans
              (physical_rule4c_success (S.slotSetup j) σ _ _ (S.reachable_slot j) _ hbJ))
          have imageI := physical_descriptorImage (S.slotSetup i) (.rule4b ρ) _ _
            (S.reachable_slot i) _ hbI
          have imageJ := physical_descriptorImage (S.slotSetup j) (.rule4b σ) _ _
            (S.reachable_slot j) _ hbJ
          rw [cI, cJ, extendLocalizedRerootCumulativeRule45Key_descriptor,
            extendLocalizedRerootCumulativeRule45Key_descriptor]
          exact compareSparseLayers_extend4c_two _ _ (length_two_of_descriptorImage imageI)
            (length_two_of_descriptorImage imageJ)

/-- Every reading of a slot has the reference kind of the slot's selection (`isSome` iff the
selection is nonempty). -/
theorem reading_kind {index : Fin 4}
    (arm4a : input.certified.OriginalRootArm S.center index .rule4a S.read)
    {r : input.certified.LocalizedRerootRule4bcReading} (hr : r ∈ (S.slotKey index).prior.readings) :
    r.reference?.isSome = (S.selection arm4a != .empty) := by
  obtain ⟨armR⟩ := input.certified.exists_originalRootArm S.center index (.rule4b .R) S.read
  obtain ⟨armS⟩ := input.certified.exists_originalRootArm S.center index (.rule4b .S) S.read
  have shape := S.readings_shape arm4a armR armS
  unfold ReadingsShape at shape
  generalize S.selection arm4a = sel at shape ⊢
  cases sel with
  | empty =>
      obtain ⟨r₀, hrs, href, _⟩ := shape
      rw [hrs] at hr
      simp at hr
      subst hr
      simp [href]
  | one sense =>
      cases sense with
      | senior =>
          obtain ⟨r₀, hrs, href, _⟩ := shape
          rw [hrs] at hr
          simp at hr
          subst hr
          simp [href]
      | junior =>
          obtain ⟨r₀, hrs, href, _⟩ := shape
          rw [hrs] at hr
          simp at hr
          subst hr
          simp [href]
  | both =>
      obtain ⟨r₀, s₀, hrs, hrefR, hrefS, _, _⟩ := shape
      rw [hrs] at hr
      simp at hr
      rcases hr with rfl | rfl
      · simp [hrefR]
      · simp [hrefS]

theorem mem_rankReadings {l : List input.certified.LocalizedRerootRule4bcReading}
    {x : input.certified.LocalizedRerootRule4bcReading} (hx : x ∈ input.certified.rankReadings l) :
    x ∈ l := by
  unfold rankReadings at hx
  split at hx
  · split_ifs at hx <;> simp at hx ⊢ <;> tauto
  · exact hx

/-- **C5.**  After a Rule-4a tie and a reference-count tie, the ordered Rule-4c reading
comparison equals the ordered Rule-4b reading comparison. -/
theorem cmp4cReadings_rank_eq {i j : Fin 4}
    (arm4aI : input.certified.OriginalRootArm S.center i .rule4a S.read)
    (arm4aJ : input.certified.OriginalRootArm S.center j .rule4a S.read)
    (hobs : input.certified.localizedRerootCumulativeRule45Observable (S.slotKey i).prior.rule4aKey =
      input.certified.localizedRerootCumulativeRule45Observable (S.slotKey j).prior.rule4aKey)
    (hcount : compare (S.slotKey i).prior.referenceCountPriority
      (S.slotKey j).prior.referenceCountPriority = .eq) :
    input.certified.compareLocalizedRerootCompoundRule4cReadings
        (input.certified.rankReadings (S.slotKey i).prior.readings)
        (input.certified.rankReadings (S.slotKey j).prior.readings) =
      input.certified.compareLocalizedRerootCompoundRule4bReadings
        (input.certified.rankReadings (S.slotKey i).prior.readings)
        (input.certified.rankReadings (S.slotKey j).prior.readings) := by
  have kindEq : (S.selection arm4aI != .empty) = (S.selection arm4aJ != .empty) := by
    rw [S.referenceCountPriority_eq arm4aI, S.referenceCountPriority_eq arm4aJ] at hcount
    rw [compare_eq_iff_eq] at hcount
    exact kind_of_count_eq _ _ hcount
  unfold compareLocalizedRerootCompoundRule4cReadings compareLocalizedRerootCompoundRule4bReadings
  have h := compareLex_map_eq
    (Ordering.byKey (fun reading : input.certified.LocalizedRerootRule4bcReading =>
      reading.rule4cKey.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))
    input.certified.compareLocalizedRerootRule4bcReadingsByRule4b id id
    (input.certified.rankReadings (S.slotKey i).prior.readings)
    (input.certified.rankReadings (S.slotKey j).prior.readings) ?_
  · simpa using h
  · intro x hx y hy
    simp only [Ordering.byKey, id]
    unfold compareLocalizedRerootRule4bcReadingsByRule4b
    simp only [Ordering.byKey]
    exact S.cmp4c_eq_cmp4b hobs (mem_rankReadings hx) (mem_rankReadings hy)
      (by rw [S.reading_kind arm4aI (mem_rankReadings hx), S.reading_kind arm4aJ
        (mem_rankReadings hy), kindEq])

/-- **The full ordered comparator after a Rule-4a tie is the signature comparison.** -/
theorem compound_eq_signatureCompare {i j : Fin 4}
    (arm4aI : input.certified.OriginalRootArm S.center i .rule4a S.read)
    (arm4aJ : input.certified.OriginalRootArm S.center j .rule4a S.read)
    {W D : ℕ} (hWi : (armGraph arm4aI).width ≤ W) (hDi : (armGraph arm4aI).height ≤ D)
    (hWj : (armGraph arm4aJ).width ≤ W) (hDj : (armGraph arm4aJ).height ≤ D)
    (tie4a : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.slotKey i).prior.rule4aKey (S.slotKey j).prior.rule4aKey = .eq) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
        (input.certified.outcomeOrdered (S.slotKey i).prior)
        (input.certified.outcomeOrdered (S.slotKey j).prior) =
      signatureCompare
        (ligandSignatureAt input.certified.moleculeGraph (actualReferenceDescriptorMap input)
          (input.certified.topUnit S.center) (armGraph arm4aI) W D)
        (ligandSignatureAt input.certified.moleculeGraph (actualReferenceDescriptorMap input)
          (input.certified.topUnit S.center) (armGraph arm4aJ) W D) := by
  have main := S.compound_afterRule4a_eq_signatureCompare arm4aI arm4aJ hWi hDi hWj hDj tie4a
  rw [← main]
  rw [input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_afterRule4a_of_tie
    (input.certified.outcomeOrdered (S.slotKey i).prior)
    (input.certified.outcomeOrdered (S.slotKey j).prior) tie4a]
  show (compare (S.slotKey i).prior.referenceCountPriority
        (S.slotKey j).prior.referenceCountPriority).then
      ((input.certified.compareLocalizedRerootCompoundRule4bReadings
          (input.certified.rankReadings (S.slotKey i).prior.readings)
          (input.certified.rankReadings (S.slotKey j).prior.readings)).then
        (input.certified.compareLocalizedRerootCompoundRule4cReadings
          (input.certified.rankReadings (S.slotKey i).prior.readings)
          (input.certified.rankReadings (S.slotKey j).prior.readings))) =
    (compare (S.slotKey i).prior.referenceCountPriority
        (S.slotKey j).prior.referenceCountPriority).then
      (input.certified.compareLocalizedRerootCompoundRule4bReadings
        (input.certified.rankReadings (S.slotKey i).prior.readings)
        (input.certified.rankReadings (S.slotKey j).prior.readings))
  apply then_congr
  intro hcount
  rw [S.cmp4cReadings_rank_eq arm4aI arm4aJ (S.observable_eq_of_tie tie4a) hcount]
  generalize input.certified.compareLocalizedRerootCompoundRule4bReadings
    (input.certified.rankReadings (S.slotKey i).prior.readings)
    (input.certified.rankReadings (S.slotKey j).prior.readings) = d
  cases d <;> rfl

end ActualCentrePhysicalSetup

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compare_extend4c_two
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compareSparseLayers_extend4c_two
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.readings_built
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.noReference_extension
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.cmp4c_eq_cmp4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.cmp4cReadings_rank_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.compound_eq_signatureCompare
