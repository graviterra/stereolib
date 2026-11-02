import TetraStereo.OneCenter.LocalizedActualOrderedRootPhysicalCorrectness
import TetraStereo.OneCenter.LocalizedActualOrderedRootIndependentPriority
import TetraStereo.OneCenter.LocalizedActualOrderedRootExecution
import TetraStereo.OneCenter.LocalizedRerootRule5Relabel
import TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation
import TetraStereo.OneCenter.LocalizedActualKeyTiePhysicalTransport
import TetraStereo.OneCenter.LocalizedPhysicalStageExtensionClosure
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000



































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open RootedTetrahedralBranchSymmetry

/-! ## Generic facts about the readings of a built compound key -/

namespace CertifiedLocalizedCIPInput

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
  (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)

/-- Every reading of a built reading list is built at its own alternative, which is one of the
alternatives. -/
theorem mem_rule4bcReadings_built :
    ∀ (alternatives : List (Option RS)) (readings : List input.LocalizedRerootRule4bcReading),
      input.buildLocalizedRerootRule4bcReadings? target view fuel cursor alternatives =
          some readings →
        ∀ r ∈ readings, r.reference? ∈ alternatives ∧
          input.buildLocalizedRerootRule4bcReading? target view fuel cursor r.reference? = some r
  | [], readings, h => by
      simp only [buildLocalizedRerootRule4bcReadings?, Option.some.injEq] at h
      subst h
      simp
  | alternative :: alternatives, readings, h => by
      simp only [buildLocalizedRerootRule4bcReadings?] at h
      cases hr : input.buildLocalizedRerootRule4bcReading? target view fuel cursor alternative with
      | none => simp [hr] at h
      | some reading =>
          cases hrs : input.buildLocalizedRerootRule4bcReadings? target view fuel cursor
              alternatives with
          | none => simp [hr, hrs] at h
          | some rest =>
              simp only [hr, hrs, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
              subst h
              intro r hr'
              rcases List.mem_cons.1 hr' with rfl | hmem
              · have refEq : alternative = r.reference? := by
                  cases alternative with
                  | none =>
                      exact (Rule4aTableBridge.reading_none_built target view fuel cursor hr).2.symm
                  | some ρ =>
                      exact (Rule4aTableBridge.reading_some_built target view fuel cursor ρ
                        hr).2.2.symm
                rw [← refEq]
                exact ⟨List.mem_cons_self, hr⟩
              · obtain ⟨hmem', hb⟩ :=
                  mem_rule4bcReadings_built alternatives rest hrs r hmem
                exact ⟨List.mem_cons_of_mem _ hmem', hb⟩

/-- A built Rule-5 reading exposes its two common-reference builds. -/
theorem rule5Reading_built {prior : input.LocalizedRerootRule4bcReading}
    {reading : input.LocalizedRerootRule5Reading}
    (h : input.buildLocalizedRerootRule5Reading? target view fuel cursor prior = some reading) :
    input.buildLocalizedRerootCumulativeRule45Key? (localizedRule5StageFor prior.reference? .R)
        target view fuel cursor = some reading.commonR ∧
      input.buildLocalizedRerootCumulativeRule45Key? (localizedRule5StageFor prior.reference? .S)
        target view fuel cursor = some reading.commonS := by
  unfold buildLocalizedRerootRule5Reading? at h
  cases hR : input.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor prior.reference? .R) target view fuel cursor with
  | none => simp [hR] at h
  | some commonR =>
      cases hS : input.buildLocalizedRerootCumulativeRule45Key?
          (localizedRule5StageFor prior.reference? .S) target view fuel cursor with
      | none => simp [hR, hS] at h
      | some commonS =>
          simp only [hR, hS, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl⟩

/-- Every Rule-5 reading of a built list is built at its own prior, which is one of the priors. -/
theorem mem_rule5Readings_built :
    ∀ (priors : List input.LocalizedRerootRule4bcReading)
      (readings : List input.LocalizedRerootRule5Reading),
      input.buildLocalizedRerootRule5Readings? target view fuel cursor priors = some readings →
        ∀ r ∈ readings, r.prior ∈ priors ∧
          input.buildLocalizedRerootRule5Reading? target view fuel cursor r.prior = some r
  | [], readings, h => by
      simp only [buildLocalizedRerootRule5Readings?, Option.some.injEq] at h
      subst h
      simp
  | prior :: priors, readings, h => by
      simp only [buildLocalizedRerootRule5Readings?] at h
      cases hr : input.buildLocalizedRerootRule5Reading? target view fuel cursor prior with
      | none => simp [hr] at h
      | some reading =>
          cases hrs : input.buildLocalizedRerootRule5Readings? target view fuel cursor priors with
          | none => simp [hr, hrs] at h
          | some rest =>
              simp only [hr, hrs, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
              subst h
              intro r hr'
              rcases List.mem_cons.1 hr' with rfl | hmem
              · have hp : r.prior = prior :=
                  input.buildLocalizedRerootRule5Reading?_prior target view fuel cursor hr
                rw [hp]
                exact ⟨List.mem_cons_self, hr⟩
              · obtain ⟨hmem', hb⟩ := mem_rule5Readings_built priors rest hrs r hmem
                exact ⟨List.mem_cons_of_mem _ hmem', hb⟩

/-- The priors of a built Rule-5 list are the given priors. -/
theorem rule5Readings_map_prior :
    ∀ (priors : List input.LocalizedRerootRule4bcReading)
      (readings : List input.LocalizedRerootRule5Reading),
      input.buildLocalizedRerootRule5Readings? target view fuel cursor priors = some readings →
        readings.map (·.prior) = priors
  | [], readings, h => by
      simp only [buildLocalizedRerootRule5Readings?, Option.some.injEq] at h
      subst h
      rfl
  | prior :: priors, readings, h => by
      simp only [buildLocalizedRerootRule5Readings?] at h
      cases hr : input.buildLocalizedRerootRule5Reading? target view fuel cursor prior with
      | none => simp [hr] at h
      | some reading =>
          cases hrs : input.buildLocalizedRerootRule5Readings? target view fuel cursor priors with
          | none => simp [hr, hrs] at h
          | some rest =>
              simp only [hr, hrs, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
              subst h
              simp only [List.map_cons, rule5Readings_map_prior priors rest hrs,
                input.buildLocalizedRerootRule5Reading?_prior target view fuel cursor hr]

variable (input)

/-- Ordering the Rule-5 readings is a permutation. -/
theorem rankRule5Readings_perm :
    ∀ readings : List input.LocalizedRerootRule5Reading,
      (input.rankRule5Readings readings).Perm readings
  | [] => List.Perm.refl _
  | [_] => List.Perm.refl _
  | [a, b] => by
      show (if input.compareRule4bcReadingsComplete a.prior b.prior = .lt then [b, a]
        else [a, b]).Perm [a, b]
      split_ifs
      · exact List.Perm.swap a b []
      · exact List.Perm.refl _
  | _ :: _ :: _ :: _ => List.Perm.refl _

theorem mem_of_mem_rankRule5Readings {readings : List input.LocalizedRerootRule5Reading}
    {r : input.LocalizedRerootRule5Reading} (h : r ∈ input.rankRule5Readings readings) :
    r ∈ readings :=
  (input.rankRule5Readings_perm readings).subset h

theorem rankRule5Readings_ne_nil {readings : List input.LocalizedRerootRule5Reading}
    (h : readings ≠ []) : input.rankRule5Readings readings ≠ [] := by
  intro hnil
  have hlen := (input.rankRule5Readings_perm readings).length_eq
  rw [hnil, List.length_nil] at hlen
  exact h (List.eq_nil_of_length_eq_zero hlen.symm)

/-- A tie of the list comparator is a pointwise tie. -/
theorem forall₂_of_compareLex_eq {α : Type*} (cmp : α → α → Ordering) :
    ∀ l m : List α, List.compareLex cmp l m = .eq →
      List.Forall₂ (fun a b => cmp a b = .eq) l m
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => by simp [List.compareLex] at h
  | _ :: _, [], h => by simp [List.compareLex] at h
  | a :: l, b :: m, h => by
      rw [List.compareLex_cons_cons, Ordering.then_eq_eq] at h
      exact List.Forall₂.cons h.1 (forall₂_of_compareLex_eq cmp l m h.2)

theorem forall₂_imp_of_mem_pointwise {α β : Type*} {R S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m →
      (∀ a b, a ∈ l → b ∈ m → R a b → S a b) → List.Forall₂ S l m
  | [], [], _, _ => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t, hmem =>
      List.Forall₂.cons (hmem _ _ List.mem_cons_self List.mem_cons_self h)
        (forall₂_imp_of_mem_pointwise t fun a b ha hb =>
          hmem a b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb))

theorem forall₂_and {α β : Type*} {R S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → List.Forall₂ S l m →
      List.Forall₂ (fun a b => R a b ∧ S a b) l m
  | [], [], _, _ => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons hr tr, List.Forall₂.cons hs ts =>
      List.Forall₂.cons ⟨hr, hs⟩ (forall₂_and tr ts)

/-- An ordered prior tie is a Rule-4a tie, equal reference counts, and a pointwise complete tie
of the ordered Rule-5 readings' priors. -/
theorem orderedPriorTie_matched (k₁ k₂ : input.LocalizedRerootCompoundRule45Key)
    (tie : input.compareLocalizedRerootCompoundRule4bcKeys (input.outcomeOrdered45 k₁).prior
      (input.outcomeOrdered45 k₂).prior = .eq)
    (priors₁ : (k₁.rule5Readings.map (·.prior)) = k₁.prior.readings)
    (priors₂ : (k₂.rule5Readings.map (·.prior)) = k₂.prior.readings) :
    input.compareLocalizedRerootCumulativeRule45Keys k₁.prior.rule4aKey k₂.prior.rule4aKey = .eq ∧
      k₁.prior.referenceCountPriority = k₂.prior.referenceCountPriority ∧
      List.Forall₂ (fun u v : input.LocalizedRerootRule5Reading =>
          input.compareRule4bcReadingsComplete u.prior v.prior = .eq)
        (input.outcomeOrdered45 k₁).rule5Readings (input.outcomeOrdered45 k₂).rule5Readings := by
  obtain ⟨h4a, hcount, h4b, h4c⟩ :=
    (input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff _ _).1 tie
  refine ⟨h4a, Nat.compare_eq_eq.1 hcount, ?_⟩
  have f4b := forall₂_of_compareLex_eq _ _ _ h4b
  have f4c := forall₂_of_compareLex_eq _ _ _ h4c
  have both := forall₂_and f4b f4c
  have priorsEq₁ : (input.outcomeOrdered45 k₁).prior.readings =
      (input.outcomeOrdered45 k₁).rule5Readings.map (·.prior) := by
    show input.rankReadings k₁.prior.readings = (input.rankRule5Readings k₁.rule5Readings).map _
    rw [input.rankRule5Readings_map_prior, priors₁]
  have priorsEq₂ : (input.outcomeOrdered45 k₂).prior.readings =
      (input.outcomeOrdered45 k₂).rule5Readings.map (·.prior) := by
    show input.rankReadings k₂.prior.readings = (input.rankRule5Readings k₂.rule5Readings).map _
    rw [input.rankRule5Readings_map_prior, priors₂]
  rw [priorsEq₁, priorsEq₂, List.forall₂_map_left_iff, List.forall₂_map_right_iff] at both
  refine both.imp ?_
  intro u v h
  unfold compareRule4bcReadingsComplete
  rw [compareLex_eq_eq]
  exact h

end CertifiedLocalizedCIPInput

/-! ## The physical centre setup -/

namespace Rule4aTableBridge
namespace ActualCentrePhysicalSetup

open LocalizedGeneralRigidPhysicalKeySeparation

variable {input : LocalizedUniversalReference.Input} (S : ActualCentrePhysicalSetup input)

/-- The production evaluation fuel. -/
local notation "evalFuel" =>
  localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input)



theorem exists_alpha : ∃ alpha : Equiv.Perm (Fin 4), ∀ index : Fin 4,
    (S.frame.cursorAt index).occurrence.1.node.current? = some (input.certified.detectedMultiCenterMolecule.ligandAtomAt S.c (alpha index)) := by
  obtain ⟨frame', alpha, frameComputed', slotSpec'⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
      S.singleBonded S.acyclic (globalCarrierFuel_adequate input) S.top
      (ActualReaderPhysicalBranchInverse.topTarget_current input S.c) S.c rfl
  have frameEq : frame' = S.frame := Option.some.inj (frameComputed'.symm.trans S.frameComputed)
  subst frameEq
  exact ⟨alpha, slotSpec'⟩

/-- A physical slot permutation of the frame. -/
noncomputable def alpha : Equiv.Perm (Fin 4) := Classical.choose S.exists_alpha

theorem slotSpec : ∀ index : Fin 4,
    (S.frame.cursorAt index).occurrence.1.node.current? =
      some (input.certified.detectedMultiCenterMolecule.ligandAtomAt S.c (S.alpha index)) :=
  Classical.choose_spec S.exists_alpha

theorem derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame S.top S.frame :=
  (input.certified.localizedOccurrenceFourLigandFrame?_eq_some_iff S.top S.frame).mp S.frameComputed


theorem inverse : GeneralRigidPhysicalBranchTransport input S.cfg S.c S.frame S.alpha :=
  generalRigidPhysicalBranchTransport_of_physicalDomain input S.noDouble S.singleBonded S.acyclic
    S.hcharge S.cfg S.c S.physicalDomain S.frame S.alpha S.frameComputed S.slotSpec

theorem readerSparse : ∀ cursor, LocalizedRule4bSparseLabel
    (ActualReaderPhysicalBranchInverse.dependencyReader input S.c cursor) :=
  actualDependencyReader_sparse_of_physicalDomain input S.singleBonded S.acyclic S.hcharge
    S.noDouble S.cfg S.c S.physicalDomain

/-- The slot setup of frame slot `i`. -/
noncomputable def frameSlotSetup (i : Fin 4) : ActualSlotPhysicalSetup input where
  c := S.c
  frame := S.frame
  frameComputed := S.frameComputed
  slot := i
  singleBonded := S.singleBonded
  acyclic := S.acyclic
  hcharge := S.hcharge
  noDouble := S.noDouble
  cfg := S.cfg
  physicalDomain := S.physicalDomain
  oAtom := input.certified.detectedMultiCenterMolecule.ligandAtomAt S.c (S.alpha i)
  oObserved := S.slotSpec i

theorem frameKey_built (i : Fin 4) :
    input.certified.buildLocalizedRerootCompoundRule45Key? S.top S.referenceView evalFuel
      (S.frame.cursorAt i) = some (S.frameKey i) :=
  actualSlotCompoundBuilt input S.c S.frame S.frameComputed i

theorem slotKeysBuilt : SlotKeysBuilt input.certified S.top S.referenceView S.frame S.frameKey :=
  S.frameKey_built

theorem rule4aKey_built (i : Fin 4) :
    input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4a S.top S.referenceView evalFuel
      (S.frame.cursorAt i) = some (S.frameKey i).prior.rule4aKey :=
  (S.frameSlotSetup i).rule4aBuilt

/-- The `WithRead?` builder at the dependency reader is the production builder. -/
theorem withRead_eq (stage : LocalizedCumulativeRule45Stage) (cursor) :
    input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
        (ActualReaderPhysicalBranchInverse.dependencyReader input S.c) evalFuel cursor =
      input.certified.buildLocalizedRerootCumulativeRule45Key? stage S.top S.referenceView evalFuel
        cursor :=
  buildWithRead_dependencyReader_eq_build (S.frameSlotSetup 0) stage evalFuel cursor

/-- The Rule-5 readings of a frame key are built, and their priors are its prior readings. -/
theorem frameKey_readings (i : Fin 4) :
    (S.frameKey i).rule5Readings.map (·.prior) = (S.frameKey i).prior.readings ∧
      ∀ r ∈ (S.frameKey i).rule5Readings,
        r.prior ∈ (S.frameKey i).prior.readings ∧
          input.certified.buildLocalizedRerootRule5Reading? S.top S.referenceView evalFuel
            (S.frame.cursorAt i) r.prior = some r := by
  obtain ⟨_, readingsBuilt⟩ := buildLocalizedRerootCompoundRule45Key?_prior_built input.certified
    S.top S.referenceView evalFuel (S.frame.cursorAt i) (S.frameKey i) (S.frameKey_built i)
  exact ⟨rule5Readings_map_prior _ _ _ _ _ _ readingsBuilt,
    fun r hr => mem_rule5Readings_built _ _ _ _ _ _ readingsBuilt r hr⟩

/-- The prior readings of a frame key are built at their own alternatives. -/
theorem frameKey_priorReadings (i : Fin 4) :
    ∀ r ∈ (S.frameKey i).prior.readings,
      r.reference? ∈ localizedRule4bcReferenceAlternatives (S.frameKey i).prior.references ∧
        input.certified.buildLocalizedRerootRule4bcReading? S.top S.referenceView evalFuel
          (S.frame.cursorAt i) r.reference? = some r := by
  obtain ⟨_, _, _, hreadings⟩ := compound_built_components _ _ _ _
    (actualSlotPriorBuilt input S.c S.frame S.frameComputed i)
  exact fun r hr => mem_rule4bcReadings_built _ _ _ _ _ _ hreadings r hr

/-- A reading's reference is `none` exactly when its key has no reference. -/
theorem reference?_eq_none_iff (i : Fin 4) {r : input.certified.LocalizedRerootRule4bcReading}
    (hr : r ∈ (S.frameKey i).prior.readings) :
    r.reference? = none ↔ (S.frameKey i).prior.references = [] := by
  obtain ⟨hmem, _⟩ := S.frameKey_priorReadings i r hr
  constructor
  · intro hnone
    rw [hnone] at hmem
    cases href : (S.frameKey i).prior.references with
    | nil => rfl
    | cons ρ rest =>
        rw [href] at hmem
        simp [localizedRule4bcReferenceAlternatives] at hmem
  · intro hnil
    rw [hnil] at hmem
    simpa [localizedRule4bcReferenceAlternatives] using hmem

/-- The reference lists of a frame key have at most two members. -/
theorem references_length_le_two (i : Fin 4) : (S.frameKey i).prior.references.length ≤ 2 := by
  obtain ⟨_, _, _, hread⟩ := compound_built_components _ _ _ _
    (actualSlotPriorBuilt input S.c S.frame S.frameComputed i)
  have shape := (input.certified.built_prior_shape S.top S.referenceView evalFuel _ _
    (actualSlotPriorBuilt input S.c S.frame S.frameComputed i)).1
  have len := buildLocalizedRerootRule4bcReadings?_length_eq input.certified S.top S.referenceView
    evalFuel _ _ _ hread
  rw [len] at shape
  cases href : (S.frameKey i).prior.references with
  | nil => simp
  | cons ρ rest =>
      rw [href] at shape
      simpa [localizedRule4bcReferenceAlternatives] using shape

/-- Reference lists of at most two members with equal count priority are both empty or both
nonempty. -/
theorem nil_iff_of_countPriority_eq :
    ∀ {refsI refsJ : List RS}, refsI.length ≤ 2 → refsJ.length ≤ 2 →
      constitutionalRule4bReferenceCountPriority refsI =
        constitutionalRule4bReferenceCountPriority refsJ →
      (refsI = [] ↔ refsJ = [])
  | [], [], _, _, _ => by simp
  | [], [_], _, _, h => by simp [constitutionalRule4bReferenceCountPriority] at h
  | [], [_, _], _, _, h => by simp [constitutionalRule4bReferenceCountPriority] at h
  | [_], [], _, _, h => by simp [constitutionalRule4bReferenceCountPriority] at h
  | [_, _], [], _, _, h => by simp [constitutionalRule4bReferenceCountPriority] at h
  | [_], [_], _, _, _ => by simp
  | [_], [_, _], _, _, _ => by simp
  | [_, _], [_], _, _, _ => by simp
  | [_, _], [_, _], _, _, _ => by simp
  | _ :: _ :: _ :: _, _, hI, _, _ => by simp at hI; omega
  | [], _ :: _ :: _ :: _, _, hJ, _ => by simp at hJ; omega
  | [_], _ :: _ :: _ :: _, _, hJ, _ => by simp at hJ; omega
  | [_, _], _ :: _ :: _ :: _, _, hJ, _ => by simp at hJ; omega

/-- The reference count determines whether the reference list is empty. -/
theorem references_nil_iff_of_count_eq {i j : Fin 4}
    (hcount : (S.frameKey i).prior.referenceCountPriority =
      (S.frameKey j).prior.referenceCountPriority) :
    (S.frameKey i).prior.references = [] ↔ (S.frameKey j).prior.references = [] := by
  obtain ⟨_, _, hcountI, _⟩ := compound_built_components _ _ _ _
    (actualSlotPriorBuilt input S.c S.frame S.frameComputed i)
  obtain ⟨_, _, hcountJ, _⟩ := compound_built_components _ _ _ _
    (actualSlotPriorBuilt input S.c S.frame S.frameComputed j)
  rw [hcountI, hcountJ] at hcount
  exact nil_iff_of_countPriority_eq (S.references_length_le_two i)
    (S.references_length_le_two j) hcount

/-! ## Matched-reading decoding -/

/-- The common-reference tables of a referenced Rule-5 reading are the Rule-5 relabelings of its
Rule-4c table (T1). -/
theorem commonR_descriptor_eq_lift (i : Fin 4) {u : input.certified.LocalizedRerootRule5Reading}
    (hu : u ∈ (S.frameKey i).rule5Readings) {ρ : RS} (hρ : u.prior.reference? = some ρ) :
    u.commonR.descriptor = u.prior.rule4cKey.descriptor.map (rule5LiftLayer (RS.R == ρ)) ∧
      u.commonS.descriptor = u.prior.rule4cKey.descriptor.map (rule5LiftLayer (RS.S == ρ)) := by
  obtain ⟨hmem, hbuild⟩ := (S.frameKey_readings i).2 u hu
  obtain ⟨_, hbuild4bc⟩ := S.frameKey_priorReadings i u.prior hmem
  rw [hρ] at hbuild4bc
  obtain ⟨_, b4c, _⟩ := reading_some_built S.top S.referenceView evalFuel _ ρ hbuild4bc
  obtain ⟨cR, cS⟩ := rule5Reading_built S.top S.referenceView evalFuel _ hbuild
  rw [hρ] at cR cS
  have liftR := input.certified.buildLocalizedRerootCumulativeRule45Key?_rule5 ρ .R S.top
    S.referenceView evalFuel (S.frame.cursorAt i)
  have liftS := input.certified.buildLocalizedRerootCumulativeRule45Key?_rule5 ρ .S S.top
    S.referenceView evalFuel (S.frame.cursorAt i)
  change input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule5 ρ .R) S.top
    S.referenceView evalFuel (S.frame.cursorAt i) = some u.commonR at cR
  change input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule5 ρ .S) S.top
    S.referenceView evalFuel (S.frame.cursorAt i) = some u.commonS at cS
  rw [liftR, b4c, Option.map_some, Option.some.injEq] at cR
  rw [liftS, b4c, Option.map_some, Option.some.injEq] at cS
  rw [← cR, ← cS]
  exact ⟨rfl, rfl⟩

/-- **Same-label decoding.**  Two Rule-5 readings of two distinct frame slots with a Rule-4a tie
and equal common-`R` descriptor tables yield a physical proper transport between the slots. -/
theorem properTransport_of_commonR_eq {i j : Fin 4} (hij : i ≠ j)
    {u v : input.certified.LocalizedRerootRule5Reading}
    (hu : u ∈ (S.frameKey i).rule5Readings) (hv : v ∈ (S.frameKey j).rule5Readings)
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.frameKey i).prior.rule4aKey (S.frameKey j).prior.rule4aKey = .eq)
    (hdesc : u.commonR.descriptor = v.commonR.descriptor) :
    ProperTransport input.certified.detectedMultiCenterMolecule S.cfg S.c (S.alpha i) (S.alpha j) := by
  classical
  obtain ⟨_, hbuildU⟩ := (S.frameKey_readings i).2 u hu
  obtain ⟨_, hbuildV⟩ := (S.frameKey_readings j).2 v hv
  obtain ⟨commonRU, _⟩ := rule5Reading_built S.top S.referenceView evalFuel _ hbuildU
  obtain ⟨commonRV, _⟩ := rule5Reading_built S.top S.referenceView evalFuel _ hbuildV
  have rule4aColumns := cumulativeRule45Tie_constitutional_columns input.certified
    (S.frameKey i).prior.rule4aKey (S.frameKey j).prior.rule4aKey rule4aTie
  have leftConstitutional : constitutionalObservable u.commonR.constitutional =
      constitutionalObservable (S.frameKey i).prior.rule4aKey.constitutional :=
    cumulative_builds_constitutional_observable_equal input.certified (S.frame.cursorAt i)
      commonRU (S.rule4aKey_built i)
  have rightConstitutional : constitutionalObservable v.commonR.constitutional =
      constitutionalObservable (S.frameKey j).prior.rule4aKey.constitutional :=
    cumulative_builds_constitutional_observable_equal input.certified (S.frame.cursorAt j)
      commonRV (S.rule4aKey_built j)
  have leftRule1a := congrArg (fun o => o.rule1a) leftConstitutional
  have leftRule1b := congrArg (fun o => o.rule1b) leftConstitutional
  have leftRule2 := congrArg (fun o => o.rule2) leftConstitutional
  have rightRule1a := congrArg (fun o => o.rule1a) rightConstitutional
  have rightRule1b := congrArg (fun o => o.rule1b) rightConstitutional
  have rightRule2 := congrArg (fun o => o.rule2) rightConstitutional
  simp only [constitutionalObservable] at leftRule1a leftRule1b leftRule2
  simp only [constitutionalObservable] at rightRule1a rightRule1b rightRule2
  have leftWithRead : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor u.prior.reference? .R)
      (ActualReaderPhysicalBranchInverse.dependencyReader input S.c) evalFuel (S.frame.cursorAt i) =
        some u.commonR := by
    rw [S.withRead_eq]; exact commonRU
  have rightWithRead : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor v.prior.reference? .R)
      (ActualReaderPhysicalBranchInverse.dependencyReader input S.c) evalFuel (S.frame.cursorAt j) =
        some v.commonR := by
    rw [S.withRead_eq]; exact commonRV
  obtain ⟨tL, tLsource, tLmatch, tLrealizes, _⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input.certified
      (localizedRule5StageFor u.prior.reference? .R)
      (ActualReaderPhysicalBranchInverse.dependencyReader input S.c) evalFuel (S.frame.cursorAt i)
      u.commonR leftWithRead
  obtain ⟨tR, tRsource, tRmatch, tRrealizes, _⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input.certified
      (localizedRule5StageFor v.prior.reference? .R)
      (ActualReaderPhysicalBranchInverse.dependencyReader input S.c) evalFuel (S.frame.cursorAt j)
      v.commonR rightWithRead
  have tableRule1aEq : (tL.tables (localizedRule5StageFor u.prior.reference? .R)).rule1a =
      (tR.tables (localizedRule5StageFor v.prior.reference? .R)).rule1a := by
    rw [tLmatch.tableMatch.1, leftRule1a, rule4aColumns.1, ← rightRule1a,
      ← tRmatch.tableMatch.1]
  have tableRule1bEq : (tL.tables (localizedRule5StageFor u.prior.reference? .R)).rule1b =
      (tR.tables (localizedRule5StageFor v.prior.reference? .R)).rule1b := by
    rw [tLmatch.tableMatch.2.1, leftRule1b, rule4aColumns.2.1, ← rightRule1b,
      ← tRmatch.tableMatch.2.1]
  have tableRule2Eq : (tL.tables (localizedRule5StageFor u.prior.reference? .R)).rule2 =
      (tR.tables (localizedRule5StageFor v.prior.reference? .R)).rule2 := by
    rw [tLmatch.tableMatch.2.2.1, leftRule2, rule4aColumns.2.2, ← rightRule2,
      ← tRmatch.tableMatch.2.2.1]
  have tableDescriptorEq :
      (tL.tables (localizedRule5StageFor u.prior.reference? .R)).descriptor =
        (tR.tables (localizedRule5StageFor v.prior.reference? .R)).descriptor := by
    rw [tLmatch.tableMatch.2.2.2, hdesc, ← tRmatch.tableMatch.2.2.2]
  have priorityEq : localizedCumulativeRule45Priority
      (localizedRule5StageFor u.prior.reference? .R) tL.label =
      localizedCumulativeRule45Priority (localizedRule5StageFor v.prior.reference? .R) tR.label :=
    headCommonR_priority_eq_of_descriptor_eq _ _ tLmatch.tableMatch tRmatch.tableMatch hdesc
  have observationEq : observation tL = observation tR := by
    cases hrefL : u.prior.reference? with
    | none =>
        cases hrefR : v.prior.reference? with
        | none =>
            exact table_observation_eq_of_rule5NoRule4bReference_columns_eq .R tL tR
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableRule1aEq)
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableRule1bEq)
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableRule2Eq)
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableDescriptorEq)
        | some refR =>
            exfalso
            have lengthEq := congrArg List.length priorityEq
            simp [hrefL, hrefR, localizedRule5StageFor, localizedCumulativeRule45Priority]
              at lengthEq
    | some refL =>
        cases hrefR : v.prior.reference? with
        | none =>
            exfalso
            have lengthEq := congrArg List.length priorityEq
            simp [hrefL, hrefR, localizedRule5StageFor, localizedCumulativeRule45Priority]
              at lengthEq
        | some refR =>
            exact table_observation_eq_of_rule5_commonReference_columns_eq refL refR .R tL tR
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableRule1aEq)
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableRule1bEq)
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableRule2Eq)
              (by simpa [hrefL, hrefR, localizedRule5StageFor] using tableDescriptorEq)
  have shapeEq : shape tL = shape tR :=
    table_shape_eq_of_columns_eq (localizedRule5StageFor u.prior.reference? .R)
      (localizedRule5StageFor v.prior.reference? .R) tL tR tableRule1aEq tableRule1bEq tableRule2Eq
  exact S.inverse (S.alpha i) (S.alpha j) (fun h => hij (S.alpha.injective h)) tL tR
    (by rw [tLsource, Equiv.symm_apply_apply]) (by rw [tRsource, Equiv.symm_apply_apply])
    tLrealizes tRrealizes shapeEq false
    (fun path nodeL nodeR foundL foundR => by
      simpa using subtreeAt?_label_eq_of_observation_eq path tL tR observationEq nodeL nodeR
        foundL foundR)

/-- **Mirror decoding.**  Two Rule-5 readings of two distinct frame slots with a Rule-4a tie,
different own references and tied Rule-4b tables yield a physical mirror transport. -/
theorem mirrorTransport_of_cross {i j : Fin 4} (hij : i ≠ j)
    {u v : input.certified.LocalizedRerootRule5Reading}
    (hu : u ∈ (S.frameKey i).rule5Readings) (hv : v ∈ (S.frameKey j).rule5Readings)
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.frameKey i).prior.rule4aKey (S.frameKey j).prior.rule4aKey = .eq)
    {ρ₁ ρ₂ : RS} (hρ₁ : u.prior.reference? = some ρ₁) (hρ₂ : v.prior.reference? = some ρ₂)
    (hne : ρ₁ ≠ ρ₂)
    (tie4b : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      u.prior.rule4bKey.descriptor v.prior.rule4bKey.descriptor = .eq) :
    MirrorTransport input.certified.detectedMultiCenterMolecule S.cfg S.c (S.alpha i) (S.alpha j) := by
  classical
  obtain ⟨hmemU, _⟩ := (S.frameKey_readings i).2 u hu
  obtain ⟨hmemV, _⟩ := (S.frameKey_readings j).2 v hv
  obtain ⟨_, hbU⟩ := S.frameKey_priorReadings i u.prior hmemU
  obtain ⟨_, hbV⟩ := S.frameKey_priorReadings j v.prior hmemV
  rw [hρ₁] at hbU
  rw [hρ₂] at hbV
  obtain ⟨b4bU, _, _⟩ := reading_some_built S.top S.referenceView evalFuel _ ρ₁ hbU
  obtain ⟨b4bV, _, _⟩ := reading_some_built S.top S.referenceView evalFuel _ ρ₂ hbV
  obtain ⟨tL, tR, tLSource, tRSource, realizesL, realizesR, hshape, _, pathLabels⟩ :=
    actual_rule4b_key_tie_labelTableTransport input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input S.c) S.readerSparse
      (S.frame.cursorAt i) (S.frame.cursorAt j) evalFuel evalFuel evalFuel evalFuel ρ₁ ρ₂
      (S.frameKey i).prior.rule4aKey (S.frameKey j).prior.rule4aKey
      u.prior.rule4bKey v.prior.rule4bKey
      (by rw [S.withRead_eq]; exact S.rule4aKey_built i)
      (by rw [S.withRead_eq]; exact S.rule4aKey_built j)
      (by rw [S.withRead_eq]; exact b4bU)
      (by rw [S.withRead_eq]; exact b4bV)
      rule4aTie tie4b
  have flagEq : referenceMirror ρ₁ ρ₂ = true := referenceMirror_eq_true_iff.mpr hne
  exact S.inverse (S.alpha i) (S.alpha j) (fun h => hij (S.alpha.injective h)) tL tR
    (by rw [tLSource, Equiv.symm_apply_apply]) (by rw [tRSource, Equiv.symm_apply_apply])
    realizesL realizesR hshape true
    (fun path nodeL nodeR foundL foundR => by
      have h := pathLabels path nodeL nodeR foundL foundR
      rw [flagEq] at h
      simpa using h)

/-! ## Under proper-distinguishability every matched pair is cross-referenced -/

section Distinct

variable (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport input.certified.detectedMultiCenterMolecule S.cfg S.c i j)
include distinct

/-- A matched pair of referenced readings has different references. -/
theorem matched_ne {i j : Fin 4} (hij : i ≠ j)
    {u v : input.certified.LocalizedRerootRule5Reading}
    (hu : u ∈ (S.frameKey i).rule5Readings) (hv : v ∈ (S.frameKey j).rule5Readings)
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.frameKey i).prior.rule4aKey (S.frameKey j).prior.rule4aKey = .eq)
    (tie : input.certified.compareRule4bcReadingsComplete u.prior v.prior = .eq)
    {ρ₁ ρ₂ : RS} (hρ₁ : u.prior.reference? = some ρ₁) (hρ₂ : v.prior.reference? = some ρ₂) :
    ρ₁ ≠ ρ₂ := by
  intro heq
  subst heq
  apply distinct (S.alpha i) (S.alpha j) (fun h => hij (S.alpha.injective h))
  apply S.properTransport_of_commonR_eq hij hu hv rule4aTie
  rw [(S.commonR_descriptor_eq_lift i hu hρ₁).1, (S.commonR_descriptor_eq_lift j hv hρ₂).1,
    input.certified.rule4cKey_descriptor_eq_of_complete_eq _ _ tie]

/-- A matched pair of referenced readings is a mirror reading. -/
theorem matched_mirrorReading {i j : Fin 4} (hij : i ≠ j)
    {u v : input.certified.LocalizedRerootRule5Reading}
    (hu : u ∈ (S.frameKey i).rule5Readings) (hv : v ∈ (S.frameKey j).rule5Readings)
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.frameKey i).prior.rule4aKey (S.frameKey j).prior.rule4aKey = .eq)
    (tie : input.certified.compareRule4bcReadingsComplete u.prior v.prior = .eq)
    {ρ₁ ρ₂ : RS} (hρ₁ : u.prior.reference? = some ρ₁) (hρ₂ : v.prior.reference? = some ρ₂) :
    LocalizedRule5SwapAndSignal.MirrorReading input.certified u v := by
  have hne := S.matched_ne distinct hij hu hv rule4aTie tie hρ₁ hρ₂
  obtain ⟨uR, uS⟩ := S.commonR_descriptor_eq_lift i hu hρ₁
  obtain ⟨vR, vS⟩ := S.commonR_descriptor_eq_lift j hv hρ₂
  have T := input.certified.rule4cKey_descriptor_eq_of_complete_eq _ _ tie
  have hswap : ρ₂ = RS.swap ρ₁ := by
    cases ρ₁ <;> cases ρ₂ <;> simp_all [RS.swap]
  subst hswap
  refine ⟨?_, ?_⟩
  · rw [uR, vS, T]; cases ρ₁ <;> rfl
  · rw [uS, vR, T]; cases ρ₁ <;> rfl

omit distinct in
/-- The complete-reading tie of two priors is a Rule-4b table tie. -/
theorem rule4b_tie_of_complete {u v : input.certified.LocalizedRerootRule4bcReading}
    (tie : input.certified.compareRule4bcReadingsComplete u v = .eq) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      u.rule4bKey.descriptor v.rule4bKey.descriptor = .eq := by
  unfold compareRule4bcReadingsComplete at tie
  rw [compareLex_eq_eq] at tie
  exact tie.1

/-- Every matched pair of an ordered prior tie between distinct slots is a mirror reading of
opposite references; an empty-reference pair is excluded. -/
theorem matched_classification {i j : Fin 4} (hij : i ≠ j)
    (tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) i j)
    {u v : input.certified.LocalizedRerootRule5Reading}
    (hu : u ∈ (S.frameKey i).rule5Readings) (hv : v ∈ (S.frameKey j).rule5Readings)
    (hcomplete : input.certified.compareRule4bcReadingsComplete u.prior v.prior = .eq) :
    ∃ ρ₁ ρ₂ : RS, u.prior.reference? = some ρ₁ ∧ v.prior.reference? = some ρ₂ ∧ ρ₁ ≠ ρ₂ ∧
      LocalizedRule5SwapAndSignal.MirrorReading input.certified u v ∧
      MirrorTransport input.certified.detectedMultiCenterMolecule S.cfg S.c (S.alpha i) (S.alpha j) := by
  obtain ⟨rule4aTie, hcount, _⟩ := input.certified.orderedPriorTie_matched _ _ tie
    (S.frameKey_readings i).1 (S.frameKey_readings j).1
  obtain ⟨hmemU, _⟩ := (S.frameKey_readings i).2 u hu
  obtain ⟨hmemV, _⟩ := (S.frameKey_readings j).2 v hv
  cases hρ₁ : u.prior.reference? with
  | none =>
      exfalso
      -- both reference lists are empty: the production keys are the ordered keys and the
      -- empty-reference prior tie is a proper transport
      have nilI : (S.frameKey i).prior.references = [] :=
        (S.reference?_eq_none_iff i hmemU).1 hρ₁
      have nilJ : (S.frameKey j).prior.references = [] :=
        (S.references_nil_iff_of_count_eq hcount).1 nilI
      have shortI : (S.frameKey i).prior.readings.length ≤ 1 := by
        obtain ⟨_, _, _, hreadI⟩ := compound_built_components _ _ _ _
          (actualSlotPriorBuilt input S.c S.frame S.frameComputed i)
        rw [buildLocalizedRerootRule4bcReadings?_length_eq input.certified S.top S.referenceView
          evalFuel _ _ _ hreadI, nilI]
        decide
      have shortJ : (S.frameKey j).prior.readings.length ≤ 1 := by
        obtain ⟨_, _, _, hreadJ⟩ := compound_built_components _ _ _ _
          (actualSlotPriorBuilt input S.c S.frame S.frameComputed j)
        rw [buildLocalizedRerootRule4bcReadings?_length_eq input.certified S.top S.referenceView
          evalFuel _ _ _ hreadJ, nilJ]
        decide
      have productionTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
          (S.frameKey i).prior (S.frameKey j).prior = .eq := by
        have h := tie
        unfold priorKeyTie orderedKeys at h
        rw [input.certified.outcomeOrdered45_prior, input.certified.outcomeOrdered45_prior,
          input.certified.outcomeOrdered_eq_self_of_length_le_one _ shortI,
          input.certified.outcomeOrdered_eq_self_of_length_le_one _ shortJ] at h
        exact h
      exact distinct (S.alpha i) (S.alpha j) (fun h => hij (S.alpha.injective h))
        (actualFrame_empty_priorTie_properTransport_generalRigid input S.singleBonded S.acyclic
          S.hcharge S.noDouble S.cfg S.c S.physicalDomain S.frame S.alpha S.inverse S.derived i j
          hij nilI nilJ productionTie)
  | some ρ₁ =>
      cases hρ₂ : v.prior.reference? with
      | none =>
          exfalso
          have nilJ : (S.frameKey j).prior.references = [] :=
            (S.reference?_eq_none_iff j hmemV).1 hρ₂
          have nilI : (S.frameKey i).prior.references = [] :=
            (S.references_nil_iff_of_count_eq hcount).2 nilJ
          have := (S.reference?_eq_none_iff i hmemU).2 nilI
          rw [hρ₁] at this
          cases this
      | some ρ₂ =>
          have hne := S.matched_ne distinct hij hu hv rule4aTie hcomplete hρ₁ hρ₂
          exact ⟨ρ₁, ρ₂, rfl, rfl, hne,
            S.matched_mirrorReading distinct hij hu hv rule4aTie hcomplete hρ₁ hρ₂,
            S.mirrorTransport_of_cross hij hu hv rule4aTie hρ₁ hρ₂ hne
              (rule4b_tie_of_complete hcomplete)⟩

/-! ## The data core of the ordered keys -/

/-- **Mirror readings at every distinct ordered-prior-tied pair.** -/
theorem orderedKeys_priorTieMirrorReadings :
    input.certified.PriorTieMirrorReadings (orderedKeys input.certified S.frameKey) := by
  intro i j hij tie
  obtain ⟨_, _, matched⟩ := input.certified.orderedPriorTie_matched _ _ tie
    (S.frameKey_readings i).1 (S.frameKey_readings j).1
  refine forall₂_imp_of_mem_pointwise matched ?_
  intro u v hu hv hcomplete
  obtain ⟨_, _, _, _, _, mirror, _⟩ := S.matched_classification distinct hij tie
    (input.certified.mem_of_mem_rankRule5Readings (readings := (S.frameKey i).rule5Readings) hu)
    (input.certified.mem_of_mem_rankRule5Readings (readings := (S.frameKey j).rule5Readings) hv)
    hcomplete
  exact mirror

omit distinct in
/-- The ordered Rule-5 reading lists are nonempty. -/
theorem orderedKeys_rule5Readings_ne_nil (i : Fin 4) :
    (orderedKeys input.certified S.frameKey i).rule5Readings ≠ [] := by
  apply input.certified.rankRule5Readings_ne_nil
  intro hnil
  have hmap := (S.frameKey_readings i).1
  rw [hnil] at hmap
  have hnil' : (S.frameKey i).prior.readings = [] := by simpa using hmap.symm
  obtain ⟨_, _, _, hreadI⟩ := compound_built_components _ _ _ _
    (actualSlotPriorBuilt input S.c S.frame S.frameComputed i)
  have len := buildLocalizedRerootRule4bcReadings?_length_eq input.certified S.top
    S.referenceView evalFuel _ _ _ hreadI
  rw [hnil', List.length_nil] at len
  have pos := referenceAlternatives_length_pos (S.frameKey i).prior.references
  rw [← len] at pos
  exact lt_irrefl 0 pos

/-- **Off-diagonal strictness of the ordered keys.**  A complete ordered tie between two distinct
slots would make the heads of their ordered Rule-5 lists equal in the common-`R` table, hence a
proper transport. -/
theorem orderedKeys_offDiagonalStrict :
    input.certified.CompoundKeyOffDiagonalStrict (orderedKeys input.certified S.frameKey) := by
  intro i j hij htie
  have tie : input.certified.compareLocalizedRerootCompoundRule45Keys
      (orderedKeys input.certified S.frameKey i) (orderedKeys input.certified S.frameKey j) = .eq := by
    simpa [compoundKeyComparison, Ordering.byKey] using htie
  obtain ⟨priorTie, readingsTie⟩ := compoundRule45Tie_prior_readings input.certified _ _ tie
  obtain ⟨rule4aTie, _, _⟩ := input.certified.orderedPriorTie_matched _ _ priorTie
    (S.frameKey_readings i).1 (S.frameKey_readings j).1
  obtain ⟨u, tailU, hu⟩ := List.exists_cons_of_ne_nil (S.orderedKeys_rule5Readings_ne_nil i)
  obtain ⟨v, tailV, hv⟩ := List.exists_cons_of_ne_nil (S.orderedKeys_rule5Readings_ne_nil j)
  rw [hu, hv] at readingsTie
  have headEq := compareLocalizedRerootCompoundRule5Readings_heads_descriptor_eq input.certified .R
    u v tailU tailV readingsTie
  simp only [localizedRerootRule5Descriptor] at headEq
  have memU : u ∈ (S.frameKey i).rule5Readings :=
    input.certified.mem_of_mem_rankRule5Readings (by rw [show input.certified.rankRule5Readings
      (S.frameKey i).rule5Readings = u :: tailU from hu]; exact List.mem_cons_self)
  have memV : v ∈ (S.frameKey j).rule5Readings :=
    input.certified.mem_of_mem_rankRule5Readings (by rw [show input.certified.rankRule5Readings
      (S.frameKey j).rule5Readings = v :: tailV from hv]; exact List.mem_cons_self)
  exact distinct (S.alpha i) (S.alpha j) (fun h => hij (S.alpha.injective h))
    (S.properTransport_of_commonR_eq hij memU memV rule4aTie headEq)

/-- The head reference of an ordered Rule-5 list at a distinct prior-tied pair. -/
theorem orderedPriorTie_head_refs {i j : Fin 4} (hij : i ≠ j)
    (tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) i j)
    {u : input.certified.LocalizedRerootRule5Reading} {tailU}
    (hu : (orderedKeys input.certified S.frameKey i).rule5Readings = u :: tailU)
    {v : input.certified.LocalizedRerootRule5Reading} {tailV}
    (hv : (orderedKeys input.certified S.frameKey j).rule5Readings = v :: tailV) :
    ∃ ρ₁ ρ₂ : RS, u.prior.reference? = some ρ₁ ∧ v.prior.reference? = some ρ₂ ∧ ρ₁ ≠ ρ₂ ∧
      MirrorTransport input.certified.detectedMultiCenterMolecule S.cfg S.c (S.alpha i) (S.alpha j) := by
  obtain ⟨_, _, matched⟩ := input.certified.orderedPriorTie_matched _ _ tie
    (S.frameKey_readings i).1 (S.frameKey_readings j).1
  have matched' : List.Forall₂ (fun u v : input.certified.LocalizedRerootRule5Reading =>
      input.certified.compareRule4bcReadingsComplete u.prior v.prior = .eq)
      (orderedKeys input.certified S.frameKey i).rule5Readings
      (orderedKeys input.certified S.frameKey j).rule5Readings := matched
  rw [hu, hv] at matched'
  obtain ⟨ρ₁, ρ₂, hρ₁, hρ₂, hne, _, transport⟩ := S.matched_classification distinct hij tie
    (input.certified.mem_of_mem_rankRule5Readings (by
      rw [show input.certified.rankRule5Readings (S.frameKey i).rule5Readings = u :: tailU from hu]
      exact List.mem_cons_self))
    (input.certified.mem_of_mem_rankRule5Readings (by
      rw [show input.certified.rankRule5Readings (S.frameKey j).rule5Readings = v :: tailV from hv]
      exact List.mem_cons_self))
    (List.forall₂_cons.1 matched').1
  exact ⟨ρ₁, ρ₂, hρ₁, hρ₂, hne, transport⟩

/-- **Prior-tie classes of the ordered keys have at most two members.** -/
theorem orderedKeys_priorTieClassAtMostTwo :
    input.certified.PriorTieClassAtMostTwo (orderedKeys input.certified S.frameKey) := by
  intro i j k tij tik
  by_contra hcon
  push_neg at hcon
  obtain ⟨hjk, hji, hki⟩ := hcon
  haveI : Std.TransCmp input.certified.compareLocalizedRerootCompoundRule4bcKeys :=
    input.certified.compareLocalizedRerootCompoundRule4bcKeys_transCmp
  have tjk : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) j k := by
    unfold priorKeyTie at tij tik ⊢
    exact Std.TransCmp.eq_trans (Std.OrientedCmp.eq_symm tij) tik
  obtain ⟨ui, tailI, hui⟩ := List.exists_cons_of_ne_nil (S.orderedKeys_rule5Readings_ne_nil i)
  obtain ⟨uj, tailJ, huj⟩ := List.exists_cons_of_ne_nil (S.orderedKeys_rule5Readings_ne_nil j)
  obtain ⟨uk, tailK, huk⟩ := List.exists_cons_of_ne_nil (S.orderedKeys_rule5Readings_ne_nil k)
  obtain ⟨ρi, ρj, hρi, hρj, hij', _⟩ :=
    S.orderedPriorTie_head_refs distinct (Ne.symm hji) tij hui huj
  obtain ⟨ρi', ρk, hρi', hρk, hik', _⟩ :=
    S.orderedPriorTie_head_refs distinct (Ne.symm hki) tik hui huk
  obtain ⟨ρj', ρk', hρj', hρk', hjk', _⟩ :=
    S.orderedPriorTie_head_refs distinct hjk tjk huj huk
  rw [hρi] at hρi'
  rw [hρj] at hρj'
  rw [hρk] at hρk'
  cases hρi'
  cases hρj'
  cases hρk'
  cases ρi <;> cases ρj <;> cases ρk <;> simp_all

/-- **Every distinct ordered-prior-tied pair is a physical enantiomorphic pair.** -/
theorem enantiomorphic_of_orderedPriorTie {i j : Fin 4}
    (tie : compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey) i j) :
    Enantiomorphic input.certified.detectedMultiCenterMolecule S.cfg S.c (S.alpha i) (S.alpha j) := by
  obtain ⟨hij, tie⟩ := tie
  obtain ⟨u, tailU, hu⟩ := List.exists_cons_of_ne_nil (S.orderedKeys_rule5Readings_ne_nil i)
  obtain ⟨v, tailV, hv⟩ := List.exists_cons_of_ne_nil (S.orderedKeys_rule5Readings_ne_nil j)
  obtain ⟨_, _, _, _, _, transport⟩ := S.orderedPriorTie_head_refs distinct hij tie hu hv
  exact ⟨fun h => hij (S.alpha.injective h), transport,
    distinct (S.alpha i) (S.alpha j) (fun h => hij (S.alpha.injective h))⟩

/-! ## The ordered Rule-5 root theorem -/

omit distinct in
/-- The real centre node at the final occurrence. -/
theorem centerReal : input.certified.RealTetrahedralCenterNode S.top.1.node ⟨S.c.1, S.c.2⟩ :=
  ⟨input.certified.carrierOccurrence_provenance_real S.singleBonded S.acyclic S.top,
    ActualReaderPhysicalBranchInverse.topTarget_current input S.c⟩

omit distinct in
/-- Actual nondegenerate coordinates at the frame slots from the canonical root coordinates. -/
theorem exists_frame_coordinates
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨S.c.1, S.c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ pointsAt : Fin 4 → CartesianPoint3,
      (∀ index : Fin 4,
        input.certified.localizedRerootCursorSpatialPoint? (S.frame.cursorAt index) =
          some (pointsAt index)) ∧
      CartesianPoint3.orientedVolume (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0 :=
  input.certified.actualFrameSpatialCoordinates_of_realNode S.top
    (input.certified.actualFrameRealNodeCoordinates_of_actualCanonicalRootCoordinates S.top
      S.singleBonded S.acyclic (globalCarrierFuel_adequate input) ⟨S.c.1, S.c.2⟩
      (ActualReaderPhysicalBranchInverse.topTarget_current input S.c) coordinates)
    S.frame S.frameComputed

/-- **The ordered Rule-5 root theorem.**  In the physical centre setup, under pairwise
proper-distinguishability of the four ligand branches and nondegenerate canonical root
coordinates, the ordered evaluator's own fixed point at the final occurrence is the pseudo-aware
classification of the oriented-volume reading of the actual slot coordinates in the sorted order;
it is lowercase exactly when the number of distinct ordered-prior-tied slot pairs is one, and
every such pair is a physical enantiomorphic pair.  No reference-count hypothesis is used. -/
theorem orderedReferenceState_top_eq_classify
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨S.c.1, S.c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ (tracked : TrackedLocalizedLigandOrder) (normalizedRS : RS)
      (pointsAt : Fin 4 → CartesianPoint3),
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input) S.top =
        some (classifyTetrahedralRSPseudo normalizedRS
          (sourceEnantiomorphicPairCount
            (compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey)))) ∧
      (∀ index : Fin 4,
        input.certified.localizedRerootCursorSpatialPoint? (S.frame.cursorAt index) =
          some (pointsAt index)) ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      SortedByRank (input.certified.compoundKeyRank (orderedKeys input.certified S.frameKey))
        tracked.highestFirst.reverse ∧
      RationalTetrahedralDescriptor (tracked.highestFirst.map pointsAt) normalizedRS ∧
      ((classifyTetrahedralRSPseudo normalizedRS
          (sourceEnantiomorphicPairCount
            (compoundPriorTieRelation input.certified
              (orderedKeys input.certified S.frameKey)))).IsLowercase ↔
        sourceEnantiomorphicPairCount
          (compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey)) = 1) ∧
      ∀ i j : Fin 4,
        compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey) i j →
          Enantiomorphic input.certified.detectedMultiCenterMolecule S.cfg S.c (S.alpha i) (S.alpha j) := by
  obtain ⟨pointsAt, spatial, nonzero⟩ := S.exists_frame_coordinates coordinates
  obtain ⟨tracked, normalizedRS, _, descriptorEq, perm, sorted, rational⟩ :=
    localizedOccurrenceRule45DescriptorOrdered?_eq_classify_of_actualGeometry S.frameComputed
      S.slotKeysBuilt (S.orderedKeys_offDiagonalStrict distinct)
      (S.orderedKeys_priorTieClassAtMostTwo distinct)
      (S.orderedKeys_priorTieMirrorReadings distinct) ⟨S.c.1, S.c.2⟩ S.centerReal pointsAt
      spatial nonzero
  refine ⟨tracked, normalizedRS, pointsAt, ?_, spatial, perm, sorted, rational,
    isLowercase_classify_iff _ _, fun i j tie => S.enantiomorphic_of_orderedPriorTie distinct tie⟩
  rw [S.orderedReferenceState_top_eq_orderedDescriptor]
  exact descriptorEq

/-! ## The sorted order refines the independent keys -/

/-- Two ligands with different independent keys are ranked by their independent keys. -/
theorem rank_lt_iff_of_independentKey_ne {ℓ m : Fin 4}
    (hne : S.independentKey ℓ ≠ S.independentKey m) :
    input.certified.compoundKeyRank (orderedKeys input.certified S.frameKey) (S.slot ℓ) <
        input.certified.compoundKeyRank (orderedKeys input.certified S.frameKey) (S.slot m) ↔
      S.independentKey ℓ < S.independentKey m := by
  have h := input.certified.compoundKeyComparison_eq_compare_rank
    (orderedKeys input.certified S.frameKey) (S.orderedKeys_offDiagonalStrict distinct)
    (S.slot ℓ) (S.slot m)
  have hcmp : compoundKeyComparison input.certified (orderedKeys input.certified S.frameKey)
      (S.slot ℓ) (S.slot m) = S.independentCompare ℓ m := by
    have hne' : S.independentCompare ℓ m ≠ .eq :=
      fun e => hne ((S.independentCompare_eq_eq_iff ℓ m).1 e)
    have record := S.orderedRootComparison_of_independent_ne hne'
    unfold orderedRootComparison at record
    show input.certified.compareLocalizedRerootCompoundRule45Keys
      (input.certified.outcomeOrdered45 (S.frameKey (S.slot ℓ)))
      (input.certified.outcomeOrdered45 (S.frameKey (S.slot m))) = _
    rw [← input.certified.compareLocalizedRerootCompoundThroughRule5_ordering,
      ← S.slotKey_eq_frameKey, ← S.slotKey_eq_frameKey, record]
  rw [← compare_lt_iff_lt, ← h, hcmp, S.independentCompare_eq_lt_iff]

/-- **The sorted order refines the independent priority.**  Read back on ligands, a rank-sorted
slot list is descending in the independent keys wherever these differ; only pairs with equal
independent keys (the Rule-5 pairs) are ordered by Rule 5. -/
theorem highestFirst_pairwise_independentKey (tracked : TrackedLocalizedLigandOrder)
    (sorted : SortedByRank (input.certified.compoundKeyRank (orderedKeys input.certified S.frameKey))
      tracked.highestFirst.reverse) :
    (tracked.highestFirst.map S.slotEquiv.symm).Pairwise fun ℓ m =>
      S.independentKey ℓ ≠ S.independentKey m → S.independentKey m < S.independentKey ℓ := by
  rw [List.pairwise_map]
  refine (List.pairwise_reverse.mp sorted).imp ?_
  intro a b hab hne
  rw [← S.rank_lt_iff_of_independentKey_ne distinct hne.symm]
  simpa [S.slot_slotEquiv_symm] using hab

end Distinct

end ActualCentrePhysicalSetup
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.properTransport_of_commonR_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.mirrorTransport_of_cross
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedKeys_offDiagonalStrict
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedKeys_priorTieClassAtMostTwo
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedKeys_priorTieMirrorReadings
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.enantiomorphic_of_orderedPriorTie
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedReferenceState_top_eq_classify
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.highestFirst_pairwise_independentKey
