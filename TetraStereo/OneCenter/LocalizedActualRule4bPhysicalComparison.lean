import TetraStereo.OneCenter.LocalizedActualRule4bPhysicalSlotArms
import TetraStereo.OneCenter.DeclarativeCIPLigandSignatureLayout
import TetraStereo.OneCenter.LocalizedPhysicalRule4aPrefixPreservation
import TetraStereo.OneCenter.LocalizedRerootCompoundRule4bcOutcomeOrder
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.OneCenter.LocalizedCumulativeConstitutionalCoherence
import TetraStereo.OneCenter.OfficialRuleMajorCompilerProjectionFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000






























namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open DeclarativeCIP
open Certificate.CanonicalSphereKey (Key)

noncomputable section
open scoped Classical

/-! ## List algebra -/

section Lists

variable {R K : Type*}

theorem compareLex_map_eq (cmp : R → R → Ordering) (kcmp : K → K → Ordering) (f₁ f₂ : R → K) :
    ∀ (l₁ l₂ : List R), (∀ x ∈ l₁, ∀ y ∈ l₂, cmp x y = kcmp (f₁ x) (f₂ y)) →
      List.compareLex cmp l₁ l₂ = List.compareLex kcmp (l₁.map f₁) (l₂.map f₂)
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | a :: l₁, b :: l₂, h => by
      simp only [List.map_cons, List.compareLex_cons_cons]
      rw [h a (by simp) b (by simp),
        compareLex_map_eq cmp kcmp f₁ f₂ l₁ l₂ fun x hx y hy =>
          h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)]

theorem then_congr {o x y : Ordering} (h : o = .eq → x = y) : o.then x = o.then y := by
  cases o with
  | lt => rfl
  | gt => rfl
  | eq => exact h rfl

end Lists

/-! ## The signature by selection -/

/-- The signature determined by a selection and a reading function. -/
def signatureOf (sel : ReferenceSelection) (f : DescriptorSense → Key StereoLabel) :
    ℕ × List (Key StereoLabel) :=
  match sel with
  | .empty => (0, [])
  | .one reference => (2, [f reference])
  | .both => (1, descendingPair (f .senior) (f .junior))

theorem ligandSignatureAt_eq_signatureOf {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom) (W D : ℕ) :
    ligandSignatureAt molecule descriptorMap unit graph W D =
      signatureOf (referenceSelection molecule descriptorMap unit graph)
        (readingAt molecule descriptorMap unit graph W D) := by
  unfold ligandSignatureAt signatureOf
  cases referenceSelection molecule descriptorMap unit graph <;> rfl

theorem signatureOf_fst (sel : ReferenceSelection) (f : DescriptorSense → Key StereoLabel) :
    (signatureOf sel f).1 = constitutionalRule4bReferenceCountPriority (toReferenceList sel) := by
  cases sel with
  | empty => rfl
  | one sense => cases sense <;> rfl
  | both => rfl

/-! ## Outcome order of two alternatives against the key comparator -/

section Rank

variable {input : CertifiedLocalizedCIPInput}

theorem rankReadings_pair_map (a b : input.LocalizedRerootRule4bcReading)
    (f : input.LocalizedRerootRule4bcReading → Key StereoLabel)
    (h : input.compareLocalizedRerootRule4bcReadingsByRule4b a b = compare (f a) (f b)) :
    (input.rankReadings [a, b]).map f = descendingPair (f a) (f b) := by
  simp only [rankReadings, descendingPair]
  by_cases hord : input.compareRule4bcReadingsComplete a b = .lt
  · rw [if_pos hord]
    have hne : input.compareLocalizedRerootRule4bcReadingsByRule4b a b ≠ .gt := by
      intro hgt
      unfold compareRule4bcReadingsComplete compareLex at hord
      rw [hgt] at hord
      simp [Ordering.then] at hord
    rw [h] at hne
    by_cases hk : compare (f a) (f b) = .lt
    · rw [if_pos hk]; rfl
    · rw [if_neg hk]
      have heq : compare (f a) (f b) = .eq := by
        cases hc : compare (f a) (f b)
        · exact absurd hc hk
        · rfl
        · exact absurd hc hne
      rw [key_compare_eq_iff] at heq
      simp [heq]
  · rw [if_neg hord]
    by_cases hk : compare (f a) (f b) = .lt
    · exfalso
      apply hord
      unfold compareRule4bcReadingsComplete compareLex
      rw [h, hk]
      rfl
    · rw [if_neg hk]; rfl

theorem mem_rankReadings_pair {a b x : input.LocalizedRerootRule4bcReading}
    (hx : x ∈ input.rankReadings [a, b]) : x = a ∨ x = b := by
  simp only [rankReadings] at hx
  split_ifs at hx with hord <;> simp at hx <;> tauto

theorem rankReadings_single (a : input.LocalizedRerootRule4bcReading) :
    input.rankReadings [a] = [a] := rfl

end Rank

/-! ## Physical tie facts -/

namespace ActualCentrePhysicalSetup

variable {input : LocalizedUniversalReference.Input} (S : ActualCentrePhysicalSetup input)



theorem scalar4a_arm_eq {index : Fin 4} {ρ : RS}
    (arm : input.certified.OriginalRootArm S.center index (.rule4b ρ) S.read) :
    scalar4a arm.key = projectCumulative 0 (S.slotKey index).prior.rule4aKey.descriptor := by
  have h := actualPhysical_rule4b_first_column (S.slotSetup index) ρ _ _ _ _
    (S.slotSetup index).rule4aBuilt (S.arm_production_built arm)
  show scalar4a arm.key = projectCumulative 0 (S.slotSetup index).key.prior.rule4aKey.descriptor
  rw [← h]
  unfold scalar4a
  exact (projectCumulative_zero _).symm

/-- Every arm of a ligand shares the constitutional observable of the slot's Rule-4a key. -/
theorem constitutionalObservable_arm_eq {index : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    (arm : input.certified.OriginalRootArm S.center index stage S.read) :
    constitutionalObservable arm.key.constitutional =
      constitutionalObservable (S.slotKey index).prior.rule4aKey.constitutional :=
  input.certified.cumulative_builds_constitutional_observable_equal
    (S.frame.cursorAt (S.slot index)) (S.arm_production_built arm) (S.slotSetup index).rule4aBuilt

theorem observable_eq_of_tie {i j : Fin 4}
    (tie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.slotKey i).prior.rule4aKey (S.slotKey j).prior.rule4aKey = .eq) :
    input.certified.localizedRerootCumulativeRule45Observable (S.slotKey i).prior.rule4aKey =
      input.certified.localizedRerootCumulativeRule45Observable (S.slotKey j).prior.rule4aKey :=
  (input.certified.compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq _ _).1 tie

/-- C3's Rule-1a condition for two stage-`.rule4b` arms of slots with equal Rule-4a observables. -/
theorem tied1a_of_observable {i j : Fin 4} {ρ σ : RS}
    (armI : input.certified.OriginalRootArm S.center i (.rule4b ρ) S.read)
    (armJ : input.certified.OriginalRootArm S.center j (.rule4b σ) S.read)
    (hobs : input.certified.localizedRerootCumulativeRule45Observable (S.slotKey i).prior.rule4aKey =
      input.certified.localizedRerootCumulativeRule45Observable (S.slotKey j).prior.rule4aKey) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armI.key.constitutional.rule1a armJ.key.constitutional.rule1a = .eq := by
  have hI := congrArg LocalizedConstitutionalObservable.rule1a (S.constitutionalObservable_arm_eq armI)
  have hJ := congrArg LocalizedConstitutionalObservable.rule1a (S.constitutionalObservable_arm_eq armJ)
  have hij := congrArg LocalizedCumulativeRule45Observable.rule1a hobs
  simp only [constitutionalObservable] at hI hJ
  simp only [localizedRerootCumulativeRule45Observable] at hij
  rw [hI, hJ, hij]
  exact CompilerProjectionFidelity.compareSparseLayers_self _
    CompilerProjectionFidelity.compareNat_self _

/-- C3's Rule-4a condition for two stage-`.rule4b` arms of slots with equal Rule-4a observables. -/
theorem tied4a_of_observable {i j : Fin 4} {ρ σ : RS}
    (armI : input.certified.OriginalRootArm S.center i (.rule4b ρ) S.read)
    (armJ : input.certified.OriginalRootArm S.center j (.rule4b σ) S.read)
    (hobs : input.certified.localizedRerootCumulativeRule45Observable (S.slotKey i).prior.rule4aKey =
      input.certified.localizedRerootCumulativeRule45Observable (S.slotKey j).prior.rule4aKey) :
    scalar4a armI.key = scalar4a armJ.key := by
  have hij := congrArg LocalizedCumulativeRule45Observable.descriptor hobs
  simp only [localizedRerootCumulativeRule45Observable] at hij
  rw [S.scalar4a_arm_eq armI, S.scalar4a_arm_eq armJ, hij]

/-- The independent reading of ligand `index` at layout `(W, D)`, on the Rule-4a arm's graph. -/
abbrev readingOf {index : Fin 4}
    (arm4a : input.certified.OriginalRootArm S.center index .rule4a S.read) (W D : ℕ)
    (reference : DescriptorSense) : Key StereoLabel :=
  readingAt input.certified.moleculeGraph (actualReferenceDescriptorMap input)
    (input.certified.topUnit S.center) (armGraph arm4a) W D reference

/-- **C3 on the physical domain.**  Two readings of slots with equal Rule-4a observables compare
by Rule 4b as the independent readings of their ligands, each read on its Rule-4a arm's graph. -/
theorem cmp4b_eq {i j : Fin 4} {ρ σ : RS}
    (arm4aI : input.certified.OriginalRootArm S.center i .rule4a S.read)
    (arm4aJ : input.certified.OriginalRootArm S.center j .rule4a S.read)
    (armI : input.certified.OriginalRootArm S.center i (.rule4b ρ) S.read)
    (armJ : input.certified.OriginalRootArm S.center j (.rule4b σ) S.read)
    (hobs : input.certified.localizedRerootCumulativeRule45Observable (S.slotKey i).prior.rule4aKey =
      input.certified.localizedRerootCumulativeRule45Observable (S.slotKey j).prior.rule4aKey)
    {W D : ℕ} (hWi : (armGraph arm4aI).width ≤ W) (hDi : (armGraph arm4aI).height ≤ D)
    (hWj : (armGraph arm4aJ).width ≤ W) (hDj : (armGraph arm4aJ).height ≤ D)
    (rI rJ : input.certified.LocalizedRerootRule4bcReading)
    (hI : rI.rule4bKey = armI.key) (hJ : rJ.rule4bKey = armJ.key) :
    input.certified.compareLocalizedRerootRule4bcReadingsByRule4b rI rJ =
      compare (S.readingOf arm4aI W D (senseOf ρ)) (S.readingOf arm4aJ W D (senseOf σ)) := by
  have hWi' : (armGraph armI).width ≤ W := by
    rw [width_eq_of_faithful input.certified.moleculeGraph S.center.1 _ armI.faithful arm4aI.faithful]
    exact hWi
  have hDi' : (armGraph armI).height ≤ D := by
    rw [height_eq_of_faithful input.certified.moleculeGraph S.center.1 _ armI.faithful arm4aI.faithful]
    exact hDi
  have hWj' : (armGraph armJ).width ≤ W := by
    rw [width_eq_of_faithful input.certified.moleculeGraph S.center.1 _ armJ.faithful arm4aJ.faithful]
    exact hWj
  have hDj' : (armGraph armJ).height ≤ D := by
    rw [height_eq_of_faithful input.certified.moleculeGraph S.center.1 _ armJ.faithful arm4aJ.faithful]
    exact hDj
  rw [compareReadingsByRule4b_eq_compare_rule4bComponent armI armJ (S.armReadback4b armI)
    (S.armReadback4b armJ) rI rJ hI hJ hWi' hDi' hWj' hDj' (S.tied1a_of_observable armI armJ hobs)
    (S.tied4a_of_observable armI armJ hobs)]
  have eI : rule4bComponent input.certified.moleculeGraph (armGraph armI)
      (readingEvidence input.certified.moleculeGraph (actualReferenceDescriptorMap input)
        (input.certified.topUnit S.center) (armGraph armI) (senseOf ρ)) W D (armGraph armI).root =
      readingAt input.certified.moleculeGraph (actualReferenceDescriptorMap input)
        (input.certified.topUnit S.center) (armGraph armI) W D (senseOf ρ) := rfl
  have eJ : rule4bComponent input.certified.moleculeGraph (armGraph armJ)
      (readingEvidence input.certified.moleculeGraph (actualReferenceDescriptorMap input)
        (input.certified.topUnit S.center) (armGraph armJ) (senseOf σ)) W D (armGraph armJ).root =
      readingAt input.certified.moleculeGraph (actualReferenceDescriptorMap input)
        (input.certified.topUnit S.center) (armGraph armJ) W D (senseOf σ) := rfl
  rw [eI, eJ,
    readingAt_eq_of_faithful input.certified.moleculeGraph (actualReferenceDescriptorMap input)
      (input.certified.topUnit S.center) S.center.1 _ armI.faithful arm4aI.faithful W D (senseOf ρ),
    readingAt_eq_of_faithful input.certified.moleculeGraph (actualReferenceDescriptorMap input)
      (input.certified.topUnit S.center) S.center.1 _ armJ.faithful arm4aJ.faithful W D (senseOf σ)]

/-- The no-reference readings of two tied slots compare equal (their Rule-4b keys are the tied
Rule-4a keys). -/
theorem cmp4b_none_eq {i j : Fin 4}
    (arm4aI : input.certified.OriginalRootArm S.center i .rule4a S.read)
    (arm4aJ : input.certified.OriginalRootArm S.center j .rule4a S.read)
    (hobs : input.certified.localizedRerootCumulativeRule45Observable (S.slotKey i).prior.rule4aKey =
      input.certified.localizedRerootCumulativeRule45Observable (S.slotKey j).prior.rule4aKey)
    (rI rJ : input.certified.LocalizedRerootRule4bcReading)
    (hI : rI.rule4bKey = arm4aI.key) (hJ : rJ.rule4bKey = arm4aJ.key) :
    input.certified.compareLocalizedRerootRule4bcReadingsByRule4b rI rJ = .eq := by
  have hij := congrArg LocalizedCumulativeRule45Observable.descriptor hobs
  simp only [localizedRerootCumulativeRule45Observable] at hij
  unfold compareLocalizedRerootRule4bcReadingsByRule4b
  simp only [Ordering.byKey]
  rw [hI, hJ, ← S.rule4aKey_eq arm4aI, ← S.rule4aKey_eq arm4aJ, hij]
  exact CompilerProjectionFidelity.compareSparseLayers_self _
    (CompilerProjectionFidelity.list_compareLex_self _ CompilerProjectionFidelity.compareNat_self) _

/-- The reading function of a ligand on its own readings: the sense named by the reading's
reference. -/
def readingFun {index : Fin 4}
    (arm4a : input.certified.OriginalRootArm S.center index .rule4a S.read) (W D : ℕ)
    (reading : input.certified.LocalizedRerootRule4bcReading) : Key StereoLabel :=
  if reading.reference? = some RS.R then S.readingOf arm4a W D .senior
  else S.readingOf arm4a W D .junior

/-! ## C4 -/

/-- **C4.**  After a Rule-4a tie of two slots, the ordered compound comparison through the
Rule-4b readings is the comparison of the independent ligand signatures at any common layout. -/
theorem compound_afterRule4a_eq_signatureCompare {i j : Fin 4}
    (arm4aI : input.certified.OriginalRootArm S.center i .rule4a S.read)
    (arm4aJ : input.certified.OriginalRootArm S.center j .rule4a S.read)
    {W D : ℕ} (hWi : (armGraph arm4aI).width ≤ W) (hDi : (armGraph arm4aI).height ≤ D)
    (hWj : (armGraph arm4aJ).width ≤ W) (hDj : (armGraph arm4aJ).height ≤ D)
    (tie4a : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.slotKey i).prior.rule4aKey (S.slotKey j).prior.rule4aKey = .eq) :
    compareLex (Ordering.byKey (fun key => key.referenceCountPriority) compare)
        (Ordering.byKey (fun key => key.readings)
          input.certified.compareLocalizedRerootCompoundRule4bReadings)
        (input.certified.outcomeOrdered (S.slotKey i).prior)
        (input.certified.outcomeOrdered (S.slotKey j).prior) =
      signatureCompare
        (ligandSignatureAt input.certified.moleculeGraph (actualReferenceDescriptorMap input)
          (input.certified.topUnit S.center) (armGraph arm4aI) W D)
        (ligandSignatureAt input.certified.moleculeGraph (actualReferenceDescriptorMap input)
          (input.certified.topUnit S.center) (armGraph arm4aJ) W D) := by
  obtain ⟨armRI⟩ := input.certified.exists_originalRootArm S.center i (.rule4b .R) S.read
  obtain ⟨armSI⟩ := input.certified.exists_originalRootArm S.center i (.rule4b .S) S.read
  obtain ⟨armRJ⟩ := input.certified.exists_originalRootArm S.center j (.rule4b .R) S.read
  obtain ⟨armSJ⟩ := input.certified.exists_originalRootArm S.center j (.rule4b .S) S.read
  have hobs := S.observable_eq_of_tie tie4a
  have hobsI := S.observable_eq_of_tie (i := i) (j := i)
    ((input.certified.compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq _ _).2 rfl)
  have hobsJ := S.observable_eq_of_tie (i := j) (j := j)
    ((input.certified.compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq _ _).2 rfl)
  have shapeI := S.readings_shape arm4aI armRI armSI
  have shapeJ := S.readings_shape arm4aJ armRJ armSJ
  have countI := S.referenceCountPriority_eq arm4aI
  have countJ := S.referenceCountPriority_eq arm4aJ
  simp only [ActualCentrePhysicalSetup.selection] at shapeI shapeJ countI countJ
  rw [ligandSignatureAt_eq_signatureOf, ligandSignatureAt_eq_signatureOf]
  show (compare (input.certified.outcomeOrdered (S.slotKey i).prior).referenceCountPriority
      (input.certified.outcomeOrdered (S.slotKey j).prior).referenceCountPriority).then
    (List.compareLex input.certified.compareLocalizedRerootRule4bcReadingsByRule4b
      (input.certified.outcomeOrdered (S.slotKey i).prior).readings
      (input.certified.outcomeOrdered (S.slotKey j).prior).readings) = _
  simp only [outcomeOrdered]
  unfold signatureCompare
  rw [countI, countJ, signatureOf_fst, signatureOf_fst]
  apply then_congr
  intro hcount
  have cmpRR := S.cmp4b_eq arm4aI arm4aJ armRI armRJ hobs hWi hDi hWj hDj
  have cmpRS := S.cmp4b_eq arm4aI arm4aJ armRI armSJ hobs hWi hDi hWj hDj
  have cmpSR := S.cmp4b_eq arm4aI arm4aJ armSI armRJ hobs hWi hDi hWj hDj
  have cmpSS := S.cmp4b_eq arm4aI arm4aJ armSI armSJ hobs hWi hDi hWj hDj
  have cmpI := S.cmp4b_eq arm4aI arm4aI armRI armSI hobsI hWi hDi hWi hDi
  have cmpJ := S.cmp4b_eq arm4aJ arm4aJ armRJ armSJ hobsJ hWj hDj hWj hDj
  have cmpNone := S.cmp4b_none_eq arm4aI arm4aJ hobs
  unfold ReadingsShape at shapeI shapeJ
  generalize referenceSelection input.certified.moleculeGraph (actualReferenceDescriptorMap input)
    (input.certified.topUnit S.center) (armGraph arm4aI) = selI at shapeI hcount ⊢
  generalize referenceSelection input.certified.moleculeGraph (actualReferenceDescriptorMap input)
    (input.certified.topUnit S.center) (armGraph arm4aJ) = selJ at shapeJ hcount ⊢
  cases selI with
  | empty =>
      obtain ⟨rI, hrsI, _, hkI⟩ := shapeI
      cases selJ with
      | empty =>
          obtain ⟨rJ, hrsJ, _, hkJ⟩ := shapeJ
          rw [hrsI, hrsJ, rankReadings_single, rankReadings_single]
          simp only [signatureOf, List.compareLex_cons_cons, List.compareLex_nil_nil]
          rw [cmpNone rI rJ hkI hkJ]
          rfl
      | one sense => exact absurd hcount (by cases sense <;> decide)
      | both => exact absurd hcount (by decide)
  | one senseI =>
      cases selJ with
      | empty => exact absurd hcount (by cases senseI <;> decide)
      | both => exact absurd hcount (by cases senseI <;> decide)
      | one senseJ =>
          cases senseI <;> cases senseJ
          all_goals
            obtain ⟨rI, hrsI, _, hkI⟩ := shapeI
            obtain ⟨rJ, hrsJ, _, hkJ⟩ := shapeJ
            rw [hrsI, hrsJ, rankReadings_single, rankReadings_single]
            simp only [signatureOf, List.compareLex_cons_cons, List.compareLex_nil_nil]
          · rw [cmpRR rI rJ hkI hkJ]; rfl
          · rw [cmpRS rI rJ hkI hkJ]; rfl
          · rw [cmpSR rI rJ hkI hkJ]; rfl
          · rw [cmpSS rI rJ hkI hkJ]; rfl
  | both =>
      obtain ⟨rRI, rSI, hrsI, hrefRI, hrefSI, hkRI, hkSI⟩ := shapeI
      cases selJ with
      | empty => exact absurd hcount (by decide)
      | one sense => exact absurd hcount (by cases sense <;> decide)
      | both =>
          obtain ⟨rRJ, rSJ, hrsJ, hrefRJ, hrefSJ, hkRJ, hkSJ⟩ := shapeJ
          rw [hrsI, hrsJ]
          simp only [signatureOf]
          have fRI : S.readingFun arm4aI W D rRI = S.readingOf arm4aI W D .senior := by
            simp [readingFun, hrefRI]
          have fSI : S.readingFun arm4aI W D rSI = S.readingOf arm4aI W D .junior := by
            simp [readingFun, hrefSI]
          have fRJ : S.readingFun arm4aJ W D rRJ = S.readingOf arm4aJ W D .senior := by
            simp [readingFun, hrefRJ]
          have fSJ : S.readingFun arm4aJ W D rSJ = S.readingOf arm4aJ W D .junior := by
            simp [readingFun, hrefSJ]
          have mapI := rankReadings_pair_map rRI rSI (S.readingFun arm4aI W D)
            (by rw [fRI, fSI]; exact cmpI rRI rSI hkRI hkSI)
          have mapJ := rankReadings_pair_map rRJ rSJ (S.readingFun arm4aJ W D)
            (by rw [fRJ, fSJ]; exact cmpJ rRJ rSJ hkRJ hkSJ)
          rw [fRI, fSI] at mapI
          rw [fRJ, fSJ] at mapJ
          rw [← mapI, ← mapJ]
          apply compareLex_map_eq
          intro x hx y hy
          rcases mem_rankReadings_pair hx with rfl | rfl <;>
            rcases mem_rankReadings_pair hy with rfl | rfl
          · rw [fRI, fRJ]; exact cmpRR _ _ hkRI hkRJ
          · rw [fRI, fSJ]; exact cmpRS _ _ hkRI hkSJ
          · rw [fSI, fRJ]; exact cmpSR _ _ hkSI hkRJ
          · rw [fSI, fSJ]; exact cmpSS _ _ hkSI hkSJ

/-- **Consequence for the full ordered comparator.**  After a Rule-4a tie, whenever the
independent signature comparison is decisive, the ordered compound Rules-4b/4c comparison returns
exactly it. -/
theorem compound_eq_signatureCompare_of_ne {i j : Fin 4}
    (arm4aI : input.certified.OriginalRootArm S.center i .rule4a S.read)
    (arm4aJ : input.certified.OriginalRootArm S.center j .rule4a S.read)
    {W D : ℕ} (hWi : (armGraph arm4aI).width ≤ W) (hDi : (armGraph arm4aI).height ≤ D)
    (hWj : (armGraph arm4aJ).width ≤ W) (hDj : (armGraph arm4aJ).height ≤ D)
    (tie4a : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.slotKey i).prior.rule4aKey (S.slotKey j).prior.rule4aKey = .eq)
    (decisive : signatureCompare
        (ligandSignatureAt input.certified.moleculeGraph (actualReferenceDescriptorMap input)
          (input.certified.topUnit S.center) (armGraph arm4aI) W D)
        (ligandSignatureAt input.certified.moleculeGraph (actualReferenceDescriptorMap input)
          (input.certified.topUnit S.center) (armGraph arm4aJ) W D) ≠ .eq) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
        (input.certified.outcomeOrdered (S.slotKey i).prior)
        (input.certified.outcomeOrdered (S.slotKey j).prior) =
      signatureCompare
        (ligandSignatureAt input.certified.moleculeGraph (actualReferenceDescriptorMap input)
          (input.certified.topUnit S.center) (armGraph arm4aI) W D)
        (ligandSignatureAt input.certified.moleculeGraph (actualReferenceDescriptorMap input)
          (input.certified.topUnit S.center) (armGraph arm4aJ) W D) := by
  have main := S.compound_afterRule4a_eq_signatureCompare arm4aI arm4aJ hWi hDi hWj hDj tie4a
  rw [← main] at decisive ⊢
  rw [input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_afterRule4a_of_tie
    (input.certified.outcomeOrdered (S.slotKey i).prior)
    (input.certified.outcomeOrdered (S.slotKey j).prior) tie4a]
  have decisive' : (compare (S.slotKey i).prior.referenceCountPriority
        (S.slotKey j).prior.referenceCountPriority).then
      (input.certified.compareLocalizedRerootCompoundRule4bReadings
        (input.certified.rankReadings (S.slotKey i).prior.readings)
        (input.certified.rankReadings (S.slotKey j).prior.readings)) ≠ .eq := decisive
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
  intro hc
  rw [hc] at decisive'
  have decisive'' : input.certified.compareLocalizedRerootCompoundRule4bReadings
      (input.certified.rankReadings (S.slotKey i).prior.readings)
      (input.certified.rankReadings (S.slotKey j).prior.readings) ≠ .eq := decisive'
  generalize input.certified.compareLocalizedRerootCompoundRule4bReadings
    (input.certified.rankReadings (S.slotKey i).prior.readings)
    (input.certified.rankReadings (S.slotKey j).prior.readings) = d at decisive'' ⊢
  cases d with
  | lt => rfl
  | gt => rfl
  | eq => exact absurd rfl decisive''

end ActualCentrePhysicalSetup

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.rankReadings_pair_map
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.scalar4a_arm_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.cmp4b_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.compound_afterRule4a_eq_signatureCompare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.compound_eq_signatureCompare_of_ne
