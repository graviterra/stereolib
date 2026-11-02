import TetraStereo.OneCenter.LocalizedActualLigandRootSlotCursor
import TetraStereo.OneCenter.LocalizedActualRule4bPhysicalReadback
import TetraStereo.OneCenter.LocalizedActualReferenceSelectionBridge
import TetraStereo.OneCenter.LocalizedPhysicalStageExtensionClosure
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The production slot keys of a detected centre are the arm keys

For a detected centre in the physical domain (`ActualCentrePhysicalSetup`: the data of
`ActualSlotPhysicalSetup` without a slot, plus the tetrahedral centre it is), every ligand index
has a slot setup `slotSetup index` at the frame slot carrying the ligand-root cursor
(`LocalizedActualLigandRootSlotCursor`).  The production compound Rules-4b/4c key of that slot
(`slotKey index`, the `prior` of `actualSlotCompoundKey`) is identified with the original-root arm
packages of the ligand at the actual molecular reader:

* `rule4aKey_eq` — its Rule-4a key is the stage-`.rule4a` arm's key;
* `references_eq` — its reference list is the independently specified selection (B7);
* `referenceCountPriority_eq` — its count priority is the criterion-(c)(i) count of that selection;
* `readings_shape` — its readings are, per the selection, the single no-reference reading (whose
  Rule-4b key is the Rule-4a key), the single `R`- or `S`-reading, or the pair `[R, S]`, with each
  reading's Rule-4b key equal to the stage-`.rule4b ρ` arm's key.

Everything is an equation between two outputs of the production builders at the same cursor and
fuel: the arm's `WithRead?` build at the molecular reader equals the production `?` build at the
final target through the reader equivalence (`actualReference_molecularReader`,
`buildWithRead_dependencyReader_eq_build`).  Nothing about the number of references is assumed.
-/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open DeclarativeCIP

noncomputable section
open scoped Classical

/-! ## Builder unfolding -/

section Builders

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
  (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)

theorem reading_none_built {r : input.LocalizedRerootRule4bcReading}
    (h : input.buildLocalizedRerootRule4bcReading? target view fuel cursor none = some r) :
    input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor =
        some r.rule4bKey ∧
      r.reference? = none := by
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
          exact ⟨rfl, rfl⟩

theorem reading_some_built (ρ : RS) {r : input.LocalizedRerootRule4bcReading}
    (h : input.buildLocalizedRerootRule4bcReading? target view fuel cursor (some ρ) = some r) :
    input.buildLocalizedRerootCumulativeRule45Key? (.rule4b ρ) target view fuel cursor =
        some r.rule4bKey ∧
      input.buildLocalizedRerootCumulativeRule45Key? (.rule4c ρ) target view fuel cursor =
        some r.rule4cKey ∧
      r.reference? = some ρ := by
  unfold buildLocalizedRerootRule4bcReading? at h
  cases h4b : input.buildLocalizedRerootCumulativeRule45Key? (.rule4b ρ) target view fuel
      cursor with
  | none => simp [h4b] at h
  | some k4b =>
      cases h4c : input.buildLocalizedRerootCumulativeRule45Key? (.rule4c ρ) target view fuel
          cursor with
      | none => simp [h4b, h4c] at h
      | some k4c =>
          simp [h4b, h4c] at h
          subst h
          exact ⟨rfl, rfl, rfl⟩

theorem readings_single_built (a : Option RS) {rs : List input.LocalizedRerootRule4bcReading}
    (h : input.buildLocalizedRerootRule4bcReadings? target view fuel cursor [a] = some rs) :
    ∃ r, rs = [r] ∧ input.buildLocalizedRerootRule4bcReading? target view fuel cursor a = some r := by
  unfold buildLocalizedRerootRule4bcReadings? at h
  cases hr : input.buildLocalizedRerootRule4bcReading? target view fuel cursor a with
  | none => simp [hr] at h
  | some r =>
      simp [hr, buildLocalizedRerootRule4bcReadings?] at h
      exact ⟨r, h.symm, rfl⟩

theorem readings_pair_built (a b : Option RS) {rs : List input.LocalizedRerootRule4bcReading}
    (h : input.buildLocalizedRerootRule4bcReadings? target view fuel cursor [a, b] = some rs) :
    ∃ r s, rs = [r, s] ∧
      input.buildLocalizedRerootRule4bcReading? target view fuel cursor a = some r ∧
      input.buildLocalizedRerootRule4bcReading? target view fuel cursor b = some s := by
  unfold buildLocalizedRerootRule4bcReadings? at h
  cases hr : input.buildLocalizedRerootRule4bcReading? target view fuel cursor a with
  | none => simp [hr] at h
  | some r =>
      cases hs : input.buildLocalizedRerootRule4bcReading? target view fuel cursor b with
      | none => simp [hr, hs, buildLocalizedRerootRule4bcReadings?] at h
      | some s =>
          simp [hr, hs, buildLocalizedRerootRule4bcReadings?] at h
          exact ⟨r, s, h.symm, rfl, rfl⟩

/-- The components of a successful compound Rules-4b/4c build. -/
theorem compound_built_components {prior : input.LocalizedRerootCompoundRule4bcKey}
    (h : input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor = some prior) :
    input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor =
        some prior.rule4aKey ∧
      prior.references =
        localizedRule4bReferencesFromRankedLabels prior.rule4aKey.rankedLabels ∧
      prior.referenceCountPriority =
        constitutionalRule4bReferenceCountPriority prior.references ∧
      input.buildLocalizedRerootRule4bcReadings? target view fuel cursor
        (localizedRule4bcReferenceAlternatives prior.references) = some prior.readings := by
  unfold buildLocalizedRerootCompoundRule4bcKey? at h
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel
      cursor with
  | none => simp [rule4aComputed] at h
  | some rule4aKey =>
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadings? target view fuel cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => simp [rule4aComputed, readingsComputed] at h
      | some readings =>
          simp [rule4aComputed, readingsComputed] at h
          subst h
          exact ⟨rfl, rfl, rfl, readingsComputed⟩

end Builders

/-! ## The centre-level physical setup -/

/-- The physical slot data of `ActualSlotPhysicalSetup` without a slot, together with the
tetrahedral centre the detected centre is. -/
structure ActualCentrePhysicalSetup (input : LocalizedUniversalReference.Input) where
  c : input.certified.detectedMultiCenterMolecule.Center
  frame : input.certified.LocalizedOccurrenceFourLigandFrame
    (LocalizedUniversalReference.carrierFuel input)
  frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
    (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame
  singleBonded : input.certified.moleculeGraph.SimpleBonded
  acyclic : input.certified.moleculeGraph.Acyclic
  hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph
  noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords
  cfg : input.certified.detectedMultiCenterMolecule.Configuration
  physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
    input.certified.detectedMultiCenterMolecule cfg c
  center : input.certified.TetrahedralCenter
  hcenter : center.1 = c.1

namespace ActualCentrePhysicalSetup

variable {input : LocalizedUniversalReference.Input} (S : ActualCentrePhysicalSetup input)

/-- The frame slot carrying the ligand-root cursor of `index`. -/
def slot (index : Fin 4) : Fin 4 :=
  ligandSlot input S.c S.frame S.frameComputed S.center S.hcenter index

theorem cursorAt_slot (index : Fin 4) :
    S.frame.cursorAt (S.slot index) = input.certified.localizedLigandRootCursor S.center index :=
  cursorAt_ligandSlot input S.c S.frame S.frameComputed S.center S.hcenter index

theorem slot_injective : Function.Injective S.slot :=
  ligandSlot_injective input S.c S.frame S.frameComputed S.center S.hcenter

theorem slot_bijective : Function.Bijective S.slot :=
  ligandSlot_bijective input S.c S.frame S.frameComputed S.center S.hcenter

/-- The slot setup of ligand `index`. -/
def slotSetup (index : Fin 4) : ActualSlotPhysicalSetup input where
  c := S.c
  frame := S.frame
  frameComputed := S.frameComputed
  slot := S.slot index
  singleBonded := S.singleBonded
  acyclic := S.acyclic
  hcharge := S.hcharge
  noDouble := S.noDouble
  cfg := S.cfg
  physicalDomain := S.physicalDomain
  oAtom := input.certified.canonicalLigandAtom S.center index
  oObserved := by rw [cursorAt_slot]; rfl

/-- The actual molecular reader at the final occurrence of the centre. -/
abbrev read :
    input.certified.LocalizedRerootCursor (input.certified.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel :=
  input.certified.molecularReader (actualReferenceDescriptorMap input)
    (ActualReaderPhysicalBranchInverse.topTarget input S.c)

theorem read_eq : S.read = ActualReaderPhysicalBranchInverse.dependencyReader input S.c :=
  actualReference_molecularReader input S.singleBonded S.acyclic S.noDouble _

/-- The arm builder at the molecular reader is the production builder at the final target. -/
theorem withRead_eq_build (stage : LocalizedCumulativeRule45Stage) (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor (LocalizedUniversalReference.carrierFuel input)) :
    input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stage S.read fuel cursor =
      input.certified.buildLocalizedRerootCumulativeRule45Key? stage
        (ActualReaderPhysicalBranchInverse.topTarget input S.c)
        (referenceDependencyView input S.c) fuel cursor := by
  rw [read_eq]
  exact buildWithRead_dependencyReader_eq_build (S.slotSetup 0) stage fuel cursor

/-- The production compound Rules-4a--5 key of the slot of `index`. -/
def slotKey (index : Fin 4) : input.certified.LocalizedRerootCompoundRule45Key :=
  (S.slotSetup index).key

/-- Every original-root arm at the molecular reader is a production build at the frame slot. -/
theorem arm_production_built {index : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    (arm : input.certified.OriginalRootArm S.center index stage S.read) :
    input.certified.buildLocalizedRerootCumulativeRule45Key? stage
        (ActualReaderPhysicalBranchInverse.topTarget input S.c)
        (referenceDependencyView input S.c)
        (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
        (S.frame.cursorAt (S.slot index)) = some arm.key := by
  rw [S.cursorAt_slot, ← S.withRead_eq_build]
  exact arm.built

/-- `ArmReadback4b` for the stage-`.rule4b ρ` arm of any ligand. -/
theorem armReadback4b {index : Fin 4} {ρ : RS}
    (arm : input.certified.OriginalRootArm S.center index (.rule4b ρ) S.read) :
    ArmReadback4b arm (actualReferenceDescriptorMap input) (input.certified.topUnit S.center) :=
  armReadback4b_of_setup_of_source (S.slotSetup index) S.hcenter.symm arm
    (arm.source.trans (by rw [ActualSlotPhysicalSetup.tree_source]; exact (S.cursorAt_slot index).symm))

theorem prior_built (index : Fin 4) :
    input.certified.buildLocalizedRerootCompoundRule4bcKey?
        (ActualReaderPhysicalBranchInverse.topTarget input S.c)
        (referenceDependencyView input S.c)
        (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
        (S.frame.cursorAt (S.slot index)) = some (S.slotKey index).prior :=
  actualSlotPriorBuilt input S.c S.frame S.frameComputed (S.slot index)

/-- The slot's Rule-4a key is the stage-`.rule4a` arm's key. -/
theorem rule4aKey_eq {index : Fin 4}
    (arm4a : input.certified.OriginalRootArm S.center index .rule4a S.read) :
    (S.slotKey index).prior.rule4aKey = arm4a.key :=
  Option.some.inj ((S.slotSetup index).rule4aBuilt.symm.trans (S.arm_production_built arm4a))

/-- The independent selection of ligand `index`, read on the stage-`.rule4a` arm's graph. -/
abbrev selection {index : Fin 4}
    (arm4a : input.certified.OriginalRootArm S.center index .rule4a S.read) : ReferenceSelection :=
  referenceSelection input.certified.moleculeGraph (actualReferenceDescriptorMap input)
    (input.certified.topUnit S.center) (armGraph arm4a)

/-- The slot's reference list is the independently specified selection (B7). -/
theorem references_eq {index : Fin 4}
    (arm4a : input.certified.OriginalRootArm S.center index .rule4a S.read) :
    (S.slotKey index).prior.references = toReferenceList (S.selection arm4a) := by
  obtain ⟨_, hrefs, _, _⟩ := compound_built_components _ _ _ _ (S.prior_built index)
  rw [hrefs, S.rule4aKey_eq arm4a]
  exact arm_references_eq_referenceSelection_of_treeLike input _
    ((ActualReaderPhysicalBranchInverse.topTarget_root input S.c).trans S.hcenter.symm)
    (ActualReaderPhysicalBranchInverse.topTarget_address input S.c) S.singleBonded S.acyclic arm4a

theorem referenceCountPriority_eq {index : Fin 4}
    (arm4a : input.certified.OriginalRootArm S.center index .rule4a S.read) :
    (S.slotKey index).prior.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority (toReferenceList (S.selection arm4a)) := by
  obtain ⟨_, _, hcount, _⟩ := compound_built_components _ _ _ _ (S.prior_built index)
  rw [hcount, S.references_eq arm4a]

/-- The shape of a slot's readings, per selection: which alternatives occur and which arm key each
Rule-4b reading carries. -/
def ReadingsShape (sel : ReferenceSelection)
    (readings : List input.certified.LocalizedRerootRule4bcReading)
    (key4a keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key) : Prop :=
  match sel with
  | .empty => ∃ r, readings = [r] ∧ r.reference? = none ∧ r.rule4bKey = key4a
  | .one .senior => ∃ r, readings = [r] ∧ r.reference? = some RS.R ∧ r.rule4bKey = keyR
  | .one .junior => ∃ r, readings = [r] ∧ r.reference? = some RS.S ∧ r.rule4bKey = keyS
  | .both => ∃ r s, readings = [r, s] ∧ r.reference? = some RS.R ∧ s.reference? = some RS.S ∧
      r.rule4bKey = keyR ∧ s.rule4bKey = keyS

/-- **The slot's readings are the arm keys.** -/
theorem readings_shape {index : Fin 4}
    (arm4a : input.certified.OriginalRootArm S.center index .rule4a S.read)
    (armR : input.certified.OriginalRootArm S.center index (.rule4b .R) S.read)
    (armS : input.certified.OriginalRootArm S.center index (.rule4b .S) S.read) :
    ReadingsShape (S.selection arm4a) (S.slotKey index).prior.readings arm4a.key armR.key
      armS.key := by
  obtain ⟨_, _, _, hreadings⟩ := compound_built_components _ _ _ _ (S.prior_built index)
  rw [S.references_eq arm4a] at hreadings
  have h4a := S.arm_production_built arm4a
  have hR := S.arm_production_built armR
  have hS := S.arm_production_built armS
  unfold ReadingsShape
  generalize S.selection arm4a = sel at hreadings ⊢
  cases sel with
  | empty =>
      simp only [toReferenceList, localizedRule4bcReferenceAlternatives] at hreadings
      obtain ⟨r, hrs, hr⟩ := readings_single_built _ _ _ _ none hreadings
      obtain ⟨hb, href⟩ := reading_none_built _ _ _ _ hr
      exact ⟨r, hrs, href, Option.some.inj (hb.symm.trans h4a)⟩
  | one sense =>
      cases sense with
      | senior =>
          simp only [toReferenceList, localizedRule4bcReferenceAlternatives, List.map] at hreadings
          obtain ⟨r, hrs, hr⟩ := readings_single_built _ _ _ _ (some RS.R) hreadings
          obtain ⟨hb, _, href⟩ := reading_some_built _ _ _ _ RS.R hr
          exact ⟨r, hrs, href, Option.some.inj (hb.symm.trans hR)⟩
      | junior =>
          simp only [toReferenceList, localizedRule4bcReferenceAlternatives, List.map] at hreadings
          obtain ⟨r, hrs, hr⟩ := readings_single_built _ _ _ _ (some RS.S) hreadings
          obtain ⟨hb, _, href⟩ := reading_some_built _ _ _ _ RS.S hr
          exact ⟨r, hrs, href, Option.some.inj (hb.symm.trans hS)⟩
  | both =>
      simp only [toReferenceList, localizedRule4bcReferenceAlternatives, List.map] at hreadings
      obtain ⟨r, s, hrs, hr, hs⟩ := readings_pair_built _ _ _ _ (some RS.R) (some RS.S) hreadings
      obtain ⟨hbR, _, hrefR⟩ := reading_some_built _ _ _ _ RS.R hr
      obtain ⟨hbS, _, hrefS⟩ := reading_some_built _ _ _ _ RS.S hs
      exact ⟨r, s, hrs, hrefR, hrefS, Option.some.inj (hbR.symm.trans hR),
        Option.some.inj (hbS.symm.trans hS)⟩

end ActualCentrePhysicalSetup

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compound_built_components
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.withRead_eq_build
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.arm_production_built
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.armReadback4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.rule4aKey_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.references_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.referenceCountPriority_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.readings_shape
