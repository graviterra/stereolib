import TetraStereo.OneCenter.LocalizedFullCompoundTieLabelDecoding
import TetraStereo.OneCenter.LocalizedEmptyRule4bReferenceDecoding
import TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Decoding matched actual compound readings at common ranked addresses

The current RuleMajorReference compound at an actual frame slot is assembled from actual
rule-major stage builds, all read with the target's dependency reader
(`buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor`).  Each reading of that compound
(one own Rule-4b alternative with its Rule-4b/4c keys, and its two common-reference Rule-5 keys)
is therefore an actual successful build at the slot cursor.  An actual traced
`RuleMajorContextArm` at the same stage, reader and cursor carries exactly that key
(`arm_key_eq_of_built`), and its trace matches the arm tree's addressed descriptor table to the
key's descriptor column (`arm_descriptor_table`).

Equal descriptor columns of two arm trees agree at every ranked address occupied in both trees,
on the stage priority vectors of the two node labels (`column_eq_at_address`).  The vectors then
decode:

* common-reference Rule-5 vectors are injective for any pair of own references
  (`fullTie_priority_injective`), so matched common readings give equal labels;
* Rule-4b vectors under opposite own references send an uppercase label to its reflection;
* Rule-4b vectors under one own reference keep an uppercase label.

The result is the label correspondence `UppercaseCorrespondence` on the very arm trees whose
constitutional tie produces the witnessed molecular automorphism.  The constitutional tie itself
is never used to read a stereo label.

An empty Rule-4b selection is decoded too: the production selector's own inversion and the arm's
exact label match make the actual Rule-4a arm tree uppercase-free
(`rule4aArm_uppercaseFree_of_references_nil`), so its correspondence holds for either mirror flag.
A no-reference reading never ties a reading with an uppercase own reference
(`rule4b_descriptor_ne_rule4a`).
-/

namespace TetraStereo.OneCenter
namespace LocalizedCyclicMatchedReadingDecode

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree

/-! ## Addressed column agreement -/

/-- Equal addressed tables of two node observations agree at every ranked address occupied in
both trees.  The trees and observations are arbitrary: each child table is recovered from the
merged parent table by `normalizedChildTable_tail_eq_table`. -/
theorem column_eq_at_address {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {α : Type*} (fObs gObs : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (address : List ℕ) :
    ∀ (t1 t2 s1 s2 : LocalizedCumulativeDecoratedTree input carrierFuel),
      table fObs t1 = table gObs t2 →
      t1.decoratedSubtreeAt? address = some s1 →
      t2.decoratedSubtreeAt? address = some s2 →
      fObs s1 = gObs s2 := by
  induction address with
  | nil =>
      intro t1 t2 s1 s2 same h1 h2
      simp only [decoratedSubtreeAt?, Option.some.injEq] at h1 h2
      rw [← h1, ← h2]
      exact table_observe_root_eq fObs gObs t1 t2 same
  | cons slot address ih =>
      intro t1 t2 s1 s2 same h1 h2
      simp only [decoratedSubtreeAt?] at h1 h2
      cases hc1 : t1.children[slot]? with
      | none => simp [hc1] at h1
      | some child1 =>
          cases hc2 : t2.children[slot]? with
          | none => simp [hc2] at h2
          | some child2 =>
              simp only [hc1] at h1
              simp only [hc2] at h2
              have childTables : table fObs child1 = table gObs child2 := by
                rw [← normalizedChildTable_tail_eq_table fObs t1 slot child1 hc1,
                  ← normalizedChildTable_tail_eq_table gObs t2 slot child2 hc2, same]
              exact ih child1 child2 s1 s2 childTables h1 h2

/-! ## Stage priority decoding -/

/-- A Rule-4b priority vector under one own reference, equal to the vector under the opposite own
reference, sends an uppercase label to its reflection. -/
theorem rule4bOpposite_priority_chiral (reference descriptor : RS)
    (label : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority (.rule4b reference) (some (.chiral descriptor)) =
      localizedCumulativeRule45Priority (.rule4b (RS.swap reference)) label) :
    label = some (.chiral (RS.swap descriptor)) := by
  cases label with
  | none =>
      exfalso
      revert same
      cases reference <;> cases descriptor <;> decide
  | some label =>
      cases label with
      | chiral other =>
          have otherEq : other = RS.swap descriptor := by
            revert same
            cases reference <;> cases descriptor <;> cases other <;> decide
          rw [otherEq]
      | pseudoasymmetric other =>
          exfalso
          revert same
          cases reference <;> cases descriptor <;> cases other <;> decide

/-- A Rule-4b priority vector under one own reference, equal to the vector under the same own
reference, keeps an uppercase label. -/
theorem rule4bSame_priority_chiral (reference descriptor : RS)
    (label : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority (.rule4b reference) (some (.chiral descriptor)) =
      localizedCumulativeRule45Priority (.rule4b reference) label) :
    label = some (.chiral descriptor) := by
  cases label with
  | none =>
      exfalso
      revert same
      cases reference <;> cases descriptor <;> decide
  | some label =>
      cases label with
      | chiral other =>
          have otherEq : other = descriptor := by
            revert same
            cases reference <;> cases descriptor <;> cases other <;> decide
          rw [otherEq]
      | pseudoasymmetric other =>
          exfalso
          revert same
          cases reference <;> cases descriptor <;> cases other <;> decide

/-! ## Actual current arms -/

/-- The trace of an actual current arm matches its addressed descriptor table to the key's
descriptor column. -/
theorem arm_descriptor_table {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (arm : input.RuleMajorContextArm carrierFuel stage read cursor) :
    table (fun node => localizedCumulativeRule45Priority stage node.label) arm.tree =
      arm.key.descriptor :=
  (LocalizedRuleMajorSortTrace.fullMatch_of_trace arm.trace).tableMatch.2.2.2

/-- An actual current arm at a stage, reader and cursor carries the key of any successful actual
build there. -/
theorem arm_key_eq_of_built {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (arm : input.RuleMajorContextArm carrierFuel stage read cursor)
    {key : input.LocalizedRerootCumulativeRule45Key}
    (built : input.buildRuleMajorCumulativeWithRead? stage read (2 * (carrierFuel + 1)) cursor =
      some key) :
    arm.key = key :=
  Option.some.inj (arm.built.symm.trans built)

/-- Matched uppercase stereo labels at every ranked address occupied in both trees: an uppercase
label on the left is matched on the right, reflected when `mirror` holds. -/
def UppercaseCorrespondence {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel) (mirror : Bool) : Prop :=
  ∀ (address : List ℕ) (leftNode rightNode : LocalizedCumulativeDecoratedTree input carrierFuel),
    left.decoratedSubtreeAt? address = some leftNode →
    right.decoratedSubtreeAt? address = some rightNode →
    ∀ descriptor : RS, leftNode.label = some (.chiral descriptor) →
      rightNode.label = some (.chiral (if mirror then RS.swap descriptor else descriptor))

/-- **Matched common-reference readings: equal labels at every common address.**  Two actual
arms at the common-reference Rule-5 stages of any own references, whose actual keys have equal
descriptor columns, carry equal labels at every ranked address occupied in both trees. -/
theorem commonReading_labels_eq {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {ownL ownR : Option RS} {common : RS}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {left right : input.LocalizedRerootCursor carrierFuel}
    (armL : input.RuleMajorContextArm carrierFuel (localizedRule5StageFor ownL common) readL left)
    (armR : input.RuleMajorContextArm carrierFuel (localizedRule5StageFor ownR common) readR right)
    (descriptors : armL.key.descriptor = armR.key.descriptor)
    (address : List ℕ) (leftNode rightNode : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftAt : armL.tree.decoratedSubtreeAt? address = some leftNode)
    (rightAt : armR.tree.decoratedSubtreeAt? address = some rightNode) :
    leftNode.label = rightNode.label := by
  have same := (arm_descriptor_table armL).trans (descriptors.trans (arm_descriptor_table armR).symm)
  exact fullTie_priority_injective ownL ownR common leftNode.label rightNode.label
    (column_eq_at_address
      (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor ownL common)
        node.label)
      (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor ownR common)
        node.label)
      address armL.tree armR.tree leftNode rightNode same leftAt rightAt)

theorem uppercaseCorrespondence_of_commonReading {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {ownL ownR : Option RS} {common : RS}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {left right : input.LocalizedRerootCursor carrierFuel}
    (armL : input.RuleMajorContextArm carrierFuel (localizedRule5StageFor ownL common) readL left)
    (armR : input.RuleMajorContextArm carrierFuel (localizedRule5StageFor ownR common) readR right)
    (descriptors : armL.key.descriptor = armR.key.descriptor) :
    UppercaseCorrespondence armL.tree armR.tree false := by
  intro address leftNode rightNode leftAt rightAt descriptor chiral
  rw [← commonReading_labels_eq armL armR descriptors address leftNode rightNode leftAt rightAt,
    chiral]
  rfl

/-- **Matched relative readings under opposite own references: reflected uppercase labels.** -/
theorem uppercaseCorrespondence_of_oppositeRule4b {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {reference : RS}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {left right : input.LocalizedRerootCursor carrierFuel}
    (armL : input.RuleMajorContextArm carrierFuel (.rule4b reference) readL left)
    (armR : input.RuleMajorContextArm carrierFuel (.rule4b (RS.swap reference)) readR right)
    (descriptors : armL.key.descriptor = armR.key.descriptor) :
    UppercaseCorrespondence armL.tree armR.tree true := by
  intro address leftNode rightNode leftAt rightAt descriptor chiral
  have same := (arm_descriptor_table armL).trans (descriptors.trans (arm_descriptor_table armR).symm)
  have column := column_eq_at_address
    (fun node => localizedCumulativeRule45Priority (.rule4b reference) node.label)
    (fun node => localizedCumulativeRule45Priority (.rule4b (RS.swap reference)) node.label)
    address armL.tree armR.tree leftNode rightNode same leftAt rightAt
  simp only at column
  rw [chiral] at column
  exact rule4bOpposite_priority_chiral reference descriptor rightNode.label column

/-- **Matched relative readings under one own reference: equal uppercase labels.** -/
theorem uppercaseCorrespondence_of_sameRule4b {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {reference : RS}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {left right : input.LocalizedRerootCursor carrierFuel}
    (armL : input.RuleMajorContextArm carrierFuel (.rule4b reference) readL left)
    (armR : input.RuleMajorContextArm carrierFuel (.rule4b reference) readR right)
    (descriptors : armL.key.descriptor = armR.key.descriptor) :
    UppercaseCorrespondence armL.tree armR.tree false := by
  intro address leftNode rightNode leftAt rightAt descriptor chiral
  have same := (arm_descriptor_table armL).trans (descriptors.trans (arm_descriptor_table armR).symm)
  have column := column_eq_at_address
    (fun node => localizedCumulativeRule45Priority (.rule4b reference) node.label)
    (fun node => localizedCumulativeRule45Priority (.rule4b reference) node.label)
    address armL.tree armR.tree leftNode rightNode same leftAt rightAt
  simp only at column
  rw [chiral] at column
  exact rule4bSame_priority_chiral reference descriptor rightNode.label column

/-! ## Uppercase-free arm trees -/

/-- Every addressed node of a decorated tree contributes its observation to the addressed table at
its own depth. -/
theorem table_entry_of_decoratedSubtreeAt {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {α : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α) (address : List ℕ) :
    ∀ (tree node : LocalizedCumulativeDecoratedTree input carrierFuel),
      tree.decoratedSubtreeAt? address = some node →
      ∃ entry ∈ (table observe tree).getD address.length [], entry.2 = observe node := by
  induction address with
  | nil =>
      intro tree node lookup
      simp only [decoratedSubtreeAt?, Option.some.injEq] at lookup
      rw [← lookup]
      refine ⟨([], observe tree), ?_, rfl⟩
      rw [List.length_nil, table_getD_zero]
      simp
  | cons slot address ih =>
      intro tree node lookup
      simp only [decoratedSubtreeAt?] at lookup
      cases hc : tree.children[slot]? with
      | none => simp [hc] at lookup
      | some child =>
          simp only [hc] at lookup
          obtain ⟨entry, member, value⟩ := ih child node lookup
          have childDeep : address.length < (table observe child).length := by
            by_contra shallow
            rw [List.getD_eq_default _ _ (by omega)] at member
            simp at member
          have bounded : (table observe child).length ≤
              localizedTreeChildLayerCount (tree.children.map (table observe)) :=
            (SparseAddress.le_foldl_max (tree.children.map (table observe))
              (fun entry => entry.length) 0).2 (table observe child)
              (List.mem_map.mpr ⟨child, List.mem_of_getElem? hc, rfl⟩)
          refine ⟨(slot :: entry.1, entry.2), ?_, value⟩
          rw [List.length_cons, table_eq_root_merge, getD_root_cons,
            mergeLocalizedTreeChildTables, SparseAddress.mergePairTable_getD,
            if_pos (by omega)]
          unfold SparseAddress.mergePairs
          apply List.mem_flatMap.mpr
          refine ⟨(table observe child, slot), ?_, ?_⟩
          · rw [List.mk_mem_zipIdx_iff_getElem?]
            simp [List.getElem?_map, hc]
          · simp only [id, OfficialRuleMajorKey.prefixLayer]
            exact List.mem_map.mpr ⟨entry, member, rfl⟩

/-- No addressed node of a decorated tree carries an uppercase label. -/
def UppercaseFree {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) : Prop :=
  ∀ (address : List ℕ) (node : LocalizedCumulativeDecoratedTree input carrierFuel),
    tree.decoratedSubtreeAt? address = some node →
    ∀ descriptor : RS, node.label ≠ some (.chiral descriptor)

/-- A chiral-free exact-label table makes the whole decorated tree uppercase-free. -/
theorem uppercaseFree_of_labelTable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (free : LocalizedLabelLayersChiralFree tree.labelTable) : UppercaseFree tree := by
  intro address node lookup descriptor chiral
  obtain ⟨entry, member, value⟩ :=
    table_entry_of_decoratedSubtreeAt (fun node => node.label) address tree node lookup
  by_cases inRange : address.length < tree.labelTable.length
  · have layerMem : tree.labelTable[address.length] ∈ tree.labelTable := List.getElem_mem inRange
    have entryMem : entry ∈ tree.labelTable[address.length] := by
      rw [← List.getD_eq_getElem _ [] inRange]
      exact member
    exact free _ layerMem entry entryMem descriptor (value.trans chiral)
  · have empty : (table (fun node => node.label) tree).getD address.length [] = [] :=
      List.getD_eq_default _ _ (by rw [← labelTable_eq_table]; omega)
    rw [empty] at member
    simp at member

/-- An uppercase-free left tree satisfies the label correspondence for every right tree and both
mirror flags. -/
theorem uppercaseCorrespondence_of_uppercaseFree {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {left : LocalizedCumulativeDecoratedTree input carrierFuel}
    (free : UppercaseFree left) (right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (mirror : Bool) : UppercaseCorrespondence left right mirror := by
  intro address leftNode rightNode leftAt _ descriptor chiral
  exact absurd chiral (free address leftNode leftAt descriptor)

/-- A Rule-4b descriptor column under an uppercase own reference never equals a Rule-4a column:
their root priority vectors have different lengths. -/
theorem rule4b_descriptor_ne_rule4a {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {reference : RS}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {left right : input.LocalizedRerootCursor carrierFuel}
    (armL : input.RuleMajorContextArm carrierFuel (.rule4b reference) readL left)
    (armR : input.RuleMajorContextArm carrierFuel .rule4a readR right) :
    armL.key.descriptor ≠ armR.key.descriptor := by
  intro same
  have tables :=
    (arm_descriptor_table armL).trans (same.trans (arm_descriptor_table armR).symm)
  have roots := table_observe_root_eq _ _ armL.tree armR.tree tables
  have lengths := congrArg List.length roots
  simp [localizedCumulativeRule45Priority] at lengths

/-! ## Readings of actual compound builds -/

section Compound

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
  (cursor : input.LocalizedRerootCursor carrierFuel)

/-- One successful Rule-5 reading build exposes its prior alternative and both actual
common-reference builds. -/
theorem rule5Reading_components {prior : input.LocalizedRerootRule4bcReading}
    {reading : input.LocalizedRerootRule5Reading}
    (built : input.buildRuleMajorCompoundRule5ReadingWith? compileStage cursor prior =
      some reading) :
    reading.prior = prior ∧
      compileStage (localizedRule5StageFor prior.reference? .R) cursor = some reading.commonR ∧
      compileStage (localizedRule5StageFor prior.reference? .S) cursor = some reading.commonS := by
  unfold buildRuleMajorCompoundRule5ReadingWith? at built
  cases hR : compileStage (localizedRule5StageFor prior.reference? .R) cursor with
  | none => simp [hR] at built
  | some commonR =>
      cases hS : compileStage (localizedRule5StageFor prior.reference? .S) cursor with
      | none => simp [hR, hS] at built
      | some commonS =>
          simp [hR, hS] at built
          subst built
          exact ⟨rfl, rfl, rfl⟩

/-- Every reading of a successful Rule-5 reading-list build is an actual common-`R` build at the
stage selected by its own prior reference. -/
theorem rule5Readings_commonR_built :
    ∀ (priors : List input.LocalizedRerootRule4bcReading)
      (readings : List input.LocalizedRerootRule5Reading),
      input.buildRuleMajorCompoundRule5ReadingsWith? compileStage cursor priors = some readings →
      ∀ reading ∈ readings,
        compileStage (localizedRule5StageFor reading.prior.reference? .R) cursor =
          some reading.commonR := by
  intro priors
  induction priors with
  | nil =>
      intro readings built reading member
      simp [buildRuleMajorCompoundRule5ReadingsWith?] at built
      subst built
      simp at member
  | cons prior priors ih =>
      intro readings built reading member
      unfold buildRuleMajorCompoundRule5ReadingsWith? at built
      cases hHead : input.buildRuleMajorCompoundRule5ReadingWith? compileStage cursor prior with
      | none => simp [hHead] at built
      | some head =>
          cases hTail : input.buildRuleMajorCompoundRule5ReadingsWith? compileStage cursor
              priors with
          | none => simp [hHead, hTail] at built
          | some tail =>
              simp [hHead, hTail] at built
              subst built
              rcases List.mem_cons.mp member with same | member
              · subst same
                obtain ⟨priorEq, commonRBuilt, -⟩ :=
                  rule5Reading_components compileStage cursor hHead
                rw [priorEq]
                exact commonRBuilt
              · exact ih tail hTail reading member

/-- The Rule-5 reading-list builder emits one reading per prior alternative. -/
theorem rule5Readings_length :
    ∀ (priors : List input.LocalizedRerootRule4bcReading)
      (readings : List input.LocalizedRerootRule5Reading),
      input.buildRuleMajorCompoundRule5ReadingsWith? compileStage cursor priors = some readings →
      readings.length = priors.length := by
  intro priors
  induction priors with
  | nil =>
      intro readings built
      simp [buildRuleMajorCompoundRule5ReadingsWith?] at built
      subst built
      rfl
  | cons prior priors ih =>
      intro readings built
      unfold buildRuleMajorCompoundRule5ReadingsWith? at built
      cases hHead : input.buildRuleMajorCompoundRule5ReadingWith? compileStage cursor prior with
      | none => simp [hHead] at built
      | some head =>
          cases hTail : input.buildRuleMajorCompoundRule5ReadingsWith? compileStage cursor
              priors with
          | none => simp [hHead, hTail] at built
          | some tail =>
              simp [hHead, hTail] at built
              subst built
              simp [ih tail hTail]

/-- One successful Rule-4b/4c reading build exposes its own reference and, for an uppercase own
reference, both actual relative builds. -/
theorem rule4bcReading_components {reference : Option RS}
    {reading : input.LocalizedRerootRule4bcReading}
    (built : input.buildRuleMajorCompoundRule4bcReadingWith? compileStage cursor reference =
      some reading) :
    reading.reference? = reference ∧
      ∀ own : RS, reference = some own →
        compileStage (.rule4b own) cursor = some reading.rule4bKey ∧
          compileStage (.rule4c own) cursor = some reading.rule4cKey := by
  cases reference with
  | none =>
      unfold buildRuleMajorCompoundRule4bcReadingWith? at built
      cases h4b : compileStage .rule4a cursor with
      | none => simp [h4b] at built
      | some key4b =>
          cases h4c : compileStage .rule4cNoReference cursor with
          | none => simp [h4b, h4c] at built
          | some key4c =>
              simp [h4b, h4c] at built
              subst built
              refine ⟨rfl, ?_⟩
              intro own impossible
              exact absurd impossible (by simp)
  | some own =>
      unfold buildRuleMajorCompoundRule4bcReadingWith? at built
      cases h4b : compileStage (.rule4b own) cursor with
      | none => simp [h4b] at built
      | some key4b =>
          cases h4c : compileStage (.rule4c own) cursor with
          | none => simp [h4b, h4c] at built
          | some key4c =>
              simp [h4b, h4c] at built
              subst built
              refine ⟨rfl, ?_⟩
              intro own' same
              have ownEq : own = own' := Option.some.inj same
              subst ownEq
              exact ⟨h4b, h4c⟩

/-- Every reading of a successful Rule-4b/4c reading-list build with an uppercase own reference
is an actual pair of relative builds at that reference. -/
theorem rule4bcReadings_built :
    ∀ (references : List (Option RS)) (readings : List input.LocalizedRerootRule4bcReading),
      input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor references =
        some readings →
      ∀ reading ∈ readings, ∀ own : RS, reading.reference? = some own →
        compileStage (.rule4b own) cursor = some reading.rule4bKey ∧
          compileStage (.rule4c own) cursor = some reading.rule4cKey := by
  intro references
  induction references with
  | nil =>
      intro readings built reading member
      simp [buildRuleMajorCompoundRule4bcReadingsWith?] at built
      subst built
      simp at member
  | cons reference references ih =>
      intro readings built reading member
      unfold buildRuleMajorCompoundRule4bcReadingsWith? at built
      cases hHead : input.buildRuleMajorCompoundRule4bcReadingWith? compileStage cursor
          reference with
      | none => simp [hHead] at built
      | some head =>
          cases hTail : input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor
              references with
          | none => simp [hHead, hTail] at built
          | some tail =>
              simp [hHead, hTail] at built
              subst built
              rcases List.mem_cons.mp member with same | member
              · subst same
                intro own ownRef
                obtain ⟨refEq, relative⟩ := rule4bcReading_components compileStage cursor hHead
                exact relative own (refEq.symm.trans ownRef)
              · exact ih tail hTail reading member

/-- A successful no-reference reading's Rule-4b key is the actual Rule-4a build. -/
theorem rule4bcReading_none_built {reading : input.LocalizedRerootRule4bcReading}
    (built : input.buildRuleMajorCompoundRule4bcReadingWith? compileStage cursor none =
      some reading) :
    compileStage .rule4a cursor = some reading.rule4bKey := by
  unfold buildRuleMajorCompoundRule4bcReadingWith? at built
  cases h4b : compileStage .rule4a cursor with
  | none => simp [h4b] at built
  | some key4b =>
      cases h4c : compileStage .rule4cNoReference cursor with
      | none => simp [h4b, h4c] at built
      | some key4c =>
          simp [h4b, h4c] at built
          subst built
          rfl

/-- Every reading of a successful Rule-4b/4c reading-list build carries one of the requested
alternatives as its own reference. -/
theorem rule4bcReadings_reference_mem :
    ∀ (references : List (Option RS)) (readings : List input.LocalizedRerootRule4bcReading),
      input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor references =
        some readings →
      ∀ reading ∈ readings, reading.reference? ∈ references := by
  intro references
  induction references with
  | nil =>
      intro readings built reading member
      simp [buildRuleMajorCompoundRule4bcReadingsWith?] at built
      subst built
      simp at member
  | cons reference references ih =>
      intro readings built reading member
      unfold buildRuleMajorCompoundRule4bcReadingsWith? at built
      cases hHead : input.buildRuleMajorCompoundRule4bcReadingWith? compileStage cursor
          reference with
      | none => simp [hHead] at built
      | some head =>
          cases hTail : input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor
              references with
          | none => simp [hHead, hTail] at built
          | some tail =>
              simp [hHead, hTail] at built
              subst built
              rcases List.mem_cons.mp member with same | member
              · subst same
                rw [(rule4bcReading_components compileStage cursor hHead).1]
                exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (ih tail hTail reading member)

/-- Every no-reference reading of a successful reading-list build has the actual Rule-4a build as
its Rule-4b key. -/
theorem rule4bcReadings_none_built :
    ∀ (references : List (Option RS)) (readings : List input.LocalizedRerootRule4bcReading),
      input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor references =
        some readings →
      ∀ reading ∈ readings, reading.reference? = none →
        compileStage .rule4a cursor = some reading.rule4bKey := by
  intro references
  induction references with
  | nil =>
      intro readings built reading member
      simp [buildRuleMajorCompoundRule4bcReadingsWith?] at built
      subst built
      simp at member
  | cons reference references ih =>
      intro readings built reading member
      unfold buildRuleMajorCompoundRule4bcReadingsWith? at built
      cases hHead : input.buildRuleMajorCompoundRule4bcReadingWith? compileStage cursor
          reference with
      | none => simp [hHead] at built
      | some head =>
          cases hTail : input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor
              references with
          | none => simp [hHead, hTail] at built
          | some tail =>
              simp [hHead, hTail] at built
              subst built
              rcases List.mem_cons.mp member with same | member
              · subst same
                intro noReference
                have referenceEq : reference = none :=
                  (rule4bcReading_components compileStage cursor hHead).1.symm.trans noReference
                subst referenceEq
                exact rule4bcReading_none_built compileStage cursor hHead
              · exact ih tail hTail reading member

/-- The Rule-4b/4c reading-list builder emits one reading per alternative. -/
theorem rule4bcReadings_length :
    ∀ (references : List (Option RS)) (readings : List input.LocalizedRerootRule4bcReading),
      input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor references =
        some readings →
      readings.length = references.length := by
  intro references
  induction references with
  | nil =>
      intro readings built
      simp [buildRuleMajorCompoundRule4bcReadingsWith?] at built
      subst built
      rfl
  | cons reference references ih =>
      intro readings built
      unfold buildRuleMajorCompoundRule4bcReadingsWith? at built
      cases hHead : input.buildRuleMajorCompoundRule4bcReadingWith? compileStage cursor
          reference with
      | none => simp [hHead] at built
      | some head =>
          cases hTail : input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor
              references with
          | none => simp [hHead, hTail] at built
          | some tail =>
              simp [hHead, hTail] at built
              subst built
              simp [ih tail hTail]

omit compileStage cursor in
/-- Ranking at most two alternatives only reorders them. -/
theorem mem_rankReadings (readings : List input.LocalizedRerootRule4bcReading)
    (reading : input.LocalizedRerootRule4bcReading) :
    reading ∈ input.rankReadings readings ↔ reading ∈ readings := by
  unfold rankReadings
  split
  · split <;> simp [or_comm]
  · rfl

omit compileStage cursor in
theorem rankReadings_length (readings : List input.LocalizedRerootRule4bcReading) :
    (input.rankReadings readings).length = readings.length := by
  unfold rankReadings
  split
  · split <;> rfl
  · rfl

/-- A successful compound build decomposes into its actual Rule-4a build, its actual reading-list
build over the P-92 alternatives, the ranked prior readings and the actual Rule-5 reading list. -/
theorem compound_components {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildRuleMajorCompoundRule45KeyWith? compileStage cursor = some compound) :
    compileStage .rule4a cursor = some compound.prior.rule4aKey ∧
      ∃ readings, input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels compound.prior.rule4aKey.rankedLabels)) =
            some readings ∧
        compound.prior.readings = input.rankReadings readings ∧
        input.buildRuleMajorCompoundRule5ReadingsWith? compileStage cursor
          compound.prior.readings = some compound.rule5Readings := by
  unfold buildRuleMajorCompoundRule45KeyWith? at built
  rcases Option.eq_none_or_eq_some (compileStage .rule4a cursor) with h4a | ⟨key, h4a⟩
  · rw [h4a] at built
    simp [Option.bind_eq_bind, Option.bind_none] at built
  · rw [h4a] at built
    simp only [Option.bind_eq_bind, Option.bind_some] at built
    rcases Option.eq_none_or_eq_some
        (input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels key.rankedLabels))) with
      hr | ⟨readings, hr⟩
    · rw [hr] at built
      simp [Option.bind_none] at built
    · rw [hr] at built
      simp only [Option.bind_some] at built
      rcases Option.eq_none_or_eq_some
          (input.buildRuleMajorCompoundRule5ReadingsWith? compileStage cursor
            (input.rankReadings readings)) with
        h5 | ⟨rule5, h5⟩
      · rw [h5] at built
        simp [Option.bind_none] at built
      · rw [h5] at built
        simp only [Option.bind_some, Option.some_inj] at built
        subst built
        exact ⟨h4a, readings, hr, rfl, h5⟩

/-- Every successful compound build has a nonempty Rule-5 reading list. -/
theorem compound_rule5Readings_ne_nil {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildRuleMajorCompoundRule45KeyWith? compileStage cursor = some compound) :
    compound.rule5Readings ≠ [] := by
  obtain ⟨_, readings, hr, ranked, h5⟩ := compound_components compileStage cursor built
  have readingsLength := rule4bcReadings_length compileStage cursor _ readings hr
  have rule5Length := rule5Readings_length compileStage cursor _ _ h5
  have positive := referenceAlternatives_length_pos
    (localizedRule4bReferencesFromRankedLabels compound.prior.rule4aKey.rankedLabels)
  intro empty
  rw [empty, ranked, rankReadings_length, readingsLength] at rule5Length
  simp at rule5Length
  omega

/-- Every successful compound build has a nonempty prior reading list. -/
theorem compound_priorReadings_ne_nil {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildRuleMajorCompoundRule45KeyWith? compileStage cursor = some compound) :
    compound.prior.readings ≠ [] := by
  obtain ⟨_, readings, hr, ranked, _⟩ := compound_components compileStage cursor built
  have readingsLength := rule4bcReadings_length compileStage cursor _ readings hr
  have positive := referenceAlternatives_length_pos
    (localizedRule4bReferencesFromRankedLabels compound.prior.rule4aKey.rankedLabels)
  intro empty
  have lengthZero : compound.prior.readings.length = 0 := by
    rw [empty]
    rfl
  rw [ranked, rankReadings_length, readingsLength] at lengthZero
  omega

end Compound

/-! ## Actual compiled compounds at a frame -/

section Frames

open LocalizedRuleMajorReference DeclarativeCIP

variable {input : LocalizedRuleMajorReference.Input}
  {target : LocalizedRuleMajorReference.Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
  (frames : ContextFrameCompilation input target unit targetUnit)

/-- Each compiled compound is the uniform rule-major compound assembly read with the target's
actual context reader. -/
theorem compound_uniform_built (index : Fin 4) :
    input.certified.buildRuleMajorCompoundRule45KeyWith?
        (fun stage position => input.certified.buildRuleMajorCumulativeWithRead? stage
          (contextOccurrenceRead input target)
          (2 * (LocalizedUniversalReference.carrierFuel input + 1)) position)
        (frames.frame.cursorAt index) = some (frames.compounds index) :=
  (input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor target
    (contextOccurrenceView input target) (2 * (LocalizedUniversalReference.carrierFuel input + 1))
    (frames.frame.cursorAt index)).symm.trans
    ((input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq target
      (contextOccurrenceView input target)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frames.frame.cursorAt index)).symm.trans (frames.compoundBuilt index))

/-- The compiled compound's Rule-4a key is the actual context-reader build at the slot. -/
theorem compound_rule4a_built (index : Fin 4) :
    input.certified.buildRuleMajorCumulativeWithRead? .rule4a (contextOccurrenceRead input target)
        (2 * (LocalizedUniversalReference.carrierFuel input + 1)) (frames.frame.cursorAt index) =
      some (frames.compounds index).prior.rule4aKey :=
  (compound_components _ _ (compound_uniform_built frames index)).1

/-- **A compiled common-`R` reading is an actual build.**  Every Rule-5 reading of the compiled
compound at a slot is the actual context-reader build at the common-`R` stage selected by its own
prior reference. -/
theorem compound_commonR_built (index : Fin 4)
    {reading : input.certified.LocalizedRerootRule5Reading}
    (member : reading ∈ (frames.compounds index).rule5Readings) :
    input.certified.buildRuleMajorCumulativeWithRead?
        (localizedRule5StageFor reading.prior.reference? .R) (contextOccurrenceRead input target)
        (2 * (LocalizedUniversalReference.carrierFuel input + 1)) (frames.frame.cursorAt index) =
      some reading.commonR := by
  obtain ⟨_, _, _, _, h5⟩ := compound_components _ _ (compound_uniform_built frames index)
  exact rule5Readings_commonR_built _ _ _ _ h5 reading member

/-- **A compiled relative reading is an actual build.**  Every prior reading of the compiled
compound at a slot with an uppercase own reference is the actual context-reader build at the
Rule-4b stage of that reference. -/
theorem compound_rule4b_built (index : Fin 4)
    {reading : input.certified.LocalizedRerootRule4bcReading}
    (member : reading ∈ (frames.compounds index).prior.readings) {own : RS}
    (ownRef : reading.reference? = some own) :
    input.certified.buildRuleMajorCumulativeWithRead? (.rule4b own)
        (contextOccurrenceRead input target)
        (2 * (LocalizedUniversalReference.carrierFuel input + 1)) (frames.frame.cursorAt index) =
      some reading.rule4bKey := by
  obtain ⟨_, readings, hr, ranked, _⟩ :=
    compound_components _ _ (compound_uniform_built frames index)
  rw [ranked, mem_rankReadings] at member
  exact (rule4bcReadings_built _ _ _ readings hr reading member own ownRef).1

/-- Every compiled compound has a nonempty Rule-5 reading list. -/
theorem compound_rule5Readings_ne_nil' (index : Fin 4) :
    (frames.compounds index).rule5Readings ≠ [] :=
  compound_rule5Readings_ne_nil _ _ (compound_uniform_built frames index)

/-- Every compiled compound has a nonempty prior reading list. -/
theorem compound_priorReadings_ne_nil' (index : Fin 4) :
    (frames.compounds index).prior.readings ≠ [] :=
  compound_priorReadings_ne_nil _ _ (compound_uniform_built frames index)

/-- A compiled no-reference reading's Rule-4b key is the actual context-reader Rule-4a build. -/
theorem compound_rule4bNone_built (index : Fin 4)
    {reading : input.certified.LocalizedRerootRule4bcReading}
    (member : reading ∈ (frames.compounds index).prior.readings)
    (noReference : reading.reference? = none) :
    input.certified.buildRuleMajorCumulativeWithRead? .rule4a
        (contextOccurrenceRead input target)
        (2 * (LocalizedUniversalReference.carrierFuel input + 1)) (frames.frame.cursorAt index) =
      some reading.rule4bKey := by
  obtain ⟨_, readings, hr, ranked, _⟩ :=
    compound_components _ _ (compound_uniform_built frames index)
  rw [ranked, mem_rankReadings] at member
  exact rule4bcReadings_none_built _ _ _ readings hr reading member noReference

/-- The compiled compound's Rule-4a key is the actual dependency-view production build. -/
theorem compound_rule4a_viewBuilt (index : Fin 4) :
    input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4a target
        (contextOccurrenceView input target)
        (2 * (LocalizedUniversalReference.carrierFuel input + 1)) (frames.frame.cursorAt index) =
      some (frames.compounds index).prior.rule4aKey := by
  rw [← input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel,
    ← input.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized]
  exact compound_rule4a_built frames index

/-- A compiled no-reference reading occurs only when the compound selects no Rule-4b
reference. -/
theorem compound_references_nil_of_reading (index : Fin 4)
    {reading : input.certified.LocalizedRerootRule4bcReading}
    (member : reading ∈ (frames.compounds index).prior.readings)
    (noReference : reading.reference? = none) :
    localizedRule4bReferencesFromRankedLabels (frames.compounds index).prior.rule4aKey.rankedLabels =
      [] := by
  obtain ⟨_, readings, hr, ranked, _⟩ :=
    compound_components _ _ (compound_uniform_built frames index)
  rw [ranked, mem_rankReadings] at member
  have referenceMem := rule4bcReadings_reference_mem _ _ _ readings hr reading member
  rw [noReference] at referenceMem
  generalize localizedRule4bReferencesFromRankedLabels
    (frames.compounds index).prior.rule4aKey.rankedLabels = references at referenceMem ⊢
  cases references with
  | nil => rfl
  | cons first rest => simp [localizedRule4bcReferenceAlternatives] at referenceMem

/-- **Empty Rule-4b selection: an uppercase-free actual arm.**  If the compiled compound at a
slot selects no Rule-4b reference, the actual current Rule-4a arm at that slot carries no
uppercase label at any address.  The inversion is the production selector's own
(`buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_chiralFree`),
read on the arm tree through its exact label match. -/
theorem rule4aArm_uppercaseFree_of_references_nil (index : Fin 4)
    (arm : input.certified.RuleMajorContextArm (LocalizedUniversalReference.carrierFuel input)
      .rule4a (contextOccurrenceRead input target) (frames.frame.cursorAt index))
    (empty : localizedRule4bReferencesFromRankedLabels
      (frames.compounds index).prior.rule4aKey.rankedLabels = []) :
    UppercaseFree arm.tree := by
  have keyEq := arm_key_eq_of_built arm (compound_rule4a_built frames index)
  have free := (input.certified.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_chiralFree
    .rule4a target (contextOccurrenceView input target) _ _ _
    (compound_rule4a_viewBuilt frames index)).mp empty
  have labelMatch : arm.tree.labelTable = arm.key.labels :=
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace arm.trace).labelMatch
  apply uppercaseFree_of_labelTable
  rw [labelMatch, keyEq]
  exact free

end Frames

end LocalizedCyclicMatchedReadingDecode
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.column_eq_at_address
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule4bOpposite_priority_chiral
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule4bSame_priority_chiral
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.arm_descriptor_table
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.arm_key_eq_of_built
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.UppercaseCorrespondence
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.commonReading_labels_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.uppercaseCorrespondence_of_commonReading
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.uppercaseCorrespondence_of_oppositeRule4b
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.uppercaseCorrespondence_of_sameRule4b
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule5Reading_components
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule5Readings_commonR_built
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule5Readings_length
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule4bcReading_components
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule4bcReadings_built
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule4bcReadings_length
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.mem_rankReadings
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rankReadings_length
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.compound_components
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.compound_rule5Readings_ne_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.compound_uniform_built
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.compound_rule4a_built
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.compound_commonR_built
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.compound_rule4b_built
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.compound_rule5Readings_ne_nil'
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.table_entry_of_decoratedSubtreeAt
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.UppercaseFree
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.uppercaseFree_of_labelTable
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.uppercaseCorrespondence_of_uppercaseFree
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule4b_descriptor_ne_rule4a
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule4bcReading_none_built
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule4bcReadings_reference_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule4bcReadings_none_built
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.compound_priorReadings_ne_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.compound_priorReadings_ne_nil'
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.compound_rule4bNone_built
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.compound_rule4a_viewBuilt
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.compound_references_nil_of_reading
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode.rule4aArm_uppercaseFree_of_references_nil
