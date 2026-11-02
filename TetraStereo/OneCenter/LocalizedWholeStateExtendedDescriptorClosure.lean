import TetraStereo.OneCenter.LocalizedUniversalWholeStateIntegrationInterface
import TetraStereo.OneCenter.LocalizedConditionalGeometryRecursivePhysicalSupport
import TetraStereo.OneCenter.LocalizedExtendedRule3ExclusionCongruence
import TetraStereo.OneCenter.LocalizedActualParentComparisonSeparation
import TetraStereo.OneCenter.LocalizedParametricRule3ConstitutionalProjection
import TetraStereo.OneCenter.LocalizedUniversalSemanticClosure
import TetraStereo.OneCenter.LocalizedUniversalReferencePipeline
import TetraStereo.OneCenter.LocalizedCarrierRealCenterActiveSimple
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false









































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## Generic list and `mapM` facts -/

/-- The length of a successful `mapM` result is the length of the input list. -/
theorem length_eq_of_mapM_eq_some {α β : Type*} (f : α → Option β) :
    ∀ {values : List α} {results : List β}, values.mapM f = some results →
      results.length = values.length
  | [], results, computed => by
      change some [] = some results at computed
      simp only [Option.some.injEq] at computed
      subst results
      rfl
  | value :: values, results, computed => by
      cases head : f value with
      | none => simp [List.mapM_cons, head] at computed
      | some result =>
          cases tail : values.mapM f with
          | none => simp [List.mapM_cons, head, tail] at computed
          | some rest =>
              simp [List.mapM_cons, head, tail] at computed
              subst results
              simp only [List.length_cons, length_eq_of_mapM_eq_some f tail]

/-- Positional extraction from a successful `mapM`: the function at the input position returns
the result at the same position. -/
theorem mapM_getElem_eq_some {α β : Type*} (f : α → Option β) :
    ∀ (values : List α) (results : List β) (computed : values.mapM f = some results)
      (index : Nat) (inRange : index < values.length),
      f (values[index]'inRange) =
        some (results[index]'(by
          rw [length_eq_of_mapM_eq_some f computed]
          exact inRange))
  | [], results, computed, index, inRange => absurd inRange (by simp)
  | value :: values, results, computed, index, inRange => by
      cases head : f value with
      | none => simp [List.mapM_cons, head] at computed
      | some result =>
          cases tail : values.mapM f with
          | none => simp [List.mapM_cons, head, tail] at computed
          | some rest =>
              simp [List.mapM_cons, head, tail] at computed
              subst results
              cases index with
              | zero => simpa using head
              | succ index =>
                  have inRange' : index < values.length := by simpa using inRange
                  simpa using mapM_getElem_eq_some f values rest tail index inRange'

/-- A `mapM` over a list on which the function is pointwise total succeeds. -/
theorem mapM_total_of_forall_exists {α β : Type*} (f : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, ∃ result, f value = some result) →
      ∃ results, values.mapM f = some results
  | [], _ => ⟨[], rfl⟩
  | value :: values, total => by
      obtain ⟨result, head⟩ := total value (by simp)
      obtain ⟨rest, tail⟩ := mapM_total_of_forall_exists f values
        (fun member present => total member (by simp [present]))
      exact ⟨result :: rest, by simp [List.mapM_cons, head, tail]⟩

/-- A successful `mapM` over a list has a result list of the input length. -/
theorem mapM_total_length {α β : Type*} (f : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, ∃ result, f value = some result) →
      ∃ results, values.mapM f = some results ∧ results.length = values.length
  | [], _ => ⟨[], rfl, rfl⟩
  | value :: values, total => by
      obtain ⟨result, head⟩ := total value (by simp)
      obtain ⟨rest, tail, length⟩ := mapM_total_length f values
        (fun member present => total member (by simp [present]))
      exact ⟨result :: rest, by simp [List.mapM_cons, head, tail], by simp [length]⟩

/-- Positional extraction from a `Forall₂` relation. -/
theorem list_forall₂_getElem {α β : Type*} {relation : α → β → Prop} :
    ∀ {left : List α} {right : List β}, List.Forall₂ relation left right →
      ∀ (index : Nat) (inLeft : index < left.length) (inRight : index < right.length),
        relation (left[index]'inLeft) (right[index]'inRight)
  | _, _, List.Forall₂.nil, index, inLeft, _ => absurd inLeft (by simp)
  | _, _, List.Forall₂.cons related _, 0, _, _ => related
  | _, _, List.Forall₂.cons _ rest, index + 1, inLeft, inRight =>
      list_forall₂_getElem rest index (by simpa using inLeft) (by simpa using inRight)

/-! ## The independent physical-support step from conditional geometry -/




theorem nodeStepPhysicalSupport_of_conditionalGeometryDomainAll
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel)) :
    LocalizedRule3ExtendedNodeStepPhysicalProjection input target view read1 read2 := by
  intro frameFuel frameCorrespondence occurrence excluded1 excluded2 equivalence
  have isSomeAgree :=
    input.rule3CallbackIsSomeAgreesOn_of_frameCorrespondence
      target view read1 read2 frameFuel frameCorrespondence occurrence
  have beforeShape :=
    input.rule3CallbackFrameShapeOn_of_frameCorrespondence
      target view read1 frameFuel occurrence
  have afterShape :=
    input.rule3CallbackFrameShapeOn_of_frameCorrespondence
      target view read2 frameFuel occurrence
  exact input.nodeOptionPhysicalCorrespondence_of_extendedPhysicalUnit_eq
    target target view view read1 read2
    (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      target view read1 frameFuel)
    (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      target view read2 frameFuel)
    occurrence excluded1 excluded2
    (input.localizedRule3ExtendedNodePhysicalUnit?_eq_of_conditionalGeometry
      target target view view read1 read2
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 frameFuel)
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 frameFuel)
      occurrence (geometry occurrence) isSomeAgree beforeShape afterShape
      excluded1 excluded2 equivalence)

/-- The accepted mutual physical-support induction under the all-occurrence conditional geometry
domain. -/
theorem localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalGeometryDomainAll
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel)) :
    ∀ fuel : Nat,
      (∀ (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId),
        LocalizedRule3ExclusionEquivalent input excluded1 excluded2 →
          ∀ cursor : input.LocalizedRerootCursor carrierFuel,
            LocalizedRule3KeyOptionPhysicalCorrespondence input
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                target view read1 fuel excluded1 cursor)
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                target view read2 fuel excluded2 cursor)) ∧
      (∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
        LocalizedRule3FrameOptionPhysicalCorrespondence input
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read1 fuel cursors)
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read2 fuel cursors)) :=
  input.localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalGeometry
    target view read1 read2 geometry

/-! ## The actual whole-state versus executable frame relation -/

/-- At every budget and every cursor list, the actual whole-state frame and the actual shipped
executable frame are either both refused or both successful with pointwise-corresponding raw and
rebuilt keys, the same coupled flag and membership-equivalent exclusions.

The proof composes the mutual support of the two arbitrary readers with the unconditional
`localizedDependencyLabel` specialization of the second reader to the executable twin. -/
theorem buildLocalizedExtendedShortCircuitRule3Frame_wholeState_option_correspondence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel))
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    LocalizedRule3FrameOptionPhysicalCorrespondence input
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
        (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) fuel cursors)
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target
        (input.localizedDependencyView state target) fuel cursors) := by
  have wholeDep :=
    (input.localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalGeometryDomainAll
      target (input.localizedDependencyView state target)
      (input.localizedWholeStateReader state)
      (fun cursor => input.localizedDependencyLabel target
        (input.localizedDependencyView state target) cursor)
      geometry fuel).2 cursors
  rw [input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_eq_buildLocalizedExtendedShortCircuitRule3FrameExec?_of_localizedDependencyLabel
    target (input.localizedDependencyView state target) fuel cursors] at wholeDep
  exact wholeDep

/-! ## Frame data decomposition -/

/-- A successful two-pass `WithRead` frame at a successor budget exposes its rebuilt-key `mapM`
pass at the predecessor fuel and the actual computed exclusions. -/
theorem exists_fuel_and_rebuilt_map_of_frameWithRead?_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    {budget : Nat} {cursors : List (input.LocalizedRerootCursor carrierFuel)}
    {frame : input.LocalizedRule3CanonicalKeyFrame}
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      target view read budget cursors = some frame) :
    ∃ fuel, budget = fuel + 1 ∧
      cursors.mapM
        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
          target view read fuel frame.excluded) = some frame.keys := by
  cases budget with
  | zero => simp [buildLocalizedExtendedShortCircuitRule3FrameWithRead?] at computed
  | succ fuel =>
      unfold buildLocalizedExtendedShortCircuitRule3FrameWithRead? at computed
      cases rawComputed : cursors.mapM
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
            target view read fuel []) with
      | none => simp [rawComputed] at computed
      | some rawKeys =>
          cases topologyComputed :
              input.localizedRule3CoupledTopologyResolutionExec? rawKeys with
          | none => simp [rawComputed, topologyComputed] at computed
          | some topology =>
              let excluded :=
                input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
              cases keysComputed : cursors.mapM
                  (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                    target view read fuel excluded) with
              | none =>
                  simp [rawComputed, topologyComputed, excluded, keysComputed] at computed
              | some keys =>
                  simp [rawComputed, topologyComputed, excluded, keysComputed] at computed
                  subst frame
                  exact ⟨fuel, rfl, by simpa [excluded] using keysComputed⟩

/-- A successful two-pass executable frame at a successor budget exposes its rebuilt-key `mapM`
pass at the predecessor fuel and the actual computed exclusions. -/
theorem exists_fuel_and_rebuilt_map_of_frameExec?_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {budget : Nat} {cursors : List (input.LocalizedRerootCursor carrierFuel)}
    {frame : input.LocalizedRule3CanonicalKeyFrame}
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view budget cursors = some frame) :
    ∃ fuel, budget = fuel + 1 ∧
      cursors.mapM
        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
          target view fuel frame.excluded) = some frame.keys := by
  cases budget with
  | zero => simp [buildLocalizedExtendedShortCircuitRule3FrameExec?] at computed
  | succ fuel =>
      unfold buildLocalizedExtendedShortCircuitRule3FrameExec? at computed
      cases rawComputed : cursors.mapM
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
            target view fuel []) with
      | none => simp [rawComputed] at computed
      | some rawKeys =>
          cases topologyComputed :
              input.localizedRule3CoupledTopologyResolutionExec? rawKeys with
          | none => simp [rawComputed, topologyComputed] at computed
          | some topology =>
              let excluded :=
                input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
              cases keysComputed : cursors.mapM
                  (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                    target view fuel excluded) with
              | none =>
                  simp [rawComputed, topologyComputed, excluded, keysComputed] at computed
              | some keys =>
                  simp [rawComputed, topologyComputed, excluded, keysComputed] at computed
                  subst frame
                  exact ⟨fuel, rfl, by simpa [excluded] using keysComputed⟩

/-! ## Positional key extraction for an actual four-ligand frame -/

/-- Positional extraction at an actual base cursor.  A successful `mapM` over the base cursor list
returns at the indexed cursor exactly the result at the same position. -/
theorem frame_mapM_cursorAt_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} {β : Type*}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (function : input.LocalizedRerootCursor carrierFuel → Option β)
    (results : List β)
    (computed : frame.cursors.mapM function = some results)
    (resultLength : results.length = 4)
    (index : Fin 4) :
    function (frame.cursorAt index) =
      some (results.get (Fin.cast resultLength.symm index)) := by
  have inRange : index.val < frame.cursors.length := by
    rw [frame.length_eq]
    exact index.isLt
  have step := mapM_getElem_eq_some function frame.cursors results computed index.val inRange
  have resultBound : index.val < results.length := by
    rw [length_eq_of_mapM_eq_some function computed]
    exact inRange
  have leftEq : frame.cursorAt index = frame.cursors[index.val]'inRange := rfl
  have rightEq : results.get (Fin.cast resultLength.symm index) =
      results[index.val]'resultBound := rfl
  rw [leftEq, rightEq]
  exact step

/-- Positional extraction from a `Forall₂` relation at a `Fin 4` index. -/
theorem forall₂_get_fin {α β : Type*} {relation : α → β → Prop}
    {left : List α} {right : List β}
    (related : List.Forall₂ relation left right)
    (leftLength : left.length = 4) (rightLength : right.length = 4)
    (index : Fin 4) :
    relation (left.get (Fin.cast leftLength.symm index))
      (right.get (Fin.cast rightLength.symm index)) := by
  have leftBound : index.val < left.length := by
    rw [leftLength]
    exact index.isLt
  have rightBound : index.val < right.length := by
    rw [rightLength]
    exact index.isLt
  have step := list_forall₂_getElem related index.val leftBound rightBound
  simpa only [List.get_eq_getElem] using step

/-- Equality of two Rule-1a/1b/2 constitutional comparisons is symmetric: the comparator decides
`eq` on one orientation exactly when it decides `eq` on the other. -/
theorem ruleMajor_compare_eq_comm {V : Type*} (first second : OfficialRuleMajorKey V) :
    (OfficialRuleMajorKey.compare first second = Ordering.eq) ↔
      (OfficialRuleMajorKey.compare second first = Ordering.eq) := by
  rw [ruleMajor_compare_eq_observable, ruleMajor_compare_eq_observable,
    compareConstitutionalObservable_eq_iff, compareConstitutionalObservable_eq_iff]
  exact ⟨Eq.symm, Eq.symm⟩

/-! ## Structural facts about the actual base slots -/

/-- A non-outward indexed cursor of an actual base is the parent-facing cursor. -/
theorem actualBase_parent_of_not_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : input.localizedOccurrenceFourLigandFrame? target = some base)
    (index : Fin 4)
    (notOutward : ¬ OutwardRerootCursor input target (base.cursorAt index)) :
    IsLocalizedActualFrameParentCursor input target (base.cursorAt index) := by
  rcases input.localizedOccurrenceFourLigandFrame_cursorAt_classification
    target base baseComputed index with
    ⟨certificate, _cursorEq, parent⟩ | ⟨_outwardCursor, _rootEq, _valid, outward⟩
  · exact parent
  · exact absurd outward notOutward

/-- A non-outward indexed cursor carries the derived parent-frame certificate and is literally the
canonical parent cursor. -/
theorem actualBase_parent_certificate_of_not_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : input.localizedOccurrenceFourLigandFrame? target = some base)
    (index : Fin 4)
    (notOutward : ¬ OutwardRerootCursor input target (base.cursorAt index)) :
    ∃ certificate : input.LocalizedParentFrameHistory target,
      base.cursorAt index =
        { occurrence := certificate.parent, previous? := some target } := by
  rcases input.localizedOccurrenceFourLigandFrame_cursorAt_classification
    target base baseComputed index with
    ⟨certificate, cursorEq, _parent⟩ | ⟨_outwardCursor, _rootEq, _valid, outward⟩
  · exact ⟨certificate, cursorEq⟩
  · exact absurd outward notOutward

/-- An outward indexed cursor realises the explicit appended-sibling address form. -/
theorem actualBase_outward_address_form
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : input.localizedOccurrenceFourLigandFrame? target = some base)
    (index : Fin 4)
    (outward : OutwardRerootCursor input target (base.cursorAt index)) :
    ∃ slot : Nat,
      (base.cursorAt index).occurrence.1.address = target.1.address ++ [slot] := by
  have present : base.cursorAt index ∈ base.cursors :=
    List.get_mem base.cursors (Fin.cast base.length_eq.symm index)
  rcases input.localizedOccurrenceFourLigandFrame_cursor_address_classification
    target base baseComputed (base.cursorAt index) present with parent | child
  · exfalso
    have step := parent.2
    have strict := outward.2.1.2
    omega
  · exact child

/-- **Actual parent/outward Rule-1b separation.**  The parent-frame certificate's node and an
outward base cursor's node have distinct Rule-1b root distances, derived from the carrier
derivation of the child across the appended sibling slot.  No direction is asserted: ring and
multiple-bond children may lie on either side. -/
theorem actualBase_outward_rule1bRootDistance_ne_parent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : input.localizedOccurrenceFourLigandFrame? target = some base)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (child : input.LocalizedRerootCursor carrierFuel)
    (childPresent : child ∈ base.cursors)
    {slot : Nat}
    (childAddress : child.occurrence.1.address = target.1.address ++ [slot]) :
    certificate.parent.1.node.rule1bRootDistance ≠
      child.occurrence.1.node.rule1bRootDistance := by
  obtain ⟨current, parentCurrent, tail, currentEq, _parentCurrentEq, historyEq,
    parentHistoryEq⟩ := certificate.history_shape input
  have targetDerived : input.DeclarativeLocalizedOccurrence carrierFuel target.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2
  have childDerived : input.DeclarativeLocalizedOccurrence carrierFuel child.occurrence.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel child.occurrence.1).mp child.occurrence.2
  have sameRoot := input.localizedOccurrenceFourLigandFrame_cursor_root
    target base baseComputed child childPresent
  obtain ⟨childNode, childAtSlot, childFrameEq⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child
      targetDerived childDerived sameRoot slot childAddress
  have childNodeEq : child.occurrence.1.node = childNode := by
    simpa using (congrArg
      (fun (frame : input.LocalizedCIPOccurrenceFrame) => frame.node) childFrameEq)
  have childNodePresent : childNode ∈ input.executableOfficialCIPChildren target.1.node :=
    List.fst_mem_of_mem_zipIdx childAtSlot
  have childNodeMem : child.occurrence.1.node ∈
      input.executableOfficialCIPChildren target.1.node := by
    rw [childNodeEq]
    exact childNodePresent
  have distanceNe :=
    LocalizedParentBranchConstitutionalSeparation.parentRule1bDistance_ne_childRule1bDistance
      input target.1.node certificate.parent.1.node current parentCurrent tail
      targetActive currentEq historyEq (certificate.parent_provenance input)
      parentHistoryEq child.occurrence.1.node childNodeMem
  exact fun same => distanceNe same.symm

/-! ## Slot agreement for the actual compiled frames -/

/-- **Actual-frame slot agreement.**

The full slots are the strictly outward base cursors.  At an outward slot the whole-state and
shipped executable Rule-3 keys are literally equal by the outward exclusion-congruence theorem,
and the whole-state and executable Rules-4a--5 keys are literally equal by outward reachability.
The unique parent-facing slot keeps only its constitutional observable.  All slots carry equal
constitutional observables by the pointwise physical/constitutional frame correspondence, and every
pair touching the parent slot is strictly separated by the actual carrier Rule-1b root distance.
No Rule-3 priority, no Rules-4/5 key and no exclusion order at the parent slot is assumed. -/
def localizedUniversalFrameSlotAgreement_of_actualFrames
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : input.localizedOccurrenceFourLigandFrame? target = some base)
    (targetActive : target.1.node.ActiveSimple)
    (wholeFrame restrictedFrame : input.LocalizedRule3CanonicalKeyFrame)
    (wholeLength : wholeFrame.keys.length = 4)
    (restrictedLength : restrictedFrame.keys.length = 4)
    (keysCorrespondence :
      List.Forall₂ (LocalizedRule3KeyPhysicalConstitutionalCorrespondence input)
        wholeFrame.keys restrictedFrame.keys)
    (excludedEquivalent :
      LocalizedRule3ExclusionEquivalent input wholeFrame.excluded restrictedFrame.excluded)
    (rule3Fuel : Nat)
    (wholeKeysComputed : base.cursors.mapM
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) rule3Fuel wholeFrame.excluded) =
        some wholeFrame.keys)
    (restrictedKeysComputed : base.cursors.mapM
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target (input.localizedDependencyView state target) rule3Fuel
        restrictedFrame.excluded) = some restrictedFrame.keys)
    (wholeRule45Keys restrictedRule45Keys : List input.LocalizedRerootCompoundRule45Key)
    (wholeRule45Length : wholeRule45Keys.length = 4)
    (restrictedRule45Length : restrictedRule45Keys.length = 4)
    (wholeRule45Computed : base.cursors.mapM
      (fun cursor => input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => state cursor.occurrence)
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor) =
        some wholeRule45Keys)
    (restrictedRule45Computed : base.cursors.mapM
      (input.buildLocalizedRerootCompoundRule45KeyExec?
        target (input.localizedDependencyView state target)
        (localizedOccurrenceRerootEvaluationFuel carrierFuel)) =
        some restrictedRule45Keys) :
    LocalizedUniversalFrameSlotAgreement input
      ({ rule3Frame := wholeFrame
         rule3Length := wholeLength
         rule45Keys := wholeRule45Keys
         rule45Length := wholeRule45Length } :
        input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
      ({ rule3Frame := restrictedFrame
         rule3Length := restrictedLength
         rule45Keys := restrictedRule45Keys
         rule45Length := restrictedRule45Length } :
        input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := by
  let full : Fin 4 → Prop := fun index =>
    OutwardRerootCursor input target (base.cursorAt index)
  have parentOfNotFull : ∀ index : Fin 4, ¬ full index →
      IsLocalizedActualFrameParentCursor input target (base.cursorAt index) := by
    intro index notFull
    exact input.actualBase_parent_of_not_outward target base baseComputed index notFull
  have parentCertificateOfNotFull : ∀ index : Fin 4, ¬ full index →
      ∃ certificate : input.LocalizedParentFrameHistory target,
        base.cursorAt index =
          { occurrence := certificate.parent, previous? := some target } := by
    intro index notFull
    exact input.actualBase_parent_certificate_of_not_outward
      target base baseComputed index notFull
  have addressOfFull : ∀ index : Fin 4, full index →
      ∃ slot : Nat,
        (base.cursorAt index).occurrence.1.address = target.1.address ++ [slot] := by
    intro index fullIndex
    exact input.actualBase_outward_address_form target base baseComputed index fullIndex
  refine
    { full := full
      atMostOneNonFull := ?_
      constitutional := ?_
      rule3_full := ?_
      rule45_full := ?_
      separated := ?_ }
  · intro index other notIndex notOther
    by_contra distinct
    exact input.localizedOccurrenceFourLigandFrame_no_two_parent_cursors
      target base baseComputed distinct
      ⟨parentOfNotFull index notIndex, parentOfNotFull other notOther⟩
  · intro index
    have step := forall₂_get_fin
      (relation := LocalizedRule3KeyPhysicalConstitutionalCorrespondence input)
      keysCorrespondence wholeLength restrictedLength index
    simpa only [LocalizedOccurrenceRule3Through5KeyFrame.keyAt] using step.2
  · intro index fullIndex
    have wholeKey := frame_mapM_cursorAt_eq_some input base
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) rule3Fuel wholeFrame.excluded)
      wholeFrame.keys wholeKeysComputed wholeLength index
    have restrictedKey := frame_mapM_cursorAt_eq_some input base
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target (input.localizedDependencyView state target) rule3Fuel
        restrictedFrame.excluded)
      restrictedFrame.keys restrictedKeysComputed restrictedLength index
    have perCursor :
        input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
            target (input.localizedDependencyView state target)
            (input.localizedWholeStateReader state) rule3Fuel wholeFrame.excluded
            (base.cursorAt index) =
          input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
            target (input.localizedDependencyView state target) rule3Fuel
            restrictedFrame.excluded (base.cursorAt index) :=
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_wholeState_eq_Exec?_of_outward_of_exclusionEquivalent
        target state rule3Fuel excludedEquivalent (base.cursorAt index) fullIndex
    have someEq : some (wholeFrame.keys.get (Fin.cast wholeLength.symm index)) =
        some (restrictedFrame.keys.get (Fin.cast restrictedLength.symm index)) :=
      wholeKey.symm.trans (perCursor.trans restrictedKey)
    have keyEq := Option.some.inj someEq
    simpa only [LocalizedOccurrenceRule3Through5KeyFrame.keyAt] using
      congrArg (fun key => key.rule3) keyEq
  · intro index fullIndex
    have wholeKey := frame_mapM_cursorAt_eq_some input base
      (fun cursor => input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => state cursor.occurrence)
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor)
      wholeRule45Keys wholeRule45Computed wholeRule45Length index
    have restrictedKey := frame_mapM_cursorAt_eq_some input base
      (input.buildLocalizedRerootCompoundRule45KeyExec?
        target (input.localizedDependencyView state target)
        (localizedOccurrenceRerootEvaluationFuel carrierFuel))
      restrictedRule45Keys restrictedRule45Computed restrictedRule45Length index
    have child : base.cursorAt index ∈ input.executableLocalizedRerootChildren
        ({ occurrence := target, previous? := none } :
          input.LocalizedRerootCursor carrierFuel) := by
      rw [← input.localizedOccurrenceFourLigandFrame_cursors_eq_executable
        target base baseComputed]
      exact List.get_mem base.cursors (Fin.cast base.length_eq.symm index)
    have perCursor :
        input.buildLocalizedRerootCompoundRule45KeyWithRead?
            (fun cursor => state cursor.occurrence)
            (localizedOccurrenceRerootEvaluationFuel carrierFuel)
            (base.cursorAt index) =
          input.buildLocalizedRerootCompoundRule45KeyExec?
            target (input.localizedDependencyView state target)
            (localizedOccurrenceRerootEvaluationFuel carrierFuel) (base.cursorAt index) :=
      (input.buildLocalizedRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
        target state (base.cursorAt index) (base.cursorAt index) child fullIndex.2.1.2
        Relation.ReflTransGen.refl
        (localizedOccurrenceRerootEvaluationFuel carrierFuel)).trans
      (input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?
        target (input.localizedDependencyView state target)
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) (base.cursorAt index))
    have someEq : some (wholeRule45Keys.get (Fin.cast wholeRule45Length.symm index)) =
        some (restrictedRule45Keys.get (Fin.cast restrictedRule45Length.symm index)) :=
      wholeKey.symm.trans (perCursor.trans restrictedKey)
    simpa only [LocalizedOccurrenceRule3Through5KeyFrame.keyAt] using
      Option.some.inj someEq
  · intro index other distinct notBoth
    by_cases indexFull : full index
    · have otherNotFull : ¬ full other := fun otherFull => notBoth ⟨indexFull, otherFull⟩
      obtain ⟨certificate, parentEq⟩ := parentCertificateOfNotFull other otherNotFull
      obtain ⟨slot, outwardAddress⟩ := addressOfFull index indexFull
      have indexPresent : base.cursorAt index ∈ base.cursors :=
        List.get_mem base.cursors (Fin.cast base.length_eq.symm index)
      have otherPresent : base.cursorAt other ∈ base.cursors :=
        List.get_mem base.cursors (Fin.cast base.length_eq.symm other)
      have indexKey := frame_mapM_cursorAt_eq_some input base
        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
          target (input.localizedDependencyView state target)
          (input.localizedWholeStateReader state) rule3Fuel wholeFrame.excluded)
        wholeFrame.keys wholeKeysComputed wholeLength index
      have otherKey := frame_mapM_cursorAt_eq_some input base
        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
          target (input.localizedDependencyView state target)
          (input.localizedWholeStateReader state) rule3Fuel wholeFrame.excluded)
        wholeFrame.keys wholeKeysComputed wholeLength other
      have distanceNe :
          (base.cursorAt other).occurrence.1.node.rule1bRootDistance ≠
            (base.cursorAt index).occurrence.1.node.rule1bRootDistance := by
        have separated := input.actualBase_outward_rule1bRootDistance_ne_parent
          target base baseComputed targetActive certificate (base.cursorAt index)
          indexPresent outwardAddress
        simpa [parentEq] using separated
      have strictParentOutward :=
        input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_compare_ne_eq_of_rule1bRootDistance_ne
          target (input.localizedDependencyView state target)
          (input.localizedWholeStateReader state)
          (input.localizedWholeStateReader state) rule3Fuel rule3Fuel
          wholeFrame.excluded wholeFrame.excluded
          (base.cursorAt other) (base.cursorAt index)
          (wholeFrame.keys.get (Fin.cast wholeLength.symm other))
          (wholeFrame.keys.get (Fin.cast wholeLength.symm index))
          otherKey indexKey distanceNe
      have comm := ruleMajor_compare_eq_comm
        (wholeFrame.keys.get (Fin.cast wholeLength.symm other)).constitutional
        (wholeFrame.keys.get (Fin.cast wholeLength.symm index)).constitutional
      have goalNe : OfficialRuleMajorKey.compare
          (wholeFrame.keys.get (Fin.cast wholeLength.symm index)).constitutional
          (wholeFrame.keys.get (Fin.cast wholeLength.symm other)).constitutional ≠
            Ordering.eq :=
        fun same => strictParentOutward (comm.mpr same)
      simpa only [LocalizedOccurrenceRule3Through5KeyFrame.keyAt] using goalNe
    · have indexNotFull : ¬ full index := indexFull
      have otherFull : full other := by
        by_contra otherNotFull
        exact input.localizedOccurrenceFourLigandFrame_no_two_parent_cursors
          target base baseComputed distinct
          ⟨parentOfNotFull index indexNotFull, parentOfNotFull other otherNotFull⟩
      obtain ⟨certificate, parentEq⟩ := parentCertificateOfNotFull index indexNotFull
      obtain ⟨slot, outwardAddress⟩ := addressOfFull other otherFull
      have otherPresent : base.cursorAt other ∈ base.cursors :=
        List.get_mem base.cursors (Fin.cast base.length_eq.symm other)
      have indexKey := frame_mapM_cursorAt_eq_some input base
        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
          target (input.localizedDependencyView state target)
          (input.localizedWholeStateReader state) rule3Fuel wholeFrame.excluded)
        wholeFrame.keys wholeKeysComputed wholeLength index
      have otherKey := frame_mapM_cursorAt_eq_some input base
        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
          target (input.localizedDependencyView state target)
          (input.localizedWholeStateReader state) rule3Fuel wholeFrame.excluded)
        wholeFrame.keys wholeKeysComputed wholeLength other
      have distanceNe :
          (base.cursorAt index).occurrence.1.node.rule1bRootDistance ≠
            (base.cursorAt other).occurrence.1.node.rule1bRootDistance := by
        have separated := input.actualBase_outward_rule1bRootDistance_ne_parent
          target base baseComputed targetActive certificate (base.cursorAt other)
          otherPresent outwardAddress
        simpa [parentEq] using separated
      have strictParentOutward :=
        input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_compare_ne_eq_of_rule1bRootDistance_ne
          target (input.localizedDependencyView state target)
          (input.localizedWholeStateReader state)
          (input.localizedWholeStateReader state) rule3Fuel rule3Fuel
          wholeFrame.excluded wholeFrame.excluded
          (base.cursorAt index) (base.cursorAt other)
          (wholeFrame.keys.get (Fin.cast wholeLength.symm index))
          (wholeFrame.keys.get (Fin.cast wholeLength.symm other))
          indexKey otherKey distanceNe
      simpa only [LocalizedOccurrenceRule3Through5KeyFrame.keyAt] using strictParentOutward

/-! ## The shared Rules-4a--5 tail at the actual key lists -/

/-- The whole-state Rules-4a--5 tail refuses whenever the supplied Rule-3 key list does not have
the required length. -/
theorem finishKeyFrameWholeState?_eq_none_of_length_ne
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (rule3Frame : input.LocalizedRule3CanonicalKeyFrame)
    (different : rule3Frame.keys.length ≠ 4) :
    input.finishKeyFrameWholeState? target state base rule3Frame = none := by
  unfold finishKeyFrameWholeState?
  dsimp only
  rw [dif_neg different]

/-- The shipped Rules-4a--5 tail refuses whenever the supplied Rule-3 key list does not have the
required length. -/
theorem finishKeyFrame?_eq_none_of_length_ne
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (rule3Frame : input.LocalizedRule3CanonicalKeyFrame)
    (different : rule3Frame.keys.length ≠ 4) :
    input.finishKeyFrame? target view base rule3Frame = none := by
  unfold finishKeyFrame?
  dsimp only
  rw [dif_neg different]

/-- The whole-state Rules-4a--5 tail at an explicit successful key list. -/
theorem finishKeyFrameWholeState?_eq_some_of_map
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (rule3Frame : input.LocalizedRule3CanonicalKeyFrame)
    (rule3Length : rule3Frame.keys.length = 4)
    (rule45Keys : List input.LocalizedRerootCompoundRule45Key)
    (computed : base.cursors.mapM
      (fun cursor => input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => state cursor.occurrence)
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor) =
        some rule45Keys)
    (rule45Length : rule45Keys.length = 4) :
    input.finishKeyFrameWholeState? target state base rule3Frame =
      some
        { rule3Frame := rule3Frame
          rule3Length := rule3Length
          rule45Keys := rule45Keys
          rule45Length := rule45Length } := by
  unfold finishKeyFrameWholeState?
  dsimp only
  rw [dif_pos rule3Length, computed]
  simp only [doBindSome_eq]
  rw [dif_pos rule45Length]

/-- The shipped Rules-4a--5 tail at an explicit successful key list. -/
theorem finishKeyFrame?_eq_some_of_map
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (rule3Frame : input.LocalizedRule3CanonicalKeyFrame)
    (rule3Length : rule3Frame.keys.length = 4)
    (rule45Keys : List input.LocalizedRerootCompoundRule45Key)
    (computed : base.cursors.mapM
      (input.buildLocalizedRerootCompoundRule45KeyExec? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel)) = some rule45Keys)
    (rule45Length : rule45Keys.length = 4) :
    input.finishKeyFrame? target view base rule3Frame =
      some
        { rule3Frame := rule3Frame
          rule3Length := rule3Length
          rule45Keys := rule45Keys
          rule45Length := rule45Length } := by
  unfold finishKeyFrame?
  dsimp only
  rw [dif_pos rule3Length, computed]
  simp only [doBindSome_eq]
  rw [dif_pos rule45Length]

/-! ## Descriptor transport at the actual key lists -/

/-- **Whole-state versus shipped descriptor at two actually compiled, corresponding key lists.**

The two four-ligand key lists come from a successful two-pass whole-state Rule-3 frame and a
successful two-pass executable Rule-3 frame over the same actual base at the same rebuilt-key
fuel; their rebuilt key lists are pointwise physically/constitutionally corresponding with
membership-equivalent exclusions.  The Rules-4a--5 tails are total at the production structural
fuel, so both succeed; slot agreement (with the unique parent slot kept observable-only and every
parent/outward pair strictly separated by actual Rule-1b carrier distance) then transports the
assembled descriptor.  No list equality at the parent slot is claimed or needed. -/
theorem descriptorFromFrameWholeState?_eq_descriptorFromFrame?_of_actualFrames
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (whole restricted : input.LocalizedRule3CanonicalKeyFrame)
    (frameCorrespondence :
      LocalizedRule3FramePhysicalConstitutionalCorrespondence input whole restricted)
    (baseComputed : input.localizedOccurrenceFourLigandFrame? target = some base)
    (targetActive : target.1.node.ActiveSimple)
    (rule3Fuel : Nat)
    (wholeKeysComputed : base.cursors.mapM
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) rule3Fuel whole.excluded) =
        some whole.keys)
    (restrictedKeysComputed : base.cursors.mapM
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target (input.localizedDependencyView state target) rule3Fuel
        restricted.excluded) = some restricted.keys) :
    input.descriptorFromFrameWholeState? target state center base (some whole) =
      input.descriptorFromFrame? target (input.localizedDependencyView state target)
        center base (some restricted) := by
  have keysCorrespondence := frameCorrespondence.2.1
  have excludedEquivalent :
      LocalizedRule3ExclusionEquivalent input whole.excluded restricted.excluded :=
    frameCorrespondence.2.2.2
  have wholeLength : whole.keys.length = 4 := by
    have step := length_eq_of_mapM_eq_some
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) rule3Fuel whole.excluded)
      wholeKeysComputed
    rw [step, base.length_eq]
  have restrictedLength : restricted.keys.length = 4 := by
    have step := length_eq_of_mapM_eq_some
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target (input.localizedDependencyView state target) rule3Fuel
        restricted.excluded)
      restrictedKeysComputed
    rw [step, base.length_eq]
  have valid : ∀ cursor ∈ base.cursors, input.LocalizedRerootCursorValid cursor :=
    fun cursor member =>
      input.localizedOccurrenceFourLigandFrame_cursor_valid target base baseComputed cursor member
  obtain ⟨wholeRule45Keys, wholeRule45Computed⟩ := mapM_total_of_forall_exists
    (fun cursor => input.buildLocalizedRerootCompoundRule45KeyWithRead?
      (fun cursor => state cursor.occurrence)
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor)
    base.cursors
    (fun cursor member =>
      input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
        (fun cursor => state cursor.occurrence) cursor (valid cursor member))
  obtain ⟨restrictedRule45Keys, restrictedRule45Raw⟩ := mapM_total_of_forall_exists
    (fun cursor => input.buildLocalizedRerootCompoundRule45Key? target
      (input.localizedDependencyView state target)
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor)
    base.cursors
    (fun cursor member =>
      input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
        target (input.localizedDependencyView state target) cursor (valid cursor member))
  have restrictedRule45Computed : base.cursors.mapM
      (input.buildLocalizedRerootCompoundRule45KeyExec?
        target (input.localizedDependencyView state target)
        (localizedOccurrenceRerootEvaluationFuel carrierFuel)) =
        some restrictedRule45Keys := by
    rw [← list_mapM_congr_on
      (input.buildLocalizedRerootCompoundRule45Key? target
        (input.localizedDependencyView state target)
        (localizedOccurrenceRerootEvaluationFuel carrierFuel))
      (input.buildLocalizedRerootCompoundRule45KeyExec? target
        (input.localizedDependencyView state target)
        (localizedOccurrenceRerootEvaluationFuel carrierFuel))
      base.cursors
      (fun cursor _ =>
        input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?
          target (input.localizedDependencyView state target)
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor)]
    exact restrictedRule45Raw
  have wholeRule45Length : wholeRule45Keys.length = 4 := by
    have step := length_eq_of_mapM_eq_some
      (fun cursor => input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => state cursor.occurrence)
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor)
      wholeRule45Computed
    rw [step, base.length_eq]
  have restrictedRule45Length : restrictedRule45Keys.length = 4 := by
    have step := length_eq_of_mapM_eq_some
      (input.buildLocalizedRerootCompoundRule45KeyExec?
        target (input.localizedDependencyView state target)
        (localizedOccurrenceRerootEvaluationFuel carrierFuel))
      restrictedRule45Computed
    rw [step, base.length_eq]
  have finishedWhole := input.finishKeyFrameWholeState?_eq_some_of_map
    target state base whole wholeLength wholeRule45Keys wholeRule45Computed wholeRule45Length
  have finishedRestricted := input.finishKeyFrame?_eq_some_of_map
    target (input.localizedDependencyView state target) base restricted restrictedLength
    restrictedRule45Keys restrictedRule45Computed restrictedRule45Length
  have agreement := input.localizedUniversalFrameSlotAgreement_of_actualFrames
    target state base baseComputed targetActive whole restricted wholeLength restrictedLength
    keysCorrespondence excludedEquivalent rule3Fuel wholeKeysComputed restrictedKeysComputed
    wholeRule45Keys restrictedRule45Keys wholeRule45Length restrictedRule45Length
    wholeRule45Computed restrictedRule45Computed
  unfold descriptorFromFrameWholeState? descriptorFromFrame?
  simp only [doBindSome_eq]
  rw [finishedWhole, finishedRestricted]
  simp only [doBindSome_eq]
  exact input.descriptorFromKeys?_eq_of_slotAgreement target
    (input.localizedDependencyView state target) center base
    ({ rule3Frame := whole
       rule3Length := wholeLength
       rule45Keys := wholeRule45Keys
       rule45Length := wholeRule45Length } :
      input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    ({ rule3Frame := restricted
       rule3Length := restrictedLength
       rule45Keys := restrictedRule45Keys
       rule45Length := restrictedRule45Length } :
      input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    agreement

/-! ## Main arbitrary-target descriptor equality -/










theorem descriptorAtWholeState?_eq_descriptorAt?_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel))
    (evaluationBudget : Nat) :
    input.descriptorAtWholeState? target state evaluationBudget =
      input.descriptorAt? target (input.localizedDependencyView state target)
        evaluationBudget := by
  unfold descriptorAtWholeState? descriptorAt?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => rfl
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => rfl
      | some base =>
          simp only [doBindSome_eq]
          have frameComputed :
              input.localizedOccurrenceFourLigandFrame? target = some base := by
            rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
            exact baseComputed
          have targetActive : target.1.node.ActiveSimple :=
            input.localizedOccurrenceDescriptorCenter?_activeSimple
              target center centerComputed
          have correspondence :=
            input.buildLocalizedExtendedShortCircuitRule3Frame_wholeState_option_correspondence
              target state geometry evaluationBudget base.cursors
          cases wholeComputed :
              input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
                (input.localizedDependencyView state target)
                (input.localizedWholeStateReader state) evaluationBudget base.cursors with
          | none =>
              cases restrictedComputed :
                  input.buildLocalizedExtendedShortCircuitRule3FrameExec? target
                    (input.localizedDependencyView state target)
                    evaluationBudget base.cursors with
              | none => rfl
              | some restricted =>
                  simp only [wholeComputed, restrictedComputed,
                    LocalizedRule3FrameOptionPhysicalCorrespondence] at correspondence
          | some whole =>
              cases restrictedComputed :
                  input.buildLocalizedExtendedShortCircuitRule3FrameExec? target
                    (input.localizedDependencyView state target)
                    evaluationBudget base.cursors with
              | none =>
                  simp only [wholeComputed, restrictedComputed,
                    LocalizedRule3FrameOptionPhysicalCorrespondence] at correspondence
              | some restricted =>
                  have frameCorrespondence :
                      LocalizedRule3FramePhysicalConstitutionalCorrespondence input
                        whole restricted := by
                    simpa only [wholeComputed, restrictedComputed,
                      LocalizedRule3FrameOptionPhysicalCorrespondence] using correspondence
                  obtain ⟨wholeFuel, wholeBudgetEq, wholeKeysComputed⟩ :=
                    input.exists_fuel_and_rebuilt_map_of_frameWithRead?_eq_some
                      target (input.localizedDependencyView state target)
                      (input.localizedWholeStateReader state) wholeComputed
                  obtain ⟨restrictedFuel, restrictedBudgetEq, restrictedKeysComputed⟩ :=
                    input.exists_fuel_and_rebuilt_map_of_frameExec?_eq_some
                      target (input.localizedDependencyView state target) restrictedComputed
                  have fuelEq : wholeFuel = restrictedFuel := by omega
                  subst restrictedFuel
                  exact input.descriptorFromFrameWholeState?_eq_descriptorFromFrame?_of_actualFrames
                    target state center base whole restricted frameCorrespondence
                    frameComputed targetActive wholeFuel wholeKeysComputed restrictedKeysComputed

/-- **Whole-state descriptor equality against the shipped production descriptor.**  At the
production Rule-3 budget, the whole-state pipeline returns exactly the shipped extended
short-circuit descriptor at the state's own dependency view. -/
theorem descriptorAtWholeState?_production_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel)) :
    input.descriptorAtWholeState? target state
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
        target (input.localizedDependencyView state target) := by
  rw [input.descriptorAtWholeState?_eq_descriptorAt?_of_conditionalGeometry
    target state geometry (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)]
  exact input.descriptorAt?_production target (input.localizedDependencyView state target)

/-- **Universal finite-budget corollary.**  At every budget at least the actual universal
preparation bound on the actual base, the universal descriptor equals the whole-state descriptor,
which in turn equals the restricted descriptor at the state's own view. -/
theorem universalDescriptor?_eq_descriptorAtWholeState?_of_bound_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel))
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base)
    (evaluationBudget : Nat)
    (enough : (prepareUniversalRule3EvaluationOutcome input base.cursors target
      (input.localizedDependencyView state target)).1 ≤ evaluationBudget) :
    input.universalDescriptor? target (input.localizedDependencyView state target) =
      input.descriptorAtWholeState? target state evaluationBudget := by
  rw [input.descriptorAtWholeState?_eq_descriptorAt?_of_conditionalGeometry
    target state geometry evaluationBudget]
  exact input.universalDescriptor?_eq_descriptorAt?_of_bound_le target
    (input.localizedDependencyView state target) base baseComputed evaluationBudget enough

/-- **Optional state uniqueness transport.**  If a state is an independent semantic reference
model in the sense of the universal semantic closure, it is the generated reference state, so the
whole-state descriptor at that state is the whole-state descriptor at the reference state and, by
the arbitrary-target equality, the shipped restricted descriptor at the reference state's own
view.  This is a transportation of the existing uniqueness theorem, not a new fixed-point
principle. -/
theorem descriptorAtWholeState?_eq_descriptorAt?_of_independentSemanticReferenceModel
    (input : LocalizedUniversalReference.Input)
    (state : input.certified.LocalizedAuxiliaryState
      (LocalizedUniversalReference.carrierFuel input))
    (model : LocalizedUniversalReference.IndependentSemanticReferenceModel input state)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (geometry : input.certified.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := LocalizedUniversalReference.carrierFuel input))
    (evaluationBudget : Nat) :
    input.certified.descriptorAtWholeState? target state evaluationBudget =
      input.certified.descriptorAt? target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target)
        evaluationBudget := by
  rw [LocalizedUniversalReference.independentSemanticReferenceModel_unique input model]
  exact input.certified.descriptorAtWholeState?_eq_descriptorAt?_of_conditionalGeometry
    target (LocalizedUniversalReference.referenceState input) geometry evaluationBudget

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

-- Kernel-authority certificates for the exported surface.

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.length_eq_of_mapM_eq_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mapM_getElem_eq_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mapM_total_of_forall_exists
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mapM_total_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.list_forall₂_getElem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.nodeStepPhysicalSupport_of_conditionalGeometryDomainAll
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalGeometryDomainAll
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedExtendedShortCircuitRule3Frame_wholeState_option_correspondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_fuel_and_rebuilt_map_of_frameWithRead?_eq_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_fuel_and_rebuilt_map_of_frameExec?_eq_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frame_mapM_cursorAt_eq_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.forall₂_get_fin
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajor_compare_eq_comm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualBase_parent_of_not_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualBase_parent_certificate_of_not_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualBase_outward_address_form
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualBase_outward_rule1bRootDistance_ne_parent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedUniversalFrameSlotAgreement_of_actualFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.finishKeyFrameWholeState?_eq_none_of_length_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.finishKeyFrame?_eq_none_of_length_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.finishKeyFrameWholeState?_eq_some_of_map
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.finishKeyFrame?_eq_some_of_map
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorFromFrameWholeState?_eq_descriptorFromFrame?_of_actualFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorAtWholeState?_eq_descriptorAt?_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorAtWholeState?_production_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.universalDescriptor?_eq_descriptorAtWholeState?_of_bound_le
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorAtWholeState?_eq_descriptorAt?_of_independentSemanticReferenceModel
