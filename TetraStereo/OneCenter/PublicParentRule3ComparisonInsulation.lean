/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import TetraStereo.OneCenter.PublicParametricRule3Through5Descriptor
import TetraStereo.OneCenter.PublicParametricRule45Availability
import TetraStereo.OneCenter.PublicExactConstitutionalObservable
import TetraStereo.OneCenter.PublicCompoundConstitutionalObservable
import TetraStereo.OneCenter.LocalizedConstitutionalRootSeparation
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through5
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace TetraStereo.OneCenter

/-! ## Small list/`Option` utilities -/

private theorem list_mapM_length_eq {α β : Type*} (f : α → Option β) :
    ∀ (values : List α) (results : List β),
      values.mapM f = some results → results.length = values.length
  | [], results, computed => by
      simp at computed
      subst results
      rfl
  | value :: values, results, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : f value with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : values.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst results
              simp [list_mapM_length_eq f values tail tailComputed]

private theorem list_mapM_exists_of_forall_exists {α β : Type*} (f : α → Option β) :
    ∀ (values : List α), (∀ value ∈ values, ∃ result, f value = some result) →
      ∃ results, values.mapM f = some results
  | [], _ => ⟨[], rfl⟩
  | value :: values, all => by
      obtain ⟨head, headComputed⟩ := all value List.mem_cons_self
      obtain ⟨tail, tailComputed⟩ :=
        list_mapM_exists_of_forall_exists f values
          (fun other present => all other (List.mem_cons_of_mem value present))
      exact ⟨head :: tail, by
        simp [List.mapM_cons, headComputed, tailComputed]⟩

/-! ## Observable-level first Rule-1b separation -/

/-- Distinct first Rule-1b spheres make the observable comparison non-tied.  Rule 1a may decide
first or may tie; when it ties, the Rule-1b component decides, and when it is strict the
comparison is already non-tied. -/
theorem compareExactConstitutionalObservable_ne_eq_of_rule1b_head_distances
    (left right : ExactConstitutionalObservable) {leftDistance rightDistance : ℕ}
    (leftHead : left.rule1b.head? = some [([], leftDistance)])
    (rightHead : right.rule1b.head? = some [([], rightDistance)])
    (different : leftDistance ≠ rightDistance) :
    compareExactConstitutionalObservable left right ≠ Ordering.eq := by
  have decisive : OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareRule1b left.rule1b right.rule1b ≠ Ordering.eq :=
    OfficialRuleMajorKey.compareSparseLayers_compareRule1b_ne_eq_of_head_distances
      leftHead rightHead different
  unfold compareExactConstitutionalObservable
  by_cases rule1aEq : OfficialRuleMajorKey.compareSparseLayers compareExactRational
      left.rule1a right.rule1a = Ordering.eq
  · rw [ConstitutionalLexAlgebra.compareLex_eq_second_of_first_eq _ _ _ _
      (by simpa [Ordering.byKey] using rule1aEq)]
    rw [ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq _ _ _ _
      (by simpa [Ordering.byKey] using decisive)]
    simpa [Ordering.byKey] using decisive
  · rw [ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq _ _ _ _
      (by simpa [Ordering.byKey] using rule1aEq)]
    simpa [Ordering.byKey] using rule1aEq

namespace ExactOfficialRuleMajorKey

/-! ## Exact-key Rule-1b head separation -/

/-- A strict Rule-1a projection decides the exact addressed-source comparison. -/
theorem compareAddressedSources_eq_rule1a_of_decisive
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) {left right : OfficialRuleMajorKey.AddressedSourceLayers V}
    (decisive : OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
      (exactRule1aLayers m left) (exactRule1aLayers m right) ≠ Ordering.eq) :
    compareAddressedSources m left right =
      OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
        (exactRule1aLayers m left) (exactRule1aLayers m right) := by
  unfold compareAddressedSources
  have := ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq
    (Ordering.byKey (exactRule1aLayers m)
      (OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber))
    (compareLex
      (Ordering.byKey rule1bLayers
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
      (Ordering.byKey (rule2Layers m)
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)))
    left right (by simpa [Ordering.byKey] using decisive)
  simpa [Ordering.byKey] using this

/-- Once Rule 1a ties, a strict Rule-1b projection decides the addressed-source comparison. -/
theorem compareAddressedSources_eq_rule1b_of_rule1a_eq_of_decisive
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) {left right : OfficialRuleMajorKey.AddressedSourceLayers V}
    (rule1aEq : OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
      (exactRule1aLayers m left) (exactRule1aLayers m right) = Ordering.eq)
    (decisive : OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareRule1b
      (rule1bLayers left) (rule1bLayers right) ≠ Ordering.eq) :
    compareAddressedSources m left right =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        (rule1bLayers left) (rule1bLayers right) := by
  unfold compareAddressedSources
  have firstEq : (Ordering.byKey (exactRule1aLayers m)
      (OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber)) left right =
      Ordering.eq := by
    simpa [Ordering.byKey] using rule1aEq
  rw [ConstitutionalLexAlgebra.compareLex_eq_second_of_first_eq _ _ left right firstEq]
  have inner := ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq
    (Ordering.byKey rule1bLayers
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
    (Ordering.byKey (rule2Layers m)
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
    left right (by simpa [Ordering.byKey] using decisive)
  simpa [Ordering.byKey] using inner

/-- Distinct first total original-root Rule-1b distances make the exact constitutional
comparison non-tied.  The Rule-1a projection is not assumed to tie: the proof splits on it. -/
theorem compare_ne_eq_of_rule1b_head_distances
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) {left right : ExactOfficialRuleMajorKey V}
    {leftDistance rightDistance : ℕ}
    (leftHead : (rule1bLayers left.sourceNodes).head? = some [([], leftDistance)])
    (rightHead : (rule1bLayers right.sourceNodes).head? = some [([], rightDistance)])
    (different : leftDistance ≠ rightDistance) :
    compare m left right ≠ Ordering.eq := by
  rw [compare_eq_compareExactConstitutionalObservable m left right]
  exact compareExactConstitutionalObservable_ne_eq_of_rule1b_head_distances
    (exactConstitutionalObservable m left) (exactConstitutionalObservable m right)
    leftHead rightHead different

/-- Convenience form taking the root-head shape of the two addressed source lists directly. -/
theorem compare_ne_eq_of_sourceNodes_head_distances
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) {left right : ExactOfficialRuleMajorKey V}
    {leftNode rightNode : OfficialCIPNode V}
    (leftHead : left.sourceNodes.head? = some [([], leftNode)])
    (rightHead : right.sourceNodes.head? = some [([], rightNode)])
    (different : leftNode.rule1bRootDistance ≠ rightNode.rule1bRootDistance) :
    compare m left right ≠ Ordering.eq :=
  compare_ne_eq_of_rule1b_head_distances m
    (rule1bLayers_head_of_sourceNodes_head leftHead)
    (rule1bLayers_head_of_sourceNodes_head rightHead)
    different

end ExactOfficialRuleMajorKey

namespace AuthoritativeChemicalInput

/-! ## Actual public Rule-3 key root heads -/

/-- Every declarative public Rule-3 spatial key starts, at its constitutional head layer, with the
singleton addressed root node of the cursor that produced it. -/
theorem DeclarativeAromaticCanonicalRule3SpatialKeyExcept.sourceNodes_head
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {fuel : Nat} {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept
      excluded fuel cursor key) :
    key.constitutional.sourceNodes.head? = some [([], cursor.occurrence.1.node)] := by
  cases derived <;> rfl

/-- Pointwise version of the preceding head statement for one complete declarative key list. -/
theorem DeclarativeAromaticCanonicalRule3SpatialKeyExceptList.forall₂
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded fuel cursors keys) :
    List.Forall₂
      (source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded fuel)
      cursors keys :=
  match derived with
  | .nil _ => .nil
  | .cons head tail => .cons head
      (DeclarativeAromaticCanonicalRule3SpatialKeyExceptList.forall₂ tail)

/-! ## The accepted one-fuel builder: Rule-3 head facts

The builder `buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?` is **not**
redeclared here.  It is the accepted declaration of `PublicParametricRule3Through5Descriptor`,
imported above and used verbatim. -/

/-- Two successful runs of the accepted one-fuel public builder with the same fuel and cursors,
but arbitrary (and possibly different) readers, share the same Rule-3 prefix. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {leftRead rightRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel}
    {fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {leftFrame rightFrame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (leftComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      leftRead fuel cursors = some leftFrame)
    (rightComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      rightRead fuel cursors = some rightFrame) :
    leftFrame.rule3Frame = rightFrame.rule3Frame := by
  have leftEq :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame
      leftRead fuel cursors leftFrame leftComputed
  have rightEq :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame
      rightRead fuel cursors rightFrame rightComputed
  simpa using leftEq.symm.trans rightEq

/-- At a successful actual Rule-3 compilation through the accepted builder, every Rule-3 key slot
has the independent root head of its actual cursor node. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule3_sourceNodes_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel}
    {fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      read fuel cursors = some frame)
    (cursorLength : cursors.length = 4)
    (index : Fin 4) :
    (frame.keyAt index).rule3.constitutional.sourceNodes.head? =
      some [([], (cursors.get (Fin.cast cursorLength.symm index)).occurrence.1.node)] := by
  have declarative :=
    (source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame_sound
      read fuel cursors frame computed).2.2.2
  have pointwise :=
    DeclarativeAromaticCanonicalRule3SpatialKeyExceptList.forall₂ declarative
  have derived := pointwise.get (i := index.val)
    (by rw [cursorLength]; exact index.isLt)
    (by rw [frame.rule3Length]; exact index.isLt)
  exact DeclarativeAromaticCanonicalRule3SpatialKeyExcept.sourceNodes_head derived

/-! ## The separate two-fuel helper (new name)

The predecessor declared a two-fuel builder under the accepted builder's name.  The genuine
two-fuel construction is retained here under a distinct name so that the public one-fuel builder
and the split-prefix construction can coexist.  Its Rule-3 pass is still exactly the accepted
reader-free public builder. -/

/-- Rule3--Rule5 frame builder with an arbitrary auxiliary-label reader and separate Rule-3 and
compound fuels.  `rule3Fuel` drives the unchanged public Rule-3 prefix; `rule45Fuel` drives the
compound through-Rule-5 keys.  This declaration has a name distinct from the accepted one-fuel
public builder. -/
noncomputable def buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (rule3Fuel rule45Fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    Option (source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let rule3Frame ← source.buildAromaticCanonicalRule3CanonicalKeyFrame? rule3Fuel cursors
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← cursors.mapM
      (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead? read rule45Fuel)
    if rule45Length : rule45Keys.length = 4 then
      some { rule3Frame, rule3Length, rule45Keys, rule45Length }
    else none
  else none

/-- **Diagonal specialization.**  When both fuels coincide, the split helper is literally the
accepted one-fuel public builder.  This is the required compatibility statement tying the new-name
helper back to the accepted declaration. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_eq_withRead_of_same_fuel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?
        read fuel fuel cursors =
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        read fuel cursors := rfl

/-- The Rule-3 prefix recorded by any successful split run is exactly the result of the
reader-free public Rule-3 builder. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_rule3Frame_computed
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel}
    {rule3Fuel rule45Fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?
      read rule3Fuel rule45Fuel cursors = some frame) :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame? rule3Fuel cursors =
      some frame.rule3Frame := by
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit? at computed
  cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      rule3Fuel cursors with
  | none => simp [rule3Computed] at computed
  | some rule3Frame =>
      by_cases rule3Length : rule3Frame.keys.length = 4
      · cases rule45Computed : cursors.mapM
            (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
              read rule45Fuel) with
        | none => simp [rule3Computed, rule3Length, rule45Computed] at computed
        | some rule45Keys =>
            by_cases rule45Length : rule45Keys.length = 4
            · simp [rule3Computed, rule3Length, rule45Computed, rule45Length] at computed
              subst frame
              simp
            · simp [rule3Computed, rule3Length, rule45Computed, rule45Length] at computed
      · simp [rule3Computed, rule3Length] at computed

/-- Declarative soundness of the unchanged Rule-3 prefix of a successful split run. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_rule3_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel}
    {rule3Fuel rule45Fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?
      read rule3Fuel rule45Fuel cursors = some frame) :
    source.DeclarativeAromaticCanonicalRule3CanonicalKeyFrame
      rule3Fuel cursors frame.rule3Frame :=
  source.buildAromaticCanonicalRule3CanonicalKeyFrame?_sound
    rule3Fuel cursors frame.rule3Frame
    (source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_rule3Frame_computed
      computed)

/-- Two successful split runs with the same Rule-3 fuel and cursors, but arbitrary (possibly
different) readers and compound fuels, share the same Rule-3 prefix. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_rule3Frame_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {leftRead rightRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel}
    {rule3Fuel leftRule45Fuel rightRule45Fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {leftFrame rightFrame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (leftComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?
      leftRead rule3Fuel leftRule45Fuel cursors = some leftFrame)
    (rightComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?
      rightRead rule3Fuel rightRule45Fuel cursors = some rightFrame) :
    leftFrame.rule3Frame = rightFrame.rule3Frame := by
  have leftEq :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_rule3Frame_computed
      leftComputed
  have rightEq :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_rule3Frame_computed
      rightComputed
  simpa using leftEq.symm.trans rightEq

/-- At a successful split run, every Rule-3 key slot has the independent root head of its actual
cursor node. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_keyAt_rule3_sourceNodes_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel}
    {rule3Fuel rule45Fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?
      read rule3Fuel rule45Fuel cursors = some frame)
    (cursorLength : cursors.length = 4)
    (index : Fin 4) :
    (frame.keyAt index).rule3.constitutional.sourceNodes.head? =
      some [([], (cursors.get (Fin.cast cursorLength.symm index)).occurrence.1.node)] := by
  have declarative :=
    (source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_rule3_sound
      computed).2.2.2
  have pointwise :=
    DeclarativeAromaticCanonicalRule3SpatialKeyExceptList.forall₂ declarative
  have derived := pointwise.get (i := index.val)
    (by rw [cursorLength]; exact index.isLt)
    (by rw [frame.rule3Length]; exact index.isLt)
  exact DeclarativeAromaticCanonicalRule3SpatialKeyExcept.sourceNodes_head derived






theorem exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (rule3Fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      rule3Fuel cursors = some rule3Frame)
    (cursorLength : cursors.length = 4)
    (valid : ∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ frame,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?
        read rule3Fuel (2 * (carrierFuel + 1)) cursors = some frame ∧
      frame.rule3Frame = rule3Frame ∧
      frame.rule45Keys.length = 4 ∧
      frame.rule3Frame.keys.length = 4 := by
  have declarative := source.buildAromaticCanonicalRule3CanonicalKeyFrame?_sound
    rule3Fuel cursors rule3Frame rule3Computed
  have pointwise :=
    DeclarativeAromaticCanonicalRule3SpatialKeyExceptList.forall₂ declarative.2.2.2
  have keysLength : rule3Frame.keys.length = 4 := by
    rw [← pointwise.length_eq, cursorLength]
  have keysExist : ∀ cursor ∈ cursors, ∃ key,
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        read (2 * (carrierFuel + 1)) cursor = some key :=
    fun cursor present =>
      source.exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_at_twice
        read cursor (valid cursor present)
  obtain ⟨keys, keysComputed⟩ := list_mapM_exists_of_forall_exists
    (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read (2 * (carrierFuel + 1))) cursors keysExist
  have keysLength45 : keys.length = 4 := by
    rw [list_mapM_length_eq (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read (2 * (carrierFuel + 1))) cursors keys keysComputed, cursorLength]
  refine ⟨{ rule3Frame := rule3Frame
            rule3Length := keysLength
            rule45Keys := keys
            rule45Length := keysLength45 }, ?_, rfl, keysLength45, keysLength⟩
  simp [buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?,
    rule3Computed, keysLength, keysComputed, keysLength45]

/-! ## Actual parent/outward frame geometry -/

/-- Every cursor of an actual four-ligand frame is a valid reroot cursor. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_roots_valid
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame) :
    ∀ cursor ∈ frame.roots, source.AromaticCanonicalRerootCursorValid cursor := by
  intro cursor present
  obtain ⟨declared, _⟩ :=
    source.aromaticCanonicalOccurrenceFourLigandFrame?_sound target frame computed
  obtain ⟨mapped, previous⟩ := declared
  have intended : cursor.occurrence.1 ∈
      source.intendedAromaticCanonicalRerootChildFrames
        { occurrence := target, previous? := none } := by
    rw [← mapped]
    exact List.mem_map_of_mem (f := fun child => child.occurrence.1) present
  have neighbor := source.mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended
    { occurrence := target, previous? := none } cursor.occurrence.1 intended
  have previousEq := previous cursor present
  unfold AromaticCanonicalRerootCursorValid
  rw [previousEq]
  simpa using neighbor

/-- Every actual four-ligand root address is either the parent address or an outward child
address of the target.  This is read off the actual frame adjacency, not assumed. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_root_address_length
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    ((frame.cursorAt index).occurrence.1.address.length + 1 = target.1.address.length ∧
        (frame.cursorAt index).occurrence.1.address = target.1.address.dropLast) ∨
      (target.1.address.length + 1 =
          (frame.cursorAt index).occurrence.1.address.length ∧
        target.1.address = (frame.cursorAt index).occurrence.1.address.dropLast) := by
  obtain ⟨declared, _⟩ :=
    source.aromaticCanonicalOccurrenceFourLigandFrame?_sound target frame computed
  obtain ⟨mapped, previous⟩ := declared
  have present : frame.cursorAt index ∈ frame.roots := List.get_mem _ _
  have intended : (frame.cursorAt index).occurrence.1 ∈
      source.intendedAromaticCanonicalRerootChildFrames
        { occurrence := target, previous? := none } := by
    rw [← mapped]
    exact List.mem_map_of_mem (f := fun child => child.occurrence.1) present
  have neighbor := source.mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended
    { occurrence := target, previous? := none }
    (frame.cursorAt index).occurrence.1 intended
  have adjacent := (source.mem_aromaticCanonicalRerootNeighborFrames_iff
    target.1 (frame.cursorAt index).occurrence.1).mp neighbor
  unfold AromaticCanonicalCarrierTreeAdjacent at adjacent
  exact adjacent.2.2

/-! ## Total original-root distance of an actual occurrence node -/

/-- Every declarative occurrence derivation preserves the original-root history length: a node
at address `path` has history of length `path.length + 1`. -/
theorem declarativeAromaticCanonicalOccurrenceSubtree_history_length
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence)
    (nodeLength : node.history.length = path.length + 1) :
    occurrence.node.history.length = occurrence.address.length + 1 := by
  revert nodeLength
  induction derived with
  | subtreeRoot path fuel node =>
      intro nodeLength
      exact nodeLength
  | subtreeDescendant childAtSlot descendant inductionHypothesis =>
      intro nodeLength
      apply inductionHypothesis
      have childLength :=
        SemanticMolecule.aromaticCanonicalOfficialCIPChild_history_length
          source.molecule source.molecule.atomCount
          (List.fst_mem_of_mem_zipIdx childAtSlot)
      rw [childLength, nodeLength, List.length_append]
      simp

/-- Every actual carrier occurrence node has history length one more than its address length. -/
theorem aromaticCanonicalOccurrence_node_history_length
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence fuel) :
    occurrence.1.node.history.length = occurrence.1.address.length + 1 :=
  source.declarativeAromaticCanonicalOccurrenceSubtree_history_length
    ((source.mem_aromaticCanonicalOccurrences_iff fuel occurrence.1).mp occurrence.2)
    rfl

/-- For a real-atom actual occurrence node, the total original-root Rule-1b observation equals
the actual carrier address length. -/
theorem aromaticCanonicalOccurrence_rule1bRootDistance_eq_address_length
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence fuel)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    occurrence.1.node.rule1bRootDistance = occurrence.1.address.length := by
  have historyLength := source.aromaticCanonicalOccurrence_node_history_length occurrence
  simp only [OfficialCIPNode.rule1bRootDistance, real, OfficialCIPNode.depth]
  omega

/-! ## Strict Rule-3 comparisons -/

/-- A strict first constitutional component makes the public Rule-3 spatial comparison
non-tied.  The comparison is reader-free by construction. -/
theorem compareAromaticCanonicalUncancelledRule3SpatialKeys_ne_eq_of_sourceNodes_head_distances
    (source : AuthoritativeChemicalInput)
    {left right : source.AromaticCanonicalUncancelledRule3SpatialKey}
    {leftNode rightNode : OfficialCIPNode source.AromaticCanonicalAtom}
    (leftHead : left.constitutional.sourceNodes.head? = some [([], leftNode)])
    (rightHead : right.constitutional.sourceNodes.head? = some [([], rightNode)])
    (different : leftNode.rule1bRootDistance ≠ rightNode.rule1bRootDistance) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys left right ≠
      Ordering.eq := by
  have constitutionalNe : ExactOfficialRuleMajorKey.compare
      source.molecule.toLocalizedMoleculeGraph
      left.constitutional right.constitutional ≠ Ordering.eq :=
    ExactOfficialRuleMajorKey.compare_ne_eq_of_sourceNodes_head_distances
      source.molecule.toLocalizedMoleculeGraph leftHead rightHead different
  unfold compareAromaticCanonicalUncancelledRule3SpatialKeys
  exact ConstitutionalLexAlgebra.compareLex_ne_eq_of_left_ne_eq _ _ _ _
    (by simpa [Ordering.byKey] using constitutionalNe)

/-- A strict Rule-3 outcome makes the public Rule3--Rule5 comparison non-tied and
pseudoasymmetry-free.  The compound keys are never consulted. -/
theorem compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_ne_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 ≠ Ordering.eq) :
    (source.compareAromaticCanonicalOccurrenceRule3Through5At
        frame left right).pseudo = false ∧
      (source.compareAromaticCanonicalOccurrenceRule3Through5At
        frame left right).ordering ≠ Ordering.eq := by
  unfold compareAromaticCanonicalOccurrenceRule3Through5At
  cases outcome : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 with
  | eq => exact absurd outcome strict
  | lt => simp [outcome]
  | gt => simp [outcome]

/-- **Actual final-record reader insulation.**  If two actual frames share the same Rule-3 prefix
and the Rule-3 comparison at the two slots of the first frame is strict, then the *complete*
`ConstitutionalRule5Comparison` record of the public comparison at those slots is literally the
same on both frames.  No equality of compound keys or of their comparison records is assumed. -/
theorem compareAromaticCanonicalOccurrenceRule3Through5At_eq_of_same_rule3Frame_of_strict
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (leftFrame rightFrame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (same : leftFrame.rule3Frame = rightFrame.rule3Frame)
    (left right : Fin 4)
    (strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftFrame.keyAt left).rule3 (leftFrame.keyAt right).rule3 ≠ Ordering.eq) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftFrame left right =
      source.compareAromaticCanonicalOccurrenceRule3Through5At rightFrame left right := by
  have leftKeyEq :=
    AromaticCanonicalOccurrenceRule3Through5KeyFrame.keyAt_rule3_eq_of_rule3Frame_eq
      (source := source) same left
  have rightKeyEq :=
    AromaticCanonicalOccurrenceRule3Through5KeyFrame.keyAt_rule3_eq_of_rule3Frame_eq
      (source := source) same right
  unfold compareAromaticCanonicalOccurrenceRule3Through5At
  dsimp only
  rw [leftKeyEq, rightKeyEq]
  cases outcome : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightFrame.keyAt left).rule3 (rightFrame.keyAt right).rule3 with
  | eq =>
      exfalso
      apply strict
      rw [leftKeyEq, rightKeyEq]
      exact outcome
  | lt => rfl
  | gt => rfl

/-! ## Functional address reading of the actual public carrier

The public occurrence carrier is defined by recursive enumeration and by an independent
declarative reachability relation.  To read a child off an address extension we expose the
functional node address map and prove that declarative reachability computes it.  This is the
public analogue of the localised `nodeAt` development and is what makes parent/outward
classification a consequence of the actual frame rather than a caller assumption. -/

/-- Walk an absolute child-slot address from a starting node. -/
def officialNodeAt? (source : AuthoritativeChemicalInput) (size : Nat)
    (node : OfficialCIPNode (Fin size)) :
    List Nat → Option (OfficialCIPNode (Fin size))
  | [] => some node
  | slot :: rest =>
      match (source.molecule.aromaticCanonicalOfficialCIPChildrenAt size node)[slot]? with
      | none => none
      | some child => source.officialNodeAt? size child rest

@[simp] theorem officialNodeAt?_nil
    (source : AuthoritativeChemicalInput) (size : Nat)
    (node : OfficialCIPNode (Fin size)) :
    source.officialNodeAt? size node [] = some node := rfl

theorem officialNodeAt?_append
    (source : AuthoritativeChemicalInput) (size : Nat)
    (node : OfficialCIPNode (Fin size)) :
    ∀ (left right : List Nat),
      source.officialNodeAt? size node (left ++ right) =
        (source.officialNodeAt? size node left).bind
          (fun reached => source.officialNodeAt? size reached right)
  | [], right => by simp [officialNodeAt?]
  | slot :: left, right => by
      cases childComputed :
          (source.molecule.aromaticCanonicalOfficialCIPChildrenAt size node)[slot]? with
      | none => simp [officialNodeAt?, childComputed]
      | some child =>
          simp only [List.cons_append, officialNodeAt?, childComputed]
          exact source.officialNodeAt?_append size child left right

/-- Absolute-address reading of any declarative occurrence derivation from a known starting
node. -/
theorem declarativeAromaticCanonicalOccurrenceSubtree_nodeAt?
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence) :
    ∀ startNode, source.officialNodeAt? source.molecule.atomCount startNode path = some node →
      source.officialNodeAt? source.molecule.atomCount startNode occurrence.address =
        some occurrence.node := by
  induction derived with
  | subtreeRoot path fuel node =>
      intro startNode start
      simpa using start
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot descendant
      inductionHypothesis =>
      intro startNode start
      have childGet :
          (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
            source.molecule.atomCount node)[slot]? = some child := by
        simpa using (List.mem_zipIdx_iff_getElem?).mp childAtSlot
      have walk : source.officialNodeAt? source.molecule.atomCount startNode
          (path ++ [slot]) = some child := by
        rw [source.officialNodeAt?_append, start]
        simp [officialNodeAt?, childGet]
      exact inductionHypothesis startNode walk

/-- The node stored at an actual carrier occurrence is exactly the functional read of its
absolute address from the atom root node. -/
theorem aromaticCanonicalOccurrence_node_eq_officialNodeAt?
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence fuel) :
    source.officialNodeAt? source.molecule.atomCount
        (OfficialCIPNode.root occurrence.1.root) occurrence.1.address =
      some occurrence.1.node := by
  refine source.declarativeAromaticCanonicalOccurrenceSubtree_nodeAt?
    ((source.mem_aromaticCanonicalOccurrences_iff fuel occurrence.1).mp occurrence.2)
    (OfficialCIPNode.root occurrence.1.root) ?_
  rfl

/-- An occurrence one address slot below another occurrence with the same source root carries an
exact official child of the shorter occurrence's node. -/
theorem aromaticCanonicalOccurrence_child_of_address_append
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (target other : source.AromaticCanonicalOccurrence fuel) {slot : Nat}
    (sameRoot : other.1.root = target.1.root)
    (extension : other.1.address = target.1.address ++ [slot]) :
    other.1.node ∈ source.molecule.aromaticCanonicalOfficialCIPChildrenAt
      source.molecule.atomCount target.1.node := by
  have targetNode := source.aromaticCanonicalOccurrence_node_eq_officialNodeAt? target
  have otherNode := source.aromaticCanonicalOccurrence_node_eq_officialNodeAt? other
  rw [sameRoot, extension] at otherNode
  rw [source.officialNodeAt?_append, targetNode] at otherNode
  simp only [Option.bind_some] at otherNode
  cases childComputed :
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount target.1.node)[slot]? with
  | none => simp [officialNodeAt?, childComputed] at otherNode
  | some child =>
      have equality : child = other.1.node := by
        simpa [officialNodeAt?, childComputed] using otherNode
      rw [← equality]
      exact (List.mem_iff_getElem?).mpr ⟨slot, childComputed⟩

/-- Generated official children are real, multiple-bond duplicates, or ring duplicates; they are
never placeholders. -/
theorem provenance_cases_of_mem_aromaticCanonicalOfficialCIPChildrenAt
    (source : AuthoritativeChemicalInput) (size : Nat)
    {node child : OfficialCIPNode (Fin size)}
    (present : child ∈ source.molecule.aromaticCanonicalOfficialCIPChildrenAt size node) :
    child.provenance = OfficialCIPNodeProvenance.realAtom ∨
      (∃ distance, child.provenance =
        OfficialCIPNodeProvenance.multipleBondDuplicate distance) ∨
      (∃ distance, child.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance) := by
  by_cases duplicate : node.isDuplicateLeaf = true
  · simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt, duplicate] at present
  · unfold SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt at present
    rw [if_neg duplicate] at present
    dsimp only at present
    rcases List.mem_append.mp present with ordinary | virtual
    · rcases List.mem_map.mp ordinary with ⟨copy, _copyPresent, equality⟩
      rw [← equality]
      by_cases copyZero : copy.2 = 0
      · by_cases presentHistory : copy.1 ∈ node.history
        · exact Or.inr (Or.inr ⟨node.duplicateRootDistance copy.1, by
            simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
              copyZero, presentHistory]⟩)
        · exact Or.inl (by
            simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
              copyZero, presentHistory])
      · exact Or.inr (Or.inl ⟨node.depth, by
          simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, copyZero]⟩)
    · cases current : node.current? with
      | none => simp [current] at virtual
      | some attached =>
          cases representative :
              source.molecule.aromaticCanonicalMancudeRepresentativeAt? size attached with
          | none => simp [current, representative] at virtual
          | some atom =>
              simp [current, representative] at virtual
              subst virtual
              exact Or.inr (Or.inl ⟨node.depth, by
                simp [OfficialCIPNode.extendMancudeDuplicate]⟩)

/-- Generated official children always carry a current atom. -/
theorem current?_isSome_of_mem_aromaticCanonicalOfficialCIPChildrenAt
    (source : AuthoritativeChemicalInput) (size : Nat)
    {node child : OfficialCIPNode (Fin size)}
    (present : child ∈ source.molecule.aromaticCanonicalOfficialCIPChildrenAt size node) :
    child.current?.isSome = true := by
  by_cases duplicate : node.isDuplicateLeaf = true
  · simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt, duplicate] at present
  · unfold SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt at present
    rw [if_neg duplicate] at present
    dsimp only at present
    rcases List.mem_append.mp present with ordinary | virtual
    · rcases List.mem_map.mp ordinary with ⟨copy, _copyPresent, equality⟩
      rw [← equality]
      simp [OfficialCIPNode.extend]
    · cases current : node.current? with
      | none => simp [current] at virtual
      | some attached =>
          cases representative :
              source.molecule.aromaticCanonicalMancudeRepresentativeAt? size attached with
          | none => simp [current, representative] at virtual
          | some atom =>
              simp [current, representative] at virtual
              subst virtual
              simp [OfficialCIPNode.extendMancudeDuplicate]

/-- Generated official children begin their history with their current atom. -/
theorem history_head_of_mem_aromaticCanonicalOfficialCIPChildrenAt
    (source : AuthoritativeChemicalInput) (size : Nat)
    {node child : OfficialCIPNode (Fin size)}
    (present : child ∈ source.molecule.aromaticCanonicalOfficialCIPChildrenAt size node) :
    child.history.head? = child.current? := by
  by_cases duplicate : node.isDuplicateLeaf = true
  · simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt, duplicate] at present
  · unfold SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt at present
    rw [if_neg duplicate] at present
    dsimp only at present
    rcases List.mem_append.mp present with ordinary | virtual
    · rcases List.mem_map.mp ordinary with ⟨copy, _copyPresent, equality⟩
      rw [← equality]
      simp [OfficialCIPNode.extend]
    · cases current : node.current? with
      | none => simp [current] at virtual
      | some attached =>
          cases representative :
              source.molecule.aromaticCanonicalMancudeRepresentativeAt? size attached with
          | none => simp [current, representative] at virtual
          | some atom =>
              simp [current, representative] at virtual
              subst virtual
              simp [OfficialCIPNode.extendMancudeDuplicate]

/-- Actual carrier nodes never have placeholder provenance, starting from a provenance-classified
node. -/
theorem declarativeAromaticCanonicalOccurrenceSubtree_provenance_cases
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence) :
    (node.provenance = OfficialCIPNodeProvenance.realAtom ∨
        (∃ distance, node.provenance =
          OfficialCIPNodeProvenance.multipleBondDuplicate distance) ∨
        (∃ distance, node.provenance =
          OfficialCIPNodeProvenance.ringDuplicate distance)) →
      occurrence.node.provenance = OfficialCIPNodeProvenance.realAtom ∨
        (∃ distance, occurrence.node.provenance =
          OfficialCIPNodeProvenance.multipleBondDuplicate distance) ∨
        (∃ distance, occurrence.node.provenance =
          OfficialCIPNodeProvenance.ringDuplicate distance) := by
  intro start
  induction derived with
  | subtreeRoot path fuel node => exact start
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot descendant
      inductionHypothesis =>
      exact inductionHypothesis
        (source.provenance_cases_of_mem_aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount (List.fst_mem_of_mem_zipIdx childAtSlot))

/-- Actual carrier occurrences never have placeholder provenance. -/
theorem aromaticCanonicalOccurrence_provenance_cases
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence fuel) :
    occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∨
      (∃ distance, occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.multipleBondDuplicate distance) ∨
      (∃ distance, occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance) :=
  source.declarativeAromaticCanonicalOccurrenceSubtree_provenance_cases
    ((source.mem_aromaticCanonicalOccurrences_iff fuel occurrence.1).mp occurrence.2)
    (Or.inl rfl)

/-- Actual carrier occurrences always carry a current atom. -/
theorem declarativeAromaticCanonicalOccurrenceSubtree_current?_isSome
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence) :
    node.current?.isSome = true → occurrence.node.current?.isSome = true := by
  intro start
  induction derived with
  | subtreeRoot path fuel node => exact start
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot descendant
      inductionHypothesis =>
      exact inductionHypothesis
        (source.current?_isSome_of_mem_aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount (List.fst_mem_of_mem_zipIdx childAtSlot))

theorem aromaticCanonicalOccurrence_current?_isSome
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence fuel) :
    occurrence.1.node.current?.isSome = true :=
  source.declarativeAromaticCanonicalOccurrenceSubtree_current?_isSome
    ((source.mem_aromaticCanonicalOccurrences_iff fuel occurrence.1).mp occurrence.2)
    rfl

/-- Actual carrier occurrence histories begin with their current atom. -/
theorem declarativeAromaticCanonicalOccurrenceSubtree_history_head
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence) :
    node.history.head? = node.current? →
      occurrence.node.history.head? = occurrence.node.current? := by
  intro start
  induction derived with
  | subtreeRoot path fuel node => exact start
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot descendant
      inductionHypothesis =>
      exact inductionHypothesis
        (source.history_head_of_mem_aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount (List.fst_mem_of_mem_zipIdx childAtSlot))

theorem aromaticCanonicalOccurrence_history_head
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence fuel) :
    occurrence.1.node.history.head? = occurrence.1.node.current? :=
  source.declarativeAromaticCanonicalOccurrenceSubtree_history_head
    ((source.mem_aromaticCanonicalOccurrences_iff fuel occurrence.1).mp occurrence.2)
    rfl

/-! ## First-occurrence indices and the all-child distance separation -/

theorem firstIndexOf?_exists_of_mem {α : Type*} [DecidableEq α] (target : α) :
    ∀ {values : List α}, target ∈ values →
      ∃ index, firstIndexOf? target values = some index
  | [], present => by simp at present
  | value :: values, present => by
      by_cases same : value = target
      · exact ⟨0, by simp [firstIndexOf?, same]⟩
      · rw [List.mem_cons] at present
        rcases present with here | later
        · exact absurd here.symm same
        · obtain ⟨index, computed⟩ :=
            firstIndexOf?_exists_of_mem target later
          exact ⟨index + 1, by
            simp [firstIndexOf?, same, computed]⟩

theorem firstIndexOf?_some_getElem? {α : Type*} [DecidableEq α] (target : α) :
    ∀ (values : List α) (index : Nat),
      firstIndexOf? target values = some index →
        values[index]? = some target
  | [], index, computed => by simp [firstIndexOf?] at computed
  | value :: values, index, computed => by
      by_cases same : value = target
      · subst same
        cases index with
        | zero => rfl
        | succ index => simp [firstIndexOf?] at computed
      · simp [firstIndexOf?, same] at computed
        cases tailIndex : firstIndexOf? target values with
        | none => simp [tailIndex] at computed
        | some tail =>
            simp [tailIndex] at computed
            have indexEq : index = tail + 1 := by omega
            subst index
            simpa using firstIndexOf?_some_getElem? target values tail tailIndex

/-- Decomposition of membership in the exact official child list into an ordinary copied child
or the single virtual mancude child. -/
theorem mem_aromaticCanonicalOfficialCIPChildrenAt_cases
    (source : AuthoritativeChemicalInput) (size : Nat)
    {node child : OfficialCIPNode (Fin size)}
    (present : child ∈ source.molecule.aromaticCanonicalOfficialCIPChildrenAt size node) :
    (∃ next copyIndex, child = node.extend next copyIndex ∧
        (next, copyIndex) ∈ source.molecule.aromaticCanonicalChildCopiesAt size node) ∨
      (∃ representative, child = node.extendMancudeDuplicate representative) := by
  by_cases duplicate : node.isDuplicateLeaf = true
  · simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt, duplicate] at present
  · unfold SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt at present
    rw [if_neg duplicate] at present
    dsimp only at present
    rcases List.mem_append.mp present with ordinary | virtual
    · rcases List.mem_map.mp ordinary with ⟨copy, copyPresent, equality⟩
      exact Or.inl ⟨copy.1, copy.2, equality.symm, copyPresent⟩
    · cases current : node.current? with
      | none => simp [current] at virtual
      | some attached =>
          cases representative :
              source.molecule.aromaticCanonicalMancudeRepresentativeAt? size attached with
          | none => simp [current, representative] at virtual
          | some atom =>
              simp [current, representative] at virtual
              subst virtual
              exact Or.inr ⟨atom, rfl⟩

/-- **All-child Rule-1b separation at an actual public node.**  For a node whose history is
`current :: parent :: tail`, no generated official child has the parent's total original-root
distance `tail.length`.  Fresh real children are farther by two spheres, multiple-bond copies
(ordinary positive copies and the virtual mancude duplicate) are farther by one, and ring
duplicates use their first-occurrence index in the reversed branch.  A ring duplicate can
therefore be nearer, equal to `tail.length + 1`, or elsewhere among the stored duplicate
distances: only non-tie is claimed.  The value `tail.length` is exactly the parent's first reverse
index, and the zero-copy parent edge is removed from the generated child copies. -/
theorem aromaticCanonicalOfficialChild_rule1bRootDistance_ne_parentDistance
    (source : AuthoritativeChemicalInput) (size : Nat)
    {node child : OfficialCIPNode (Fin size)}
    (present : child ∈ source.molecule.aromaticCanonicalOfficialCIPChildrenAt size node)
    {current parentAtom : Fin size} {tail : List (Fin size)}
    (currentEq : node.current? = some current)
    (historyEq : node.history = current :: parentAtom :: tail) :
    child.rule1bRootDistance ≠ tail.length := by
  rcases source.mem_aromaticCanonicalOfficialCIPChildrenAt_cases size present with
    ⟨next, copyIndex, childEq, copyPresent⟩ | ⟨representative, childEq⟩
  · rcases source.provenance_cases_of_mem_aromaticCanonicalOfficialCIPChildrenAt
      size present with realCase | multipleCase | ringCase
    · rw [childEq] at realCase
      simp only [OfficialCIPNode.extend, OfficialCIPNode.childProvenance] at realCase
      by_cases copyZero : copyIndex = 0
      · subst copyZero
        by_cases presentHistory : next ∈ node.history
        · simp [presentHistory] at realCase
        · have lengthEq : node.history.length = tail.length + 2 := by
            rw [historyEq]
            simp
          have distance : (node.extend next 0).rule1bRootDistance = tail.length + 2 := by
            simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
              OfficialCIPNode.childProvenance, presentHistory, OfficialCIPNode.depth,
              lengthEq]
          rw [childEq]
          omega
      · have multiple := realCase
        simp [OfficialCIPNode.childProvenance, copyZero] at multiple
    · obtain ⟨distanceValue, multipleEq⟩ := multipleCase
      rw [childEq] at multipleEq
      simp only [OfficialCIPNode.extend, OfficialCIPNode.childProvenance] at multipleEq
      have copyPositive : copyIndex ≠ 0 := by
        intro copyZero
        rw [copyZero] at multipleEq
        by_cases presentHistory : next ∈ node.history <;>
          simp [presentHistory] at multipleEq
      have distance : (node.extend next copyIndex).rule1bRootDistance = node.depth := by
        simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
          OfficialCIPNode.childProvenance, copyPositive]
      have depth : node.depth = tail.length + 1 := by
        simp [OfficialCIPNode.depth, historyEq]
      rw [childEq]
      omega
    · obtain ⟨distanceValue, ringEq⟩ := ringCase
      rw [childEq] at ringEq
      simp only [OfficialCIPNode.extend, OfficialCIPNode.childProvenance] at ringEq
      have copyZero : copyIndex = 0 := by
        by_contra copyPositive
        simp [copyPositive] at ringEq
      subst copyZero
      have presentHistory : next ∈ node.history := by
        by_contra absent
        simp [absent] at ringEq
      have parentEq : node.parent? = some parentAtom := by
        simp [OfficialCIPNode.parent?, historyEq]
      have copyInFiltered : (next, 0) ∈
          (source.molecule.aromaticCanonicalOrdinaryNeighborCopiesAt size current).filter
            (fun copy => !(copy.1 == parentAtom && copy.2 == 0)) := by
        simpa [SemanticMolecule.aromaticCanonicalChildCopiesAt, currentEq, parentEq]
          using copyPresent
      have excluded : next ≠ parentAtom := by
        rw [List.mem_filter] at copyInFiltered
        have notParent := copyInFiltered.2
        intro same
        rw [same] at notParent
        simp at notParent
      have distance : (node.extend next 0).rule1bRootDistance =
          node.duplicateRootDistance next := by
        simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
          OfficialCIPNode.childProvenance, presentHistory]
      rw [childEq]
      intro equal
      have reversePresent : next ∈ node.history.reverse := List.mem_reverse.mpr presentHistory
      obtain ⟨index, indexEq⟩ := firstIndexOf?_exists_of_mem next reversePresent
      have duplicateEq : node.duplicateRootDistance next = index := by
        unfold OfficialCIPNode.duplicateRootDistance
        rw [indexEq]
        rfl
      have indexBound : index = tail.length := by omega
      have reverseGet := firstIndexOf?_some_getElem? next node.history.reverse index indexEq
      have indexLtRev : index < node.history.reverse.length := by
        by_contra tooLarge
        have noneEq : node.history.reverse[index]? = none := by
          rw [List.getElem?_eq_none_iff]
          exact Nat.le_of_not_lt tooLarge
        rw [noneEq] at reverseGet
        cases reverseGet
      have indexLt : index < node.history.length := by simpa using indexLtRev
      rw [List.getElem?_reverse (l := node.history) (i := index) indexLt] at reverseGet
      have indexOne : node.history.length - 1 - index = 1 := by
        rw [historyEq] at *
        simp only [List.length_cons] at *
        omega
      rw [indexOne, historyEq] at reverseGet
      simp at reverseGet
      exact excluded reverseGet.symm
  · rw [childEq]
    simp only [OfficialCIPNode.extendMancudeDuplicate]
    have distance : node.depth = tail.length + 1 := by
      simp [OfficialCIPNode.depth, historyEq]
    simp [OfficialCIPNode.rule1bRootDistance]
    omega

/-! ## Parent-child history and provenance bridges -/

/-- A generated child's history is its head followed by exactly its parent's history.  This is the
converse direction needed to recover the parent branch from a child history. -/
theorem node_history_tail_of_mem_aromaticCanonicalOfficialCIPChildrenAt
    (source : AuthoritativeChemicalInput) (size : Nat)
    {node child : OfficialCIPNode (Fin size)}
    (present : child ∈ source.molecule.aromaticCanonicalOfficialCIPChildrenAt size node)
    {head : Fin size} {tail : List (Fin size)}
    (historyEq : child.history = head :: tail) :
    node.history = tail := by
  rcases source.mem_aromaticCanonicalOfficialCIPChildrenAt_cases size present with
    ⟨next, copyIndex, childEq, _copyPresent⟩ | ⟨representative, childEq⟩
  · rw [childEq] at historyEq
    simp only [OfficialCIPNode.extend_history] at historyEq
    exact (List.cons.inj historyEq).2
  · rw [childEq] at historyEq
    simp only [OfficialCIPNode.extendMancudeDuplicate_history] at historyEq
    exact (List.cons.inj historyEq).2

/-- A node with an actual generated child is real: duplicate leaves have no generated children,
and the actual-carrier provenance cases exclude placeholders. -/
theorem provenance_real_of_mem_aromaticCanonicalOfficialCIPChildrenAt
    (source : AuthoritativeChemicalInput) (size : Nat)
    {node child : OfficialCIPNode (Fin size)}
    (present : child ∈ source.molecule.aromaticCanonicalOfficialCIPChildrenAt size node)
    (origin : node.provenance = OfficialCIPNodeProvenance.realAtom ∨
      (∃ distance, node.provenance =
        OfficialCIPNodeProvenance.multipleBondDuplicate distance) ∨
      (∃ distance, node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance)) :
    node.provenance = OfficialCIPNodeProvenance.realAtom := by
  rcases origin with real | multiple | ring
  · exact real
  · obtain ⟨distance, equality⟩ := multiple
    simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt,
      OfficialCIPNode.isDuplicateLeaf, equality] at present
  · obtain ⟨distance, equality⟩ := ring
    simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt,
      OfficialCIPNode.isDuplicateLeaf, equality] at present

/-! ## Actual frame cursor roots and the broadened parent/outward pair -/

/-- Every root cursor of an actual four-ligand frame is a carrier neighbor of the target. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_cursor_mem_neighborFrames
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ frame.roots) :
    cursor.occurrence.1 ∈ source.aromaticCanonicalRerootNeighborFrames
      (fuel := carrierFuel) target.1 := by
  obtain ⟨declared, _⟩ :=
    source.aromaticCanonicalOccurrenceFourLigandFrame?_sound target frame computed
  obtain ⟨mapped, _previous⟩ := declared
  have intended : cursor.occurrence.1 ∈
      source.intendedAromaticCanonicalRerootChildFrames
        { occurrence := target, previous? := none } := by
    rw [← mapped]
    exact List.mem_map_of_mem (f := fun child => child.occurrence.1) present
  exact source.mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended
    { occurrence := target, previous? := none } cursor.occurrence.1 intended

/-- Every root cursor of an actual four-ligand frame retains the target root. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_cursor_root
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ frame.roots) :
    cursor.occurrence.1.root = target.1.root := by
  have neighbor :=
    source.aromaticCanonicalOccurrenceFourLigandFrame_cursor_mem_neighborFrames
      target frame computed cursor present
  have adjacent := (source.mem_aromaticCanonicalRerootNeighborFrames_iff
    target.1 cursor.occurrence.1).mp neighbor
  exact adjacent.2.1

/-- A structural parent-versus-outward pair of slots of an actual four-ligand frame.

The pair records the actual frame slots, their address orientation read off the actual frame
adjacency, and the resulting total original-root Rule-1b observations.  It deliberately has **no**
`outwardReal` field: an outward ligand may be any generated official child, including a
multiple-bond copy or a ring duplicate.  The only separation it asserts is non-tie; no fixed
direction of the comparison is assumed. -/
structure AromaticCanonicalParentOutwardLigandPair
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) where
  /-- The actual frame slot occupied by the parent occurrence. -/
  parentSlot : Fin 4
  /-- The actual frame slot occupied by the outward ligand occurrence. -/
  outwardSlot : Fin 4
  /-- The two ligand slots are distinct. -/
  distinct : parentSlot ≠ outwardSlot
  /-- The parent slot is at the immediate shorter carrier address. -/
  parent_address :
    (frame.cursorAt parentSlot).occurrence.1.address = target.1.address.dropLast
  /-- The parent slot is exactly one carrier step shorter than the target. -/
  parent_address_length :
    (frame.cursorAt parentSlot).occurrence.1.address.length + 1 = target.1.address.length
  /-- The sibling slot occupied by the outward child. -/
  outward_slot : Nat
  /-- The outward slot extends the target address by one sibling slot. -/
  outward_address :
    (frame.cursorAt outwardSlot).occurrence.1.address =
      target.1.address ++ [outward_slot]
  /-- The outward slot is exactly one carrier step longer than the target. -/
  outward_address_length :
    target.1.address.length + 1 =
      (frame.cursorAt outwardSlot).occurrence.1.address.length
  /-- A real parent occurrence has total original-root distance one below the target address. -/
  parent_distance :
    (frame.cursorAt parentSlot).occurrence.1.node.rule1bRootDistance =
      target.1.address.length - 1
  /-- No actual child kind, including generated duplicates, has the parent distance. -/
  outward_distance_ne :
    (frame.cursorAt outwardSlot).occurrence.1.node.rule1bRootDistance ≠
      target.1.address.length - 1

namespace AromaticCanonicalParentOutwardLigandPair

/-- The actual parent cursor selected by the pair. -/
def parentCursor (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {target : source.AromaticCanonicalOccurrence carrierFuel}
    {frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel}
    (pair : source.AromaticCanonicalParentOutwardLigandPair target frame) :
    source.AromaticCanonicalRerootCursor carrierFuel :=
  frame.cursorAt pair.parentSlot

/-- The actual outward cursor selected by the pair. -/
def outwardCursor (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {target : source.AromaticCanonicalOccurrence carrierFuel}
    {frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel}
    (pair : source.AromaticCanonicalParentOutwardLigandPair target frame) :
    source.AromaticCanonicalRerootCursor carrierFuel :=
  frame.cursorAt pair.outwardSlot

/-- **Non-tie guard for the broadened pair.**  The parent and outward total original-root Rule-1b
distances differ, with the parent at the actual shortened address distance and the outward child
at any other actual child kind.  This is the kernel-checkable counterpart of the pair structure's
promised separation. -/
theorem rule1bRootDistance_ne
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {target : source.AromaticCanonicalOccurrence carrierFuel}
    {frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel}
    (pair : source.AromaticCanonicalParentOutwardLigandPair target frame) :
    (pair.parentCursor source).occurrence.1.node.rule1bRootDistance ≠
      (pair.outwardCursor source).occurrence.1.node.rule1bRootDistance := by
  unfold parentCursor outwardCursor
  rw [pair.parent_distance]
  intro equal
  exact pair.outward_distance_ne equal.symm

end AromaticCanonicalParentOutwardLigandPair

/-- **Every actual parent/outward slot pair yields a broadened ligand pair.**  The slot orientation
is read from the actual four-ligand frame adjacency; the parent history is recovered from the
actual target branch, and the outward separation covers every generated child kind. -/
theorem exists_aromaticCanonicalParentOutwardLigandPair_ofFrame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame)
    (parentSlot outwardSlot : Fin 4)
    (distinct : parentSlot ≠ outwardSlot)
    (parentLength :
      (frame.cursorAt parentSlot).occurrence.1.address.length + 1 =
        target.1.address.length)
    (outwardLength :
      target.1.address.length + 1 =
        (frame.cursorAt outwardSlot).occurrence.1.address.length) :
    ∃ pair : source.AromaticCanonicalParentOutwardLigandPair target frame,
      pair.parentSlot = parentSlot ∧ pair.outwardSlot = outwardSlot := by
  let parentCursor := frame.cursorAt parentSlot
  let outwardCursor := frame.cursorAt outwardSlot
  have parentPresent : parentCursor ∈ frame.roots := List.get_mem _ _
  have outwardPresent : outwardCursor ∈ frame.roots := List.get_mem _ _
  have parentNeighbor :=
    source.aromaticCanonicalOccurrenceFourLigandFrame_cursor_mem_neighborFrames
      target frame computed parentCursor parentPresent
  have outwardNeighbor :=
    source.aromaticCanonicalOccurrenceFourLigandFrame_cursor_mem_neighborFrames
      target frame computed outwardCursor outwardPresent
  have parentRoot :
      parentCursor.occurrence.1.root = target.1.root :=
    source.aromaticCanonicalOccurrenceFourLigandFrame_cursor_root
      target frame computed parentCursor parentPresent
  have outwardRoot :
      outwardCursor.occurrence.1.root = target.1.root :=
    source.aromaticCanonicalOccurrenceFourLigandFrame_cursor_root
      target frame computed outwardCursor outwardPresent
  /- Read the parent address orientation from the actual adjacency. -/
  have parentAddress :
      parentCursor.occurrence.1.address = target.1.address.dropLast := by
    rcases source.aromaticCanonicalOccurrenceFourLigandFrame_root_address_length
      target frame computed parentSlot with parentCase | outwardCase
    · exact parentCase.2
    · omega
  /- Read the outward sibling address orientation from the actual adjacency. -/
  have targetAddress_eq_dropLast :
      target.1.address = outwardCursor.occurrence.1.address.dropLast := by
    rcases source.aromaticCanonicalOccurrenceFourLigandFrame_root_address_length
      target frame computed outwardSlot with parentCase | outwardCase
    · omega
    · exact outwardCase.2
  have outwardLength' :
      target.1.address.length + 1 =
        outwardCursor.occurrence.1.address.length := by
    simpa [outwardCursor] using outwardLength
  have outwardNonempty : outwardCursor.occurrence.1.address ≠ [] := by
    intro empty
    have zero : outwardCursor.occurrence.1.address.length = 0 := by simp [empty]
    omega
  have outwardAddress :
      outwardCursor.occurrence.1.address =
        target.1.address ++ [outwardCursor.occurrence.1.address.getLast outwardNonempty] := by
    calc
      outwardCursor.occurrence.1.address =
          outwardCursor.occurrence.1.address.dropLast ++
            [outwardCursor.occurrence.1.address.getLast outwardNonempty] :=
        (List.dropLast_append_getLast
          (l := outwardCursor.occurrence.1.address) outwardNonempty).symm
      _ = target.1.address ++
            [outwardCursor.occurrence.1.address.getLast outwardNonempty] := by
        rw [← targetAddress_eq_dropLast]
  /- The target is an actual generated child of the parent occurrence. -/
  have targetNonempty : target.1.address ≠ [] := by
    intro empty
    have zero : target.1.address.length = 0 := by simp [empty]
    omega
  have targetExtension :
      target.1.address = parentCursor.occurrence.1.address ++
        [target.1.address.getLast targetNonempty] := by
    calc
      target.1.address = target.1.address.dropLast ++
          [target.1.address.getLast targetNonempty] :=
        (List.dropLast_append_getLast
          (l := target.1.address) targetNonempty).symm
      _ = parentCursor.occurrence.1.address ++
          [target.1.address.getLast targetNonempty] := by
        rw [parentAddress]
  have parentChild :
      target.1.node ∈ source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount parentCursor.occurrence.1.node :=
    source.aromaticCanonicalOccurrence_child_of_address_append
      parentCursor.occurrence target parentRoot.symm targetExtension
  /- Decompose the actual target branch. -/
  have targetHistoryLength :=
    source.aromaticCanonicalOccurrence_node_history_length target
  have targetAddressPositive : 0 < target.1.address.length := by omega
  have historyLength : 2 ≤ target.1.node.history.length := by omega
  cases targetHistory : target.1.node.history with
  | nil => simp [targetHistory] at historyLength
  | cons current rest =>
      cases rest with
      | nil => simp [targetHistory] at historyLength
      | cons parentAtom tail =>
          have currentEq : target.1.node.current? = some current := by
            have head := source.aromaticCanonicalOccurrence_history_head target
            rw [targetHistory] at head
            simpa using head.symm
          have parentHistory : parentCursor.occurrence.1.node.history =
              parentAtom :: tail :=
            source.node_history_tail_of_mem_aromaticCanonicalOfficialCIPChildrenAt
              source.molecule.atomCount parentChild targetHistory
          have parentProvenanceCases :=
            source.aromaticCanonicalOccurrence_provenance_cases parentCursor.occurrence
          have parentReal :
              parentCursor.occurrence.1.node.provenance =
                OfficialCIPNodeProvenance.realAtom :=
            source.provenance_real_of_mem_aromaticCanonicalOfficialCIPChildrenAt
              source.molecule.atomCount parentChild parentProvenanceCases
          have parentDistance :
              parentCursor.occurrence.1.node.rule1bRootDistance = tail.length := by
            simp [OfficialCIPNode.rule1bRootDistance, parentReal,
              OfficialCIPNode.depth, parentHistory]
          have tailLength : tail.length = target.1.address.length - 1 := by
            have lengths : (current :: parentAtom :: tail).length =
                target.1.address.length + 1 := by
              rw [← targetHistory]
              exact targetHistoryLength
            simp only [List.length_cons] at lengths
            omega
          /- The outward occurrence is an actual generated child of the target. -/
          have outwardChild :
              outwardCursor.occurrence.1.node ∈
                source.molecule.aromaticCanonicalOfficialCIPChildrenAt
                  source.molecule.atomCount target.1.node :=
            source.aromaticCanonicalOccurrence_child_of_address_append
              target outwardCursor.occurrence outwardRoot outwardAddress
          have outwardDistanceNe : outwardCursor.occurrence.1.node.rule1bRootDistance ≠
              tail.length :=
            source.aromaticCanonicalOfficialChild_rule1bRootDistance_ne_parentDistance
              source.molecule.atomCount outwardChild currentEq targetHistory
          refine ⟨
            { parentSlot := parentSlot
              outwardSlot := outwardSlot
              distinct := distinct
              parent_address := parentAddress
              parent_address_length := parentLength
              outward_slot := outwardCursor.occurrence.1.address.getLast outwardNonempty
              outward_address := outwardAddress
              outward_address_length := outwardLength
              parent_distance := ?_
              outward_distance_ne := ?_ }, rfl, rfl⟩
          · rw [← tailLength]
            exact parentDistance
          · intro equal
            rw [← tailLength] at equal
            exact outwardDistanceNe equal

/-! ## One-fuel availability wrapper and the same-fuel insulation endpoint -/






theorem exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      (2 * (carrierFuel + 1)) cursors = some rule3Frame)
    (cursorLength : cursors.length = 4)
    (valid : ∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ frame,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        read (2 * (carrierFuel + 1)) cursors = some frame ∧
      frame.rule3Frame = rule3Frame ∧
      frame.rule45Keys.length = 4 ∧
      frame.rule3Frame.keys.length = 4 := by
  obtain ⟨frame, splitComputed, rule3Eq, keysLength, rule3KeysLength⟩ :=
    source.exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_at_twice
      read (2 * (carrierFuel + 1)) cursors rule3Frame rule3Computed cursorLength valid
  refine ⟨frame, ?_, rule3Eq, keysLength, rule3KeysLength⟩
  rw [← source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_eq_withRead_of_same_fuel]
  exact splitComputed

/-- **Actual same-fuel parent/outward Rule3--Rule5 insulation endpoint.**

Given an actual four-ligand frame, an actual broadened parent/outward pair of its slots, an
arbitrary Rule-3 fuel whose actual public Rule-3 builder run succeeds on the frame roots, and two
arbitrary auxiliary-label readers, both split Rule3--Rule5 frames are constructed at the same
Rule-3 fuel and at the eager compound fuel `2 * (carrierFuel + 1)`.  The terminal
`ConstitutionalRule5Comparison` records at the pair slots are literally equal across the two
readers, and both are non-tied and pseudoasymmetry-free.

The Rule-3 frame availability is the only premise about the actual public builder.  No compound
key, compound comparison, label reader, or outward provenance is assumed. -/
theorem exists_sameFuel_parentOutward_rule3Through5_comparison_insulation
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame)
    (pair : source.AromaticCanonicalParentOutwardLigandPair target frame)
    (rule3Fuel : Nat)
    (rule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      rule3Fuel frame.roots = some rule3Frame)
    (leftRead rightRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel) :
    ∃ leftFrame rightFrame,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?
          leftRead rule3Fuel (2 * (carrierFuel + 1)) frame.roots = some leftFrame ∧
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?
          rightRead rule3Fuel (2 * (carrierFuel + 1)) frame.roots = some rightFrame ∧
      leftFrame.rule3Frame = rule3Frame ∧
      rightFrame.rule3Frame = rule3Frame ∧
      source.compareAromaticCanonicalOccurrenceRule3Through5At
          leftFrame pair.parentSlot pair.outwardSlot =
        source.compareAromaticCanonicalOccurrenceRule3Through5At
          rightFrame pair.parentSlot pair.outwardSlot ∧
      (source.compareAromaticCanonicalOccurrenceRule3Through5At
          leftFrame pair.parentSlot pair.outwardSlot).pseudo = false ∧
      (source.compareAromaticCanonicalOccurrenceRule3Through5At
          rightFrame pair.parentSlot pair.outwardSlot).pseudo = false ∧
      (source.compareAromaticCanonicalOccurrenceRule3Through5At
          leftFrame pair.parentSlot pair.outwardSlot).ordering ≠ Ordering.eq ∧
      (source.compareAromaticCanonicalOccurrenceRule3Through5At
          rightFrame pair.parentSlot pair.outwardSlot).ordering ≠ Ordering.eq := by
  have valid :=
    source.aromaticCanonicalOccurrenceFourLigandFrame_roots_valid target frame computed
  obtain ⟨leftFrame, leftComputed, leftRule3Eq, _leftKeysLength, _leftRule3KeysLength⟩ :=
    source.exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_at_twice
      leftRead rule3Fuel frame.roots rule3Frame rule3Computed frame.rootsLength valid
  obtain ⟨rightFrame, rightComputed, rightRule3Eq, _rightKeysLength, _rightRule3KeysLength⟩ :=
    source.exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_at_twice
      rightRead rule3Fuel frame.roots rule3Frame rule3Computed frame.rootsLength valid
  have sameRule3 : leftFrame.rule3Frame = rightFrame.rule3Frame := by
    rw [leftRule3Eq, rightRule3Eq]
  have parentHead :
      (leftFrame.keyAt pair.parentSlot).rule3.constitutional.sourceNodes.head? =
        some [([], (frame.cursorAt pair.parentSlot).occurrence.1.node)] := by
    have derived :=
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_keyAt_rule3_sourceNodes_head
        (read := leftRead) (rule3Fuel := rule3Fuel)
        (rule45Fuel := 2 * (carrierFuel + 1))
        (cursors := frame.roots) (frame := leftFrame) leftComputed
        frame.rootsLength pair.parentSlot
    simpa [AromaticCanonicalOccurrenceFourLigandFrame.cursorAt] using derived
  have outwardHead :
      (leftFrame.keyAt pair.outwardSlot).rule3.constitutional.sourceNodes.head? =
        some [([], (frame.cursorAt pair.outwardSlot).occurrence.1.node)] := by
    have derived :=
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_keyAt_rule3_sourceNodes_head
        (read := leftRead) (rule3Fuel := rule3Fuel)
        (rule45Fuel := 2 * (carrierFuel + 1))
        (cursors := frame.roots) (frame := leftFrame) leftComputed
        frame.rootsLength pair.outwardSlot
    simpa [AromaticCanonicalOccurrenceFourLigandFrame.cursorAt] using derived
  have distanceNe :
      (frame.cursorAt pair.parentSlot).occurrence.1.node.rule1bRootDistance ≠
        (frame.cursorAt pair.outwardSlot).occurrence.1.node.rule1bRootDistance := by
    simpa [AromaticCanonicalParentOutwardLigandPair.parentCursor,
      AromaticCanonicalParentOutwardLigandPair.outwardCursor] using
      pair.rule1bRootDistance_ne source
  have strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftFrame.keyAt pair.parentSlot).rule3
      (leftFrame.keyAt pair.outwardSlot).rule3 ≠ Ordering.eq :=
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys_ne_eq_of_sourceNodes_head_distances
      parentHead outwardHead distanceNe
  have comparisonEq :=
    source.compareAromaticCanonicalOccurrenceRule3Through5At_eq_of_same_rule3Frame_of_strict
      leftFrame rightFrame sameRule3 pair.parentSlot pair.outwardSlot strict
  have leftNonTie :=
    source.compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_ne_eq
      leftFrame pair.parentSlot pair.outwardSlot strict
  have rightPseudo :
      (source.compareAromaticCanonicalOccurrenceRule3Through5At
        rightFrame pair.parentSlot pair.outwardSlot).pseudo = false := by
    rw [← comparisonEq]
    exact leftNonTie.1
  have rightOrdering :
      (source.compareAromaticCanonicalOccurrenceRule3Through5At
        rightFrame pair.parentSlot pair.outwardSlot).ordering ≠ Ordering.eq := by
    rw [← comparisonEq]
    exact leftNonTie.2
  exact ⟨leftFrame, rightFrame, leftComputed, rightComputed, leftRule3Eq, rightRule3Eq,
    comparisonEq, leftNonTie.1, rightPseudo, leftNonTie.2, rightOrdering⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter

/-! ## Kernel guards -/

assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_eq_withRead_of_same_fuel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithReadSplit?_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame_cursor_root
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.node_history_tail_of_mem_aromaticCanonicalOfficialCIPChildrenAt
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.provenance_real_of_mem_aromaticCanonicalOfficialCIPChildrenAt
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOfficialChild_rule1bRootDistance_ne_parentDistance
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalParentOutwardLigandPair.rule1bRootDistance_ne
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_aromaticCanonicalParentOutwardLigandPair_ofFrame
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalOccurrenceRule3Through5At_eq_of_same_rule3Frame_of_strict
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_sameFuel_parentOutward_rule3Through5_comparison_insulation
