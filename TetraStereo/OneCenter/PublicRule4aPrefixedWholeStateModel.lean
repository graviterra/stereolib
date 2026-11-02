/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.OneCenter.PublicRule4aPrefixedDescriptorBackend
import TetraStereo.OneCenter.PublicWholeStateRule3Through5Model
import TetraStereo.KernelOnly





































set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-! ## The corrected diagonal record -/

/-- **Actual corrected self-comparison.**  Comparing one corrected through-Rule-5 key with itself
returns exactly `{ordering := eq, pseudo := false}`: the Rule-4a prefix ties by actual comparator
reflexivity, and the unchanged legacy suffix is reflexive on the diagonal.  This is the
parent/parent case of the corrected tie seam. -/
theorem compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_self
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalRerootCompoundRule45Key) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5 key key =
      { ordering := Ordering.eq, pseudo := false } := by
  have rule4aTie :
      source.compareAromaticCanonicalCumulativeRule45Keys
        key.prior.rule4aKey key.prior.rule4aKey = Ordering.eq := by
    letI : Std.TransCmp source.compareAromaticCanonicalCumulativeRule45Keys :=
      source.compareAromaticCanonicalCumulativeRule45Keys_transCmp
    exact Std.ReflCmp.compare_self
  rw [source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_of_rule4a_tie
    key key rule4aTie]
  exact source.compareAromaticCanonicalRerootCompoundThroughRule5_self key

/-! ## Corrected spatial evidence and descriptor under an arbitrary reader

Only the compound reader inside the shipped frame builder changes.  The Rule-3 pass, the actual
four-ligand frame, the corrected safe tracked sorter, the exact point read and the shipped
descriptor classification are reused unchanged. -/

/-- Corrected Rule-4a-prefixed spatial evidence under an arbitrary total label reader. -/
noncomputable def aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidenceWithRead?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (ruleFuel : Nat) :
    Option (source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  let base ← source.aromaticCanonicalOccurrenceFourLigandFrame? target
  let keys ← source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
    read ruleFuel base.roots
  let tracked ←
    source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? keys
  let points ← tracked.highestFirst.mapM fun index =>
    source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }

/-- **Exact restricted specialization of the corrected spatial evidence**, at every rule fuel. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidenceWithRead?_eq_spatialEvidence?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ ruleFuel : Nat,
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidenceWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
        target ruleFuel =
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
        target view ruleFuel := by
  intro ruleFuel
  unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidenceWithRead?
    aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
  simp only [source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_eq_rule3Through5KeyFrame?
    target view ruleFuel]

/-- Corrected Rule-4a-prefixed descriptor under an arbitrary total label reader. -/
noncomputable def aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (ruleFuel : Nat) : Option AromaticCanonicalAuxiliaryLabel := do
  let evidence ←
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidenceWithRead?
      read target ruleFuel
  let raw ← CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- **Exact restricted specialization of the corrected descriptor**, at every rule fuel. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?_eq_descriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ ruleFuel : Nat,
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
        target ruleFuel =
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
        target view ruleFuel := by
  intro ruleFuel
  unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
    aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
  rw [source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidenceWithRead?_eq_spatialEvidence?
    target view ruleFuel]

/-! ## The corrected tie seam

The seam is the corrected counterpart of `AromaticCanonicalOccurrenceRule3Through5FrameTieSeam`:
the Rule-3 half is literally shared, and the *corrected* compound through-Rule-5 records agree on
pairs that the shared reader-free Rule-3 comparison leaves tied.  Where Rule 3 decides, the
corrected frame comparator ignores the compound records entirely.
-/

/-- Two actual frames whose Rule-3 half is literally shared and whose **corrected** compound
through-Rule-5 records agree on every pair tied by the shared Rule-3 comparison. -/
structure AromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameTieSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    Prop where
  /-- The actual Rule-3 canonical frame is literally shared. -/
  sharedRule3Frame : left.rule3Frame = right.rule3Frame
  /-- The corrected direct compound comparison records agree on every pair whose shared Rule-3
  comparison is a tie.  No condition is imposed where Rule 3 already decides the order. -/
  rule45PairComparisonsOnTies : ∀ (leftIndex rightIndex : Fin 4),
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (left.keyAt leftIndex).rule3 (left.keyAt rightIndex).rule3 = Ordering.eq →
    source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5
        (left.keyAt leftIndex).rule45 (left.keyAt rightIndex).rule45 =
      source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5
        (right.keyAt leftIndex).rule45 (right.keyAt rightIndex).rule45

/-- Build the corrected tie seam from two actual successful arbitrary-reader builds.  The shared
Rule-3 frame is derived from determinism of the reader-free pass, not assumed; only the tied-pair
corrected compound comparison condition remains to be supplied. -/
theorem AromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameTieSeam.of_computations
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (leftComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      read fuel cursors = some left)
    (rightComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
      fuel cursors = some right)
    (ties : ∀ (leftIndex rightIndex : Fin 4),
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
          (left.keyAt leftIndex).rule3 (left.keyAt rightIndex).rule3 = Ordering.eq →
      source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5
          (left.keyAt leftIndex).rule45 (left.keyAt rightIndex).rule45 =
        source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5
          (right.keyAt leftIndex).rule45 (right.keyAt rightIndex).rule45) :
    source.AromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameTieSeam left right := by
  have rightRestricted :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        target view fuel cursors = some right := by
    rw [← source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_eq_rule3Through5KeyFrame?
      target view fuel cursors]
    exact rightComputed
  exact ⟨
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame_eq_of_both_some
      read target view fuel cursors left right leftComputed rightRestricted,
    ties⟩

/-- **Corrected actual comparison transport from the tie seam.**  Where Rule 3 decides, both sides
return the same strict ordinary record; where it ties, the corrected compound record equality of
the seam applies. -/
theorem compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_eq_of_tieSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameTieSeam
      left right)
    (leftIndex rightIndex : Fin 4) :
    source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
        left leftIndex rightIndex =
      source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
        right leftIndex rightIndex := by
  unfold compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
  dsimp only
  rw [← AromaticCanonicalOccurrenceRule3Through5KeyFrame.keyAt_rule3_eq_of_rule3Frame_eq
      seam.sharedRule3Frame leftIndex,
    ← AromaticCanonicalOccurrenceRule3Through5KeyFrame.keyAt_rule3_eq_of_rule3Frame_eq
      seam.sharedRule3Frame rightIndex]
  generalize rule3Comparison :
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (left.keyAt leftIndex).rule3 (left.keyAt rightIndex).rule3 = outcome
  cases outcome
  · simp [rule3Comparison]
  · simp [rule3Comparison,
      seam.rule45PairComparisonsOnTies leftIndex rightIndex rule3Comparison]
  · simp [rule3Comparison]

/-- The corrected safe tracked sorter, including the exact pseudo-comparison count, transports
along the corrected tie seam. -/
theorem safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_of_tieSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameTieSeam
      left right) :
    source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? left =
      source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder? right :=
  source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_of_compare
    right left
    (fun leftIndex rightIndex =>
      source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_eq_of_tieSeam
        seam leftIndex rightIndex)

/-- Corrected descriptor transport on the same actual four-ligand base from the tie seam.  The
priority-ordered coordinates are read from the shared base, so only the corrected tracked order
has to transport. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?_eq_of_tieSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameTieSeam
      left right)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) :
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor? left base =
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor? right base := by
  unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?
  rw [source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_of_tieSeam
    seam]

/-- **Conditional corrected descriptor transport for an arbitrary reader.**  If the corrected
arbitrary-reader descriptor and the shipped corrected restricted descriptor succeed on the same
actual four-ligand base and their key frames are related by the corrected tie seam, then the two
corrected descriptors are equal as whole `Option`s.  No descriptor value is assumed and no
comparison equality is required where Rule 3 already decides. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?_eq_descriptor?_of_keyFrameTieSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some base)
    (wholeFrame restrictedFrame :
      source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (wholeComputed :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        read ruleFuel base.roots = some wholeFrame)
    (restrictedComputed :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        target view ruleFuel base.roots = some restrictedFrame)
    (seam : source.AromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameTieSeam
      wholeFrame restrictedFrame) :
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
        read target ruleFuel =
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
        target view ruleFuel := by
  unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
    aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
    aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidenceWithRead?
    aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
  rw [baseComputed]
  simp
  rw [wholeComputed, restrictedComputed]
  simp
  rw [source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_of_tieSeam
    seam]
  cases centerC : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp
  | some perceivedCenter =>
      simp
      cases trackedC :
          source.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?
            restrictedFrame with
      | none => simp
      | some tracked =>
          simp
          repeat rw [Option.bind_assoc]
          rfl

/-- Whole-state specialization of the conditional corrected transport: the only remaining premise
for a general internal target is the corrected tie seam between the two actual key frames. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_keyFrameTieSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (ruleFuel : Nat)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some base)
    (wholeFrame restrictedFrame :
      source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (wholeComputed :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        (source.aromaticCanonicalWholeStateReader state) ruleFuel base.roots =
          some wholeFrame)
    (restrictedComputed :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        target (source.aromaticCanonicalDependencyView state target) ruleFuel base.roots =
          some restrictedFrame)
    (seam : source.AromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameTieSeam
      wholeFrame restrictedFrame) :
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state) target ruleFuel =
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
        target (source.aromaticCanonicalDependencyView state target) ruleFuel :=
  source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?_eq_descriptor?_of_keyFrameTieSeam
    target (source.aromaticCanonicalWholeStateReader state)
    (source.aromaticCanonicalDependencyView state target) ruleFuel base baseComputed
    wholeFrame restrictedFrame wholeComputed restrictedComputed seam

/-! ## Discharge of the corrected tie seam from actual four-ligand geometry

The two actual frames are built at one fuel on the same actual four-ligand roots.  Their Rule-3
half is literally shared.  For the corrected compound records on a tied pair the two actual slots
are classified by their actual addresses:

* two outward children obtain whole-`Option` equality of their compound computations from the
  shipped whole-state key agreement, hence literal key equality and therefore record equality;
* two parent slots coincide by actual parent-slot uniqueness, so both comparisons are the actual
  corrected diagonal record `{ordering := eq, pseudo := false}`;
* a parent/outward pair (in either order) cannot be tied at all, because the actual Rule-1b root
  distances differ and Rule 3 therefore already decides.

No tie condition, pair certificate or desired availability is assumed. -/

/-- **The corrected tie seam holds for the two actual frames.** -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_wholeState_ties_rule4aPrefixed
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some base)
    (wholeFrame restrictedFrame :
      source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (wholeComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      (source.aromaticCanonicalWholeStateReader state) fuel base.roots = some wholeFrame)
    (restrictedComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      (fun cursor => source.aromaticCanonicalDependencyLabel target
        (source.aromaticCanonicalDependencyView state target) cursor)
      fuel base.roots = some restrictedFrame)
    (leftIndex rightIndex : Fin 4)
    (tie : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (wholeFrame.keyAt leftIndex).rule3 (wholeFrame.keyAt rightIndex).rule3 =
        Ordering.eq) :
    source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5
        (wholeFrame.keyAt leftIndex).rule45 (wholeFrame.keyAt rightIndex).rule45 =
      source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5
        (restrictedFrame.keyAt leftIndex).rule45
        (restrictedFrame.keyAt rightIndex).rule45 := by
  obtain ⟨wholeLeftKey, wholeLeftComputed, wholeLeftEq⟩ :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule45
      wholeComputed base.rootsLength leftIndex
  obtain ⟨wholeRightKey, wholeRightComputed, wholeRightEq⟩ :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule45
      wholeComputed base.rootsLength rightIndex
  obtain ⟨restrictedLeftKey, restrictedLeftComputed, restrictedLeftEq⟩ :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule45
      restrictedComputed base.rootsLength leftIndex
  obtain ⟨restrictedRightKey, restrictedRightComputed, restrictedRightEq⟩ :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule45
      restrictedComputed base.rootsLength rightIndex
  have leftClass :=
    source.aromaticCanonicalOccurrenceFourLigandFrame_slot_address_classification
      target base baseComputed leftIndex
  have rightClass :=
    source.aromaticCanonicalOccurrenceFourLigandFrame_slot_address_classification
      target base baseComputed rightIndex
  by_cases leftParent :
      (base.cursorAt leftIndex).occurrence.1.address.length + 1 =
        target.1.address.length
  · by_cases rightParent :
        (base.cursorAt rightIndex).occurrence.1.address.length + 1 =
          target.1.address.length
    · -- Both slots sit at the actual parent address, hence they are the same slot.
      have indexEq : leftIndex = rightIndex :=
        source.aromaticCanonicalOccurrenceFourLigandFrame_parent_slot_unique
          target base baseComputed leftParent rightParent
      subst rightIndex
      rw [source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_self,
        source.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_self]
    · -- Parent on the left, outward child on the right: Rule 3 already decides.
      have rightOutward :
          target.1.address.length + 1 =
            (base.cursorAt rightIndex).occurrence.1.address.length := by
        rcases rightClass with parent | outward
        · omega
        · exact outward.1
      exact absurd tie
        (source.aromaticCanonicalOccurrenceFourLigandFrame_rule3_ne_of_parent_outward
          (source.aromaticCanonicalWholeStateReader state) target base baseComputed
          wholeFrame wholeComputed leftIndex rightIndex leftParent rightOutward)
  · -- The left slot is outward.
    have leftOutward :
        target.1.address.length + 1 =
          (base.cursorAt leftIndex).occurrence.1.address.length := by
      rcases leftClass with parent | outward
      · omega
      · exact outward.1
    by_cases rightParent :
        (base.cursorAt rightIndex).occurrence.1.address.length + 1 =
          target.1.address.length
    · -- Outward child on the left, parent on the right: Rule 3 already decides, in the
      -- reverse orientation.  Swap the tie with the oriented-comparator law.
      have strict :=
        source.aromaticCanonicalOccurrenceFourLigandFrame_rule3_ne_of_parent_outward
          (source.aromaticCanonicalWholeStateReader state) target base baseComputed
          wholeFrame wholeComputed rightIndex leftIndex rightParent leftOutward
      have tieReversed :
          source.compareAromaticCanonicalUncancelledRule3SpatialKeys
            (wholeFrame.keyAt rightIndex).rule3 (wholeFrame.keyAt leftIndex).rule3 =
              Ordering.eq := by
        letI : Std.TransCmp
            source.compareAromaticCanonicalUncancelledRule3SpatialKeys :=
          source.compareAromaticCanonicalUncancelledRule3SpatialKeys_transCmp
        rw [Std.OrientedCmp.eq_swap
          (cmp := source.compareAromaticCanonicalUncancelledRule3SpatialKeys)
          (a := (wholeFrame.keyAt rightIndex).rule3)
          (b := (wholeFrame.keyAt leftIndex).rule3), tie]
        rfl
      exact absurd tieReversed strict
    · -- Both slots are outward: the shipped whole-state key agreement applies slotwise.
      have leftPresent : base.cursorAt leftIndex ∈ base.roots := List.get_mem _ _
      have rightPresent : base.cursorAt rightIndex ∈ base.roots := List.get_mem _ _
      have leftKeyEq : wholeLeftKey = restrictedLeftKey := by
        apply Option.some.inj
        rw [← wholeLeftComputed, ← restrictedLeftComputed]
        exact
          source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_dependencyLabel_of_ligandRoot
            target state fuel (base.cursorAt leftIndex)
            (source.aromaticCanonicalOccurrenceFourLigandFrame?_roots_mem_rerootChildren
              target base baseComputed (base.cursorAt leftIndex) leftPresent)
            (by omega)
      have rightKeyEq : wholeRightKey = restrictedRightKey := by
        apply Option.some.inj
        rw [← wholeRightComputed, ← restrictedRightComputed]
        exact
          source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_dependencyLabel_of_ligandRoot
            target state fuel (base.cursorAt rightIndex)
            (source.aromaticCanonicalOccurrenceFourLigandFrame?_roots_mem_rerootChildren
              target base baseComputed (base.cursorAt rightIndex) rightPresent)
            (by omega)
      rw [wholeLeftEq, wholeRightEq, restrictedLeftEq, restrictedRightEq,
        leftKeyEq, rightKeyEq]

/-- **Parent/outward corrected comparison is strict and ordinary.**  At an actual frame, a parent
slot against an outward slot is already decided by the reader-free Rule 3, so the corrected frame
comparator never reaches the Rule-4a-prefixed Rules-4a--5 suffix: its ordering is strict and its
pseudoasymmetry flag is `false`.  This exposes the parent-insulation consequence used inside the
tie-seam discharge. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_parent_outward_strict
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some base)
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (frameComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      read fuel base.roots = some frame)
    (parentSlot outwardSlot : Fin 4)
    (parentLength :
      (base.cursorAt parentSlot).occurrence.1.address.length + 1 =
        target.1.address.length)
    (outwardLength :
      target.1.address.length + 1 =
        (base.cursorAt outwardSlot).occurrence.1.address.length) :
    (source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
        frame parentSlot outwardSlot).ordering ≠ Ordering.eq ∧
      (source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At
        frame parentSlot outwardSlot).pseudo = false := by
  have strict :=
    source.aromaticCanonicalOccurrenceFourLigandFrame_rule3_ne_of_parent_outward
      read target base baseComputed frame frameComputed parentSlot outwardSlot
      parentLength outwardLength
  generalize compared : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt parentSlot).rule3 (frame.keyAt outwardSlot).rule3 = outcome
  cases outcome
  · simp [compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At, compared]
  · exact absurd compared strict
  · have recordEq :=
      source.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_of_rule3_gt
        frame parentSlot outwardSlot compared
    rw [recordEq]
    simp

/-! ## Unconditional corrected whole-state descriptor equality for every target -/











theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel) :
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state) target
        (2 * (carrierFuel + 1)) =
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
        target (source.aromaticCanonicalDependencyView state target)
        (2 * (carrierFuel + 1)) := by
  cases baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target with
  | none =>
      unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
        aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
        aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidenceWithRead?
        aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
      rw [baseComputed]
      simp
  | some base =>
      cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
          (2 * (carrierFuel + 1)) base.roots with
      | none =>
          unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
            aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
            aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidenceWithRead?
            aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
          rw [baseComputed]
          simp [rule3Computed, buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?,
            buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?]
      | some rule3Frame =>
          by_cases rule3Length : rule3Frame.keys.length = 4
          · obtain ⟨wholeFrame, wholeComputed⟩ :=
              source.exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_at_twice_of_rule3Frame
                (source.aromaticCanonicalWholeStateReader state) base.roots rule3Frame
                rule3Computed base.rootsLength
                (source.aromaticCanonicalOccurrenceFourLigandFrame_roots_valid_model
                  target base baseComputed)
            obtain ⟨restrictedFrame, restrictedComputed⟩ :=
              source.exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_at_twice_of_rule3Frame
                target (source.aromaticCanonicalDependencyView state target) base.roots
                rule3Frame rule3Computed base.rootsLength
                (source.aromaticCanonicalOccurrenceFourLigandFrame_roots_valid_model
                  target base baseComputed)
            have restrictedWithRead :
                source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
                  (fun cursor => source.aromaticCanonicalDependencyLabel target
                    (source.aromaticCanonicalDependencyView state target) cursor)
                  (2 * (carrierFuel + 1)) base.roots = some restrictedFrame := by
              rw [source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_eq_rule3Through5KeyFrame?
                target (source.aromaticCanonicalDependencyView state target)]
              exact restrictedComputed
            exact
              source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_keyFrameTieSeam
                target state (2 * (carrierFuel + 1)) base baseComputed
                wholeFrame restrictedFrame wholeComputed restrictedComputed
                (AromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameTieSeam.of_computations
                  source (source.aromaticCanonicalWholeStateReader state) target
                  (source.aromaticCanonicalDependencyView state target)
                  (2 * (carrierFuel + 1)) base.roots wholeFrame restrictedFrame
                  wholeComputed restrictedWithRead
                  (source.aromaticCanonicalOccurrenceFourLigandFrame_wholeState_ties_rule4aPrefixed
                    target state base baseComputed wholeFrame restrictedFrame
                    wholeComputed restrictedWithRead))
          · unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
              aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
              aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidenceWithRead?
              aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
            rw [baseComputed]
            simp [rule3Computed, rule3Length,
              buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?,
              buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?]

/-! ## Corrected canonical descriptor characterization

The corrected canonical predicate stores only the actual corrected evidence builder, the actual
rational point handedness and the corrected pseudo-comparison count.  It does not store a
comparison record or a desired descriptor. -/

/-- Canonical corrected Rule-3--5 descriptor meaning at one target and dependency view. -/
def CanonicalAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) (descriptor : AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∃ evidence raw,
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
        target view ruleFuel = some evidence ∧
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons

/-- Success of the corrected descriptor is exactly the corrected canonical meaning. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) (descriptor : AromaticCanonicalAuxiliaryLabel) :
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
        target view ruleFuel = some descriptor ↔
      source.CanonicalAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor
        target view ruleFuel descriptor := by
  constructor
  · intro computed
    unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor? at computed
    cases evidenceComputed :
        source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidence?
          target view ruleFuel with
    | none => simp [evidenceComputed] at computed
    | some evidence =>
        cases rawComputed :
            CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points with
        | none => simp [evidenceComputed, rawComputed] at computed
        | some raw =>
            simp [evidenceComputed, rawComputed] at computed
            subst descriptor
            exact ⟨evidence, raw, evidenceComputed,
              (CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?_eq_some_iff
                evidence.points raw).mp rawComputed, rfl⟩
  · rintro ⟨evidence, raw, evidenceComputed, handedness, rfl⟩
    unfold aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
    rw [evidenceComputed]
    change (do
      let observed ←
        CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points
      some (classifyTetrahedralRSPseudo observed evidence.tracked.pseudoComparisons)) =
      some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)
    rw [(CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?_eq_some_iff
      evidence.points raw).mpr handedness]
    rfl

/-- Failure of the corrected descriptor is exactly the absence of any corrected canonical
meaning. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_none_iff_no_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) :
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
        target view ruleFuel = none ↔
      ¬ ∃ descriptor,
        source.CanonicalAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor
          target view ruleFuel descriptor := by
  constructor
  · intro refused ⟨descriptor, canonical⟩
    have accepted :=
      (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
        target view ruleFuel descriptor).mpr canonical
    rw [refused] at accepted
    contradiction
  · intro absent
    cases computed : source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
        target view ruleFuel with
    | none => rfl
    | some descriptor =>
        exact (absent ⟨descriptor,
          (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
            target view ruleFuel descriptor).mp computed⟩).elim

/-! ## Corrected complete-outcome semantics and its own reference state -/

/-- Declarative complete outcome of the corrected Rule-3--5 evaluator. -/
def DeclarativeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Outcome
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (ruleFuel : Nat) (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) : Prop :=
  match outcome with
  | none =>
      ¬ ∃ descriptor,
        source.CanonicalAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor
          target (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor
  | some descriptor =>
      source.CanonicalAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor
        target (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor

/-- The corrected declarative outcome is exactly the corrected restricted descriptor result. -/
theorem declarativeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Outcome_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (ruleFuel : Nat) (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) :
    source.DeclarativeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Outcome
        ruleFuel state target outcome ↔
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor? target
        (source.aromaticCanonicalDependencyView state target) ruleFuel = outcome := by
  cases outcome with
  | none =>
      exact (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_none_iff_no_canonical
        target (source.aromaticCanonicalDependencyView state target) ruleFuel).symm
  | some descriptor =>
      exact (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
        target (source.aromaticCanonicalDependencyView state target)
        ruleFuel descriptor).symm

/-- Corrected source-canonical occurrence semantics built from the corrected descriptor. -/
noncomputable def aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalRuleSemantics carrierFuel where
  DeclarativeDerivation :=
    source.DeclarativeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Outcome ruleFuel
  executableRule := fun target view =>
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
      target view ruleFuel
  derivation_executable_iff := by
    intro state target outcome
    exact source.declarativeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Outcome_iff
      ruleFuel state target outcome

/-- **The corrected semantics has exactly one complete occurrence model.** -/
theorem existsUnique_aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Model
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    ∃! state,
      (source.aromaticCanonicalOccurrenceSystem
        (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel ruleFuel)).CIPModel state :=
  source.existsUnique_aromaticCanonicalCIPModel
    (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel)

/-- Every label in any corrected concrete model is exactly one corrected canonical occurrence
result. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Model_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (descriptor : AromaticCanonicalAuxiliaryLabel) :
    state target = some descriptor ↔
      source.CanonicalAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor target
        (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor := by
  have fixed :=
    (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)).cipModel_iff_executableStateStep_fixed
      (source.aromaticCanonicalDerivationStepCorrespondence
        (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel ruleFuel)) state |>.mp model
  have atTarget := congrFun fixed target
  rw [← atTarget]
  exact source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
    target (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor

/-- **The corrected restricted reference state.**  It is the decoded causal closure of the
*corrected* semantics; the legacy reference state is not reused, and no equality with legacy
outputs is assumed. -/
noncomputable def aromaticCanonicalRule4aPrefixedRestrictedReferenceState
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} (ruleFuel : Nat) :
    source.AromaticCanonicalAuxiliaryState carrierFuel :=
  DeclarativeCIP.OccurrenceScheduler.decode
    (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel))
    (@source.AromaticCanonicalDepthDependency carrierFuel)
    (DeclarativeCIP.OccurrenceScheduler.closure
      (source.aromaticCanonicalOccurrenceSystem
        (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel ruleFuel))
      (@source.AromaticCanonicalDepthDependency carrierFuel))

/-- The corrected restricted reference state is a complete corrected model. -/
theorem aromaticCanonicalRule4aPrefixedRestrictedReferenceState_cipModel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} (ruleFuel : Nat) :
    (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)).CIPModel
      (source.aromaticCanonicalRule4aPrefixedRestrictedReferenceState ruleFuel) :=
  source.aromaticCanonicalSchedulerClosure_cipModel
    (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel)

/-! ## Actual full-state model -/

/-- A state is a corrected whole-state model when every coordinate equals the corrected descriptor
read from the **full state** at the same coordinate. -/
def AromaticCanonicalRule4aPrefixedWholeStateFixedPoint
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (ruleFuel : Nat) (state : source.AromaticCanonicalAuxiliaryState carrierFuel) : Prop :=
  ∀ target,
    state target =
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state) target ruleFuel

/-- **Model locality at the common fuel for every target.**  In the unique corrected model at rule
fuel `2 * (carrierFuel + 1)`, the stored label at **every** source-canonical occurrence target is
exactly the corrected whole-state descriptor computed there.  This composes the actual corrected
descriptor equality with the corrected canonical model characterization. -/
theorem aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Model_eq_descriptorWithRead?_of_wholeState
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel (2 * (carrierFuel + 1)))).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    state target =
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state) target
        (2 * (carrierFuel + 1)) := by
  let view := source.aromaticCanonicalDependencyView state target
  have locality :=
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_at_twice
      target state
  have modelIff : ∀ descriptor,
      state target = some descriptor ↔
        source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor? target view
          (2 * (carrierFuel + 1)) = some descriptor := by
    intro descriptor
    rw [source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Model_eq_some_iff_canonical
      state model target descriptor]
    exact (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
      target view (2 * (carrierFuel + 1)) descriptor).symm
  rw [locality]
  cases restricted : source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
      target view (2 * (carrierFuel + 1)) with
  | none =>
      cases stored : state target with
      | none => rfl
      | some descriptor =>
          have accepted := (modelIff descriptor).mp stored
          rw [restricted] at accepted
          cases accepted
  | some descriptor => exact (modelIff descriptor).mpr restricted

/-- The corrected restricted reference state is a full-state model at the common fuel. -/
theorem aromaticCanonicalRule4aPrefixedRestrictedReferenceState_wholeStateFixedPoint
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) :
    source.AromaticCanonicalRule4aPrefixedWholeStateFixedPoint
      (2 * (carrierFuel + 1))
      (source.aromaticCanonicalRule4aPrefixedRestrictedReferenceState
        (carrierFuel := carrierFuel) (2 * (carrierFuel + 1))) := by
  intro target
  exact
    source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Model_eq_descriptorWithRead?_of_wholeState
      (source.aromaticCanonicalRule4aPrefixedRestrictedReferenceState
        (carrierFuel := carrierFuel) (2 * (carrierFuel + 1)))
      (source.aromaticCanonicalRule4aPrefixedRestrictedReferenceState_cipModel
        (carrierFuel := carrierFuel) (2 * (carrierFuel + 1)))
      target

/-- A corrected whole-state fixed point is a complete model of the corrected semantics: the
whole-state entrypoint and the typed dependency-view entrypoint coincide at the common fuel, so
the full-state fixed-point equation is exactly executable regeneration. -/
theorem aromaticCanonicalRule4aPrefixedWholeStateFixedPoint_cipModel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (fixed : source.AromaticCanonicalRule4aPrefixedWholeStateFixedPoint
      (2 * (carrierFuel + 1)) state) :
    (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel (2 * (carrierFuel + 1)))).CIPModel state := by
  have stepEq :
      (source.aromaticCanonicalOccurrenceSystem
        (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel (2 * (carrierFuel + 1)))).executableStep state =
        state := by
    funext target
    have locality :=
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_at_twice
        target state
    calc
      (source.aromaticCanonicalOccurrenceSystem
        (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel (2 * (carrierFuel + 1)))).executableStep state target =
          source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?
            target (source.aromaticCanonicalDependencyView state target)
            (2 * (carrierFuel + 1)) := rfl
      _ = source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
            (source.aromaticCanonicalWholeStateReader state) target
            (2 * (carrierFuel + 1)) := locality.symm
      _ = state target := (fixed target).symm
  rw [(source.aromaticCanonicalOccurrenceSystem
    (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel (2 * (carrierFuel + 1)))).cipModel_iff_executableStateStep_fixed
    (source.aromaticCanonicalDerivationStepCorrespondence
      (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel (2 * (carrierFuel + 1)))) state]
  exact stepEq

/-- **Model iff actual full-state equations.**  At the common fuel, being a complete model of the
corrected semantics is equivalent to satisfying the actual corrected whole-state fixed-point
equations coordinatewise.  Both directions are proved: the forward direction is the corrected
local model characterization, the reverse direction is executable regeneration through the
corrected whole-state/dependency-view equality. -/
theorem aromaticCanonicalRule4aPrefixedCIPModel_iff_wholeStateFixedPoint
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel) :
    (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel (2 * (carrierFuel + 1)))).CIPModel state ↔
      source.AromaticCanonicalRule4aPrefixedWholeStateFixedPoint
        (2 * (carrierFuel + 1)) state := by
  constructor
  · intro model target
    exact
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Model_eq_descriptorWithRead?_of_wholeState
        state model target
  · intro fixed
    exact source.aromaticCanonicalRule4aPrefixedWholeStateFixedPoint_cipModel state fixed

/-- **Every actual full-state fixed point is the independently generated corrected reference
state.**  This is uniqueness against *all* states satisfying the corrected whole-state equations;
the witness is the decoded causal closure of the corrected semantics, not a legacy state. -/
theorem aromaticCanonicalRule4aPrefixedWholeStateFixedPoint_eq_restrictedReferenceState
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (fixed : source.AromaticCanonicalRule4aPrefixedWholeStateFixedPoint
      (2 * (carrierFuel + 1)) state) :
    state = source.aromaticCanonicalRule4aPrefixedRestrictedReferenceState
      (carrierFuel := carrierFuel) (2 * (carrierFuel + 1)) := by
  obtain ⟨witness, _witnessModel, unique⟩ :=
    source.existsUnique_aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Model
      carrierFuel (2 * (carrierFuel + 1))
  rw [unique state
      (source.aromaticCanonicalRule4aPrefixedWholeStateFixedPoint_cipModel state fixed),
    unique (source.aromaticCanonicalRule4aPrefixedRestrictedReferenceState
        (carrierFuel := carrierFuel) (2 * (carrierFuel + 1)))
      (source.aromaticCanonicalRule4aPrefixedRestrictedReferenceState_cipModel
        (carrierFuel := carrierFuel) (2 * (carrierFuel + 1)))]

/-- **The actual full-state model is unique.**  There is exactly one state whose every coordinate
is the corrected descriptor read from that same full state at fuel `2 * (carrierFuel + 1)`.  The
witness is the corrected restricted reference state; uniqueness is the uniqueness of the corrected
complete occurrence model, not legacy model sharing. -/
theorem existsUnique_aromaticCanonicalRule4aPrefixedWholeStateModel
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) :
    ∃! state : source.AromaticCanonicalAuxiliaryState carrierFuel,
      source.AromaticCanonicalRule4aPrefixedWholeStateFixedPoint
        (2 * (carrierFuel + 1)) state := by
  obtain ⟨witness, witnessModel, unique⟩ :=
    source.existsUnique_aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Model
      carrierFuel (2 * (carrierFuel + 1))
  refine ⟨witness, ?_, ?_⟩
  · intro target
    exact
      source.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Model_eq_descriptorWithRead?_of_wholeState
        witness witnessModel target
  · intro other otherFixed
    exact unique other
      (source.aromaticCanonicalRule4aPrefixedWholeStateFixedPoint_cipModel other otherFixed)

end AuthoritativeChemicalInput
end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedCompoundThroughRule5_self
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidenceWithRead?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5SpatialEvidenceWithRead?_eq_spatialEvidence?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?_eq_descriptor?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameTieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameTieSeam.of_computations
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_eq_of_tieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.safeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5TrackedOrder?_eq_of_tieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5FrameDescriptor?_eq_of_tieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?_eq_descriptor?_of_keyFrameTieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_keyFrameTieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5At_parent_outward_strict
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame_wholeState_ties_rule4aPrefixed
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.CanonicalAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Descriptor?_eq_none_iff_no_canonical
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.DeclarativeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Outcome
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.declarativeAromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Outcome_iff
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5AuxiliarySemantics
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.existsUnique_aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Model
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Model_eq_some_iff_canonical
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedRestrictedReferenceState
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedRestrictedReferenceState_cipModel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalRule4aPrefixedWholeStateFixedPoint
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedOccurrenceRule3Through5Model_eq_descriptorWithRead?_of_wholeState
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedRestrictedReferenceState_wholeStateFixedPoint
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedWholeStateFixedPoint_cipModel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedCIPModel_iff_wholeStateFixedPoint
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4aPrefixedWholeStateFixedPoint_eq_restrictedReferenceState
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.existsUnique_aromaticCanonicalRule4aPrefixedWholeStateModel
