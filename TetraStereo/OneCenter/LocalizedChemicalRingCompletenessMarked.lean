import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessStrict
import TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Generated-state meaning of the actual ring evaluator at every detected centre

`LocalizedChemicalRingCompletenessStrict` covers centres whose four arms already have distinct
independent empty-state keys. This module removes that restriction: at **every** detected centre
of the ring domain the output of the actual sparse evaluator is a closed-form function of two
independent data only — the physical configuration sign of the centre and the descending orders
of the independent keys evaluated on the **actually generated** auxiliary facts of the tied
children (`assignCenter_eq`, distant-reference twin `distant_assignCenter_eq`):

* strict empty-state keys: the uppercase letter of the physical sign in the key order;
* otherwise, for every eligible reference ligand (frame atoms in tied runs of the independent
  order, `tiedLigands`, characterised in `mem_tiedLigands_iff`), the reading is the physical sign
  in the descending order of the independent marked keys `markedKeys` (retained Rules 1–5 key then
  canonical marker) on the appended generated facts, or a refusal when those keys still tie or the
  facts conflict (`readingOf`); the output is the mirror case classification of the two consensus
  values for the original and reflected geometry, whose generated facts are themselves computed
  under the reflected geometry.

Consequences, all with the actual generated state and no sorting-success premise on the
evaluator itself:

* `assignCenter_of_separated`: if the generated facts separate every eligible reference with a
  common marked handedness `h`, and the facts generated under the reflected geometry separate
  them with handedness `h'`, then the centre receives the uppercase physical letter in the marked
  order when `h' = h` and the lowercase letter when `h' = -h`. This is the exact mechanism of
  pseudoasymmetry: lowercase arises precisely when reflecting the molecule reverses the marked
  priority order.
* `assignCenter_none_iff`, `assignCenter_none_of_reading_none`, `assignCenter_none_of_disagree`:
  refusal happens exactly when, for the original or reflected geometry, some eligible reference
  is unreadable (marked keys still tied, or conflicting generated facts) or two eligible
  references read different letters.

Hypotheses: intake agreement, admission, localized single bonds, simple-bonded graph (through
`RootData`), and calibrated coordinates at the centre. Rings, ring duplicates, arbitrary depth,
empty and multiple references are allowed. No desired label, acyclicity, rigidity or final
correctness is assumed. The remaining chemical converse — when the independent physical situation
forces `Separated` — is isolated by these statements, not proved here.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingOrderingTransport LocalizedChemicalRingCompletenessStrict
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedPromotedRanking LocalizedMarkedRetainedPromotedOperations
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations sparseOperations_eq)
open LocalizedMarkedOperationEvaluator (markedReading? underWith)
open LocalizedGenericMarkedRecalculation (Geometry readback? atomsAt? rankedAtoms? consistent strict
  caseFromMirror? mirror readback_mirror eligibleOf consensus appendFacts? structuralDepth
  caseFromMirror?_eq_swap caseFromMirror?_eq_same)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open scoped Classical

/-! ## Generic key-order facts on four slots -/

section Generic

variable {K : Type} [LinearOrder K]

/-- Strictness of the actual adjacent decisions is injectivity of the key family. -/
theorem strict_iff_injective (cmp : K → K → Ordering)
    (lt_iff : ∀ a b, cmp a b = Ordering.lt ↔ a < b)
    (eq_iff : ∀ a b, cmp a b = Ordering.eq ↔ a = b) (keys : Fin 4 → K) :
    strict (adjacentBy (fun a b => some (cmp (keys a) (keys b))) (keyOrder keys (List.finRange 4))) =
        true ↔ Function.Injective keys := by
  have split : strict (adjacentBy (fun a b => some (cmp (keys a) (keys b)))
      (keyOrder keys (List.finRange 4))) = true ↔
      ∀ decision ∈ adjacentBy (fun a b => some (cmp (keys a) (keys b)))
        (keyOrder keys (List.finRange 4)), decision = some Ordering.gt :=
    ⟨all_gt_of_strict _, strict_of_all_gt _⟩
  rw [split, adjacentBy_key_all_gt_iff cmp lt_iff eq_iff,
    keyOrder_chain_iff_injective _ _ (List.nodup_finRange 4)]
  constructor
  · intro h a b equal
    exact h a (List.mem_finRange a) b (List.mem_finRange b) equal
  · intro inj a _ b _ equal
    exact inj equal

theorem keyOrder_length (keys : Fin 4 → K) : (keyOrder keys (List.finRange 4)).length = 4 := by
  rw [(keyOrder_perm keys _).length_eq, List.length_finRange]

theorem keyOrder_nodup (keys : Fin 4 → K) : (keyOrder keys (List.finRange 4)).Nodup :=
  (keyOrder_perm keys _).nodup_iff.mpr (List.nodup_finRange 4)

/-- The frame slot at priority position `p` of the descending key order. -/
noncomputable def slotAt (keys : Fin 4 → K) (p : Fin 4) : Fin 4 :=
  (keyOrder keys (List.finRange 4))[p.val]'(by rw [keyOrder_length]; exact p.isLt)

theorem slotAt_injective (keys : Fin 4 → K) : Function.Injective (slotAt keys) := by
  intro p q equal
  exact Fin.ext ((keyOrder_nodup keys).getElem_inj_iff.mp equal)

/-- Priority positions to frame slots. -/
noncomputable def slotPerm (keys : Fin 4 → K) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (slotAt_injective keys))

theorem keyOrder_eq_slots (keys : Fin 4 → K) :
    keyOrder keys (List.finRange 4) =
      [slotPerm keys 0, slotPerm keys 1, slotPerm keys 2, slotPerm keys 3] :=
  list_four_eq _ (keyOrder_length keys)

end Generic

/-! ## Small list and option facts -/

theorem filterMap_eq_map_of {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a = some (g a)) → l.filterMap f = l.map g
  | [], _ => rfl
  | a :: l, h => by
      rw [List.map_cons, List.filterMap_cons_some (h a List.mem_cons_self),
        filterMap_eq_map_of f g l (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem rankedAtoms?_mk (atoms positions : List Nat) (unique : Bool) (count : Nat) :
    rankedAtoms? atoms { positions := positions, unique := unique, pseudoComparisons := count } =
      if unique = true then atomsAt? atoms positions else none := rfl

theorem consensus_map_const {α : Type} (l : List α) (ne : l ≠ []) (f : α → Option RS) (v : RS)
    (h : ∀ a ∈ l, f a = some v) : consensus (l.map f) = some v := by
  rw [consensus_eq_some_iff]
  refine ⟨fun empty => ne (List.map_eq_nil_iff.mp empty), ?_⟩
  intro e member
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
  exact h a ha

theorem consensus_map_none {α : Type} (l : List α) (f : α → Option RS) (a : α) (ha : a ∈ l)
    (refused : f a = none) : consensus (l.map f) = none := by
  cases h : consensus (l.map f) with
  | none => rfl
  | some v =>
      have all := ((consensus_eq_some_iff _ _).mp h).2 none (List.mem_map.mpr ⟨a, ha, refused⟩)
      cases all

theorem consensus_map_disagree {α : Type} (l : List α) (f : α → Option RS) (a b : α)
    (ha : a ∈ l) (hb : b ∈ l) (va vb : RS) (fa : f a = some va) (fb : f b = some vb)
    (ne : va ≠ vb) : consensus (l.map f) = none := by
  cases h : consensus (l.map f) with
  | none => rfl
  | some v =>
      have alla := ((consensus_eq_some_iff _ _).mp h).2 _ (List.mem_map.mpr ⟨a, ha, fa⟩)
      have allb := ((consensus_eq_some_iff _ _).mp h).2 _ (List.mem_map.mpr ⟨b, hb, fb⟩)
      exact absurd ((Option.some.inj alla).trans (Option.some.inj allb).symm) ne

theorem caseFromMirror?_eq_none_iff (x y : Option RS) :
    caseFromMirror? x y = none ↔ x = none ∨ y = none := by
  cases x <;> cases y <;> simp [caseFromMirror?]

theorem letterOfSign_neg (s : ℝ) (unit : s = 1 ∨ s = -1) :
    letterOfSign (-s) = (letterOfSign s).swap := by
  rcases unit with rfl | rfl <;> norm_num [letterOfSign, RS.swap]

theorem swap_swap (v : RS) : v.swap.swap = v := by cases v <;> rfl

theorem mul_unit {a b : ℝ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

/-! ## The actual root stages in independent terms -/

section Root

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (data : RootData input mol c)

/-- Ligand enumeration along a permutation of priority positions. -/
noncomputable def enumeration (π : Equiv.Perm (Fin 4)) : List Nat :=
  [(input.detectedMultiCenterMolecule.ligandAtomAt c (π 0)).val,
    (input.detectedMultiCenterMolecule.ligandAtomAt c (π 1)).val,
    (input.detectedMultiCenterMolecule.ligandAtomAt c (π 2)).val,
    (input.detectedMultiCenterMolecule.ligandAtomAt c (π 3)).val]

/-- Priority permutation of a key family on the frame slots: position `p` holds the ligand in
the slot of rank `p`. -/
noncomputable def rankPerm {K : Type} [LinearOrder K] (keys : Fin 4 → K) : Equiv.Perm (Fin 4) :=
  (slotPerm keys).trans data.ligandOf

theorem priorityPerm_eq_rankPerm :
    priorityPerm input mol single c data =
      rankPerm input mol c data (rootKeys input single data.target data.real data.detected) := by
  ext p
  rfl

theorem ranked_eq_rank {K : Type} [LinearOrder K] (keys : Fin 4 → K) :
    atomsAt? data.atoms ((keyOrder keys (List.finRange 4)).map data.read.index) =
      some (enumeration input c (rankPerm input mol c data keys)) := by
  rw [data.read.atoms, mapM_eq_some_map _
    (fun slot => (input.detectedMultiCenterMolecule.ligandAtomAt c (data.ligandOf slot)).val) _
    (fun slot _ => data.atomAt_eq slot), keyOrder_eq_slots]
  rfl

/-- The independent marked keys of the four root slots: retained Rules-1–5 key on the state,
then the actual marker for the reference, with the actual layout. Its equality to the independent
canonical marker is proved by `LocalizedMarkedRetainedCanonicalFrame.refinedKey_eq_canonical`. -/
noncomputable def markedKeys (temp : OccurrenceAuxState) (reference : input.Atom) :
    Fin 4 → RefinedKey :=
  refinedKey input single temp data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl reference
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))

theorem frames_frame (temp : OccurrenceAuxState) :
    (rawStateFrames input single temp data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame = data.frame := by
  have h := (rawStateFrames input single temp data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frameComputed
  rw [data.frameExec] at h
  exact (Option.some.inj h).symm

/-- The actual sparse marked stage at the root, for any state and in-range reference. -/
theorem marked_root (temp : OccurrenceAuxState) (mark : Nat)
    (bound : mark < input.certified.input.molecule.atomCount) :
    ∃ count, (sparseOperations input mol).marked temp (canonicalCenterRoot c.1.val) mark =
      some { positions := (keyOrder (markedKeys input mol single c data temp ⟨mark, bound⟩)
                (List.finRange 4)).map data.read.index,
             unique := strict (adjacentBy (fun left right => some (compare
                (markedKeys input mol single c data temp ⟨mark, bound⟩ left)
                (markedKeys input mol single c data temp ⟨mark, bound⟩ right)))
                (keyOrder (markedKeys input mol single c data temp ⟨mark, bound⟩)
                  (List.finRange 4))),
             pseudoComparisons := count } := by
  have oldTotal : ∀ a b, ∃ order,
      rawStateBefore input temp data.target data.frame a b = some order := by
    intro a b
    have h := rawStateBefore_eq_keys input single temp data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl a b
    rw [frames_frame input mol single c data temp] at h
    exact ⟨_, h⟩
  have newTotal : ∀ a b, ∃ order,
      LocalizedMarkedRetainedPromotedRanking.before input temp data.target ⟨mark, bound⟩
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) data.frame a b =
          some order := by
    intro a b
    have h := before_eq_refined input single temp data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl ⟨mark, bound⟩
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) a b
    rw [frames_frame input mol single c data temp] at h
    exact ⟨_, h⟩
  obtain ⟨count, counted⟩ := adjacentPromotionCount?_exists _ _ oldTotal newTotal
    (keyOrder (markedKeys input mol single c data temp ⟨mark, bound⟩) (List.finRange 4))
  refine ⟨count, ?_⟩
  rw [sparseOperations_eq]
  show marked? input mol temp (canonicalCenterRoot c.1.val) mark = _
  unfold marked? markedWithLayout?
  rw [dif_pos bound, data.found]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [data.rawFrame]
  simp only [Option.bind_some]
  rw [data.frameExec]
  simp only [Option.bind_some]
  rw [partition?_eq input single temp data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl ⟨mark, bound⟩]
  simp only [Option.bind_some]
  rw [data.read.positions]
  simp only [Option.bind_some]
  unfold markedKeys at counted ⊢
  rw [counted]
  rfl

/-- The actual marked reading at the root: the geometry read in the independent marked order
when those keys are injective, otherwise refusal. -/
theorem markedReading_root (geom : Geometry) (temp : OccurrenceAuxState) (mark : Nat)
    (bound : mark < input.certified.input.molecule.atomCount) :
    markedReading? mol (sparseOperations input mol) geom temp (canonicalCenterRoot c.1.val) mark =
      if Function.Injective (markedKeys input mol single c data temp ⟨mark, bound⟩) then
        readback? geom (enumeration input c
          (rankPerm input mol c data (markedKeys input mol single c data temp ⟨mark, bound⟩)))
      else none := by
  obtain ⟨count, h⟩ := marked_root input mol single c data temp mark bound
  unfold markedReading?
  rw [data.rawFrame]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [h]
  simp only [Option.bind_some]
  rw [rankedAtoms?_mk]
  by_cases inj : Function.Injective (markedKeys input mol single c data temp ⟨mark, bound⟩)
  · rw [if_pos ((strict_iff_injective compare refined_compare_lt_iff refined_compare_eq_iff _).mpr
      inj), ranked_eq_rank input mol c data, Option.bind_some, if_pos inj]
  · rw [if_neg (fun h => inj ((strict_iff_injective compare refined_compare_lt_iff
      refined_compare_eq_iff _).mp h)), Option.bind_none, if_neg inj]

/-- Ligand indices of the actual eligible references at the root: the frame atoms in tied runs
of the independent empty-state order, in the actual selection order. -/
noncomputable def tiedLigands : List (Fin 4) :=
  (tiedEntries false (sortedSlots input mol single c data)
    (adjacentBy (fun left right => some (compare
      (rootKeys input single data.target data.real data.detected left)
      (rootKeys input single data.target data.real data.detected right)))
      (sortedSlots input mol single c data))).map data.ligandOf

theorem eligible_root :
    eligibleOf data.atoms ((sortedSlots input mol single c data).map data.read.index)
        (adjacentBy (fun left right => some (compare
          (rootKeys input single data.target data.real data.detected left)
          (rootKeys input single data.target data.real data.detected right)))
          (sortedSlots input mol single c data)) =
      (tiedLigands input mol single c data).map
        (fun i => (input.detectedMultiCenterMolecule.ligandAtomAt c i).val) := by
  rw [eligibleOf_tiedEntries]
  unfold tiedLigands
  rw [List.map_map]
  apply filterMap_eq_map_of
  intro slot _
  simp only [Function.comp_apply, data.read.atom slot, data.atomAt_eq slot]

/-- A ligand is an eligible reference exactly when another ligand has the same independent
empty-state key. -/
theorem mem_tiedLigands_iff (i : Fin 4) :
    i ∈ tiedLigands input mol single c data ↔
      ∃ j, j ≠ i ∧ rootKeys input single data.target data.real data.detected (data.ligandOf.symm j) =
        rootKeys input single data.target data.real data.detected (data.ligandOf.symm i) := by
  unfold tiedLigands
  rw [List.mem_map]
  constructor
  · rintro ⟨slot, member, rfl⟩
    rw [tiedEntries_mem compare completeLigandRule5Key_compare_eq_iff _ _
      (sortedSlots_nodup input mol single c data) (keyOrder_pairwise _ _)] at member
    obtain ⟨_, other, _, ne, equal⟩ := member
    refine ⟨data.ligandOf other, fun h => ne (data.ligandOf.injective h), ?_⟩
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact equal
  · rintro ⟨j, ne, equal⟩
    refine ⟨data.ligandOf.symm i, ?_, Equiv.apply_symm_apply _ _⟩
    rw [tiedEntries_mem compare completeLigandRule5Key_compare_eq_iff _ _
      (sortedSlots_nodup input mol single c data) (keyOrder_pairwise _ _)]
    exact ⟨(sortedSlots_perm input mol single c data).mem_iff.mpr (List.mem_finRange _),
      data.ligandOf.symm j,
      (sortedSlots_perm input mol single c data).mem_iff.mpr (List.mem_finRange _),
      fun h => ne (data.ligandOf.symm.injective h), equal⟩

theorem tiedLigands_ne_nil
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected)) :
    tiedLigands input mol single c data ≠ [] := by
  intro empty
  apply notInj
  intro a b equal
  by_contra ne
  have member : data.ligandOf a ∈ tiedLigands input mol single c data := by
    rw [mem_tiedLigands_iff]
    refine ⟨data.ligandOf b, fun h => ne (data.ligandOf.injective h).symm, ?_⟩
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact equal.symm
  rw [empty] at member
  simp at member

/-- The reading of one eligible reference ligand from the generated facts `under`: the actual
marked step on the appended state. -/
noncomputable def readingOf (geom : Geometry) (under : Nat → OccurrenceAuxState) (i : Fin 4) :
    Option RS :=
  (appendFacts? [] (under (input.detectedMultiCenterMolecule.ligandAtomAt c i).val)).bind fun temp =>
    if Function.Injective (markedKeys input mol single c data temp
        (input.detectedMultiCenterMolecule.ligandAtomAt c i)) then
      readback? geom (enumeration input c (rankPerm input mol c data
        (markedKeys input mol single c data temp (input.detectedMultiCenterMolecule.ligandAtomAt c i))))
    else none

theorem readingOf_mirror (geom : Geometry) (under : Nat → OccurrenceAuxState) (i : Fin 4) :
    readingOf input mol single c data (mirror geom) under i =
      (readingOf input mol single c data geom under i).map RS.swap := by
  unfold readingOf
  cases appendFacts? [] (under (input.detectedMultiCenterMolecule.ligandAtomAt c i).val) with
  | none => rfl
  | some temp =>
      rw [Option.bind_some, Option.bind_some]
      split_ifs
      · exact readback_mirror _ _
      · rfl

/-- **The actual root step in independent terms**, for any geometry and any child facts. -/
theorem rawStep_root (geom : Geometry) (under : Nat → OccurrenceAuxState) :
    LocalizedMarkedOperationEvaluator.rawStep? mol (sparseOperations input mol) geom [] none
        (canonicalCenterRoot c.1.val) under =
      if Function.Injective (rootKeys input single data.target data.real data.detected) then
        readback? geom (enumeration input c (priorityPerm input mol single c data))
      else consensus ((tiedLigands input mol single c data).map
        (readingOf input mol single c data geom under)) := by
  have ord : (sparseOperations input mol).ordinary [] (canonicalCenterRoot c.1.val) = _ :=
    ordinary_root input mol single c data
  unfold LocalizedMarkedOperationEvaluator.rawStep?
  rw [data.rawFrame, ord]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have good : ¬ (¬ data.atoms.Nodup ∨ consistent (adjacentBy (fun left right => some (compare
      (rootKeys input single data.target data.real data.detected left)
      (rootKeys input single data.target data.real data.detected right)))
      (sortedSlots input mol single c data)) = false) := by
    rw [consistent_root input mol single c data]
    simp [data.nodup]
  rw [if_neg good]
  by_cases inj : Function.Injective (rootKeys input single data.target data.real data.detected)
  · rw [if_pos (strict_root input mol single c data inj), ranked_eq input mol single c data,
      Option.bind_some, if_pos inj]
    rfl
  · have notStrict : ¬ strict (adjacentBy (fun left right => some (compare
        (rootKeys input single data.target data.real data.detected left)
        (rootKeys input single data.target data.real data.detected right)))
        (sortedSlots input mol single c data)) = true := by
      rw [strict_iff_injective compare completeLigandRule5Key_compare_lt_iff
        completeLigandRule5Key_compare_eq_iff]
      exact inj
    rw [if_neg notStrict, if_neg inj]
    show consensus _ = _
    rw [eligible_root input mol single c data, List.map_map]
    apply congrArg consensus
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    unfold readingOf
    congr 1
    funext temp
    exact markedReading_root input mol single c data geom temp _
      (input.detectedMultiCenterMolecule.ligandAtomAt c i).isLt

end Root

/-! ## Chemical endpoints -/

section Endpoints

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (c : input.detectedMultiCenterMolecule.Center)
  (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)

/-- The actually generated facts of the tied children under inherited reference `r`
(immediate-frame recursion, actual sparse operations, structural depth). -/
noncomputable def generated (geom : Geometry) : Nat → OccurrenceAuxState :=
  underWith mol (sparseOperations input mol) geom [] (canonicalCenterRoot c.1.val)
    (LocalizedMarkedOperationEvaluator.facts mol (sparseOperations input mol)
      (structuralDepth mol (canonicalCenterRoot c.1.val)))

/-- The same for the distant-reference recursion. -/
noncomputable def distantGenerated (geom : Geometry) : Nat → OccurrenceAuxState :=
  underWith mol (sparseOperations input mol) geom [] (canonicalCenterRoot c.1.val)
    (LocalizedPhysicalMarkedDistantEvaluator.facts mol (sparseOperations input mol)
      (structuralDepth mol (canonicalCenterRoot c.1.val)))

include calibrated in
theorem readback_enum (π : Equiv.Perm (Fin 4)) :
    readback? (inputGeometry input) (enumeration input c π) =
      some (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c *
        permHandedness π)) :=
  readback_enumeration input cfg c calibrated π

include calibrated in
/-- **Generated-state meaning of the actual output at any detected centre.** -/
theorem assignCenter_eq (data : RootData input mol c) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val =
      if Function.Injective (rootKeys input single data.target data.real data.detected) then
        some (.chiral (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c *
          permHandedness (priorityPerm input mol single c data))))
      else caseFromMirror?
        (consensus ((tiedLigands input mol single c data).map
          (readingOf input mol single c data (inputGeometry input)
            (generated input mol c (inputGeometry input)))))
        (consensus ((tiedLigands input mol single c data).map
          (readingOf input mol single c data (mirror (inputGeometry input))
            (generated input mol c (mirror (inputGeometry input)))))) := by
  unfold LocalizedMarkedOperationEvaluator.assignCenter? LocalizedMarkedOperationEvaluator.descriptor?
    LocalizedMarkedOperationEvaluator.descriptorWith? LocalizedMarkedOperationEvaluator.rawWith?
  rw [rawStep_root input mol single c data, rawStep_root input mol single c data]
  by_cases inj : Function.Injective (rootKeys input single data.target data.real data.detected)
  · rw [if_pos inj, if_pos inj, if_pos inj, readback_mirror, readback_enum input cfg c calibrated]
    simp [caseFromMirror?, swap_ne]
  · rw [if_neg inj, if_neg inj, if_neg inj]
    rfl

include calibrated in
/-- The distant-reference recursion has the same meaning with its own generated facts. -/
theorem distant_assignCenter_eq (data : RootData input mol c) :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val =
      if Function.Injective (rootKeys input single data.target data.real data.detected) then
        some (.chiral (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c *
          permHandedness (priorityPerm input mol single c data))))
      else caseFromMirror?
        (consensus ((tiedLigands input mol single c data).map
          (readingOf input mol single c data (inputGeometry input)
            (distantGenerated input mol c (inputGeometry input)))))
        (consensus ((tiedLigands input mol single c data).map
          (readingOf input mol single c data (mirror (inputGeometry input))
            (distantGenerated input mol c (mirror (inputGeometry input)))))) := by
  unfold LocalizedPhysicalMarkedDistantEvaluator.assignCenter?
    LocalizedPhysicalMarkedDistantEvaluator.descriptor?
    LocalizedPhysicalMarkedDistantEvaluator.descriptorWith?
    LocalizedPhysicalMarkedDistantEvaluator.rawWith?
  rw [LocalizedPhysicalMarkedDistantReference.rawStep_none,
    LocalizedPhysicalMarkedDistantReference.rawStep_none,
    rawStep_root input mol single c data, rawStep_root input mol single c data]
  by_cases inj : Function.Injective (rootKeys input single data.target data.real data.detected)
  · rw [if_pos inj, if_pos inj, if_pos inj, readback_mirror, readback_enum input cfg c calibrated]
    simp [caseFromMirror?, swap_ne]
  · rw [if_neg inj, if_neg inj, if_neg inj]
    rfl

/-- The generated facts `under` separate every eligible reference, with a common handedness `h`
of the independent marked order. -/
def Separated (data : RootData input mol c) (under : Nat → OccurrenceAuxState) (h : ℝ) : Prop :=
  ∀ i ∈ tiedLigands input mol single c data, ∃ temp,
    appendFacts? [] (under (input.detectedMultiCenterMolecule.ligandAtomAt c i).val) = some temp ∧
    Function.Injective (markedKeys input mol single c data temp
      (input.detectedMultiCenterMolecule.ligandAtomAt c i)) ∧
    permHandedness (rankPerm input mol c data (markedKeys input mol single c data temp
      (input.detectedMultiCenterMolecule.ligandAtomAt c i))) = h

include calibrated in
theorem readingOf_eq_of_separated (data : RootData input mol c) (under : Nat → OccurrenceAuxState)
    (h : ℝ) (sep : Separated input mol single c data under h) (i : Fin 4)
    (mem : i ∈ tiedLigands input mol single c data) :
    readingOf input mol single c data (inputGeometry input) under i =
      some (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)) := by
  obtain ⟨temp, app, inj, hand⟩ := sep i mem
  unfold readingOf
  rw [app, Option.bind_some, if_pos inj, readback_enum input cfg c calibrated, hand]

include calibrated in
/-- Mirror case classification of separated readings: uppercase when the facts generated under
the reflected geometry keep the marked handedness, lowercase when they reverse it. -/
theorem case_of_separated (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (h h' : ℝ) (under under' : Nat → OccurrenceAuxState)
    (sep : Separated input mol single c data under h)
    (sep' : Separated input mol single c data under' h') :
    caseFromMirror?
        (consensus ((tiedLigands input mol single c data).map
          (readingOf input mol single c data (inputGeometry input) under)))
        (consensus ((tiedLigands input mol single c data).map
          (readingOf input mol single c data (mirror (inputGeometry input)) under'))) =
      if h' = h then
        some (.chiral (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)))
      else some (.pseudoasymmetric (pseudoRSOfRS
        (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)))) := by
  have ne := tiedLigands_ne_nil input mol single c data notInj
  obtain ⟨i, mem⟩ := List.exists_mem_of_ne_nil _ ne
  obtain ⟨_, _, _, hEq⟩ := sep i mem
  obtain ⟨_, _, _, hEq'⟩ := sep' i mem
  have hUnit : h = 1 ∨ h = -1 := by
    rw [← hEq]
    exact permHandedness_eq_one_or_eq_neg_one _
  have hUnit' : h' = 1 ∨ h' = -1 := by
    rw [← hEq']
    exact permHandedness_eq_one_or_eq_neg_one _
  have sUnit := configurationSign_unit input cfg c
  rw [consensus_map_const _ ne _ _
      (fun j mj => readingOf_eq_of_separated input mol single cfg c calibrated data under h sep j mj),
    consensus_map_const _ ne _
      (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h')).swap
      (fun j mj => by
        rw [readingOf_mirror, readingOf_eq_of_separated input mol single cfg c calibrated data
          under' h' sep' j mj]
        rfl)]
  by_cases same : h' = h
  · rw [if_pos same, same, caseFromMirror?_eq_swap]
  · rw [if_neg same]
    have neg : h' = -h := by
      rcases hUnit with rfl | rfl <;> rcases hUnit' with rfl | rfl
      · exact absurd rfl same
      · norm_num
      · norm_num
      · exact absurd rfl same
    rw [neg, mul_neg, letterOfSign_neg _ (mul_unit sUnit hUnit), swap_swap, caseFromMirror?_eq_same]

include calibrated in
/-- **Completeness on the actual generated state.** When the generated facts separate every
eligible reference with common handedness `h` (original geometry) and `h'` (reflected
geometry), the centre receives the physical letter in the marked order: uppercase for `h' = h`,
lowercase for `h' = -h`. -/
theorem assignCenter_of_separated (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (h h' : ℝ)
    (sep : Separated input mol single c data (generated input mol c (inputGeometry input)) h)
    (sep' : Separated input mol single c data
      (generated input mol c (mirror (inputGeometry input))) h') :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val =
      if h' = h then
        some (.chiral (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)))
      else some (.pseudoasymmetric (pseudoRSOfRS
        (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)))) := by
  rw [assignCenter_eq input mol single cfg c calibrated data, if_neg notInj]
  exact case_of_separated input mol single cfg c calibrated data notInj h h' _ _ sep sep'

include calibrated in
theorem distant_assignCenter_of_separated (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (h h' : ℝ)
    (sep : Separated input mol single c data (distantGenerated input mol c (inputGeometry input)) h)
    (sep' : Separated input mol single c data
      (distantGenerated input mol c (mirror (inputGeometry input))) h') :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val =
      if h' = h then
        some (.chiral (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)))
      else some (.pseudoasymmetric (pseudoRSOfRS
        (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)))) := by
  rw [distant_assignCenter_eq input mol single cfg c calibrated data, if_neg notInj]
  exact case_of_separated input mol single cfg c calibrated data notInj h h' _ _ sep sep'

include calibrated in
/-- **Exact refusal condition** at a constitutionally tied centre. -/
theorem assignCenter_none_iff (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected)) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val = none ↔
      consensus ((tiedLigands input mol single c data).map
        (readingOf input mol single c data (inputGeometry input)
          (generated input mol c (inputGeometry input)))) = none ∨
      consensus ((tiedLigands input mol single c data).map
        (readingOf input mol single c data (mirror (inputGeometry input))
          (generated input mol c (mirror (inputGeometry input))))) = none := by
  rw [assignCenter_eq input mol single cfg c calibrated data, if_neg notInj,
    caseFromMirror?_eq_none_iff]

include calibrated in
/-- An unreadable eligible reference (marked keys still tied on the generated facts, or
conflicting facts) forces refusal. -/
theorem assignCenter_none_of_reading_none (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (i : Fin 4) (mem : i ∈ tiedLigands input mol single c data)
    (refused : readingOf input mol single c data (inputGeometry input)
      (generated input mol c (inputGeometry input)) i = none) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val = none := by
  rw [assignCenter_none_iff input mol single cfg c calibrated data notInj]
  exact Or.inl (consensus_map_none _ _ i mem refused)

include calibrated in
/-- Two eligible references reading different letters force refusal. -/
theorem assignCenter_none_of_disagree (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (i j : Fin 4) (mi : i ∈ tiedLigands input mol single c data)
    (mj : j ∈ tiedLigands input mol single c data) (vi vj : RS)
    (ri : readingOf input mol single c data (inputGeometry input)
      (generated input mol c (inputGeometry input)) i = some vi)
    (rj : readingOf input mol single c data (inputGeometry input)
      (generated input mol c (inputGeometry input)) j = some vj) (ne : vi ≠ vj) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val = none := by
  rw [assignCenter_none_iff input mol single cfg c calibrated data notInj]
  exact Or.inl (consensus_map_disagree _ _ i j mi mj vi vj ri rj ne)

end Endpoints

end TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.strict_iff_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.ranked_eq_rank
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.marked_root
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.markedReading_root
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.eligible_root
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.mem_tiedLigands_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.tiedLigands_ne_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.readingOf_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.rawStep_root
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.assignCenter_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.distant_assignCenter_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.case_of_separated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.assignCenter_of_separated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.distant_assignCenter_of_separated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.assignCenter_none_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.assignCenter_none_of_reading_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked.assignCenter_none_of_disagree
