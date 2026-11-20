import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusStabilizer
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmTwin
import TetraStereo.OneCenter.LocalizedChemicalRingInheritedFixedReferenceRefusal
import TetraStereo.OneCenter.LocalizedChemicalRingContextIndependence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

/-!
Reference independence of the actual generated facts in the four root arms.

An inherited root mark enters the recursion only through a marked reading at a tied occurrence.
Inside arm `a` the mark `a` itself is sealed by the history, so an actual ordinary tie is an
actual marked tie and reconstructs a symmetry fixing the history and `a`. The finite
classification then leaves two cases: the spoke rotation fixes the history and every root mark,
and refuses every root-mark reading; or the occurrence is `o+` or `o-`, where the accepted
separation shows the ordinary keys are in fact injective. With injective ordinary keys the
marker never decides, so all root-mark readings coincide.

The conclusion is equality of the actual recursively generated fact lists for all four root
marks, on both geometry sides. No label value, reading success or marker comparison is assumed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusContext

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitAllCalibration
open LocalizedChemicalRingReferenceOrbitStabilizer
open LocalizedChemicalRingReferenceConsensusSymmetry LocalizedChemicalRingReferenceConsensusStabilizer
open LocalizedChemicalRingReferenceConsensusArmPrior LocalizedChemicalRingReferenceConsensusArmBranch
open LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingSenseTransport (factsWith factsWith_succ descriptorWith)
open LocalizedChemicalRingCompletenessMarked (slotPerm keyOrder_eq_slots enumeration)
open LocalizedChemicalRingPhysicalSense (inputGeometry relabelOf relabelOf_val atomOf center_of_degree
  readback_none_of_not_good inputGeometry_outside count)
open LocalizedActualBoundaryObservationReadback (outwardChild_node_mem)
open LocalizedActualOutwardRule1bEquivalence (ActualOutwardSiblingPair)
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader
open LocalizedMarkedReachableConfigurations (Reached reached_root reached_child)
open LocalizedMarkedTerminalReferenceScope (Descends descendant_reached history_mono)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachedFrameNeighbors (frame_atoms_perm_neighbors reached_atom_valid)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedConfigurationTransport (readback_none_of_missing)
open LocalizedMarkedCyclicDiscardedReference (rankedAtoms_subset)
open LocalizedMarkedOperationEvaluator (markedReading? tiedChildren mem_tiedChildren_actual)
open LocalizedPhysicalMarkedDistantReference (inheritedRead?)
open LocalizedChemicalRingOutwardKeyWitness (actual_outward_default_tie_witness)
open LocalizedChemicalRingOrientationInduction (mirror_mirror)
open LocalizedGenericMarkedRecalculation (frameAtoms? frameAtomsOf frameAtoms?_forcedLeaf readback?
  appendFacts? mirror readback_mirror structuralDepth flatMap_congr_mem)

/-- The four actually eligible root references. -/
def RootMark (m : Fin 46) : Prop := m = 28 ∨ m = 29 ∨ m = 30 ∨ m = 31

/-! ## Injective ordinary keys decide the marked order -/

section Order

variable {A B : Type} [LinearOrder A] [LinearOrder B]

theorem keyOrder_lex_eq (P : Fin 4 → A) (M : Fin 4 → B) (injective : Function.Injective P) :
    keyOrder (fun s => toLex (P s, M s)) (List.finRange 4) = keyOrder P (List.finRange 4) := by
  have nodup := (keyOrder_perm P (List.finRange 4)).nodup_iff.mpr (List.nodup_finRange 4)
  have first : (keyOrder (fun s => toLex (P s, M s)) (List.finRange 4)).Pairwise
      (fun a b => P b ≤ P a) := (keyOrder_pairwise _ _).imp (by
    intro a b le
    rcases Prod.Lex.toLex_le_toLex.mp le with lt | ⟨eq, _⟩
    · exact le_of_lt lt
    · exact le_of_eq eq)
  have second := keyOrder_pairwise P (List.finRange 4)
  have perm := (keyOrder_perm (fun s => toLex (P s, M s)) (List.finRange 4)).trans
    (keyOrder_perm P (List.finRange 4)).symm
  exact perm.eq_of_pairwise (fun a b _ _ ab ba => injective (le_antisymm ba ab)) first second

theorem slotPerm_lex_eq (P : Fin 4 → A) (M : Fin 4 → B) (injective : Function.Injective P) :
    slotPerm (fun s => toLex (P s, M s)) = slotPerm P := by
  have same := keyOrder_lex_eq P M injective
  rw [keyOrder_eq_slots, keyOrder_eq_slots] at same
  simp only [List.cons.injEq, and_true] at same
  apply Equiv.ext
  intro i
  fin_cases i
  · exact same.1
  · exact same.2.1
  · exact same.2.2.1
  · exact same.2.2.2

end Order

noncomputable section
open scoped Classical

/-! ## Readings as marked key orders -/

abbrev gen (node : RawMolecule.CanonicalBranchNode) (depth : Nat) (side : Bool) (mark : Nat) :
    OccurrenceAuxState :=
  generated certified mol node depth side mark

abbrev reading (node : RawMolecule.CanonicalBranchNode) (depth : Nat) (side : Bool) (mark : Nat) :
    Option RS :=
  inheritedRead? mol (sparseOperations certified mol) (observedGeometry certified side) [] node
    (generated certified mol node depth side) mark

private theorem rawSingle : LocalizedMarkedReachedFrameNeighbors.SingleBonded mol :=
  raw_single mol certified structure_agreement admissible.1.1 admissible.1.2 supported single_bonded

theorem reading_eq_marked (node : RawMolecule.CanonicalBranchNode) (depth : Nat) (side : Bool)
    (mark : Nat) :
    reading node depth side mark =
      markedReading? mol (sparseOperations certified mol) (observedGeometry certified side)
        (gen node depth side mark) node mark := by
  have extension := LocalizedChemicalRingCompletenessGeneratedFacts.extension_succeeds
    LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations certified mol)
    admissible.1.1 rawSingle admissible.1.2 depth (observedGeometry certified side) node mark
  change appendFacts? [] (gen node depth side mark) = some (gen node depth side mark) at extension
  unfold reading inheritedRead?
  change ((appendFacts? [] (gen node depth side mark)).bind fun temp =>
    markedReading? mol (sparseOperations certified mol) (observedGeometry certified side) temp node
      mark) = _
  rw [extension, Option.bind_some]

theorem reading_none_of_frame_none (node : RawMolecule.CanonicalBranchNode) (depth : Nat)
    (side : Bool) (mark : Nat) (noFrame : frameAtoms? mol node = none) :
    reading node depth side mark = none := by
  rw [reading_eq_marked]
  simp [markedReading?, noFrame]

theorem reading_none_of_three (node : RawMolecule.CanonicalBranchNode) (depth : Nat)
    (side : Bool) (mark : Nat) (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (three : (mol.canonicalIncidentNeighbors node.atom).length = 3)
    (perm : atoms.Perm (mol.canonicalIncidentNeighbors node.atom ++ [mol.atomCount])) :
    reading node depth side mark = none := by
  have original : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) →
      readback? (inputGeometry certified) L = none := by
    intro L sub
    have phantomNone : inputGeometry certified mol.atomCount = none :=
      inputGeometry_outside certified _ (by rw [count mol certified structure_agreement])
    by_cases phantom : mol.atomCount ∈ L
    · exact readback_none_of_missing _ L _ phantom phantomNone
    · have subNeighbors : ∀ y ∈ L, y ∈ mol.canonicalIncidentNeighbors node.atom := by
        intro y hy
        have member := perm.mem_iff.mp (sub y hy)
        rw [List.mem_append, List.mem_singleton] at member
        rcases member with inside | isPhantom
        · exact inside
        · exact absurd (isPhantom ▸ hy) phantom
      apply readback_none_of_not_good
      rintro ⟨four, nodup⟩
      have := (nodup.subperm subNeighbors).length_le
      rw [four, three] at this
      omega
  have observed : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) →
      readback? (observedGeometry certified side) L = none := by
    intro L sub
    cases side with
    | false => exact original L sub
    | true =>
        change readback? (mirror (inputGeometry certified)) L = none
        rw [readback_mirror, original L sub]
        rfl
  rw [reading_eq_marked]
  unfold markedReading?
  rw [frame]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases (sparseOperations certified mol).marked (gen node depth side mark) node mark with
  | none => rfl
  | some ranking =>
      simp only [Option.bind_some]
      cases h : LocalizedGenericMarkedRecalculation.rankedAtoms? atoms ranking with
      | none => rfl
      | some ranked =>
          simp only [Option.bind_some]
          exact observed ranked (rankedAtoms_subset atoms ranking ranked h)

/-- With injective ordinary keys the marked rank is the ordinary rank, for every reference. -/
theorem rank_marked_eq (c : physical.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData certified mol c node) (state : OccurrenceAuxState) (mark : Fin 46)
    (injective : Function.Injective (rawStateKeys certified single_bonded state data.target data.real
      ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl)) :
    rank certified mol c node data (markedKeys certified mol single_bonded c node data state mark) =
      rank certified mol c node data (rawStateKeys certified single_bonded state data.target data.real
        ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl) := by
  unfold rank
  congr 1
  exact slotPerm_lex_eq _ _ injective

/-- Injective ordinary keys determine the reading, independently of the reference marker. -/
theorem reading_of_prior_injective (c : physical.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData certified mol c node) (depth : Nat) (side : Bool) (mark : Fin 46)
    (injective : Function.Injective (rawStateKeys certified single_bonded (gen node depth side mark.val)
      data.target data.real ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl)) :
    reading node depth side mark.val =
      readback? (observedGeometry certified side) (enumeration certified c
        (rank certified mol c node data (rawStateKeys certified single_bonded
          (gen node depth side mark.val) data.target data.real
          ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl))) := by
  rw [reading_eq_marked, marked_reading_eq certified mol single_bonded c node data]
  have keysInjective : Function.Injective (markedKeys certified mol single_bonded c node data
      (gen node depth side mark.val) mark) := by
    intro a b same
    apply injective
    exact congrArg (fun key : RefinedKey => (ofLex key).1) same
  rw [if_pos keysInjective, rank_marked_eq c node data _ mark injective]

/-! ## From an ordinary tie to a history- and arm-fixing symmetry -/

private theorem sealed_core (a b : Fin 46) (node : RawMolecule.CanonicalBranchNode)
    (path : Descends mol (nodeOf [0, a.val]) node) (notStart : node.atom ≠ a.val)
    (children : mol.canonicalChildren (nodeOf [0, a.val]) = [nodeOf [0, a.val, b.val]])
    (neighbors : ∀ n : Fin 46, graph.Adj n a → n = 0 ∨ n = b) :
    ∀ n : Fin 46, graph.Adj n a → n.val ∈ node.history := by
  intro n adjacent
  rcases path.cases_head with same | ⟨child, edge, rest⟩
  · exact absurd (by rw [← same]; rfl) notStart
  · rw [children, List.mem_singleton] at edge
    subst edge
    have below := history_mono rest
    rcases neighbors n adjacent with rfl | rfl
    · exact below (by simp [nodeOf])
    · exact below (by simp [nodeOf])

/-- All neighbors of a root mark lie in the history of a center occurrence in its arm. -/
theorem arm_sealed (a : Fin 46) (allowed : RootMark a) (node : RawMolecule.CanonicalBranchNode)
    (path : Descends mol (nodeOf [0, a.val]) node) (notStart : node.atom ≠ a.val) :
    ∀ n : Fin 46, graph.Adj n a → n.val ∈ node.history := by
  rcases allowed with rfl | rfl | rfl | rfl
  · exact sealed_core 28 32 node path notStart (by decide +kernel)
      (by intro n; fin_cases n <;> decide +kernel)
  · exact sealed_core 29 33 node path notStart (by decide +kernel)
      (by intro n; fin_cases n <;> decide +kernel)
  · exact sealed_core 30 34 node path notStart (by decide +kernel)
      (by intro n; fin_cases n <;> decide +kernel)
  · exact sealed_core 31 35 node path notStart (by decide +kernel)
      (by intro n; fin_cases n <;> decide +kernel)

private theorem slot_current (c : physical.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData certified mol c node) (state : OccurrenceAuxState) (slot : Fin 4) :
    ((frames certified single_bonded state data.target data.real
      ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame.cursorAt
      slot).occurrence.1.node.current? = some (referenceAt certified mol c node data slot) := by
  have frameEq : (frames certified single_bonded state data.target data.real
      ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame = data.frame :=
    Option.some.inj ((frames certified single_bonded state data.target data.real
      ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl).frameComputed.symm.trans
      data.frameExec)
  have mapped : (((frames certified single_bonded state data.target data.real
      ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame.cursorAt
      slot).occurrence.1.node.current?).map Fin.val =
      some (referenceAt certified mol c node data slot).val := by
    change LocalizedChemicalRingFrameReadback.atomAt certified _ slot = _
    rw [frameEq, data.atomAt_eq]
    rfl
  cases found : ((frames certified single_bonded state data.target data.real
      ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame.cursorAt
      slot).occurrence.1.node.current? with
  | none => simp [found] at mapped
  | some b =>
      simp only [found, Option.map_some, Option.some.injEq] at mapped
      exact congrArg some (Fin.ext mapped)

/-- The real outward attachment is not in the occurrence history. -/
private theorem real_child_fresh (target : certified.LocalizedCIPOccurrence (retainedCarrierFuel certified))
    (pair : ActualOutwardSiblingPair certified (retainedCarrierFuel certified))
    (targetEq : pair.target = { occurrence := target, previous? := none })
    (x : Fin 46) (current : pair.left.occurrence.1.node.current? = some x)
    (real : pair.left.occurrence.1.node.provenance = .realAtom) :
    x ∉ target.1.node.history := by
  have member := outwardChild_node_mem certified pair.target pair.left pair.leftRoot pair.leftSlot
    pair.leftAddress
  rw [targetEq] at member
  obtain ⟨next, copy, same⟩ := MolecularEvidenceTree.executableOfficialCIPChildren_extend
    certified _ _ member
  rw [same, OfficialCIPNode.extend_current?, Option.some.injEq] at current
  rw [same] at real
  have fresh := ((MolecularEvidenceTree.childProvenance_eq_realAtom_iff _ next copy).mp real).2
  rw [current] at fresh
  exact fresh

theorem history_of_data (c : physical.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData certified mol c node) (n : Fin 46) (member : n.val ∈ node.history) :
    n ∈ data.target.1.node.history := by
  have mapped := (LocalizedMarkedCarrierLookup.lookup?_sound certified _ _ data.found).history
  rw [← mapped] at member
  obtain ⟨m, present, same⟩ := List.mem_map.mp member
  have equal : m = n := Fin.ext same
  rw [← equal]
  exact present

/-- An actual ordinary tie at a center occurrence of a root arm reconstructs one symmetry
fixing the history and the arm mark and exchanging the two tied attachments. -/
theorem tie_symmetry (a : Fin 46) (allowed : RootMark a) (c : physical.Center)
    (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData certified mol c node)
    (path : Descends mol (nodeOf [0, a.val]) node) (notStart : node.atom ≠ a.val)
    (state : OccurrenceAuxState) (left right : Fin 4) (different : left ≠ right)
    (tie : rawStateKeys certified single_bonded state data.target data.real
        ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl left =
      rawStateKeys certified single_bonded state data.target data.real
        ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl right) :
    ∃ e : physical.Aut,
      (∀ atom ∈ data.target.1.node.history, e.val atom = atom) ∧ e.val a = a ∧
      e.val (referenceAt certified mol c node data left) =
        referenceAt certified mol c node data right := by
  obtain ⟨center, centerCurrent⟩ := certified.localizedRerootCursor_current_exists
    (⟨data.target, none⟩ : certified.LocalizedRerootCursor (retainedCarrierFuel certified))
  have rawAllowed : a = 28 ∨ a = 29 ∨ a = 30 ∨ a = 31 := allowed
  obtain ⟨pair, targetEq, leftEq, rightEq, realL, realR⟩ := prior_tie_real_outward certified
    single_bonded state data.target data.real ⟨certified.molecularFrameUnit data.target.1, data.detected⟩
    rfl (Classical.choice (arm_tied_branch a rawAllowed c node data path)) center centerCurrent
    left right different tie
  have currentL : pair.left.occurrence.1.node.current? = some (referenceAt certified mol c node data left) := by
    rw [leftEq]
    exact slot_current c node data state left
  have currentR : pair.right.occurrence.1.node.current? = some (referenceAt certified mol c node data right) := by
    rw [rightEq]
    exact slot_current c node data state right
  have sealedRaw := arm_sealed a allowed node path notStart
  have sealedHistory : ∀ neighbor, graph.Adj neighbor a → neighbor ∈ data.target.1.node.history :=
    fun neighbor adjacent => history_of_data c node data neighbor (sealedRaw neighbor adjacent)
  have aInHistory : a ∈ data.target.1.node.history := by
    apply history_of_data c node data
    obtain ⟨rest, same⟩ := descends_history a.val node path
    rw [same]
    simp
  have freshL := real_child_fresh data.target pair targetEq _ currentL realL
  have freshR : referenceAt certified mol c node data right ∉ data.target.1.node.history :=
    real_child_fresh data.target
      { target := pair.target, left := pair.right, right := pair.left,
        leftPrevious := pair.rightPrevious, rightPrevious := pair.leftPrevious,
        leftRoot := pair.rightRoot, rightRoot := pair.leftRoot,
        leftSlot := pair.rightSlot, rightSlot := pair.leftSlot,
        leftAddress := pair.rightAddress, rightAddress := pair.leftAddress }
      targetEq _ currentR realR
  have refined := refined_tie_of_sealed_prior_tie certified single_bonded state data.target data.real
    ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl a (retainedCarrierFuel certified)
    (2 * (retainedCarrierFuel certified + 1)) left right pair targetEq leftEq rightEq realL realR
    _ _ currentL currentR
    (fun same => freshL (same ▸ aInHistory)) (fun same => freshR (same ▸ aInHistory))
    sealedHistory (fun adjacent => freshL (sealedHistory _ adjacent))
    (fun adjacent => freshR (sealedHistory _ adjacent)) tie
  have rootL := pair.leftRoot
  have rootR := pair.rightRoot
  have addressL := pair.leftAddress
  have addressR := pair.rightAddress
  rw [targetEq, leftEq] at rootL addressL
  rw [targetEq, rightEq] at rootR addressR
  rw [leftEq] at realL
  rw [rightEq] at realR
  obtain ⟨e, _, fixed, entry, reference, _⟩ := actual_outward_default_tie_witness certified single_bonded
    state data.target data.real ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl a
    left right _ _ (slot_current c node data state left) (slot_current c node data state right)
    realL realR rootL rootR pair.leftSlot pair.rightSlot addressL addressR refined ⟨0, constant_charge⟩
  exact ⟨e, fixed, reference, entry⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusContext

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusContext.keyOrder_lex_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusContext.slotPerm_lex_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusContext.reading_eq_marked
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusContext.reading_of_prior_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusContext.arm_sealed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusContext.tie_symmetry
