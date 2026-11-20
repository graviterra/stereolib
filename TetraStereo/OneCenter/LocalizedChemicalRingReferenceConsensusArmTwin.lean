import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmMirror
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmBranch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

/-!
Separation at the opposite occurrence `o- = [0,29,33,27,26]`, on both geometry sides.

The argument is the one accepted at `o+`, with sealed reference 29 and the covering path
`[0,29,33,27,26,34,38,42,40,3,14,8,15,4,16,9,6,2]`. A tie reconstructs one automorphism fixing
the history of `o-` and 29 and sending 34 to 35. It therefore fixes 28, sends 30 to 31, and is
odd at center 2; the matched covered label would make it proper there. The covering history
has a trivial stabilizer, which supplies the label. No label value or physical sign is assumed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmTwin

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitAllCalibration (otherCurrent)
open LocalizedChemicalRingReferenceOrbitStabilizer LocalizedChemicalRingReferenceOrbitOtherArmSymmetry
open LocalizedChemicalRingReferenceOrbitCoveringSymmetry (four_pins_rigid)
open LocalizedChemicalRingReferenceConsensusSymmetry
open LocalizedChemicalRingReferenceConsensusArmSeparation (tailPath)
open LocalizedChemicalRingReferenceConsensusArmPrior LocalizedChemicalRingReferenceConsensusArmBranch
open LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingSelectedRefusalWitness
open LocalizedChemicalRingCoveredPathOrientation LocalizedChemicalRingCoveredPathMirrorOrientation
open LocalizedChemicalRingBoundaryWitnessExecution
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingPrescribedPathFactMatch
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedChemicalRingPhysicalSense (inputGeometry relabelOf relabelOf_val)
open LocalizedMarkedReachableConfigurations (Reached reached_root reached_child)
open LocalizedMarkedTerminalReferenceScope (Descends descendant_reached)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedOperationEvaluator (tiedChildren)
open LocalizedChemicalRingFrameReadback (atomAt)
open LocalizedChemicalRingMovedSlotEligibility (moved_child_selected)
open LocalizedChemicalRingOrientationInduction (descriptorWith_mirror_none_iff)
open LocalizedGenericMarkedRecalculation (mirror)
open RetainedRingSymmetryReconstruction (BondedChain)

def twinPath : List (Fin 46) := [0, 29, 33, 27, 26]
def twinNode : RawMolecule.CanonicalBranchNode := nodeOf (twinPath.map Fin.val)
def twinChild : RawMolecule.CanonicalBranchNode := nodeOf [0, 29, 33, 27, 26, 34]
def twinCoveringPath : List (Fin 46) := twinPath ++ tailPath
def twinCovering : RawMolecule.CanonicalBranchNode := nodeOf (twinCoveringPath.map Fin.val)

private def twinRoute (n : Nat) := nodeOf ((twinCoveringPath.map Fin.val).take (n + 2))

private theorem twin_edges (i : Fin 16) :
    twinRoute (i.val + 1) ∈ mol.canonicalChildren (twinRoute i.val) := by
  fin_cases i <;> decide +kernel

private theorem route_descends (first last : Nat) (order : first ≤ last) (bound : last ≤ 16) :
    Descends mol (twinRoute first) (twinRoute last) := by
  induction last, order using Nat.le_induction with
  | base => exact .refl
  | succ last _ ih =>
      exact (ih (by omega)).tail (twin_edges ⟨last, by omega⟩)

theorem twin_arm_reached : Reached mol (nodeOf [0, 29]) :=
  reached_child mol (canonicalCenterRoot 0) (nodeOf [0, 29]) (reached_root mol 0 (by decide))
    (by decide +kernel)

theorem twin_descends : Descends mol (nodeOf [0, 29]) twinNode := route_descends 0 3 (by omega) (by omega)
theorem twin_child_descends : Descends mol twinChild twinCovering := route_descends 4 16 (by omega) (by omega)
theorem twin_covering_descends : Descends mol (nodeOf [0, 29]) twinCovering :=
  route_descends 0 16 (by omega) (by omega)
theorem twin_child_edge : twinChild ∈ mol.canonicalChildren twinNode := by decide +kernel

theorem twin_reached : Reached mol twinNode := descendant_reached twin_arm_reached twin_descends
theorem twin_covering_reached : Reached mol twinCovering :=
  descendant_reached twin_arm_reached twin_covering_descends

theorem twin_covering_detected (a : Fin 46) (detected : a ∈ graph.tetrahedralCenterSet) :
    a ∈ twinCoveringPath := by
  rw [detected_inventory] at detected
  fin_cases a <;> simp_all [twinCoveringPath, twinPath, tailPath]

noncomputable section
open scoped Classical

def twinData : OccurrenceData certified mol otherCurrent twinNode :=
  Classical.choice (occurrenceData_exists certified mol structure_agreement admissible supported
    single_bonded otherCurrent twinNode twin_reached rfl rfl)

def twinCoveringData : OccurrenceData certified mol current twinCovering :=
  Classical.choice (occurrenceData_exists certified mol structure_agreement admissible supported
    single_bonded current twinCovering twin_covering_reached rfl rfl)

abbrev twinUnit : DetectedOccurrence graph :=
  ⟨certified.molecularFrameUnit twinData.target.1, twinData.detected⟩

/-- The actual snapshot below `o-`, with inherited reference 29. -/
abbrev twinState (side : Bool) (depth : Nat) : OccurrenceAuxState :=
  snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
    (observedGeometry certified side) twinNode 29

theorem twin_history : twinData.target.1.node.history = twinPath.reverse := by
  apply List.map_injective_iff.mpr Fin.val_injective
  have history := (LocalizedMarkedCarrierLookup.lookup?_sound certified _ _ twinData.found).history
  simpa only [twinNode, nodeOf, List.map_reverse] using history

theorem twin_root : twinData.target.1.root = (0 : Fin 46) := by
  have packed := certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded twinData.target)
  apply Option.some.inj
  simpa only [twin_history, List.reverse_reverse, twinPath, List.head?_cons] using
    packed.sourceHead.symm

private def ligandAt (a : Fin 46) (adjacent : physical.mol.Adj otherCurrent.1 a) : Fin 4 :=
  Classical.choose (physical.ligandAtomAt_surjective otherCurrent a adjacent)

def twinSlot34 : Fin 4 := twinData.ligandOf.symm (ligandAt 34 (by decide +kernel))
def twinSlot35 : Fin 4 := twinData.ligandOf.symm (ligandAt 35 (by decide +kernel))

theorem twin_slot_atoms :
    referenceAt certified mol otherCurrent twinNode twinData twinSlot34 = (34 : Fin 46) ∧
    referenceAt certified mol otherCurrent twinNode twinData twinSlot35 = (35 : Fin 46) := by
  constructor
  · simpa only [referenceAt, twinSlot34, ligandAt, Equiv.apply_symm_apply] using
      Classical.choose_spec (physical.ligandAtomAt_surjective otherCurrent (34 : Fin 46) (by decide +kernel))
  · simpa only [referenceAt, twinSlot35, ligandAt, Equiv.apply_symm_apply] using
      Classical.choose_spec (physical.ligandAtomAt_surjective otherCurrent (35 : Fin 46) (by decide +kernel))

theorem twin_slots_distinct : twinSlot34 ≠ twinSlot35 := by
  intro same
  have atoms := twin_slot_atoms
  rw [same] at atoms
  exact (by decide : (34 : Fin 46) ≠ 35) (atoms.1.symm.trans atoms.2)

private theorem twin_slot_current (state : OccurrenceAuxState) (slot : Fin 4) (a : Fin 46)
    (atAtom : referenceAt certified mol otherCurrent twinNode twinData slot = a) :
    ((frames certified single_bonded state twinData.target twinData.real twinUnit rfl).frame.cursorAt
      slot).occurrence.1.node.current? = some a := by
  have frameEq : (frames certified single_bonded state twinData.target twinData.real twinUnit rfl).frame =
      twinData.frame :=
    Option.some.inj ((frames certified single_bonded state twinData.target twinData.real twinUnit
      rfl).frameComputed.symm.trans twinData.frameExec)
  have mapped : (((frames certified single_bonded state twinData.target twinData.real twinUnit
      rfl).frame.cursorAt slot).occurrence.1.node.current?).map Fin.val = some a.val := by
    change atomAt certified _ slot = some a.val
    rw [frameEq, twinData.atomAt_eq]
    exact congrArg (fun x : Fin 46 => some x.val) atAtom
  cases found : ((frames certified single_bonded state twinData.target twinData.real twinUnit
      rfl).frame.cursorAt slot).occurrence.1.node.current? with
  | none => simp [found] at mapped
  | some b =>
      simp only [found, Option.map_some, Option.some.injEq] at mapped
      exact congrArg some (Fin.ext mapped)

private theorem twin_history_fixed :
    ∀ value ∈ twinNode.history, relabelOf certified otherPhysicalAut.val value = value := by
  intro value member
  have history : twinNode.history = [26, 27, 33, 29, 0] := rfl
  rw [history] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem twin_selected_child :
    twinChild ∈ tiedChildren mol (sparseOperations certified mol) [] twinNode :=
  moved_child_selected certified mol structure_agreement admissible supported single_bonded
    otherPhysicalAut otherCurrent twinNode twinData twin_reached twin_history_fixed (34 : Fin 46)
    (by decide +kernel) (by change (35 : Fin 46) ≠ (34 : Fin 46); decide)
    twinChild twin_child_edge rfl

/-- The history of the covering occurrence has a trivial stabilizer. -/
private theorem twin_covering_rigid (e : physical.Aut)
    (historyFixed : ∀ atom ∈ twinCovering.history, relabelOf certified e.val atom = atom) :
    e = 1 := by
  have pin (a : Fin 46) (member : a ∈ twinCoveringPath) : e.val a = a := by
    have present : a.val ∈ twinCovering.history :=
      List.mem_reverse.mpr (List.mem_map.mpr ⟨a, member, rfl⟩)
    have same := historyFixed _ present
    rw [relabelOf_val] at same
    exact Fin.ext same
  let g : graph.Aut := ⟨e.val, e.2.1⟩
  have fixed0 : g.val (0 : Fin 46) = (0 : Fin 46) := pin 0 (by decide)
  have fixed29 : g.val (29 : Fin 46) = (29 : Fin 46) := pin 29 (by decide)
  have fixed34 : g.val (34 : Fin 46) = (34 : Fin 46) := pin 34 (by decide)
  have fixed2 : g.val (2 : Fin 46) = (2 : Fin 46) := pin 2 (by decide)
  have fixed8 : g.val (8 : Fin 46) = (8 : Fin 46) := pin 8 (by decide)
  have fixed28 : g.val (28 : Fin 46) = (28 : Fin 46) := by
    apply fixed_of_signature graph g ([29] : List (Fin 46)) (28 : Fin 46)
    · intro a member
      rw [List.mem_singleton.mp member]
      exact fixed29
    · unfold SignatureUnique
      decide +kernel
  have fixed30 : g.val (30 : Fin 46) = (30 : Fin 46) := by
    apply fixed_of_signature graph g ([34] : List (Fin 46)) (30 : Fin 46)
    · intro a member
      rw [List.mem_singleton.mp member]
      exact fixed34
    · unfold SignatureUnique
      decide +kernel
  have fixed5 : g.val (5 : Fin 46) = (5 : Fin 46) := by
    apply fixed_of_signature graph g ([2, 8] : List (Fin 46)) (5 : Fin 46)
    · intro a member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact fixed2
      · exact fixed8
    · unfold SignatureUnique
      decide +kernel
  exact Subtype.ext (four_pins_rigid g fixed0 fixed28 fixed30 fixed5)

private theorem twin_covering_descriptor_exists (side : Bool) (depth : Nat) :
    ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
      depth (observedGeometry certified side) [] (some 29) twinCovering = some value := by
  have original : ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol
      (sparseOperations certified mol) depth (inputGeometry certified) [] (some 29) twinCovering =
        some value :=
    LocalizedChemicalRingReferenceStabilizerSuccess.descriptor_exists certified mol structure_agreement
      admissible supported single_bonded cfg current calibrated twinCovering twinCoveringData
      (Classical.choice (arm_tied_branch (29 : Fin 46) (by decide) current twinCovering twinCoveringData
        twin_covering_descends))
      depth (29 : Fin 46) ⟨0, constant_charge⟩ (fun e historyFixed _ => twin_covering_rigid e historyFixed)
  cases side with
  | false => exact original
  | true =>
      change ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol
        (sparseOperations certified mol) depth (mirror (inputGeometry certified)) [] (some 29)
        twinCovering = some value
      cases observed : LocalizedChemicalRingInheritedFallback.descriptor? mol
          (sparseOperations certified mol) depth (mirror (inputGeometry certified)) [] (some 29)
          twinCovering with
      | none =>
          have refused : LocalizedChemicalRingInheritedFallback.descriptor? mol
              (sparseOperations certified mol) depth (inputGeometry certified) [] (some 29)
              twinCovering = none :=
            (descriptorWith_mirror_none_iff mol (sparseOperations certified mol)
              LocalizedChemicalRingInheritedFallback.rawStep? depth (inputGeometry certified)
              [] (some 29) twinCovering).mp observed
          obtain ⟨value, computed⟩ := original
          rw [computed] at refused
          cases refused
      | some value => exact ⟨value, rfl⟩

/-- The covering terminal's label is present in the snapshot below `o-` on both sides. -/
theorem twin_covering_label_present (side : Bool) (depth : Nat) (adequate : 13 ≤ depth) :
    ((twinState side depth).factAt? twinCovering).map factLabel ≠ none := by
  intro absent
  have budget : twinCovering.history.length ≤ depth + twinNode.history.length := by
    have lengths : twinCovering.history.length = 18 ∧ twinNode.history.length = 5 := by
      decide +kernel
    omega
  have refused := LocalizedChemicalRingSelectedFactCompleteness.candidate_absence_refusal
    certified mol depth (observedGeometry certified side) twinNode twinChild twinCovering 29
    twin_selected_child twin_child_descends budget absent
  obtain ⟨value, computed⟩ := twin_covering_descriptor_exists side
    (depth + twinNode.history.length - twinCovering.history.length)
  rw [computed] at refused
  cases refused

private theorem tail_valid :
    ResidualObsPath graph twinData.target.1.node.history.reverse (34 : Fin 46) tailPath := by
  rw [twin_history, List.reverse_reverse]
  refine ⟨by decide, rfl, by decide, ?_, ?_⟩
  · decide +kernel
  · simp only [tailPath, BondedChain]
    decide +kernel

private theorem tail_query :
    rawPathNode twinData.target.1.root (boundaryPath twinData.target tailPath) = twinCovering := by
  unfold boundaryPath
  rw [twin_history, twin_root]
  rfl

private theorem o18_image (e : graph.Aut) (entry : e.val (34 : Fin 46) = (35 : Fin 46)) :
    e.val (30 : Fin 46) = (31 : Fin 46) := by
  have finite : ∀ x : Fin 46, graph.Adj 35 x → graph.atomZ x = graph.atomZ 30 →
      graph.atomMass x = graph.atomMass 30 → x = 31 := by
    intro x
    fin_cases x <;> decide +kernel
  apply finite
  · rw [← entry]
    exact (MoleculeGraph.Aut.adj_iff (m := graph) e 34 30).mpr (by decide +kernel)
  · exact MoleculeGraph.Aut.atomZ_eq (m := graph) e 30
  · exact MoleculeGraph.Aut.atomMass_eq (m := graph) e 30

private theorem o16_image (e : graph.Aut) (fixed : e.val (29 : Fin 46) = (29 : Fin 46)) :
    e.val (28 : Fin 46) = (28 : Fin 46) :=
  fixed_of_signature graph e ([29] : List (Fin 46)) (28 : Fin 46)
    (by
      intro a member
      rw [List.mem_singleton.mp member]
      exact fixed)
    (by unfold SignatureUnique; decide +kernel)

/-- **Separation at `o-`** for the actual marked keys of reference 29, on either side. -/
theorem twin_refined_separate (side : Bool) (depth : Nat) (adequate : 13 ≤ depth) :
    refinedKey certified single_bonded (twinState side depth)
        twinData.target twinData.real twinUnit rfl (29 : Fin 46)
        (retainedCarrierFuel certified) (2 * (retainedCarrierFuel certified + 1)) twinSlot34 ≠
      refinedKey certified single_bonded (twinState side depth)
        twinData.target twinData.real twinUnit rfl (29 : Fin 46)
        (retainedCarrierFuel certified) (2 * (retainedCarrierFuel certified + 1)) twinSlot35 := by
  intro tie
  have branch := Classical.choice (arm_tied_branch (29 : Fin 46) (by decide) otherCurrent twinNode
    twinData twin_descends)
  obtain ⟨center, centerCurrent⟩ := certified.localizedRerootCursor_current_exists
    (⟨twinData.target, none⟩ : certified.LocalizedRerootCursor (retainedCarrierFuel certified))
  obtain ⟨_, pair, _, _, _, _, _, targetEq, leftEq, rightEq, _, _, _, realL, realR⟩ :=
    LocalizedChemicalRingSelectedOutwardTie.selected_refined_tie_real_outward certified single_bonded
      branch.rootCursor branch.rootAddress branch.arm branch.arm' branch.member branch.member'
      branch.different branch.real branch.real' branch.read branch.read' branch.key branch.key'
      branch.built branch.built' branch.tie (twinState side depth) twinData.target twinData.real
      branch.inside branch.nonroot center centerCurrent twinUnit rfl (29 : Fin 46)
      (retainedCarrierFuel certified) (2 * (retainedCarrierFuel certified + 1)) twinSlot34 twinSlot35
      twin_slots_distinct tie
  have rootL := pair.leftRoot
  have rootR := pair.rightRoot
  have addressL := pair.leftAddress
  have addressR := pair.rightAddress
  rw [targetEq, leftEq] at rootL addressL
  rw [targetEq, rightEq] at rootR addressR
  rw [leftEq] at realL
  rw [rightEq] at realR
  have currentL := twin_slot_current (twinState side depth) twinSlot34 34 twin_slot_atoms.1
  have currentR := twin_slot_current (twinState side depth) twinSlot35 35 twin_slot_atoms.2
  obtain ⟨_, matched⟩ := actual_outward_default_tie_prescribed_fact_match certified single_bonded
    (twinState side depth) twinData.target twinData.real twinUnit rfl (29 : Fin 46) twinSlot34 twinSlot35
    (34 : Fin 46) (35 : Fin 46) currentL currentR realL realR rootL rootR pair.leftSlot pair.rightSlot
    addressL addressR tie ⟨0, constant_charge⟩
  have detected : IsDetectedCenter graph (pathTerminal tailPath tail_valid.nonempty) :=
    (graph.isTetrahedralCenter_iff_neighborFinset_card _).mp
      ((graph.mem_tetrahedralCenterSet _).mp current.2)
  obtain ⟨π, automorphism, historyFixed, entry, referenceFixed, _, _, _, _, facts⟩ :=
    matched ⟨tailPath, tail_valid⟩ detected
  let g : graph.Aut := ⟨π, automorphism⟩
  let e : physical.Aut := graph.detectedMultiCenterAutOfGraphAut g
  have rootFixed : π (0 : Fin 46) = (0 : Fin 46) :=
    historyFixed (0 : Fin 46) (by rw [twin_history]; decide)
  obtain ⟨centerFixed, negative⟩ := other_exchange_lower_negative cfg e rootFixed
    (o16_image g referenceFixed) (o18_image g entry)
  have imageCalibrated : LocalizedRecursiveAuxiliaryPhysicalDomain.ActualPhysicalCalibratedCoordinates
      certified physical cfg (physical.centerPerm e current) := by
    rw [centerFixed]
    exact calibrated
  have boundaryFixed : ∀ atom ∈ twinData.target.1.node.history.reverse, e.val atom = atom := by
    intro atom member
    exact historyFixed atom (List.mem_reverse.mp member)
  have covered : ∀ c : physical.Center, c.1.val ∈
      (rawPathNode twinData.target.1.root (boundaryPath twinData.target tailPath)).history := by
    intro c
    rw [tail_query]
    exact List.mem_reverse.mpr (List.mem_map.mpr ⟨c.1, twin_covering_detected c.1 c.2, rfl⟩)
  cases observed : ((twinState side depth).factAt? (rawPathNode twinData.target.1.root
      (boundaryPath twinData.target tailPath))).map factLabel with
  | none =>
      rw [tail_query] at observed
      exact twin_covering_label_present side depth adequate observed
  | some label =>
      have sym := LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut
        certified mol structure_agreement admissible supported e
      have cov := LocalizedChemicalRingSemanticSymmetry.actual_covariant
        certified mol structure_agreement admissible supported single_bonded e
      have stepMap := LocalizedChemicalRingInheritedFallback.stepMap sym admissible.1.1 admissible.1.2
        (raw_single mol certified structure_agreement admissible.1.1 admissible.1.2 supported
          single_bonded) cov
      have proper : LocalizedPhysicalMarkedParityCompleteness.relativeSign physical cfg e current = 1 := by
        cases side with
        | false =>
            exact relativeSign_of_covered_snapshot certified mol structure_agreement admissible
              supported single_bonded cfg e LocalizedChemicalRingInheritedFallback.rawStep? stepMap
              (LocalizedChemicalRingInheritedFallback.stepCongr mol (sparseOperations certified mol))
              (LocalizedChemicalRingInheritedFallback.stepFlip mol (sparseOperations certified mol))
              twinData.target (29 : Fin 46) (34 : Fin 46) boundaryFixed referenceFixed tailPath tail_valid
              current rfl calibrated imageCalibrated covered depth twinNode twin_reached facts label observed
        | true =>
            exact relativeSign_of_covered_mirror_snapshot certified mol structure_agreement
              admissible supported single_bonded cfg e LocalizedChemicalRingInheritedFallback.rawStep?
              stepMap
              (LocalizedChemicalRingInheritedFallback.stepCongr mol (sparseOperations certified mol))
              (LocalizedChemicalRingInheritedFallback.stepFlip mol (sparseOperations certified mol))
              twinData.target (29 : Fin 46) (34 : Fin 46) boundaryFixed referenceFixed tailPath tail_valid
              current rfl calibrated imageCalibrated covered depth twinNode twin_reached facts label observed
      rw [negative] at proper
      norm_num at proper

/-- **Ordinary separation at `o-`**, on either geometry side. -/
theorem twin_prior_separate (side : Bool) (depth : Nat) (adequate : 13 ≤ depth) :
    rawStateKeys certified single_bonded (twinState side depth)
        twinData.target twinData.real twinUnit rfl twinSlot34 ≠
      rawStateKeys certified single_bonded (twinState side depth)
        twinData.target twinData.real twinUnit rfl twinSlot35 := by
  intro prior
  obtain ⟨center, centerCurrent⟩ := certified.localizedRerootCursor_current_exists
    (⟨twinData.target, none⟩ : certified.LocalizedRerootCursor (retainedCarrierFuel certified))
  obtain ⟨pair, targetEq, leftEq, rightEq, realL, realR⟩ := prior_tie_real_outward certified
    single_bonded (twinState side depth) twinData.target twinData.real twinUnit rfl
    (Classical.choice (arm_tied_branch (29 : Fin 46) (by decide) otherCurrent twinNode twinData
      twin_descends))
    center centerCurrent twinSlot34 twinSlot35 twin_slots_distinct prior
  have currentL : pair.left.occurrence.1.node.current? = some (34 : Fin 46) := by
    rw [leftEq]
    exact twin_slot_current _ twinSlot34 34 twin_slot_atoms.1
  have currentR : pair.right.occurrence.1.node.current? = some (35 : Fin 46) := by
    rw [rightEq]
    exact twin_slot_current _ twinSlot35 35 twin_slot_atoms.2
  have sealedHistory : ∀ neighbor, graph.Adj neighbor (29 : Fin 46) →
      neighbor ∈ twinData.target.1.node.history := by
    rw [twin_history]
    have finite : ∀ n : Fin 46, graph.Adj n (29 : Fin 46) → n ∈ twinPath.reverse := by
      intro n
      fin_cases n <;> decide +kernel
    exact finite
  apply twin_refined_separate side depth adequate
  exact refined_tie_of_sealed_prior_tie certified single_bonded (twinState side depth) twinData.target
    twinData.real twinUnit rfl (29 : Fin 46) (retainedCarrierFuel certified)
    (2 * (retainedCarrierFuel certified + 1)) twinSlot34 twinSlot35 pair targetEq leftEq rightEq
    realL realR (34 : Fin 46) (35 : Fin 46) currentL currentR (by decide) (by decide) sealedHistory
    (by decide +kernel) (by decide +kernel) prior

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmTwin

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmTwin.twin_descends
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmTwin.twin_selected_child
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmTwin.twin_covering_label_present
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmTwin.twin_refined_separate
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmTwin.twin_prior_separate
