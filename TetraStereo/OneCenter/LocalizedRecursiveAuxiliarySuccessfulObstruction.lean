import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration
import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# A successful false lowercase: success-soundness fails on the recursive calibrated domain

On the decorated hidden-parity cage (`LocalizedRecursiveAuxiliaryParityDecoration`) the actual
evaluator **returns** a descriptor at the root and that descriptor is **lowercase**, while the
physical root has **no** enantiomorphic pair (and is pairwise properly distinguishable, every
non-root centre calibrated).

Mechanism, all from actual generated labels:

1. `C*A` is constitutionally separated (its outward neighbours H, F, C differ in atomic number; its
   parent slot is separated by the actual Rule-1a tie of the two root arms), and calibrated: its
   actual state is `some (.chiral raw)`.
2. The arm swap obeys the *blind* mirror sign law (`blindMirror`): mirror law at `C*A`, accepted
   refusal witnesses at the cage bridgeheads. By the accepted `law_of_reach_blind` the actual state
   at `C*B` is the mirrored letter, and by `priorTie_of_blindMirror` the two root arms have an
   actual **prior tie** (Rules 1–4).
3. The full keys still differ (the arm cursors carry opposite actual letters), so the four root keys
   are injective and the root returns; its retained pair count is exactly one, so it is lowercase.
4. Physically the bridgehead parity of cage A differs from cage B, so no mirror (or proper) branch
   transport relates the arms: physical pair count `0`.

The retained observation is blind to configurations at refused centres. Two arms whose *observed*
centres are mirror images are classified as an enantiomorphic pair although the whole physical
arms are not mirror images. No reader agreement, inverse, pair-count relation, root key, selected
reference or output is assumed. Chemical realizability of the short cage is not established.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction

noncomputable section

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
open TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup
open TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode
open TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport
open TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness
open TetraStereo.OneCenter.LocalizedCyclicRootArmReachability
open TetraStereo.OneCenter.MoleculeGraph
open CertifiedLocalizedCIPInput
open LocalizedRuleMajorReference
open scoped Classical

/-! ## Root frame facts -/

theorem domainAtFrames :
    RecursiveAuxiliaryPhysicalDomain decReference.certified detectedCfg decFrames.center := by
  rw [decCenter]
  exact detectedDomain

abbrev armTargetA : Occurrence decReference := (decFrames.frame.cursorAt slotA).occurrence
abbrev armTargetB : Occurrence decReference := (decFrames.frame.cursorAt slotB).occurrence

theorem armA_real : armTargetA.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  (rootFrame_cursor_facts simple_bonded decFrames decAddress decReal slotA).1

theorem armB_real : armTargetB.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  (rootFrame_cursor_facts simple_bonded decFrames decAddress decReal slotB).1

theorem armA_history : armTargetA.1.node.history = ([3, 0] : List (Fin 21)) := by
  have facts : armTargetA.1.node.history =
      [decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
        (decFrames.detectedLigandPermutation slotA), decFrames.center.1] :=
    (rootFrame_cursor_facts simple_bonded decFrames decAddress decReal slotA).2.2
  rw [facts, slotA_spec, decCenter]
  rfl

theorem armA_root : armTargetA.1.root = (0 : Fin 21) := by
  rw [(rootFrame_cursor_facts simple_bonded decFrames decAddress decReal slotA).2.1, decCenter]
  rfl

theorem armA_current : armTargetA.1.node.current? = some (3 : Fin 21) := by
  have ligand := decFrames.ligandAt slotA
  rw [slotA_spec] at ligand
  exact ligand

theorem armB_current : armTargetB.1.node.current? = some (12 : Fin 21) := by
  have ligand := decFrames.ligandAt slotB
  rw [slotB_spec] at ligand
  exact ligand

/-! ## The blind mirror consequences (accepted ParityEvidence) -/

/-- **The two decorated root arms have an actual prior tie.** -/
theorem armsPriorTie : decReference.certified.compareLocalizedRerootCompoundRule4bcKeys
    (decFrames.compounds slotA).prior (decFrames.compounds slotB).prior = .eq :=
  priorTie_of_blindMirror simple_bonded decFrames decAddress decReal slots_ne detectedCfg
    domainAtFrames armSwap armSwap_root armSwap_AB blindMirror

theorem transport_A_B :
    decReference.certified.transportOccurrence simple_bonded armSwap armTargetA = armTargetB := by
  have outward := decReference.certified.localizedOccurrenceFourLigandFrame_root_all_outward
    decTarget decFrames.frame (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed decFrames)
    decAddress
  have historyFixed : ∀ x ∈ decTarget.1.node.history,
      (armSwap : Equiv.Perm (Fin 21)) x = x := by
    intro x hx
    rw [decHistory, List.mem_singleton] at hx
    subst hx
    rfl
  have slots := transportCursor_slot_of_history simple_bonded decFrames decReal armSwap
    (outward slotA).2 (outward slotB).2 historyFixed armSwap_AB
  have occurrenceEq := congrArg
    (fun cursor : decReference.certified.LocalizedRerootCursor (carrierFuel decReference) =>
      cursor.occurrence) slots
  simpa only [decReference.certified.transportCursor_occurrence] using occurrenceEq

/-- The actual state at `C*B` is the mirrored actual state at `C*A`. -/
theorem stateB_of_stateA {raw : RS}
    (stateA : referenceState decReference armTargetA = some (.chiral raw)) :
    referenceState decReference armTargetB = some (.chiral (RS.swap raw)) := by
  have law : referenceState decReference
        (decReference.certified.transportOccurrence simple_bonded armSwap armTargetA) =
      (referenceState decReference armTargetA).map (retainedPhysicalLetter true) :=
    law_of_reach_blind simple_bonded decFrames decAddress decReal slots_ne detectedCfg
      domainAtFrames armSwap true armSwap_root armSwap_AB blindMirror armTargetA
      ⟨decFrames.frame.cursorAt slotA, rfl, Relation.ReflTransGen.refl⟩
  rw [transport_A_B, stateA] at law
  simpa [retainedPhysicalLetter] using law

/-! ## The actual label at `C*A` -/

theorem armA_isDetected : IsDetectedCenter decReference.certified.moleculeGraph
    (decReference.certified.molecularFrameUnit armTargetA.1).atom := by
  have head : armTargetA.1.node.history.head? = some (3 : Fin 21) := by rw [armA_history]; rfl
  have last : armTargetA.1.node.history.getLast? = some armTargetA.1.root := by
    rw [armA_history, armA_root]; rfl
  rw [decReference.certified.molecularFrameUnit_atom_eq_current armTargetA.1 head last]
  rw [IsDetectedCenter]
  apply (decReference.certified.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mp
  apply (decReference.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp
  exact (degree_four_iff 3).mpr (by decide)

def armUnit : DetectedOccurrence decReference.certified.moleculeGraph :=
  ⟨decReference.certified.molecularFrameUnit armTargetA.1, armA_isDetected⟩

def armFrames : ContextFrameCompilation decReference armTargetA armUnit rfl :=
  cyclicContextFrameCompilation decReference simple_bonded armTargetA armA_real armUnit rfl

theorem armA_parent : armTargetA.1.node.parent? = some (0 : Fin 21) := by
  simp [OfficialCIPNode.parent?, armA_history]

private theorem armA_outwardCursor_atom_range
    (child : decReference.certified.LocalizedRerootCursor (carrierFuel decReference))
    (childOut : child.occurrence.1 ∈
      decReference.certified.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel decReference) armTargetA.1) :
    ∃ atom : decReference.certified.Atom,
      child.occurrence.1.node = armTargetA.1.node.extend atom 0 ∧
      child.occurrence.1.node.current? = some atom ∧
        (atom = (4 : Fin 21) ∨ atom = (5 : Fin 21) ∨ atom = (6 : Fin 21)) := by
  obtain ⟨w, _slot, nodeEq, _current, _rootEq, _addressEq, _zip, notParent, adjacent⟩ :=
    decReference.certified.simpleBond_outwardFrame_extend_zero simple_bonded
      armTargetA armA_current armA_real child.occurrence.1 childOut
  have nodeCurrent : child.occurrence.1.node.current? = some w := by
    rw [nodeEq]
    simp [OfficialCIPNode.extend]
  have wNotZero : w ≠ (0 : Fin 21) := by
    intro same
    rw [same, armA_parent] at notParent
    exact notParent rfl
  have neighbors : ∀ x : Fin 21, graph.Adj 3 x → x = 0 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by decide
  rcases neighbors w adjacent with h | h | h | h
  · exact (wNotZero h).elim
  · exact ⟨w, nodeEq, nodeCurrent, Or.inl h⟩
  · exact ⟨w, nodeEq, nodeCurrent, Or.inr (Or.inl h)⟩
  · exact ⟨w, nodeEq, nodeCurrent, Or.inr (Or.inr h)⟩

private theorem armA_outwardPair_atom_range
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair
      decReference.certified (carrierFuel decReference))
    (targetEq : pair.target = ({ occurrence := armTargetA, previous? := none } :
      decReference.certified.LocalizedRerootCursor (carrierFuel decReference)))
    (side : Bool) :
    ∃ atom : decReference.certified.Atom,
      (if side then pair.left else pair.right).occurrence.1.node =
          armTargetA.1.node.extend atom 0 ∧
      (if side then pair.left else pair.right).occurrence.1.node.current? = some atom ∧
        (atom = (4 : Fin 21) ∨ atom = (5 : Fin 21) ∨ atom = (6 : Fin 21)) := by
  have targetOccurrence : pair.target.occurrence = armTargetA := by
    simpa only [armTargetA] using congrArg (fun c : decReference.certified.LocalizedRerootCursor
      (carrierFuel decReference) => c.occurrence) targetEq
  have targetAddress : pair.target.occurrence.1.address = armTargetA.1.address :=
    congrArg (fun occurrence : Occurrence decReference => occurrence.1.address) targetOccurrence
  have targetRoot : pair.target.occurrence.1.root = armTargetA.1.root :=
    congrArg (fun occurrence : Occurrence decReference => occurrence.1.root) targetOccurrence
  cases side with
  | false =>
      have out : pair.right.occurrence.1 ∈
          decReference.certified.localizedCarrierOutwardChildFrames
            (fuel := carrierFuel decReference) armTargetA.1 := by
        apply (decReference.certified.mem_localizedCarrierOutwardChildFrames_iff
          armTargetA.1 pair.right.occurrence.1).mpr
        have h : pair.right.occurrence.1.address = armTargetA.1.address ++ [pair.rightSlot] := by
          rw [pair.rightAddress, targetAddress]
        refine ⟨pair.right.occurrence.2, pair.rightRoot.trans targetRoot, ?_, ?_⟩
        · rw [h]
          simp
        · rw [h]
          simp
      simpa using armA_outwardCursor_atom_range pair.right out
  | true =>
      have out : pair.left.occurrence.1 ∈
          decReference.certified.localizedCarrierOutwardChildFrames
            (fuel := carrierFuel decReference) armTargetA.1 := by
        apply (decReference.certified.mem_localizedCarrierOutwardChildFrames_iff
          armTargetA.1 pair.left.occurrence.1).mpr
        have h : pair.left.occurrence.1.address = armTargetA.1.address ++ [pair.leftSlot] := by
          rw [pair.leftAddress, targetAddress]
        refine ⟨pair.left.occurrence.2, pair.leftRoot.trans targetRoot, ?_, ?_⟩
        · rw [h]
          simp
        · rw [h]
          simp
      simpa using armA_outwardCursor_atom_range pair.left out

private theorem armA_outwardPair_separated
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair
      decReference.certified (carrierFuel decReference))
    (targetEq : pair.target = ({ occurrence := armTargetA, previous? := none } :
      decReference.certified.LocalizedRerootCursor (carrierFuel decReference)))
    (distinct : pair.left ≠ pair.right) :
    LocalizedCyclicGeneralRigidPriority.ConstitutionallySeparated pair.left pair.right := by
  obtain ⟨leftAtom, leftNode, leftCurrent, leftRange⟩ :=
    armA_outwardPair_atom_range pair targetEq true
  obtain ⟨rightAtom, rightNode, rightCurrent, rightRange⟩ :=
    armA_outwardPair_atom_range pair targetEq false
  simp at leftNode leftCurrent leftRange
  simp at rightNode rightCurrent rightRange
  have atomsDistinct : leftAtom ≠ rightAtom := by
    intro same
    have nodeEq : pair.left.occurrence.1.node = pair.right.occurrence.1.node := by
      rw [leftNode, rightNode, same]
    exact distinct (LocalizedActualBoundaryObservationReadback.outwardChild_eq_of_node_eq
      decReference.certified simple_bonded pair.target pair.left pair.right
      pair.leftPrevious pair.rightPrevious pair.leftRoot pair.rightRoot pair.leftSlot
      pair.rightSlot pair.leftAddress pair.rightAddress nodeEq)
  have atomicNumbersDistinct : graph.atomZ leftAtom ≠ graph.atomZ rightAtom := by
    intro equalZ
    apply atomsDistinct
    rcases leftRange with rfl | rfl | rfl <;> rcases rightRange with rfl | rfl | rfl <;>
      first | rfl | exact absurd equalZ (by decide)
  apply LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.constitutionallySeparated_of_rootAtomicNumber_ne
    decReference.certified
  rw [LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.cursorRootAtomicNumber_eq_atomZ_of_current
      decReference.certified pair.left leftCurrent,
    LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.cursorRootAtomicNumber_eq_atomZ_of_current
      decReference.certified pair.right rightCurrent]
  exact atomicNumbersDistinct

theorem armA_strict :
    LocalizedCyclicGeneralRigidPriority.FrameConstitutionalStrict armFrames.frame := by
  let rootCursor : decReference.certified.LocalizedRerootCursor (carrierFuel decReference) :=
    { occurrence := decTarget, previous? := none }
  let armCursor := decFrames.frame.cursorAt slotA
  let closingCursor := decFrames.frame.cursorAt slotB
  have computed : decReference.certified.localizedOccurrenceFourLigandFrame? decTarget =
      some decFrames.frame :=
    LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed decFrames
  have armMem := LocalizedCyclicGeneralRigidPriority.frame_cursorAt_mem_executable
    decTarget decFrames.frame computed slotA
  have closingMem := LocalizedCyclicGeneralRigidPriority.frame_cursorAt_mem_executable
    decTarget decFrames.frame computed slotB
  have armDistinct : armCursor.occurrence ≠ closingCursor.occurrence := by
    intro same
    have currents : armCursor.occurrence.1.node.current? =
        closingCursor.occurrence.1.node.current? :=
      congrArg (fun occurrence : Occurrence decReference => occurrence.1.node.current?) same
    rw [armA_current, armB_current] at currents
    exact absurd (Option.some.inj currents) (by decide)
  let rootRead := contextOccurrenceRead decReference decTarget
  have armBuilt : decReference.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a rootRead (2 * (carrierFuel decReference + 1)) armCursor =
      some (decFrames.stages slotA).a.key :=
    (decReference.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
      rootRead (2 * (carrierFuel decReference + 1)) armCursor).symm.trans
      (decFrames.stages slotA).a.built
  have closingBuilt : decReference.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a rootRead (2 * (carrierFuel decReference + 1)) closingCursor =
      some (decFrames.stages slotB).a.key :=
    (decReference.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
      rootRead (2 * (carrierFuel decReference + 1)) closingCursor).symm.trans
      (decFrames.stages slotB).a.built
  have targetNonroot : armTargetA.1.address ≠ [] := by
    have addressEq := (rootFramePair decFrames decAddress slotA slotA).leftAddress
    intro empty
    change armTargetA.1.address = _ at addressEq
    rw [empty] at addressEq
    simp at addressEq
  exact LocalizedCyclicGeneralRigidPriority.frameConstitutionalStrict_of_rootArmRule1aTie
    decReference.certified simple_bonded rootCursor decAddress armCursor closingCursor armMem
    closingMem armDistinct armA_real armB_real rootRead rootRead
    (decFrames.stages slotA).a.key (decFrames.stages slotB).a.key armBuilt closingBuilt
    (rootArms_rule1aTie_of_atoms simple_bonded decFrames decAddress decReal armSwap
      armSwap_root armSwap_AB)
    armTargetA armA_real ⟨rfl, List.prefix_rfl⟩ armFrames.frame
    (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed armFrames) targetNonroot
    (fun pair pairTarget distinct => armA_outwardPair_separated pair pairTarget distinct)

/-- **The actual generated state at `C*A` is an uppercase letter.** -/
theorem armA_isChiral :
    ∃ raw : RS, referenceState decReference armTargetA = some (.chiral raw) := by
  obtain ⟨pointAt, observed, _volumeNonzero, signEq⟩ := detectedCoordinates armFrames.center
  let points : Fin 4 → CartesianPoint3 :=
    fun slot => pointAt (armFrames.detectedLigandPermutation slot)
  have available := LocalizedCyclicGeneralRigidGeneratedLabels.actualCoordinates_of_calibrated
    armFrames pointAt observed
  have sign := LocalizedCyclicGeneralRigidGeneratedLabels.priorityVolume_sign_of_calibrated
    armFrames armA_strict simple_bonded detectedCfg pointAt signEq
  have signUnit :
      decReference.certified.detectedMultiCenterMolecule.configurationSign detectedCfg
          armFrames.center *
        permHandedness armFrames.detectedLigandPermutation *
        permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder
          armFrames armA_strict simple_bonded) = 1 ∨
      decReference.certified.detectedMultiCenterMolecule.configurationSign detectedCfg
          armFrames.center *
        permHandedness armFrames.detectedLigandPermutation *
        permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder
          armFrames armA_strict simple_bonded) = -1 := by
    rw [← permHandedness_mul, ← permHandedness_mul]
    exact permHandedness_eq_one_or_eq_neg_one _
  have nonzero : reindexedVolume points
      (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder armFrames armA_strict
        simple_bonded) ≠ 0 := by
    intro zero
    have signZero := (rationalVolumeSign_eq_zero_iff _).mpr zero
    change rationalVolumeSign (reindexedVolume points
      (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder armFrames armA_strict
        simple_bonded)) = _ at sign
    rw [signZero] at sign
    rcases signUnit with one | negOne
    · rw [one] at sign
      norm_num at sign
    · rw [negOne] at sign
      norm_num at sign
  exact LocalizedCyclicGeneralRigidGeneratedLabels.referenceState_isChiral
    armFrames armA_strict simple_bonded points available nonzero

/-! ## The root: injective keys, success, lowercase -/

private theorem rootSlot_observation (slot : Fin 4) :
    (graph.atomZ (decReference.certified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
        (decFrames.detectedLigandPermutation slot)) = 6 ∧
      (slot = slotA ∨ slot = slotB)) ∨
    (graph.atomZ (decReference.certified.detectedMultiCenterMolecule.ligandAtomAt
        decFrames.center (decFrames.detectedLigandPermutation slot)) ≠ 6 ∧
      ∀ other : Fin 4,
        graph.atomZ (decReference.certified.detectedMultiCenterMolecule.ligandAtomAt
            decFrames.center (decFrames.detectedLigandPermutation other)) =
          graph.atomZ (decReference.certified.detectedMultiCenterMolecule.ligandAtomAt
            decFrames.center (decFrames.detectedLigandPermutation slot)) → other = slot) := by
  let m := decReference.certified.detectedMultiCenterMolecule
  have injective : ∀ a b : Fin 4, m.ligandAtomAt decFrames.center
      (decFrames.detectedLigandPermutation a) = m.ligandAtomAt decFrames.center
      (decFrames.detectedLigandPermutation b) → a = b := fun a b h =>
    decFrames.detectedLigandPermutation.injective (m.ligandAtomAt_injective _ h)
  have adjacentOf : ∀ s : Fin 4, graph.Adj 0
      (m.ligandAtomAt decFrames.center (decFrames.detectedLigandPermutation s)) := by
    intro s
    have h := m.ligandAtomAt_adj decFrames.center (decFrames.detectedLigandPermutation s)
    have h0 : decFrames.center.1 = (0 : Fin 21) := by rw [decCenter]; rfl
    rw [h0] at h
    exact h
  have rootNeighbors : ∀ x : Fin 21, graph.Adj 0 x → x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 12 := by
    decide
  have zOf : ∀ x : Fin 21, graph.Adj 0 x →
      (graph.atomZ x = 6 ↔ x = 3 ∨ x = 12) := by decide
  have uniqueOf : ∀ x y : Fin 21, graph.Adj 0 x → graph.Adj 0 y → graph.atomZ x ≠ 6 →
      graph.atomZ y = graph.atomZ x → y = x := by decide
  by_cases six : graph.atomZ (m.ligandAtomAt decFrames.center
      (decFrames.detectedLigandPermutation slot)) = 6
  · left
    refine ⟨six, ?_⟩
    rcases (zOf _ (adjacentOf slot)).mp six with h | h
    · exact Or.inl (injective _ _ (h.trans slotA_spec.symm))
    · exact Or.inr (injective _ _ (h.trans slotB_spec.symm))
  · right
    refine ⟨six, fun other equalZ => injective _ _ ?_⟩
    exact uniqueOf _ _ (adjacentOf slot) (adjacentOf other) six equalZ

private theorem slots_of_atomZ_eq {i j : Fin 4}
    (equalZ : graph.atomZ (decReference.certified.detectedMultiCenterMolecule.ligandAtomAt
        decFrames.center (decFrames.detectedLigandPermutation i)) =
      graph.atomZ (decReference.certified.detectedMultiCenterMolecule.ligandAtomAt
        decFrames.center (decFrames.detectedLigandPermutation j))) :
    i = j ∨ (i = slotA ∧ j = slotB) ∨ (i = slotB ∧ j = slotA) := by
  rcases rootSlot_observation i with ⟨sixI, hi⟩ | ⟨notSix, unique⟩
  · rcases rootSlot_observation j with ⟨_sixJ, hj⟩ | ⟨notSixJ, _⟩
    · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inl rfl
    · exact absurd (equalZ.symm.trans sixI) notSixJ
  · exact Or.inl (unique j equalZ.symm).symm

private theorem atomZ_eq_of_rule4aTie {i j : Fin 4}
    (rule4aTie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        ((decFrames.stages i).a.key.constitutional.rule1a)
        ((decFrames.stages j).a.key.constitutional.rule1a) = Ordering.eq) :
    graph.atomZ (decReference.certified.detectedMultiCenterMolecule.ligandAtomAt
        decFrames.center (decFrames.detectedLigandPermutation i)) =
      graph.atomZ (decReference.certified.detectedMultiCenterMolecule.ligandAtomAt
        decFrames.center (decFrames.detectedLigandPermutation j)) := by
  have rootZ := LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.actual_rule1a_tie_rootAtomicNumber_eq
    decReference.certified (decFrames.stages i).a.built (decFrames.stages j).a.built rule4aTie
  rw [← LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.cursorRootAtomicNumber_eq_atomZ_of_current
      decReference.certified _ (decFrames.ligandAt i),
    ← LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.cursorRootAtomicNumber_eq_atomZ_of_current
      decReference.certified _ (decFrames.ligandAt j)]
  exact rootZ

private theorem atomZ_eq_of_priorTie {i j : Fin 4}
    (priorTie : decReference.certified.compareLocalizedRerootCompoundRule4bcKeys
      (decFrames.compounds i).prior (decFrames.compounds j).prior = .eq) :
    graph.atomZ (decReference.certified.detectedMultiCenterMolecule.ligandAtomAt
        decFrames.center (decFrames.detectedLigandPermutation i)) =
      graph.atomZ (decReference.certified.detectedMultiCenterMolecule.ligandAtomAt
        decFrames.center (decFrames.detectedLigandPermutation j)) := by
  have rule4aTie :=
    ((decReference.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff _ _).mp
      priorTie).1
  obtain ⟨armL⟩ := nonempty_rootArm decFrames .rule4a i
  obtain ⟨armR⟩ := nonempty_rootArm decFrames .rule4a j
  have constitutionalTie := armTie_of_rule4aTie decFrames armL armR rule4aTie
  have columns := (officialRuleMajorKey_compare_eq_iff _ _).mp constitutionalTie
  have rule1aTie := (compareSparseLayers_compareNat_eq_iff _ _).mpr columns.1
  have rootZ := LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.actual_rule1a_tie_rootAtomicNumber_eq
    decReference.certified armL.built armR.built rule1aTie
  have currentL := decFrames.ligandAt i
  have currentR := decFrames.ligandAt j
  rw [← LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.cursorRootAtomicNumber_eq_atomZ_of_current
      decReference.certified _ currentL,
    ← LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.cursorRootAtomicNumber_eq_atomZ_of_current
      decReference.certified _ currentR]
  exact rootZ

/-- A full tie of the actual root compounds forces equal actual states at the two arm cursors. -/
theorem fullTie_armStates_eq {i j : Fin 4}
    (fullTie : decReference.certified.compareLocalizedRerootCompoundRule45Keys
      (decFrames.compounds i) (decFrames.compounds j) = Ordering.eq) :
    referenceState decReference (decFrames.frame.cursorAt i).occurrence =
      referenceState decReference (decFrames.frame.cursorAt j).occurrence := by
  obtain ⟨_priorTie, readingsTie⟩ :=
    fullTie_rule45Tie_prior_and_readings decReference.certified _ _ fullTie
  obtain ⟨headL, tailL, eqL⟩ :=
    fullTie_list_exists_cons_of_ne_nil (compound_rule5Readings_ne_nil' decFrames i)
  obtain ⟨headR, tailR, eqR⟩ :=
    fullTie_list_exists_cons_of_ne_nil (compound_rule5Readings_ne_nil' decFrames j)
  have consTie : decReference.certified.compareLocalizedRerootCompoundRule5Readings .R
      (headL :: tailL) (headR :: tailR) = Ordering.eq := by
    rw [← eqL, ← eqR]
    exact readingsTie
  have heads := fullTie_compareRule5Readings_cons_cons_eq decReference.certified .R headL headR
    tailL tailR consTie
  have commonR : headL.commonR.descriptor = headR.commonR.descriptor := by
    simpa only [localizedRerootRule5Descriptor] using heads
  have leftMember : headL ∈ (decFrames.compounds i).rule5Readings := by
    rw [eqL]
    exact List.mem_cons_self
  have rightMember : headR ∈ (decFrames.compounds j).rule5Readings := by
    rw [eqR]
    exact List.mem_cons_self
  obtain ⟨armL⟩ := nonempty_rootArm decFrames
    (localizedRule5StageFor headL.prior.reference? .R) i
  obtain ⟨armR⟩ := nonempty_rootArm decFrames
    (localizedRule5StageFor headR.prior.reference? .R) j
  have keyL := arm_key_eq_of_built armL (compound_commonR_built decFrames i leftMember)
  have keyR := arm_key_eq_of_built armR (compound_commonR_built decFrames j rightMember)
  have descriptors : armL.key.descriptor = armR.key.descriptor := by
    rw [keyL, keyR]
    exact commonR
  have leftAt : armL.tree.decoratedSubtreeAt? [] = some armL.tree := rfl
  have rightAt : armR.tree.decoratedSubtreeAt? [] = some armR.tree := rfl
  have labels := commonReading_labels_eq armL armR descriptors [] armL.tree armR.tree
    leftAt rightAt
  have leftFacts := arm_subtree_branch_facts decFrames decAddress decReal i armL leftAt
  have rightFacts := arm_subtree_branch_facts decFrames decAddress decReal j armR rightAt
  have leftState : armL.tree.label =
      referenceState decReference (decFrames.frame.cursorAt i).occurrence := by
    calc
      armL.tree.label = contextOccurrenceRead decReference decTarget armL.tree.source :=
        arm_label_eq_read armL [] armL.tree leftAt
      _ = referenceState decReference armL.tree.source.occurrence := by
        change decReference.certified.localizedDependencyLabel decTarget
          (decReference.certified.localizedDependencyView (referenceState decReference) decTarget)
          armL.tree.source = _
        exact decReference.certified.localizedDependencyLabel_eq_state_of_dependency decTarget
          (referenceState decReference) armL.tree.source leftFacts.2.2.2
      _ = referenceState decReference (decFrames.frame.cursorAt i).occurrence := by
        rw [armL.sourceEq]
  have rightState : armR.tree.label =
      referenceState decReference (decFrames.frame.cursorAt j).occurrence := by
    calc
      armR.tree.label = contextOccurrenceRead decReference decTarget armR.tree.source :=
        arm_label_eq_read armR [] armR.tree rightAt
      _ = referenceState decReference armR.tree.source.occurrence := by
        change decReference.certified.localizedDependencyLabel decTarget
          (decReference.certified.localizedDependencyView (referenceState decReference) decTarget)
          armR.tree.source = _
        exact decReference.certified.localizedDependencyLabel_eq_state_of_dependency decTarget
          (referenceState decReference) armR.tree.source rightFacts.2.2.2
      _ = referenceState decReference (decFrames.frame.cursorAt j).occurrence := by
        rw [armR.sourceEq]
  exact leftState.symm.trans (labels.trans rightState)

private theorem compoundTie_of_keys_eq {i j : Fin 4}
    (keys : canonicalCutKeys decReference simple_bonded decRoot i =
      canonicalCutKeys decReference simple_bonded decRoot j) :
    decReference.certified.compareLocalizedRerootCompoundRule45Keys
      (decFrames.compounds i) (decFrames.compounds j) = Ordering.eq := by
  have keyCmp : compare
      (canonicalCutKeys decReference simple_bonded decRoot i)
      (canonicalCutKeys decReference simple_bonded decRoot j) = Ordering.eq :=
    (completeLigandRule5Key_compare_eq_iff _ _).mpr keys
  have retainedEq := canonicalCutKeys_eq_retainedKeys (input := decReference) simple_bonded decRoot
  dsimp [canonicalCutKeys, LocalizedCyclicRootIndependentJudgment.canonicalCutKeys] at keyCmp
  rw [retainedEq] at keyCmp
  have ordering := decFrames.retainedActual_fullOrdering simple_bonded i j
  rw [CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_ordering] at ordering
  exact ordering.trans keyCmp

/-- **The actual four retained root keys are injective.** -/
theorem root_keys_injective (raw : RS)
    (stateA : referenceState decReference armTargetA = some (.chiral raw)) :
    Function.Injective (canonicalCutKeys decReference simple_bonded decRoot) := by
  intro i j keys
  by_contra different
  have fullTie := compoundTie_of_keys_eq keys
  have priorTie := (fullTie_rule45Tie_prior_and_readings decReference.certified _ _ fullTie).1
  rcases slots_of_atomZ_eq (atomZ_eq_of_priorTie priorTie) with same | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact different same
  · have states := fullTie_armStates_eq fullTie
    rw [show (decFrames.frame.cursorAt slotA).occurrence = armTargetA from rfl,
      show (decFrames.frame.cursorAt slotB).occurrence = armTargetB from rfl, stateA,
      stateB_of_stateA stateA] at states
    cases raw <;> simp [RS.swap] at states
  · have states := fullTie_armStates_eq fullTie
    rw [show (decFrames.frame.cursorAt slotA).occurrence = armTargetA from rfl,
      show (decFrames.frame.cursorAt slotB).occurrence = armTargetB from rfl, stateA,
      stateB_of_stateA stateA] at states
    cases raw <;> simp [RS.swap] at states

/-- **The actual root returns a descriptor.** -/
theorem root_returns : ∃ descriptor : LocalizedAuxiliaryLabel,
    referenceState decReference decTarget = some descriptor := by
  obtain ⟨raw, stateA⟩ := armA_isChiral
  have injective := root_keys_injective raw stateA
  obtain ⟨pointAt, _observed, _volume, _sign, frameCoordinates, volume⟩ :=
    frames_coordinates (singleBonded := simple_bonded) (center := decRoot) detectedGeometry
  let points : Fin 4 → CartesianPoint3 :=
    fun slot => pointAt (decFrames.detectedLigandPermutation slot)
  obtain ⟨descriptor, judgment⟩ :=
    (LocalizedRetainedCompleteMirrorCovariance.completeRootDescriptorJudgment_exists_iff
      (canonicalCutKeys decReference simple_bonded decRoot) points).2 ⟨injective, volume⟩
  have retained : RetainedContextualDescriptorJudgmentAt
      decReference.certified.moleculeGraph (descriptorMap decReference)
      (finalCenterUnit decReference decRoot)
      (decFrames.canonicalCutGraphs simple_bonded) decFrames.W decFrames.D
      decFrames.actualCoordinates descriptor := by
    refine ⟨points, ?_, ?_⟩
    · intro slot
      exact frameCoordinates slot
    · simpa [canonicalCutKeys, LocalizedCyclicRootIndependentJudgment.canonicalCutKeys,
        points] using judgment
  exact ⟨descriptor, (decFrames.referenceState_some_iff_canonicalCutJudgment
    simple_bonded descriptor).2 retained⟩

/-- Exactly one unordered pair satisfies a two-element symmetric relation. -/
theorem pairCount_one (a b : Fin 4) (distinct : a ≠ b)
    [DecidableRel (fun x y : Fin 4 => (x = a ∧ y = b) ∨ (x = b ∧ y = a))] :
    sourceEnantiomorphicPairCount (fun x y : Fin 4 => (x = a ∧ y = b) ∨ (x = b ∧ y = a)) = 1 := by
  fin_cases a <;> fin_cases b <;> simp_all [sourceEnantiomorphicPairCount]

/-- **The actual retained prior pairs of the root are exactly the two decorated arms.** -/
theorem retainedPriorPair_iff (i j : Fin 4) (distinct : i ≠ j) :
    CompletePriorPair decFrames.retainedKeys i j ↔
      (i = slotA ∧ j = slotB) ∨ (i = slotB ∧ j = slotA) := by
  constructor
  · rintro ⟨_, priorEq⟩
    have priorTie := (decFrames.retainedActual_priorComparison simple_bonded i j).trans
      ((completeLigandPriorKey_compare_eq_iff _ _).mpr priorEq)
    rcases slots_of_atomZ_eq (atomZ_eq_of_priorTie priorTie) with same | pair | pair
    · exact absurd same distinct
    · exact Or.inl pair
    · exact Or.inr pair
  · have tieAB : (ofLex (decFrames.retainedKeys slotA)).1 = (ofLex (decFrames.retainedKeys slotB)).1 :=
      (completeLigandPriorKey_compare_eq_iff _ _).mp
        ((decFrames.retainedActual_priorComparison simple_bonded slotA slotB).symm.trans
          armsPriorTie)
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨slots_ne, tieAB⟩
    · exact ⟨slots_ne.symm, tieAB.symm⟩

theorem retainedPairCount_eq_one : completeRule5PairCount decFrames.retainedKeys = 1 := by
  unfold completeRule5PairCount
  rw [sourceEnantiomorphicPairCount_congr (CompletePriorPair decFrames.retainedKeys)
    (fun x y : Fin 4 => (x = slotA ∧ y = slotB) ∨ (x = slotB ∧ y = slotA))
    retainedPriorPair_iff]
  exact pairCount_one slotA slotB slots_ne

/-- **Every descriptor returned by the actual root is lowercase.** -/
theorem root_returned_isLowercase {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState decReference decTarget = some descriptor) :
    descriptor.IsLowercase := by
  have iff := decFrames.referenceState_lowercase_iff_canonicalCut simple_bonded returned
  have keysEq : retainedContextualFrameKeysAt decReference.certified.moleculeGraph
      (descriptorMap decReference) (finalCenterUnit decReference decRoot)
      (decFrames.canonicalCutGraphs simple_bonded) decFrames.W decFrames.D =
      decFrames.retainedKeys :=
    canonicalCutKeys_eq_retainedKeys simple_bonded decRoot
  rw [keysEq] at iff
  exact iff.mpr retainedPairCount_eq_one

/-! ## The counterexample -/

/-- **Success-soundness fails on the recursive calibrated domain.** For the 21-atom single-bond
formal input with calibrated coordinates:

* every physical-domain predicate holds: simple bonds, constant formal charge, every non-root
  detected centre calibrated, calibrated root geometry, and the root branches pairwise properly
  distinguishable; no two distinct root branches are related by any proper or mirror transport, so
  the physical enantiomorphic pair count is `0`;
* yet the actual generated states at the two decorated arm centres are opposite uppercase letters,
  the two arms have an actual prior tie, the actual root **returns** a descriptor, that descriptor is
  **lowercase**, and `analyze` reports it.

Hence an actual returned lowercase status does not agree with the physical enantiomorphic-pair
count on this domain. -/
theorem successfulFalseLowercase :
    decReference.certified.moleculeGraph.SimpleBonded ∧
    AcyclicCutBranchAutomorphism.ConstantFormalCharge decReference.certified.moleculeGraph ∧
    RecursiveAuxiliaryPhysicalDomain decReference.certified detectedCfg decRoot ∧
    RootPhysicalGeometry decReference.certified decReference.certified.detectedMultiCenterMolecule
      detectedCfg decRoot ∧
    MultiCenterMolecule.PairwiseProperDistinguishable
      decReference.certified.detectedMultiCenterMolecule detectedCfg decRoot ∧
    (∀ i j : Fin 4, i ≠ j → ∀ mirror : Bool,
      ¬ BranchTransport decReference.certified.detectedMultiCenterMolecule detectedCfg decRoot i j
        mirror) ∧
    physicalEnantiomorphicPairCount decReference.certified.detectedMultiCenterMolecule detectedCfg
      decRoot = 0 ∧
    (∃ raw : RS, referenceState decReference armTargetA = some (.chiral raw) ∧
      referenceState decReference armTargetB = some (.chiral (RS.swap raw))) ∧
    decReference.certified.compareLocalizedRerootCompoundRule4bcKeys
      (decFrames.compounds slotA).prior (decFrames.compounds slotB).prior = .eq ∧
    ∃ descriptor : LocalizedAuxiliaryLabel,
      referenceState decReference decTarget = some descriptor ∧ descriptor.IsLowercase ∧
        (decRoot.val.val, some descriptor) ∈ analyze decReference := by
  obtain ⟨raw, stateA⟩ := armA_isChiral
  obtain ⟨descriptor, returned⟩ := root_returns
  refine ⟨simple_bonded, constant_charge, detectedDomain, detectedGeometry, detectedPairwise,
    fun i j distinct mirror => detected_noTransport i j mirror distinct, detectedPairCount,
    ⟨raw, stateA, stateB_of_stateA stateA⟩, armsPriorTie, descriptor, returned,
    root_returned_isLowercase returned, ?_⟩
  rw [analyze_eq_referenceReport decReference]
  exact List.mem_map.mpr ⟨decRoot,
    (decReference.certified.mem_canonicalTetrahedralCenters_iff decRoot).mpr decRoot.2,
    Prod.ext rfl returned⟩

/-- The conditional success-soundness statement is false here: a returned descriptor is lowercase
although the physical pair count is not one. -/
theorem not_successSound :
    ¬ ∀ descriptor : LocalizedAuxiliaryLabel,
      referenceState decReference decTarget = some descriptor →
        (descriptor.IsLowercase ↔
          physicalEnantiomorphicPairCount decReference.certified.detectedMultiCenterMolecule
            detectedCfg decRoot = 1) := by
  intro sound
  obtain ⟨descriptor, returned⟩ := root_returns
  have lower := root_returned_isLowercase returned
  have count := (sound descriptor returned).mp lower
  rw [detectedPairCount] at count
  exact absurd count (by decide)

end

end TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction.armsPriorTie
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction.stateB_of_stateA
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction.armA_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction.armA_isChiral
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction.root_keys_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction.root_returns
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction.retainedPairCount_eq_one
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction.root_returned_isLowercase
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction.successfulFalseLowercase
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction.not_successSound
