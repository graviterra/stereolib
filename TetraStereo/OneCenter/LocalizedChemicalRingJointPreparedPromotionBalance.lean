import Mathlib.Data.List.Perm.Basic
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRefusalCharacterization
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalTransport
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionOutcomes
import TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport
import TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransportExecution
import TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts
import TetraStereo.OneCenter.LocalizedChemicalRingResidualOrientationStep
import TetraStereo.OneCenter.LocalizedMarkedCarrierLookup
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
# Actual selected promotion balance under an odd boundary symmetry

The actual selected fallback family of `LocalizedChemicalRingJointPreparedPromotionOutcomes`
is indexed by the slots of the detected molecular frame.  An odd physical symmetry fixing the
occurrence history and the retained references acts on those slots by `slotAction`.  This module
derives, without assuming any population covariance:

* the actual selected slots are only permuted by `slotAction` (the covariance is extracted from
  the accepted joint-operation context-order transport and the actual generated-state
  congruence);
* each selected actual fallback at the image slot is the optional R/S swap of the fallback at
  the source slot, using calibrated physical transport at the same observed geometry;
* consequently the actual selected fallback multiset is paired with its pointwise optional-R/S
  swap, on either observed geometry side and for every retained reference list.

The resulting signed promotion balance is therefore `some 0`, not `none`.  The conversion from
an absent optional reading to the completed `unresolved` outcome is *not* an identification with
operational failure: it is the proved physical completeness theorem
`promotionOutcomeAt_eq_completed` of the existing actual-outcome module, whose proof uses the
calibrated `fallback_none_iff`.  No runtime policy, rule applicability, desired descriptor or
source-step joining is changed here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open DeclarativeCIP.ProductionOccurrenceRules456
open LocalizedChemicalRingInheritedRefusalCases
  (OccurrenceData observedGeometry referenceAt)
open LocalizedChemicalRingJointPreparedExecution (generated fallback)
open LocalizedChemicalRingPreparedContextRecursion (childrenUnder preparedFacts)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingJointMarkerFrameExecution
  (selectedSlots contextOrder?_eq eligible_eq)
open LocalizedChemicalRingJointPreparedPromotionOutcomes
  (actualReadings actualOutcomes actualOutcomes_eq_completed actualAggregate_eq_completed)
open LocalizedChemicalRingPromotionAggregation
  (completedOutcome completedAggregate completedAggregate_eq_none_of_swap_perm
    completedAggregate_eq_consensus readingBalance readingBalance_perm readingBalance_swap
    completed_balance)
open LocalizedChemicalRingResidualThreeCycleRefusal
  (slotAction referenceAt_action center_fixed)
open LocalizedChemicalRingJointPreparedPhysicalTransport
  (map_eq_self_of_pointwise actual_fallback_transport_of_slot strictDescendant_child
    strictDescendant_closed)
open LocalizedChemicalRingResidualOrientationStep (agreeOn_strictDescendants)
open LocalizedChemicalRingSemanticSymmetry (structuralSymmetry_of_aut)
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingSenseTransport (AgreeOn)
open LocalizedChemicalRingOrientationReadback (flipBy_eq_swap)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedChemicalRingJointPreparedRefusalCharacterization (OddBoundarySymmetry)
open LocalizedChemicalRingJointOperationTransport (contextOrder?_ordinaryRel)
open LocalizedChemicalRingJointOperationTransportExecution (actual_preparedChildren_map)
open LocalizedChemicalRingPreparedContextFacts (preparedChildrenUnder_keys_nodup)
open LocalizedChemicalRingJointPreparedCovariance (StateRel)
open LocalizedChemicalRingJointPreparedGeometryCongruence (preparedFacts_congr)
open LocalizedGenericMarkedRecalculation
  (Geometry flatMap_congr_mem frameAtoms? consensus)

noncomputable section
open scoped Classical

/-! ## Geometry congruence of actual generated states -/

/-- Generated actual child facts depend on the geometry only through strict-descendant
readbacks.  This is the congruence used to compare the pulled-back image context with the
physical context at the fixed occurrence. -/
theorem generated_congr
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (first second : Geometry)
    (node : RawMolecule.CanonicalBranchNode) (references : List input.Atom)
    (agree : AgreeOn (StrictDescendant mol node) mol first second) :
    generated input mol depth first node references =
      generated input mol depth second node references := by
  have funEq :
      childrenUnder mol (preparedFacts mol (jointOperations input mol) depth) first [] node =
        childrenUnder mol (preparedFacts mol (jointOperations input mol) depth) second [] node := by
    funext M
    unfold childrenUnder
    exact flatMap_congr_mem _ _ _
      (fun child member =>
        preparedFacts_congr mol (jointOperations input mol) (StrictDescendant mol node)
          (strictDescendant_closed mol node) depth first second agree [] M child
          (strictDescendant_child mol node child member))
  unfold generated
  exact congrFun funEq (references.map Fin.val)

/-! ## A pure list core -/

/-- If a list of slots is permuted by `action`, and every selected reading at the image slot is
the optional R/S swap of the reading at the source slot, then the reading list is permuted by
its pointwise optional swap. -/
theorem list_perm_map_swap_of_perm_action {α : Type} (S : List α) (action : α → α)
    (read : α → Option RS)
    (permutation : S.Perm (S.map action))
    (readSwap : ∀ slot ∈ S, read (action slot) = (read slot).map RS.swap) :
    (S.map read).Perm ((S.map read).map (Option.map RS.swap)) := by
  have rhs : (S.map read).map (Option.map RS.swap) = (S.map action).map read := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro slot member
    rw [Function.comp_apply, Function.comp_apply]
    exact (readSwap slot member).symm
  have permMap : (S.map read).Perm ((S.map action).map read) :=
    List.Perm.map read permutation
  rwa [← rhs] at permMap

/-! ## Selected-slot covariance under the odd slot action -/

/-- The actual selected slot population of the physical generated context is preserved, up to
permutation, by the slot action induced by a history-fixing molecular automorphism.  No selected
set covariance is assumed: this is derived from the accepted joint-operation context-order
transport, the actual generated-state map, and strict-descendant geometry congruence. -/
theorem selectedSlots_perm_slotAction
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node)
    (reached : Reached mol node) (current : node.atom = c.1.val)
    (ePhys : input.detectedMultiCenterMolecule.Aut)
    (historyFixed : ∀ atom ∈ node.history,
      relabelOf input (ePhys : Equiv.Perm input.Atom) atom = atom)
    (references : List input.Atom)
    (fixedReferences : ∀ reference ∈ references,
      ((ePhys : Equiv.Perm input.Atom) reference).val = reference.val)
    (depth : Nat) (geom : Geometry)
    (childAgree : AgreeOn (StrictDescendant mol node) mol
      (pullback (relabelOf input (ePhys : Equiv.Perm input.Atom)) geom) geom) :
    List.Perm
      (selectedSlots input mol single c node data
        (generated input mol depth geom node references) references)
      ((selectedSlots input mol single c node data
        (generated input mol depth geom node references) references).map
        (slotAction input mol ePhys c node data)) := by
  let graphAut : input.moleculeGraph.Aut :=
    ⟨ePhys, MultiCenterMolecule.Aut.mem_molAut input.detectedMultiCenterMolecule ePhys⟩
  have historyFixedGraph : ∀ atom ∈ node.history,
      relabelOf input (graphAut : Equiv.Perm input.Atom) atom = atom :=
    fun atom member => historyFixed atom member
  have fixedReferencesGraph : ∀ reference ∈ references,
      ((graphAut : Equiv.Perm input.Atom) reference).val = reference.val :=
    fun reference member => fixedReferences reference member
  have childAgreeGraph : AgreeOn (StrictDescendant mol node) mol
      (pullback (relabelOf input (graphAut : Equiv.Perm input.Atom)) geom) geom :=
    childAgree
  have hnode : mapNode (relabelOf input (graphAut : Equiv.Perm input.Atom)) node = node :=
    LocalizedChemicalRingResidualReadingTransport.mapNode_eq_of_history_fixed mol _
      node reached historyFixedGraph
  have hL : (references.map Fin.val).map
        (relabelOf input (graphAut : Equiv.Perm input.Atom)) = references.map Fin.val := by
    apply map_eq_self_of_pointwise
    intro mark member
    rw [List.mem_map] at member
    obtain ⟨reference, refMember, rfl⟩ := member
    exact (relabelOf_val input (graphAut : Equiv.Perm input.Atom) reference).trans
      (fixedReferencesGraph reference refMember)
  have hchildren :
      StateRel (relabelOf input (graphAut : Equiv.Perm input.Atom))
        (generated input mol depth geom node references)
        (generated input mol depth
          (pullback (relabelOf input (graphAut : Equiv.Perm input.Atom)) geom) node references) := by
    have h := actual_preparedChildren_map input mol agreement admissible supported single graphAut
      (structuralSymmetry_of_aut input mol agreement admissible supported ePhys)
      depth geom (references.map Fin.val) node reached
    simp only [hL, hnode] at h
    simpa only [generated] using h
  have unique :
      ((generated input mol depth
        (pullback (relabelOf input (graphAut : Equiv.Perm input.Atom)) geom)
        node references).map (·.key)).Nodup := by
    have h := preparedChildrenUnder_keys_nodup mol (jointOperations input mol) admissible.1.1
      (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
      admissible.1.2 depth
      (pullback (relabelOf input (graphAut : Equiv.Perm input.Atom)) geom) [] node
      (references.map Fin.val)
    simpa only [generated] using h
  have raw' : frameAtoms? mol
      (mapNode (relabelOf input (graphAut : Equiv.Perm input.Atom)) node) =
        some data.atoms := by
    rw [hnode]
    exact data.rawFrame
  have rel := contextOrder?_ordinaryRel input mol agreement admissible supported single graphAut
    (structuralSymmetry_of_aut input mol agreement admissible supported ePhys)
    node reached data.atoms data.atoms data.rawFrame raw'
    (generated input mol depth
      (pullback (relabelOf input (graphAut : Equiv.Perm input.Atom)) geom) node references)
    (generated input mol depth geom node references)
    hchildren unique (references.map Fin.val)
  have rel' := rel
  simp only [hL, hnode] at rel'
  rw [contextOrder?_eq input mol single c node data
        (generated input mol depth geom node references) references,
      contextOrder?_eq input mol single c node data
        (generated input mol depth
          (pullback (relabelOf input (graphAut : Equiv.Perm input.Atom)) geom) node references)
        references] at rel'
  rw [LocalizedChemicalRingSenseTransport.ordinaryRel_some_some] at rel'
  obtain ⟨_, _, _, eligiblePerm⟩ := rel'
  rw [eligible_eq input mol single c node data
        (generated input mol depth geom node references) references,
      eligible_eq input mol single c node data
        (generated input mol depth
          (pullback (relabelOf input (graphAut : Equiv.Perm input.Atom)) geom) node references)
        references] at eligiblePerm
  have hstate :
      generated input mol depth
          (pullback (relabelOf input (graphAut : Equiv.Perm input.Atom)) geom) node references =
        generated input mol depth geom node references :=
    generated_congr input mol depth
      (pullback (relabelOf input (graphAut : Equiv.Perm input.Atom)) geom) geom node references
      childAgreeGraph
  rw [hstate] at eligiblePerm
  have refInjective : Function.Injective
      (fun slot : Fin 4 => (referenceAt input mol c node data slot).val) := by
    intro a b equal
    apply data.ligandOf.injective
    apply input.detectedMultiCenterMolecule.ligandAtomAt_injective c
    apply Fin.ext
    simpa only [referenceAt] using equal
  have centerFixed := center_fixed input mol ePhys c node reached current historyFixed
  have mapEq :
      (List.map (fun slot : Fin 4 => (referenceAt input mol c node data slot).val)
        (selectedSlots input mol single c node data
          (generated input mol depth geom node references) references)).map
        (relabelOf input (graphAut : Equiv.Perm input.Atom)) =
      ((selectedSlots input mol single c node data
        (generated input mol depth geom node references) references).map
        (slotAction input mol ePhys c node data)).map
        (fun slot : Fin 4 => (referenceAt input mol c node data slot).val) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro slot _
    rw [Function.comp_apply, Function.comp_apply, relabelOf_val]
    exact congrArg (fun atom : input.Atom => atom.val)
      (referenceAt_action input mol ePhys c node data centerFixed slot).symm
  have permIndices : List.Perm
      (selectedSlots input mol single c node data
        (generated input mol depth geom node references) references)
      ((selectedSlots input mol single c node data
        (generated input mol depth geom node references) references).map
        (slotAction input mol ePhys c node data)) := by
    rw [mapEq] at eligiblePerm
    exact (List.map_perm_map_iff refInjective).mp eligiblePerm
  exact permIndices

/-! ## Per-slot physical fallback transport -/

/-- Under an odd physical symmetry, the actual fallback at the image slot is exactly the
optional R/S swap of the actual fallback at the source slot, at the same observed geometry. -/
theorem fallback_slotAction_eq_map_swap
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node)
    (reached : Reached mol node) (current : node.atom = c.1.val)
    (ePhys : input.detectedMultiCenterMolecule.Aut)
    (historyFixed : ∀ atom ∈ node.history,
      relabelOf input (ePhys : Equiv.Perm input.Atom) atom = atom)
    (references : List input.Atom)
    (fixedReferences : ∀ reference ∈ references,
      ((ePhys : Equiv.Perm input.Atom) reference).val = reference.val)
    (depth : Nat) (reflected : Bool)
    (childAgree : AgreeOn (StrictDescendant mol node) mol
      (pullback (relabelOf input (ePhys : Equiv.Perm input.Atom))
        (observedGeometry input reflected))
      (observedGeometry input reflected))
    (odd : relativeSign input.detectedMultiCenterMolecule cfg ePhys c = -1)
    (slot : Fin 4) :
    fallback input mol c node data depth (observedGeometry input reflected) references
        (slotAction input mol ePhys c node data slot) =
      (fallback input mol c node data depth (observedGeometry input reflected) references
        slot).map RS.swap := by
  let graphAut : input.moleculeGraph.Aut :=
    ⟨ePhys, MultiCenterMolecule.Aut.mem_molAut input.detectedMultiCenterMolecule ePhys⟩
  have historyFixedGraph : ∀ atom ∈ node.history,
      relabelOf input (graphAut : Equiv.Perm input.Atom) atom = atom :=
    fun atom member => historyFixed atom member
  have fixedReferencesGraph : ∀ reference ∈ references,
      ((graphAut : Equiv.Perm input.Atom) reference).val = reference.val :=
    fun reference member => fixedReferences reference member
  have childAgreeGraph : AgreeOn (StrictDescendant mol node) mol
      (pullback (relabelOf input (graphAut : Equiv.Perm input.Atom))
        (observedGeometry input reflected))
      (observedGeometry input reflected) :=
    childAgree
  have centerFixed := center_fixed input mol ePhys c node reached current historyFixed
  have moves :
      relabelOf input (graphAut : Equiv.Perm input.Atom)
          (referenceAt input mol c node data slot).val =
        (referenceAt input mol c node data
          (slotAction input mol ePhys c node data slot)).val := by
    rw [relabelOf_val]
    exact congrArg (fun atom : input.Atom => atom.val)
      (referenceAt_action input mol ePhys c node data centerFixed slot).symm
  have transported := actual_fallback_transport_of_slot input mol agreement admissible supported
    single cfg graphAut ePhys rfl
    (structuralSymmetry_of_aut input mol agreement admissible supported ePhys)
    calibrated c node current reached data reflected childAgreeGraph depth references
    historyFixedGraph fixedReferencesGraph slot
    (slotAction input mol ePhys c node data slot) moves
  rw [flipBy_eq_swap (relativeSign input.detectedMultiCenterMolecule cfg ePhys c)
    (by rw [odd]; norm_num)] at transported
  exact transported

/-! ## The actual selected fallback multiset is swap-paired -/

/-- The actual selected fallback family at any reached occurrence carrying an odd boundary
symmetry is permuted by the pointwise optional R/S swap, for every retained reference list and
either observed geometry side. -/
theorem actualReadings_perm_swap_of_oddBoundary
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node)
    (reached : Reached mol node) (current : node.atom = c.1.val)
    (B references : List input.Atom)
    (boundary : data.target.1.node.history.reverse = B ++ [c.1])
    (outside : c.1 ∉ B)
    (depth : Nat) (reflected : Bool)
    (obstruction : OddBoundarySymmetry input cfg c B references) :
    List.Perm
      (actualReadings input mol single c node data depth references reflected)
      ((actualReadings input mol single c node data depth references reflected).map
        (Option.map RS.swap)) := by
  obtain ⟨ePhys, fixedBoundary, fixedReferences, odd, properOff⟩ := obstruction
  have sound : data.target.1.node.history.map (fun atom : input.Atom => atom.val) =
      node.history :=
    (LocalizedMarkedCarrierLookup.lookup?_sound input node data.target data.found).history
  have carriedAll : ∀ atom ∈ B ++ [c.1], atom.val ∈ node.history := by
    intro atom member
    rw [← sound]
    exact List.mem_map.mpr
      ⟨atom, List.mem_reverse.mp (boundary.symm ▸ member), rfl⟩
  have carried : ∀ atom ∈ B, atom.val ∈ node.history :=
    fun atom member => carriedAll atom (List.mem_append_left [c.1] member)
  have historyFixed : ∀ value ∈ node.history,
      relabelOf input (ePhys : Equiv.Perm input.Atom) value = value := by
    intro value member
    rw [← sound] at member
    obtain ⟨atom, present, rfl⟩ := List.mem_map.mp member
    have inB : atom ∈ B ++ [c.1] := boundary ▸ List.mem_reverse.mpr present
    rw [relabelOf_val, fixedBoundary atom inB]
  have fixedReferencesVal : ∀ reference ∈ references,
      ((ePhys : Equiv.Perm input.Atom) reference).val = reference.val :=
    fun reference member =>
      congrArg (fun atom : input.Atom => atom.val) (fixedReferences reference member)
  have proper : ∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph B c.1 d.1 → d.1 ≠ c.1 →
        relativeSign input.detectedMultiCenterMolecule cfg ePhys d = 1 := by
    intro d member different
    apply properOff
    intro present
    rcases List.mem_append.mp present with inB | last
    · exact inComponent_not_mem input.moleculeGraph member inB
    · exact different (List.mem_singleton.mp last)
  have base := agreeOn_strictDescendants input mol agreement admissible supported single cfg ePhys
    calibrated B node c.1 current.symm outside carried reached proper
  have childAgree : AgreeOn (StrictDescendant mol node) mol
      (pullback (relabelOf input (ePhys : Equiv.Perm input.Atom))
        (observedGeometry input reflected))
      (observedGeometry input reflected) := by
    cases reflected with
    | false => exact base
    | true =>
        simpa only [observedGeometry, Bool.true_eq, if_true, mirror_pullback] using base.mirror
  have selectedPerm : List.Perm
      (selectedSlots input mol single c node data
        (generated input mol depth (observedGeometry input reflected) node references) references)
      ((selectedSlots input mol single c node data
        (generated input mol depth (observedGeometry input reflected) node references) references).map
        (slotAction input mol ePhys c node data)) :=
    selectedSlots_perm_slotAction input mol agreement admissible supported single c node data
      reached current ePhys historyFixed references fixedReferencesVal depth
      (observedGeometry input reflected) childAgree
  have fallbackSwap : ∀ slot ∈ selectedSlots input mol single c node data
        (generated input mol depth (observedGeometry input reflected) node references) references,
      fallback input mol c node data depth (observedGeometry input reflected) references
          (slotAction input mol ePhys c node data slot) =
        (fallback input mol c node data depth (observedGeometry input reflected) references
          slot).map RS.swap :=
    fun slot _ =>
      fallback_slotAction_eq_map_swap input mol agreement admissible supported single cfg
        calibrated c node data reached current ePhys historyFixed references fixedReferencesVal
        depth reflected childAgree odd slot
  have listPerm := list_perm_map_swap_of_perm_action
    (selectedSlots input mol single c node data
      (generated input mol depth (observedGeometry input reflected) node references) references)
    (slotAction input mol ePhys c node data)
    (fallback input mol c node data depth (observedGeometry input reflected) references)
    selectedPerm fallbackSwap
  simpa only [actualReadings] using listPerm

/-! ## Balance and consensus endpoints -/

/-- Pure adapter corollary: a completed optional-reading list paired with its pointwise R/S swap
has signed promotion balance exactly zero.  The physical input list must still be justified as
completed nonuniqueness, not operational failure. -/
theorem completedPromotionBalance_eq_zero_of_swap_perm (readings : List (Option RS))
    (permutation : readings.Perm (readings.map (Option.map RS.swap))) :
    promotionBalance (readings.map completedOutcome) = some 0 := by
  have balanceEq := readingBalance_perm permutation
  rw [readingBalance_swap] at balanceEq
  have zero : readingBalance readings = 0 := by omega
  rw [completed_balance, zero]

/-- The completed actual selected family has signed promotion balance zero under an odd
boundary symmetry. -/
theorem actualCompletedPromotionBalance_eq_zero_of_oddBoundary
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node)
    (reached : Reached mol node) (current : node.atom = c.1.val)
    (B references : List input.Atom)
    (boundary : data.target.1.node.history.reverse = B ++ [c.1])
    (outside : c.1 ∉ B)
    (depth : Nat) (reflected : Bool)
    (obstruction : OddBoundarySymmetry input cfg c B references) :
    promotionBalance
        ((actualReadings input mol single c node data depth references reflected).map
          completedOutcome) = some 0 :=
  completedPromotionBalance_eq_zero_of_swap_perm _
    (actualReadings_perm_swap_of_oddBoundary input mol agreement admissible supported single cfg
      calibrated c node data reached current B references boundary outside depth reflected
      obstruction)

/-- The actual promotion outcomes themselves have signed balance zero: the calibrated
completeness theorem turns absent readings into completed `unresolved`, never into operational
failure. -/
theorem actualPromotionBalance_eq_zero_of_oddBoundary
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node)
    (reached : Reached mol node) (current : node.atom = c.1.val)
    (B references : List input.Atom)
    (boundary : data.target.1.node.history.reverse = B ++ [c.1])
    (outside : c.1 ∉ B)
    (depth : Nat) (reflected : Bool)
    (obstruction : OddBoundarySymmetry input cfg c B references) :
    promotionBalance (actualOutcomes input mol single c node data depth references reflected) =
      some 0 := by
  rw [actualOutcomes_eq_completed input mol single c node data depth references reflected
    agreement admissible supported cfg (calibrated c)]
  exact actualCompletedPromotionBalance_eq_zero_of_oddBoundary input mol agreement admissible
    supported single cfg calibrated c node data reached current B references boundary outside
    depth reflected obstruction

/-- The completed actual aggregate is the accepted empty consensus, not a fail-closed `none`. -/
theorem actualCompletedAggregate_eq_none_of_oddBoundary
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node)
    (reached : Reached mol node) (current : node.atom = c.1.val)
    (B references : List input.Atom)
    (boundary : data.target.1.node.history.reverse = B ++ [c.1])
    (outside : c.1 ∉ B)
    (depth : Nat) (reflected : Bool)
    (obstruction : OddBoundarySymmetry input cfg c B references) :
    completedAggregate (actualReadings input mol single c node data depth references reflected) =
      some none :=
  completedAggregate_eq_none_of_swap_perm _
    (actualReadings_perm_swap_of_oddBoundary input mol agreement admissible supported single cfg
      calibrated c node data reached current B references boundary outside depth reflected
      obstruction)

/-- The actual fail-closed outcome aggregate equals the accepted empty consensus. -/
theorem actualAggregate_eq_none_of_oddBoundary
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node)
    (reached : Reached mol node) (current : node.atom = c.1.val)
    (B references : List input.Atom)
    (boundary : data.target.1.node.history.reverse = B ++ [c.1])
    (outside : c.1 ∉ B)
    (depth : Nat) (reflected : Bool)
    (obstruction : OddBoundarySymmetry input cfg c B references) :
    promotionAggregate (actualOutcomes input mol single c node data depth references reflected) =
      some none := by
  rw [actualAggregate_eq_completed input mol single c node data depth references reflected
    agreement admissible supported cfg (calibrated c)]
  exact actualCompletedAggregate_eq_none_of_oddBoundary input mol agreement admissible supported
    single cfg calibrated c node data reached current B references boundary outside depth
    reflected obstruction

/-- The actual selected family has the accepted empty consensus. -/
theorem actualConsensus_eq_none_of_oddBoundary
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node)
    (reached : Reached mol node) (current : node.atom = c.1.val)
    (B references : List input.Atom)
    (boundary : data.target.1.node.history.reverse = B ++ [c.1])
    (outside : c.1 ∉ B)
    (depth : Nat) (reflected : Bool)
    (obstruction : OddBoundarySymmetry input cfg c B references) :
    consensus (actualReadings input mol single c node data depth references reflected) = none := by
  have permutation := actualReadings_perm_swap_of_oddBoundary input mol agreement admissible
    supported single cfg calibrated c node data reached current B references boundary outside
    depth reflected obstruction
  have aggregate := completedAggregate_eq_none_of_swap_perm
    (actualReadings input mol single c node data depth references reflected) permutation
  rw [completedAggregate_eq_consensus
    (actualReadings input mol single c node data depth references reflected)
    (fun _ => permutation)] at aggregate
  exact Option.some.inj aggregate

/-- The completed actual aggregate equals the actual accepted consensus on this family. -/
theorem actualCompletedAggregate_eq_consensus_of_oddBoundary
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node)
    (reached : Reached mol node) (current : node.atom = c.1.val)
    (B references : List input.Atom)
    (boundary : data.target.1.node.history.reverse = B ++ [c.1])
    (outside : c.1 ∉ B)
    (depth : Nat) (reflected : Bool)
    (obstruction : OddBoundarySymmetry input cfg c B references) :
    completedAggregate (actualReadings input mol single c node data depth references reflected) =
      some (consensus (actualReadings input mol single c node data depth references reflected)) :=
  completedAggregate_eq_consensus _
    (fun _ =>
      actualReadings_perm_swap_of_oddBoundary input mol agreement admissible supported single cfg
        calibrated c node data reached current B references boundary outside depth reflected
        obstruction)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance.generated_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance.list_perm_map_swap_of_perm_action
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance.selectedSlots_perm_slotAction
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance.fallback_slotAction_eq_map_swap
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance.actualReadings_perm_swap_of_oddBoundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance.completedPromotionBalance_eq_zero_of_swap_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance.actualCompletedPromotionBalance_eq_zero_of_oddBoundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance.actualPromotionBalance_eq_zero_of_oddBoundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance.actualCompletedAggregate_eq_none_of_oddBoundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance.actualAggregate_eq_none_of_oddBoundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance.actualConsensus_eq_none_of_oddBoundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance.actualCompletedAggregate_eq_consensus_of_oddBoundary
