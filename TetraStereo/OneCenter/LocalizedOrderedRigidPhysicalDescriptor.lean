import TetraStereo.OneCenter.LocalizedOrderedFirstSphereDescriptor
import TetraStereo.OneCenter.LocalizedActualRigidFrameCompleteness
import TetraStereo.OneCenter.LocalizedGeneralRigidCalibratedRootReader
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.OneCenter.LocalizedTetrahedralPermutationExistence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Ordered fixed-point labels from local constitutional rigidity

This module joins the actual-frame rigidity and geometry results to the ordered evaluator at its
own fixed-point view. It requires no global physical domain rooted at the target.
-/

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedUniversalReference
open AcyclicCutBranchAutomorphism

noncomputable section
open scoped Classical

private theorem finRangeMapPermFour (e : Equiv.Perm (Fin 4)) :
    ((List.finRange 4).map e).Perm (List.finRange 4) := by
  have nd : ((List.finRange 4).map e).Nodup := (List.nodup_finRange 4).map e.injective
  apply List.perm_of_nodup_nodup_toFinset_eq nd (List.nodup_finRange 4)
  have h₁ : ((List.finRange 4).map e).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup nd]; simp)
  have h₂ : (List.finRange 4).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup (List.nodup_finRange 4)]; simp)
  rw [h₁, h₂]

private theorem mapMCanonicalObserved (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (pointsAt : Fin 4 → CartesianPoint3)
    (observed : ∀ i, input.spatialPointAt? (input.canonicalLigandAtom center i) =
      some (pointsAt i)) :
    ∀ order : List (Fin 4),
      order.mapM (fun i => input.spatialPointAt?
        (input.canonicalLigandAtom center i)) = some (order.map pointsAt) := by
  intro order
  induction order with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.mapM_cons, observed i]
      rw [ih]
      rfl

/-- At a real constitutionally rigid target, the ordered evaluator uses the same strict
highest-first geometry as the independent physical rule-major outcome. The frame and its slot
permutation are actual: no priority, comparator success, or global physical-domain premise is
provided. -/
theorem orderedReferenceState_eq_chiral_iff_independentPhysicalGeometry
    (input : LocalizedUniversalReference.Input) {fuel : Nat}
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame fuel)
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target = some frame)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.certified.moleculeGraph center.1)
    (hacyc : input.certified.moleculeGraph.Acyclic)
    (hsimple : input.certified.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (enough : input.certified.certified.input.molecule.atomCount ≤ fuel)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ i, (frame.cursorAt i).occurrence.1.node.current? =
      some (input.certified.canonicalLigandAtom center (alpha i)))
    (pointsAt : Fin 4 → CartesianPoint3)
    (observed : ∀ i, input.certified.spatialPointAt?
      (input.certified.canonicalLigandAtom center i) = some (pointsAt i))
    (nonzero : CartesianPoint3.orientedVolume (pointsAt 0) (pointsAt 1)
      (pointsAt 2) (pointsAt 3) ≠ 0) :
    ∃ order : List (Fin 4),
      IndependentPhysicalHighestFirst input.certified target
        (input.certified.localizedDependencyView
          (input.certified.orderedReferenceState fuel) target)
        frame derived hsimple hacyc order ∧
      ∀ raw, input.certified.orderedReferenceState fuel target = some (.chiral raw) ↔
        RationalTetrahedralDescriptor (order.map fun i => pointsAt (alpha i)) raw := by
  let view := input.certified.localizedDependencyView
    (input.certified.orderedReferenceState fuel) target
  obtain ⟨order, independent⟩ :=
    exists_independentPhysicalHighestFirst input.certified target view frame derived center
      centerReal rigid hacyc hsimple hcharge enough
  refine ⟨order, independent, ?_⟩
  let keys : Fin 4 → input.certified.LocalizedRerootCompoundRule45Key :=
    frame.compoundKeyAt input.certified target view derived
  have separated : ConstitutionallySeparatedActualKeys input.certified keys :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input.certified target view frame
      derived center centerReal rigid hacyc hsimple hcharge enough
  have offDiagonal : input.certified.CompoundKeyOffDiagonalStrict keys :=
    input.certified.compoundKeyOffDiagonalStrict_of_priorSeparated keys separated
  have rankInjective : Function.Injective (input.certified.compoundKeyRank keys) :=
    input.certified.compoundKeyRank_injective keys offDiagonal
  let priority : Fin 4 → Nat := fun i => input.certified.compoundKeyRank keys (alpha.symm i)
  have priorityInjective : Function.Injective priority := by
    intro i j h
    apply alpha.symm.injective
    exact rankInjective (by simpa [priority] using h)
  have orderedEq := input.certified.compareLocalizedOccurrenceThroughRule5OrderedAt?_eq_of_rigidFrame
    target view frame derived center centerReal rigid hacyc hsimple hcharge enough
  have priorityOrder : ∀ ℓ m, ℓ ≠ m →
      input.certified.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame
        (alpha.symm ℓ) (alpha.symm m) =
        strictRankComparison (fun i => priority (alpha i))
          (alpha.symm ℓ) (alpha.symm m) := by
    intro ℓ m hne
    rw [orderedEq]
    simpa [priority] using input.certified.compareLocalizedOccurrenceThroughRule5At?_eq_strictRankComparison
      target view frame keys
      (fun i => frame.compoundKeyAt_built input.certified target view derived i)
      separated (alpha.symm ℓ) (alpha.symm m) (fun h => hne (alpha.symm.injective h))
  have orderPerm : order.Perm (List.finRange 4) := independent.1
  let canonicalOrder : List (Fin 4) := order.map alpha
  have canonicalOrderPerm : canonicalOrder.Perm (List.finRange 4) := by
    exact (orderPerm.map alpha).trans (finRangeMapPermFour alpha)
  have orderSorted : canonicalOrder.Pairwise (fun left right => priority right < priority left) := by
    apply List.pairwise_map.mpr
    apply independent.2.imp
    intro left right hphysical
    have hne : left ≠ right := by
      intro h
      subst right
      have compared := (frameSlotPhysicalOutcome_iff_constitutionalCompare input.certified
        target view frame derived hsimple hacyc left left Ordering.gt).mpr hphysical
      have self : OfficialRuleMajorKey.compare
          ((frame.compoundKeyAt input.certified target view derived left).prior.rule4aKey.constitutional)
          ((frame.compoundKeyAt input.certified target view derived left).prior.rule4aKey.constitutional) =
          Ordering.eq := CompilerProjectionFidelity.compare_eq_eq_of_sameConstitution
            ⟨rfl, rfl, rfl, rfl⟩
      rw [self] at compared
      cases compared
    have rank := frameSlotPhysicalOutcome_rank_lt_of_gt input.certified target view frame
      derived center centerReal rigid hacyc hsimple hcharge enough left right hne hphysical
    simpa [priority] using rank
  have canonicalPoints : canonicalOrder.mapM (fun i => input.certified.spatialPointAt?
      (input.certified.canonicalLigandAtom center i)) = some (canonicalOrder.map pointsAt) :=
    mapMCanonicalObserved input.certified center pointsAt observed canonicalOrder
  obtain ⟨raw, rational⟩ :=
    rationalTetrahedralDescriptor_exists_of_permutation pointsAt canonicalOrder
      canonicalOrderPerm nonzero
  have rawComputed : descriptorOfPriorityOrderedPoints? (canonicalOrder.map pointsAt) = some raw :=
    (descriptorOfPriorityOrderedPoints?_eq_some_iff (canonicalOrder.map pointsAt) raw).mpr rational
  have spatialCorrespondence : ∀ i,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
        input.certified.spatialPointAt?
          (input.certified.canonicalLigandAtom center (alpha i)) := by
    intro i
    rw [input.certified.localizedRerootCursorSpatialPoint?_eq_of_spatialPointAt
      frame (fun i => input.certified.canonicalLigandAtom center (alpha i))
      (fun i => pointsAt (alpha i)) ligandLink (fun i => observed (alpha i)) i,
      observed (alpha i)]
  have computed := orderedReferenceState_eq_chiral_of_strictPriorityCallback input target frame
    frameComputed center centerReal alpha priority priorityInjective priorityOrder
    canonicalOrder canonicalOrderPerm orderSorted (canonicalOrder.map pointsAt)
    spatialCorrespondence canonicalPoints raw rawComputed
  intro raw'
  constructor
  · intro stateEq
    have hRaw : raw' = raw := by
      have h := computed.symm.trans stateEq
      have hChiral : LocalizedTetrahedralRSPseudoDescriptor.chiral raw =
          LocalizedTetrahedralRSPseudoDescriptor.chiral raw' := Option.some.inj h
      have hr : raw = raw' := by injection hChiral
      exact hr.symm
    cases hRaw
    simpa [canonicalOrder, List.map_map] using rational
  · intro rational'
    have rationalCanonical :
        RationalTetrahedralDescriptor (canonicalOrder.map pointsAt) raw' := by
      simpa [canonicalOrder, List.map_map] using rational'
    have rawEq : raw = raw' := Option.some.inj
      (rawComputed.symm.trans
        ((descriptorOfPriorityOrderedPoints?_eq_some_iff (canonicalOrder.map pointsAt) raw').mpr
          rationalCanonical))
    cases rawEq
    exact computed

/-- A detected general-rigid calibrated centre supplies the actual top frame and the hypotheses
of the local theorem. This facade uses no `ActualGeneralRigidPhysicalDomain`. -/
theorem orderedTop_eq_chiral_iff_independentPhysicalGeometry_of_calibratedCenter
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (center : input.certified.TetrahedralCenter)
    (calibrated : ActualGeneralRigidCalibratedCenter input.certified cfg center) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)) (pointsAt : Fin 4 → CartesianPoint3)
      (order : List (Fin 4))
      (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
        (ActualReaderPhysicalBranchInverse.topTarget input ⟨center.1, center.2⟩) = some frame),
      (∀ i, (frame.cursorAt i).occurrence.1.node.current? =
        some (input.certified.canonicalLigandAtom center (alpha i))) ∧
      (∀ i, input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center i) = some (pointsAt i)) ∧
      IndependentPhysicalHighestFirst input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input ⟨center.1, center.2⟩)
        (input.certified.localizedDependencyView
          (input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input))
          (ActualReaderPhysicalBranchInverse.topTarget input ⟨center.1, center.2⟩))
        frame
        (input.certified.localizedOccurrenceFourLigandFrame?_sound
          (ActualReaderPhysicalBranchInverse.topTarget input ⟨center.1, center.2⟩)
          frame frameComputed)
        singleBonded acyclic order ∧
      ∀ raw, input.certified.orderedReferenceState
          (LocalizedUniversalReference.carrierFuel input)
          (ActualReaderPhysicalBranchInverse.topTarget input ⟨center.1, center.2⟩) =
          some (.chiral raw) ↔
        RationalTetrahedralDescriptor (order.map fun i => pointsAt (alpha i)) raw := by
  let target := ActualReaderPhysicalBranchInverse.topTarget input ⟨center.1, center.2⟩
  let rigidGraph := constitutionallyRigidGraphAt_of_generalRigidCalibratedCenter calibrated
  have targetCurrent : target.1.node.current? = some center.1 :=
    ActualReaderPhysicalBranchInverse.topTarget_current input ⟨center.1, center.2⟩
  obtain ⟨frame, alpha, pointsAt, frameComputed, ligandLink, _spatial, observed, _calibration⟩ :=
    exists_frameAndCalibration_of_generalRigidCenter input singleBonded acyclic cfg center target
      targetCurrent calibrated
  have derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame :=
    input.certified.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed
  have centerReal : input.certified.RealTetrahedralCenterNode target.1.node center :=
    ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic target, targetCurrent⟩
  obtain ⟨_rigidData, calibratedPoints, calibratedObserved, calibratedNonzero, _signEq⟩ :=
    calibrated
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    exact globalCarrierFuel_adequate input
  have pointAtEq : pointsAt = calibratedPoints := by
    funext i
    exact Option.some.inj ((observed i).symm.trans (calibratedObserved i))
  have nonzeroAt : CartesianPoint3.orientedVolume (pointsAt 0) (pointsAt 1)
      (pointsAt 2) (pointsAt 3) ≠ 0 := by
    rw [pointAtEq]
    exact calibratedNonzero
  obtain ⟨order, independent, iffGeometry⟩ :=
    orderedReferenceState_eq_chiral_iff_independentPhysicalGeometry input target frame
      frameComputed derived center centerReal
      rigidGraph
      acyclic singleBonded hcharge enough alpha ligandLink pointsAt observed nonzeroAt
  exact ⟨frame, alpha, pointsAt, order, frameComputed, ligandLink, observed,
    independent, iffGeometry⟩

/-- The same top-centre result for a physical configuration written in the detected molecule's
original ligand enumeration. The canonical reindexing is local to coordinate readback; no global
physical domain or root case analysis is used. -/
theorem orderedTop_eq_chiral_iff_independentPhysicalGeometry_of_physicalCalibratedCenter
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg center) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)) (pointsAt : Fin 4 → CartesianPoint3)
      (order : List (Fin 4))
      (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
        (ActualReaderPhysicalBranchInverse.topTarget input ⟨center.1, center.2⟩) = some frame),
      (∀ i, (frame.cursorAt i).occurrence.1.node.current? =
        some (input.certified.canonicalLigandAtom ⟨center.1, center.2⟩ (alpha i))) ∧
      (∀ i, input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom ⟨center.1, center.2⟩ i) = some (pointsAt i)) ∧
      IndependentPhysicalHighestFirst input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input ⟨center.1, center.2⟩)
        (input.certified.localizedDependencyView
          (input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input))
          (ActualReaderPhysicalBranchInverse.topTarget input ⟨center.1, center.2⟩))
        frame
        (input.certified.localizedOccurrenceFourLigandFrame?_sound
          (ActualReaderPhysicalBranchInverse.topTarget input ⟨center.1, center.2⟩)
          frame frameComputed)
        singleBonded acyclic order ∧
      ∀ raw, input.certified.orderedReferenceState
          (LocalizedUniversalReference.carrierFuel input)
          (ActualReaderPhysicalBranchInverse.topTarget input ⟨center.1, center.2⟩) =
          some (.chiral raw) ↔
        RationalTetrahedralDescriptor
          (order.map fun i => pointsAt (alpha i)) raw := by
  exact orderedTop_eq_chiral_iff_independentPhysicalGeometry_of_calibratedCenter input
    singleBonded acyclic hcharge (input.certified.canonicalReindexConfiguration cfg)
    ⟨center.1, center.2⟩
    (actualGeneralRigidCalibratedCenter_of_physicalGeneralRigidCalibratedCenter
      input.certified cfg center calibrated)

end
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.orderedReferenceState_eq_chiral_iff_independentPhysicalGeometry
assert_kernel_only TetraStereo.OneCenter.orderedTop_eq_chiral_iff_independentPhysicalGeometry_of_calibratedCenter
assert_kernel_only TetraStereo.OneCenter.orderedTop_eq_chiral_iff_independentPhysicalGeometry_of_physicalCalibratedCenter
