import TetraStereo.OneCenter.LocalizedOrderedPhysicalMoleculeDomain
import TetraStereo.OneCenter.LocalizedOrderedRigidPhysicalDescriptor
import TetraStereo.OneCenter.LocalizedOrderedReportInventory
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
open CertifiedLocalizedCIPInput
open AcyclicCutBranchAutomorphism
noncomputable section

private theorem perm_finRange_map (e : Equiv.Perm (Fin 4)) :
    ((List.finRange 4).map e).Perm (List.finRange 4) := by
  have nd := (List.nodup_finRange 4).map e.injective
  apply List.perm_of_nodup_nodup_toFinset_eq nd (List.nodup_finRange 4)
  have left : ((List.finRange 4).map e).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup nd]; simp)
  have right : (List.finRange 4).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _
      (by rw [List.toFinset_card_of_nodup (List.nodup_finRange 4)]; simp)
  rw [left, right]

/-- Local physical rigidity and nondegenerate source geometry force an actual uppercase result
at the centre's own final occurrence, with no auxiliary-state or comparison hypothesis. -/
theorem orderedTop_exists_chiral_of_physicalCalibratedCenter
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg center) :
    ∃ rs : RS, input.certified.orderedReferenceState
      (LocalizedUniversalReference.carrierFuel input)
      (ActualReaderPhysicalBranchInverse.topTarget input center) = some (.chiral rs) := by
  obtain ⟨frame, alpha, points, order, computed, _link, observed, highest, meaning⟩ :=
    orderedTop_eq_chiral_iff_independentPhysicalGeometry_of_physicalCalibratedCenter
      input singleBonded acyclic hcharge cfg center calibrated
  obtain ⟨_, canonicalPoints, canonicalObserved, nonzero, _⟩ :=
    actualGeneralRigidCalibratedCenter_of_physicalGeneralRigidCalibratedCenter
      input.certified cfg center calibrated
  have pointsEq : points = canonicalPoints := by
    funext i
    exact Option.some.inj ((observed i).symm.trans (canonicalObserved i))
  have perm : (order.map alpha).Perm (List.finRange 4) :=
    (highest.1.map alpha).trans (perm_finRange_map alpha)
  obtain ⟨rs, geometry⟩ := rationalTetrahedralDescriptor_exists_of_permutation
    canonicalPoints (order.map alpha) perm nonzero
  refine ⟨rs, (meaning rs).2 ?_⟩
  simpa only [pointsEq, List.map_map, Function.comp_def] using geometry

namespace OrderedTreePhysicalDomain
variable {input : LocalizedUniversalReference.Input}
  {cfg : input.certified.detectedMultiCenterMolecule.Configuration}
  {root : input.certified.detectedMultiCenterMolecule.Center}
  (domain : OrderedTreePhysicalDomain input cfg root)
include domain

/-- Every non-root, non-twin detected centre returns an uppercase descriptor at arbitrary depth. -/
theorem nonroot_exists_chiral (center : input.certified.TetrahedralCenter)
    (different : (⟨center.1, center.2⟩ :
      input.certified.detectedMultiCenterMolecule.Center) ≠ root)
    (notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩) :
    ∃ rs : RS, input.certified.orderedReferenceState
      (LocalizedUniversalReference.carrierFuel input)
      (input.certified.localizedFinalOccurrenceExecutable
        (LocalizedUniversalReference.carrierFuel input) center) = some (.chiral rs) := by
  rcases domain.centers.centerCase ⟨center.1, center.2⟩ different with twin | calibrated
  · exact (notTwin twin).elim
  · rw [input.certified.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence]
    exact orderedTop_exists_chiral_of_physicalCalibratedCenter input
      domain.singleBonded domain.acyclic domain.constantCharge cfg
      ⟨center.1, center.2⟩ calibrated

/-- In the entire physical class, missing results are exactly the independent physical
terminal-twin cases.  They cannot be caused by bounded comparison or sorting failure. -/
theorem final_none_iff_terminalTwin (center : input.certified.TetrahedralCenter) :
    input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
        (input.certified.localizedFinalOccurrenceExecutable
          (LocalizedUniversalReference.carrierFuel input) center) = none ↔
      ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩ := by
  constructor
  · intro absent
    by_cases atRoot : (⟨center.1, center.2⟩ :
        input.certified.detectedMultiCenterMolecule.Center) = root
    · obtain ⟨label, present, _⟩ := domain.root_assignment
      have centerEq : center = domain.rootCenter := by
        apply Subtype.ext
        exact congrArg Subtype.val atRoot
      rw [centerEq, input.certified.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence]
        at absent
      have impossible : False := by
        change input.certified.orderedReferenceState
          (LocalizedUniversalReference.carrierFuel input)
          (ActualReaderPhysicalBranchInverse.topTarget input root) = none at absent
        rw [present] at absent
        cases absent
      exact impossible.elim
    · by_contra notTwin
      obtain ⟨rs, present⟩ := domain.nonroot_exists_chiral center atRoot notTwin
      rw [present] at absent
      cases absent
  · exact domain.terminalTwin_final_none center

theorem report_none_iff_terminalTwin (center : input.certified.TetrahedralCenter) :
    (center.1.1, none) ∈ LocalizedOrderedReference.analyze input ↔
      ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩ := by
  rw [LocalizedOrderedReference.mem_analyze_iff]
  constructor
  · rintro ⟨other, sameAtom, absent⟩
    have sameCenter : other = center := Subtype.ext (Fin.ext sameAtom)
    subst other
    exact (domain.final_none_iff_terminalTwin center).1 absent
  · intro twin
    exact ⟨center, rfl, (domain.final_none_iff_terminalTwin center).2 twin⟩

end OrderedTreePhysicalDomain
end
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.orderedTop_exists_chiral_of_physicalCalibratedCenter
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.nonroot_exists_chiral
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.final_none_iff_terminalTwin
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.report_none_iff_terminalTwin
