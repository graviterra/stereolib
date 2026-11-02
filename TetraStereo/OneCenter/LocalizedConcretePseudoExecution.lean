import TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity
import TetraStereo.OneCenter.LocalizedPhysicalPseudoEndToEnd
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false













































namespace TetraStereo.OneCenter.LocalizedConcretePseudoExecution

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity
open TetraStereo.Certificate.Dependency






private theorem val_cast_eq
    {m1 m2 : MultiCenterMolecule Atom} (h : m1 = m2) (c : m1.Center) :
    ((h ▸ c) : m2.Center).1 = c.1 := by
  cases h
  rfl

/-- Generic cast elimination for ligand readback.  After the cast is eliminated the two readbacks
are definitionally the same. -/
private theorem ligandAtomAt_cast_eq
    {m1 m2 : MultiCenterMolecule Atom} (h : m1 = m2) (c : m1.Center) (i : Fin 4) :
    m2.ligandAtomAt (h ▸ c) i = m1.ligandAtomAt c i := by
  cases h
  rfl



theorem val_cast_reindexFrames_detected
    (τ : m.Center → Equiv.Perm (Fin 4))
    (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
    (c : m.Center) :
    ((hτ ▸ c) : input.certified.detectedMultiCenterMolecule.Center).1 = c.1 :=
  val_cast_eq hτ c



theorem reindexFrames_ligandAtomAt_cast
    (τ : m.Center → Equiv.Perm (Fin 4))
    (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
    (c : m.Center) (i : Fin 4) :
    input.certified.detectedMultiCenterMolecule.ligandAtomAt (hτ ▸ c) i =
      m.ligandAtomAt c (τ c i) := by
  have h := ligandAtomAt_cast_eq hτ c i
  simpa [MultiCenterMolecule.reindexFrames_ligandAtomAt] using h



theorem detectedRoot_val
    (τ : m.Center → Equiv.Perm (Fin 4))
    (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
    (rootD : input.certified.detectedMultiCenterMolecule.Center)
    (hrootD : rootD = hτ ▸ root) :
    rootD.1 = atom0 := by
  rw [hrootD]
  simpa [root] using val_cast_reindexFrames_detected τ hτ root



theorem detectedRoot_center_eq_rootTetrahedral
    (τ : m.Center → Equiv.Perm (Fin 4))
    (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
    (rootD : input.certified.detectedMultiCenterMolecule.Center)
    (hrootD : rootD = hτ ▸ root) :
    (⟨rootD.1, rootD.2⟩ : input.certified.TetrahedralCenter) = rootTetrahedral :=
  Subtype.ext (by
    simpa [rootTetrahedral] using detectedRoot_val τ hτ rootD hrootD)

/-! ## Canonical root coordinates at the actual detected root -/









theorem actualCanonicalRootCoordinates_detectedRoot
    (τ : m.Center → Equiv.Perm (Fin 4))
    (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
    (rootD : input.certified.detectedMultiCenterMolecule.Center)
    (hrootD : rootD = hτ ▸ root) :
    input.certified.ActualCanonicalRootCoordinates
      (⟨rootD.1, rootD.2⟩ : input.certified.TetrahedralCenter) := by
  let center : input.certified.TetrahedralCenter := ⟨rootD.1, rootD.2⟩
  let pointAt : Fin 4 → CartesianPoint3 :=
    fun i => pointOfAtom (input.certified.canonicalLigandAtom center i)
  refine ⟨pointAt, ?_, ?_⟩
  · intro i
    simpa [pointAt] using
      spatialPointAt_atom (input.certified.canonicalLigandAtom center i)
  · let beta : Equiv.Perm (Fin 4) := input.certified.canonicalLigandReindex rootD
    let alpha : Equiv.Perm (Fin 4) := beta.symm.trans (τ root)
    have hcanon : ∀ i : Fin 4,
        input.certified.canonicalLigandAtom center i = rootLigand (alpha i) := by
      intro i
      have hreindex := input.certified.canonicalLigandReindex_spec rootD (beta.symm i)
      have hcanonical : input.certified.canonicalLigandAtom center i =
          input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD (beta.symm i) := by
        rw [show beta (beta.symm i) = i from Equiv.apply_symm_apply beta i] at hreindex
        simpa [center] using hreindex.symm
      have hdetected :
          input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD (beta.symm i) =
            rootLigand (τ root (beta.symm i)) := by
        rw [hrootD]
        rw [reindexFrames_ligandAtomAt_cast τ hτ root (beta.symm i)]
        exact ligandAtomAt_root _
      rw [hcanonical, hdetected]
      rfl
    have hpointEq : ∀ i : Fin 4, pointAt i = rootPoints (alpha i) := by
      intro i
      simpa [pointAt, rootPoints] using congrArg pointOfAtom (hcanon i)
    have hnonzero :=
      cartesianOrientedVolume_perm_ne_zero rootPoints alpha root_volume_ne_zero
    simpa [hpointEq] using hnonzero



theorem exists_actualCanonicalRootCoordinates :
    ∃ (τ : m.Center → Equiv.Perm (Fin 4))
      (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
      (rootD : input.certified.detectedMultiCenterMolecule.Center),
      rootD = hτ ▸ root ∧
        input.certified.ActualCanonicalRootCoordinates
          (⟨rootD.1, rootD.2⟩ : input.certified.TetrahedralCenter) := by
  obtain ⟨τ, hτ, _cfgD, rootD, _hcfgD, hrootD, _domain, _distinct, _enantiomorphic,
    _classification, _count, _disjoint, _branch⟩ :=
    LocalizedPhysicalDomainNonvacuity.detected_physicalWitness_actual
  exact ⟨τ, hτ, rootD, hrootD,
    actualCanonicalRootCoordinates_detectedRoot τ hτ rootD hrootD⟩








theorem detectedRoot_physicalBranchDomain
    (τ : m.Center → Equiv.Perm (Fin 4))
    (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
    (rootD : input.certified.detectedMultiCenterMolecule.Center)
    (hrootD : rootD = hτ ▸ root)
    (branch : ∀ i : Fin 4, PhysicalBranchDomain input rootTetrahedral
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD i)) :
    ∀ i : Fin 4, PhysicalBranchDomain input
      (⟨rootD.1, rootD.2⟩ : input.certified.TetrahedralCenter)
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD i) := by
  intro i
  rw [detectedRoot_center_eq_rootTetrahedral τ hτ rootD hrootD]
  exact branch i











theorem actualPhysicalExecution_of_detectedRoot
    (τ : m.Center → Equiv.Perm (Fin 4))
    (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
    (cfgD : input.certified.detectedMultiCenterMolecule.Configuration)
    (rootD : input.certified.detectedMultiCenterMolecule.Center)
    (hrootD : rootD = hτ ▸ root)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfgD rootD)
    (distinct : MultiCenterMolecule.PairwiseProperDistinguishable
      input.certified.detectedMultiCenterMolecule cfgD rootD)
    (branch : ∀ i : Fin 4, PhysicalBranchDomain input rootTetrahedral
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD i)) :
    (∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
        LocalizedUniversalReference.referenceState input
            (ActualReaderPhysicalBranchInverse.topTarget input rootD) = some descriptor ∧
          (descriptor.IsLowercase ↔
            physicalEnantiomorphicPairCount
              input.certified.detectedMultiCenterMolecule cfgD rootD = 1)) ∧
      (∀ nodes : LocalizedUniversalReference.Nodes input,
        ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
          lookup
              (LocalizedUniversalReference.evaluate input nodes).facts
              (ActualReaderPhysicalBranchInverse.topTarget input rootD) = some descriptor ∧
            (descriptor.IsLowercase ↔
              physicalEnantiomorphicPairCount
                input.certified.detectedMultiCenterMolecule cfgD rootD = 1)) ∧
        (∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
          LocalizedUniversalReference.referenceState input
              (ActualReaderPhysicalBranchInverse.topTarget input rootD) = some descriptor ∧
            input.certified.universalDescriptor?
                (ActualReaderPhysicalBranchInverse.topTarget input rootD)
                (input.certified.localizedDependencyView
                  (LocalizedUniversalReference.referenceState input)
                  (ActualReaderPhysicalBranchInverse.topTarget input rootD)) =
              some descriptor ∧
              input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
                  (ActualReaderPhysicalBranchInverse.topTarget input rootD)
                  (input.certified.localizedDependencyView
                    (LocalizedUniversalReference.referenceState input)
                    (ActualReaderPhysicalBranchInverse.topTarget input rootD)) =
                some descriptor ∧
                (descriptor.IsLowercase ↔
                  physicalEnantiomorphicPairCount
                    input.certified.detectedMultiCenterMolecule cfgD rootD = 1)) := by
  have branchDomains :=
    detectedRoot_physicalBranchDomain τ hτ rootD hrootD branch
  have coordinates := actualCanonicalRootCoordinates_detectedRoot τ hτ rootD hrootD
  have physical :=
    TetraStereo.OneCenter.exists_referenceState_descriptor_lowercase_iff_physicalCount_of_physicalDomain
      input input_noDoubleRecords simpleBonded acyclic constantFormalCharge cfgD rootD
      domain distinct branchDomains coordinates
  have production :=
    TetraStereo.OneCenter.exists_prepared_and_production_descriptor_iff_physicalCount_of_physicalDomain
      input input_noDoubleRecords simpleBonded acyclic constantFormalCharge cfgD rootD
      domain distinct branchDomains coordinates
  refine ⟨physical, ?_, production⟩
  intro nodes
  obtain ⟨descriptor, stateEq, lowercase⟩ := physical
  refine ⟨descriptor, ?_, lowercase⟩
  rw [LocalizedUniversalReference.evaluate_state]
  exact stateEq

/-! ## The concrete final theorems -/




theorem exists_actual_referenceState_lowercase :
    ∃ (τ : m.Center → Equiv.Perm (Fin 4))
      (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
      (cfgD : input.certified.detectedMultiCenterMolecule.Configuration)
      (rootD : input.certified.detectedMultiCenterMolecule.Center),
      cfgD = hτ ▸ m.reindexConfiguration τ cfg ∧
      rootD = hτ ▸ root ∧
      ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
        LocalizedUniversalReference.referenceState input
            (ActualReaderPhysicalBranchInverse.topTarget input rootD) = some descriptor ∧
          descriptor.IsLowercase := by
  obtain ⟨τ, hτ, cfgD, rootD, hcfgD, hrootD, domain, distinct, _enantiomorphic,
    _classification, count, _disjoint, branch⟩ :=
    LocalizedPhysicalDomainNonvacuity.detected_physicalWitness_actual
  obtain ⟨⟨descriptor, stateEq, lowercaseIff⟩, _evaluate, _production⟩ :=
    actualPhysicalExecution_of_detectedRoot τ hτ cfgD rootD hrootD domain distinct branch
  exact ⟨τ, hτ, cfgD, rootD, hcfgD, hrootD, descriptor, stateEq,
    lowercaseIff.mpr count⟩




theorem forall_nodes_exists_actual_evaluate_lowercase :
    ∃ (τ : m.Center → Equiv.Perm (Fin 4))
      (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
      (cfgD : input.certified.detectedMultiCenterMolecule.Configuration)
      (rootD : input.certified.detectedMultiCenterMolecule.Center),
      cfgD = hτ ▸ m.reindexConfiguration τ cfg ∧
      rootD = hτ ▸ root ∧
      ∀ nodes : LocalizedUniversalReference.Nodes input,
        ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
          lookup
              (LocalizedUniversalReference.evaluate input nodes).facts
              (ActualReaderPhysicalBranchInverse.topTarget input rootD) = some descriptor ∧
            descriptor.IsLowercase := by
  obtain ⟨τ, hτ, cfgD, rootD, hcfgD, hrootD, domain, distinct, _enantiomorphic,
    _classification, count, _disjoint, branch⟩ :=
    LocalizedPhysicalDomainNonvacuity.detected_physicalWitness_actual
  obtain ⟨_plain, evaluate, _production⟩ :=
    actualPhysicalExecution_of_detectedRoot τ hτ cfgD rootD hrootD domain distinct branch
  refine ⟨τ, hτ, cfgD, rootD, hcfgD, hrootD, ?_⟩
  intro nodes
  obtain ⟨descriptor, evalEq, lowercaseIff⟩ := evaluate nodes
  exact ⟨descriptor, evalEq, lowercaseIff.mpr count⟩





theorem exists_actual_prepared_and_production_lowercase :
    ∃ (τ : m.Center → Equiv.Perm (Fin 4))
      (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
      (cfgD : input.certified.detectedMultiCenterMolecule.Configuration)
      (rootD : input.certified.detectedMultiCenterMolecule.Center),
      cfgD = hτ ▸ m.reindexConfiguration τ cfg ∧
      rootD = hτ ▸ root ∧
      ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
        LocalizedUniversalReference.referenceState input
            (ActualReaderPhysicalBranchInverse.topTarget input rootD) = some descriptor ∧
          input.certified.universalDescriptor?
              (ActualReaderPhysicalBranchInverse.topTarget input rootD)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (ActualReaderPhysicalBranchInverse.topTarget input rootD)) =
            some descriptor ∧
            input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
                (ActualReaderPhysicalBranchInverse.topTarget input rootD)
                (input.certified.localizedDependencyView
                  (LocalizedUniversalReference.referenceState input)
                  (ActualReaderPhysicalBranchInverse.topTarget input rootD)) =
              some descriptor ∧
              descriptor.IsLowercase := by
  obtain ⟨τ, hτ, cfgD, rootD, hcfgD, hrootD, domain, distinct, _enantiomorphic,
    _classification, count, _disjoint, branch⟩ :=
    LocalizedPhysicalDomainNonvacuity.detected_physicalWitness_actual
  obtain ⟨_plain, _evaluate, ⟨descriptor, stateEq, preparedEq, productionEq, lowercaseIff⟩⟩ :=
    actualPhysicalExecution_of_detectedRoot τ hτ cfgD rootD hrootD domain distinct branch
  exact ⟨τ, hτ, cfgD, rootD, hcfgD, hrootD, descriptor, stateEq, preparedEq,
    productionEq, lowercaseIff.mpr count⟩

end TetraStereo.OneCenter.LocalizedConcretePseudoExecution

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePseudoExecution.val_cast_reindexFrames_detected
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePseudoExecution.reindexFrames_ligandAtomAt_cast
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePseudoExecution.detectedRoot_val
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePseudoExecution.detectedRoot_center_eq_rootTetrahedral
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePseudoExecution.actualCanonicalRootCoordinates_detectedRoot
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePseudoExecution.exists_actualCanonicalRootCoordinates
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePseudoExecution.detectedRoot_physicalBranchDomain
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePseudoExecution.actualPhysicalExecution_of_detectedRoot
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePseudoExecution.exists_actual_referenceState_lowercase
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePseudoExecution.forall_nodes_exists_actual_evaluate_lowercase
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePseudoExecution.exists_actual_prepared_and_production_lowercase
