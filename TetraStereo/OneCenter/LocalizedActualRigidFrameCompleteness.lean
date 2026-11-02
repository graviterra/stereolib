/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.LocalizedConstitutionallyRigidFrameNormalization
import TetraStereo.OneCenter.LocalizedRealizedTreeCutIsomorphism
import TetraStereo.OneCenter.LocalizedUniqueNearestRule4bReference
import TetraStereo.OneCenter.LocalizedActualKeyTiePhysicalTransport
import TetraStereo.OneCenter.LocalizedAcyclicFourLigandFrameCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open AcyclicCutBranchAutomorphism


















































namespace CertifiedLocalizedCIPInput






def canonicalLigandEquiv (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) :
    Fin 4 ≃ input.moleculeGraph.Neighbor center.1 :=
  Equiv.ofBijective (input.canonicalLigandNeighbor center)
    (input.canonicalLigandNeighbor_bijective center)

/-- The canonical ligand equivalence reads back the canonical ligand atom. -/
@[simp] theorem canonicalLigandEquiv_apply_coe (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    (input.canonicalLigandEquiv center index).1 =
      input.canonicalLigandAtom center index := rfl

end CertifiedLocalizedCIPInput

/-! ## Actual trees from three constitutional columns -/









theorem rootedCutBranchIso_of_actualFrame_constitutionalColumns
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.canonicalLigandAtom center (alpha index)))
    (left right : Fin 4)
    (rule1aEq :
      ((frame.compoundKeyAt input target view derived) left).prior.rule4aKey.constitutional.rule1a =
        ((frame.compoundKeyAt input target view derived) right).prior.rule4aKey.constitutional.rule1a)
    (rule1bEq :
      ((frame.compoundKeyAt input target view derived) left).prior.rule4aKey.constitutional.rule1b =
        ((frame.compoundKeyAt input target view derived) right).prior.rule4aKey.constitutional.rule1b)
    (rule2Eq :
      ((frame.compoundKeyAt input target view derived) left).prior.rule4aKey.constitutional.rule2 =
        ((frame.compoundKeyAt input target view derived) right).prior.rule4aKey.constitutional.rule2) :
    Nonempty (RootedCutBranchIso input.moleculeGraph center.1
      (input.canonicalLigandAtom center (alpha left))
      (input.canonicalLigandAtom center (alpha right))) := by
  -- Each prior build exposes its retained actual Rule-4a build.
  have compoundLeft : input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left) =
      some ((frame.compoundKeyAt input target view derived) left) :=
    frame.compoundKeyAt_built input target view derived left
  have compoundRight : input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right) =
      some ((frame.compoundKeyAt input target view derived) right) :=
    frame.compoundKeyAt_built input target view derived right
  have priorLeft : input.buildLocalizedRerootCompoundRule4bcKey? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left) =
      some ((frame.compoundKeyAt input target view derived) left).prior :=
    (buildLocalizedRerootCompoundRule45Key?_prior_built input target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left)
      ((frame.compoundKeyAt input target view derived) left) compoundLeft).1
  have priorRight : input.buildLocalizedRerootCompoundRule4bcKey? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right) =
      some ((frame.compoundKeyAt input target view derived) right).prior :=
    (buildLocalizedRerootCompoundRule45Key?_prior_built input target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right)
      ((frame.compoundKeyAt input target view derived) right) compoundRight).1
  have rule4aLeft : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left) =
      some ((frame.compoundKeyAt input target view derived) left).prior.rule4aKey :=
    input.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left)
      ((frame.compoundKeyAt input target view derived) left).prior priorLeft
  have rule4aRight : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right) =
      some ((frame.compoundKeyAt input target view derived) right).prior.rule4aKey :=
    input.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right)
      ((frame.compoundKeyAt input target view derived) right).prior priorRight
  -- Specializing the callback builder to the actual dependency reader recovers those builds.
  have withReadLeft : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left) =
      some ((frame.compoundKeyAt input target view derived) left).prior.rule4aKey := by
    rw [input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      .rule4a target view]
    exact rule4aLeft
  have withReadRight : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right) =
      some ((frame.compoundKeyAt input target view derived) right).prior.rule4aKey := by
    rw [input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      .rule4a target view]
    exact rule4aRight

  obtain ⟨tLeft, tRight, sourceLeft, sourceRight, _tableLeft, _tableRight,
    realizesLeft, realizesRight, shapeEq, _treeMatch⟩ :=
    exists_matchedTrees_of_buildWithRead input .rule4a .rule4a
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt left) (frame.cursorAt right)
      (((frame.compoundKeyAt input target view derived) left).prior.rule4aKey)
      (((frame.compoundKeyAt input target view derived) right).prior.rule4aKey)
      withReadLeft withReadRight rule1aEq rule1bEq rule2Eq
  -- Frame provenance: each slot is one of the declared children of the target.
  have presentLeft : frame.cursorAt left ∈ frame.cursors := by
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm left)
  have presentRight : frame.cursorAt right ∈ frame.cursors := by
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm right)
  -- Each slot's previous occurrence is the actual target.
  have previousLeft : tLeft.source.previous? = some target := by
    rw [sourceLeft]
    simpa using derived.1.2 (frame.cursorAt left) presentLeft
  have previousRight : tRight.source.previous? = some target := by
    rw [sourceRight]
    simpa using derived.1.2 (frame.cursorAt right) presentRight
  -- Each slot cursor is valid.
  have validLeft : input.LocalizedRerootCursorValid tLeft.source := by
    rw [sourceLeft]
    exact frame.cursorAt_valid input target derived left
  have validRight : input.LocalizedRerootCursorValid tRight.source := by
    rw [sourceRight]
    exact frame.cursorAt_valid input target derived right
  -- Both slots share the original root of the target.
  have sameRootLeft : tLeft.source.occurrence.1.root = target.1.root := by
    rw [sourceLeft]
    exact input.localizedRerootChildren_root_eq
      { occurrence := target, previous? := none }
      (frame.cursorAt left) frame.cursors derived.1 presentLeft
  have sameRootRight : tRight.source.occurrence.1.root = target.1.root := by
    rw [sourceRight]
    exact input.localizedRerootChildren_root_eq
      { occurrence := target, previous? := none }
      (frame.cursorAt right) frame.cursors derived.1 presentRight
  -- Each slot observes its physical ligand atom.
  have observedLeft : tLeft.source.occurrence.1.node.current? =
      some (input.canonicalLigandAtom center (alpha left)) := by
    rw [sourceLeft]
    exact ligandLink left
  have observedRight : tRight.source.occurrence.1.node.current? =
      some (input.canonicalLigandAtom center (alpha right)) := by
    rw [sourceRight]
    exact ligandLink right
  -- The actual realised trees assemble the actual rooted cut-branch isomorphism.
  exact ⟨rootedCutBranchIso_of_shapeMatch
    (input := input) (carrierFuel := carrierFuel)
    (singleBonded := singleBonded) (acyclic := acyclic)
    (c := center.1)
    (u := input.canonicalLigandAtom center (alpha left))
    (v := input.canonicalLigandAtom center (alpha right))
    (previousL := target) (previousR := target)
    enough shapeEq realizesLeft realizesRight
    previousLeft validLeft sameRootLeft previousRight validRight sameRootRight
    observedLeft centerReal.2 observedRight centerReal.2
    (input.canonicalLigandAtom_adj center (alpha left))
    (input.canonicalLigandAtom_adj center (alpha right))⟩

/-! ## The per-frame rooted cut-branch isomorphism -/

/-- **Per-frame `PriorTieYieldsRootedCutBranchIso` at the actual production fuel.**  For the actual
four-ligand frame of an actual target, two distinct frame slots whose actual prior Rules-4b/4c keys
tie carry isomorphic rooted physical cut branches at the actual centre atom `center.1`.

All data are those of the input: the graph is `input.moleculeGraph`, the root is the target's real
tetrahedral centre atom, the branch atoms are the canonical executable ligand enumeration composed
with the slot permutation `alpha`, and the keys are the actual `compoundKeyAt` slots at fuel
`localizedOccurrenceRerootEvaluationFuel carrierFuel`. -/
theorem priorTieYieldsRootedCutBranchIso_at_actualFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.canonicalLigandAtom center (alpha index))) :
    PriorTieYieldsRootedCutBranchIso input
      (frame.compoundKeyAt input target view derived)
      input.moleculeGraph center.1
      (fun index => input.canonicalLigandAtom center (alpha index)) := by
  intro left right _different tie
  -- A prior compound tie exposes the actual Rule-4a comparator tie.
  have rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys
      ((frame.compoundKeyAt input target view derived) left).prior.rule4aKey
      ((frame.compoundKeyAt input target view derived) right).prior.rule4aKey =
      Ordering.eq :=
    (input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      ((frame.compoundKeyAt input target view derived) left).prior
      ((frame.compoundKeyAt input target view derived) right).prior).mp tie |>.1
  -- The Rule-4a tie exposes the three constitutional columns.
  have columns := cumulativeRule45Tie_constitutional_columns input
    ((frame.compoundKeyAt input target view derived) left).prior.rule4aKey
    ((frame.compoundKeyAt input target view derived) right).prior.rule4aKey rule4aTie
  exact rootedCutBranchIso_of_actualFrame_constitutionalColumns input target view frame derived
    center centerReal singleBonded acyclic enough alpha ligandLink left right
    columns.1 columns.2.1 columns.2.2





theorem constitutionalTieYieldsRootedCutBranchIso_at_actualFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.canonicalLigandAtom center (alpha index)))
    (left right : Fin 4)
    (tie : OfficialRuleMajorKey.compare
      ((frame.compoundKeyAt input target view derived) left).prior.rule4aKey.constitutional
      ((frame.compoundKeyAt input target view derived) right).prior.rule4aKey.constitutional =
      Ordering.eq) :
    Nonempty (RootedCutBranchIso input.moleculeGraph center.1
      (input.canonicalLigandAtom center (alpha left))
      (input.canonicalLigandAtom center (alpha right))) := by
  have columns := (officialRuleMajorKey_compare_eq_iff
    ((frame.compoundKeyAt input target view derived) left).prior.rule4aKey.constitutional
    ((frame.compoundKeyAt input target view derived) right).prior.rule4aKey.constitutional).mp tie
  exact rootedCutBranchIso_of_actualFrame_constitutionalColumns input target view frame derived
    center centerReal singleBonded acyclic enough alpha ligandLink left right
    columns.1 columns.2.1 columns.2.2

/-! ## Deriving the slot permutation from the actual frame -/





theorem exists_ligandPermutation_of_actualFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel) :
    ∃ alpha : Equiv.Perm (Fin 4),
      ∀ index : Fin 4,
        (frame.cursorAt index).occurrence.1.node.current? =
          some (input.canonicalLigandAtom center (alpha index)) := by
  have computed : input.localizedOccurrenceFourLigandFrame? target = some frame :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mpr derived
  obtain ⟨ligand, ligandSpec⟩ :=
    input.exists_localizedOccurrenceFourLigandFrame_neighborEquiv
      singleBonded acyclic enough target centerReal.2 frame computed
  let alpha : Equiv.Perm (Fin 4) := ligand.trans (input.canonicalLigandEquiv center).symm
  refine ⟨alpha, fun index => ?_⟩
  have readsBack : input.canonicalLigandEquiv center (alpha index) = ligand index := by
    simp [alpha]
  calc
    (frame.cursorAt index).occurrence.1.node.current? = some (ligand index).1 :=
      ligandSpec index
    _ = some (input.canonicalLigandEquiv center (alpha index)).1 := by rw [readsBack]
    _ = some (input.canonicalLigandAtom center (alpha index)) := by
      rw [input.canonicalLigandEquiv_apply_coe]

/-- **Per-frame interface, with the slot permutation derived rather than supplied.**  The
per-frame rooted cut-branch isomorphism of `priorTieYieldsRootedCutBranchIso_at_actualFrame`,
stated existentially in the slot permutation so that no frame-to-canonical slot link is assumed. -/
theorem exists_priorTieYieldsRootedCutBranchIso_at_actualFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel) :
    ∃ alpha : Equiv.Perm (Fin 4),
      PriorTieYieldsRootedCutBranchIso input
        (frame.compoundKeyAt input target view derived)
        input.moleculeGraph center.1
        (fun index => input.canonicalLigandAtom center (alpha index)) := by
  obtain ⟨alpha, ligandLink⟩ :=
    exists_ligandPermutation_of_actualFrame input target frame derived center centerReal
      singleBonded acyclic enough
  exact ⟨alpha, priorTieYieldsRootedCutBranchIso_at_actualFrame input target view frame derived
    center centerReal singleBonded acyclic enough alpha ligandLink⟩

/-! ## Actual key separation from graph-level rigidity -/





theorem constitutionallySeparatedActualFrameKeys_of_graphRigid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.moleculeGraph center.1)
    (hacyc : input.moleculeGraph.Acyclic)
    (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.canonicalLigandAtom center (alpha index))) :
    CertifiedLocalizedCIPInput.ConstitutionallySeparatedActualKeys input
      (frame.compoundKeyAt input target view derived) :=
  constitutionallySeparatedActualKeys_of_graphRigid input
    (frame.compoundKeyAt input target view derived) input.moleculeGraph center.1
    rigid hacyc hsimple hcharge
    (fun index => input.canonicalLigandAtom center (alpha index))
    (fun index => input.canonicalLigandAtom_adj center (alpha index))
    (fun _ _ same => alpha.injective (input.canonicalLigandAtom_injective center same))
    (priorTieYieldsRootedCutBranchIso_at_actualFrame input target view frame derived
      center centerReal hsimple hacyc enough alpha ligandLink)



theorem constitutionallySeparatedActualFrameKeys_of_actualFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.moleculeGraph center.1)
    (hacyc : input.moleculeGraph.Acyclic)
    (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel) :
    CertifiedLocalizedCIPInput.ConstitutionallySeparatedActualKeys input
      (frame.compoundKeyAt input target view derived) := by
  obtain ⟨alpha, ligandLink⟩ :=
    exists_ligandPermutation_of_actualFrame input target frame derived center centerReal
      hsimple hacyc enough
  exact constitutionallySeparatedActualFrameKeys_of_graphRigid input target view frame derived
    center centerReal rigid hacyc hsimple hcharge enough alpha ligandLink

/-! ## No constitutional three-column tie at the actual frame -/








theorem constitutionalCompare_ne_at_actualFrame_of_graphRigid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.moleculeGraph center.1)
    (hacyc : input.moleculeGraph.Acyclic)
    (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.canonicalLigandAtom center (alpha index)))
    (left right : Fin 4) (different : left ≠ right) :
    OfficialRuleMajorKey.compare
      ((frame.compoundKeyAt input target view derived) left).prior.rule4aKey.constitutional
      ((frame.compoundKeyAt input target view derived) right).prior.rule4aKey.constitutional ≠
      Ordering.eq := by
  intro tie
  have distinct : input.canonicalLigandAtom center (alpha left) ≠
      input.canonicalLigandAtom center (alpha right) := by
    intro same
    exact different (alpha.injective (input.canonicalLigandAtom_injective center same))
  exact no_rootedCutBranchIso_of_pointwise_fixed input.moleculeGraph center.1
    (input.canonicalLigandAtom center (alpha left))
    (input.canonicalLigandAtom center (alpha right))
    hacyc (input.canonicalLigandAtom_adj center (alpha left))
    (input.canonicalLigandAtom_adj center (alpha right)) distinct hsimple hcharge rigid
    (constitutionalTieYieldsRootedCutBranchIso_at_actualFrame input target view frame derived
      center centerReal hsimple hacyc enough alpha ligandLink left right tie)





theorem constitutionalCompare_ne_at_actualFrame_of_graphRigid_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.moleculeGraph center.1)
    (hacyc : input.moleculeGraph.Acyclic)
    (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (left right : Fin 4) (different : left ≠ right) :
    OfficialRuleMajorKey.compare
      ((frame.compoundKeyAt input target view derived) left).prior.rule4aKey.constitutional
      ((frame.compoundKeyAt input target view derived) right).prior.rule4aKey.constitutional ≠
      Ordering.eq := by
  obtain ⟨alpha, ligandLink⟩ :=
    exists_ligandPermutation_of_actualFrame input target frame derived center centerReal
      hsimple hacyc enough
  exact constitutionalCompare_ne_at_actualFrame_of_graphRigid input target view frame derived
    center centerReal rigid hacyc hsimple hcharge enough alpha ligandLink left right different

/-! ## Descriptor endpoints without the key-table interface -/







theorem localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_physicalFrame_noInterface
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.moleculeGraph center.1)
    (hacyc : input.moleculeGraph.Acyclic) (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.canonicalLigandAtom center (alpha index)))
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      input.localizedOccurrenceRule45Descriptor? target view =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) := by
  have separated : CertifiedLocalizedCIPInput.ConstitutionallySeparatedActualKeys input
      (frame.compoundKeyAt input target view derived) :=
    constitutionallySeparatedActualFrameKeys_of_graphRigid input target view frame derived
      center centerReal rigid hacyc hsimple hcharge enough alpha ligandLink
  exact input.localizedConstitutionalRigidFrame_descriptor_eq_chiral_of_physicalFrame
    target view frame derived (frame.compoundKeyAt input target view derived)
    (fun index => frame.compoundKeyAt_built input target view derived index)
    separated center centerReal pointsAt spatial parity writtenParity



theorem localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_physicalFrame_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.moleculeGraph center.1)
    (hacyc : input.moleculeGraph.Acyclic) (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      input.localizedOccurrenceRule45Descriptor? target view =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) := by
  have separated : CertifiedLocalizedCIPInput.ConstitutionallySeparatedActualKeys input
      (frame.compoundKeyAt input target view derived) :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input target view frame derived
      center centerReal rigid hacyc hsimple hcharge enough
  exact input.localizedConstitutionalRigidFrame_descriptor_eq_chiral_of_physicalFrame
    target view frame derived (frame.compoundKeyAt input target view derived)
    (fun index => frame.compoundKeyAt_built input target view derived index)
    separated center centerReal pointsAt spatial parity writtenParity





theorem localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_detectedRigid_noInterface
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigid input.detectedMultiCenterMolecule
      ⟨center.1, center.2⟩)
    (hacyc : input.moleculeGraph.Acyclic) (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.canonicalLigandAtom center (alpha index)))
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      input.localizedOccurrenceRule45Descriptor? target view =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) :=
  localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_physicalFrame_noInterface
    input target view frame derived center centerReal
    (constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input
      ⟨center.1, center.2⟩ rigid)
    hacyc hsimple hcharge alpha ligandLink enough pointsAt spatial parity writtenParity



theorem localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_detectedRigid_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigid input.detectedMultiCenterMolecule
      ⟨center.1, center.2⟩)
    (hacyc : input.moleculeGraph.Acyclic) (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) = some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      input.localizedOccurrenceRule45Descriptor? target view =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) :=
  localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_physicalFrame_derived
    input target view frame derived center centerReal
    (constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input
      ⟨center.1, center.2⟩ rigid)
    hacyc hsimple hcharge enough pointsAt spatial parity writtenParity

/-! ## Generated reference-state readback without the key-table interface -/






theorem referenceState_reader_eq_chiral_of_constitutionallyRigidFrame_noInterface
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.certified.moleculeGraph center.1)
    (hacyc : input.certified.moleculeGraph.Acyclic)
    (hsimple : input.certified.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.canonicalLigandAtom center (alpha index)))
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
        some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.certified.localizedOccurrenceRule45TrackedOrder? target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      LocalizedUniversalReference.referenceState input target =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) := by
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    simp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel,
      LocalizedReference.Input.molecule]
  obtain ⟨tracked, trackedComputed, pseudo, descriptorEq⟩ :=
    localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_physicalFrame_noInterface
      input.certified target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target)
      frame derived center centerReal rigid hacyc hsimple hcharge alpha ligandLink enough
      pointsAt spatial parity writtenParity
  refine ⟨tracked, trackedComputed, pseudo, ?_⟩
  exact input.certified.localizedCIPModel_reader_eq_chiral_of_rule45_descriptor
    (input.certified.localizedOccurrenceRule45AuxiliarySemantics
      (LocalizedUniversalReference.carrierFuel input))
    (LocalizedUniversalReference.referenceState input)
    (LocalizedUniversalReference.referenceState_bareRule45CIPModel_of_noDoubleRecords
      input noDouble)
    target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target)
    (RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))
    rfl descriptorEq




theorem referenceState_reader_eq_chiral_of_detectedRigid_noInterface
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigid input.certified.detectedMultiCenterMolecule
      ⟨center.1, center.2⟩)
    (hacyc : input.certified.moleculeGraph.Acyclic)
    (hsimple : input.certified.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.canonicalLigandAtom center (alpha index)))
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
        some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.certified.localizedOccurrenceRule45TrackedOrder? target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      LocalizedUniversalReference.referenceState input target =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) :=
  referenceState_reader_eq_chiral_of_constitutionallyRigidFrame_noInterface input noDouble target
    frame derived center centerReal
    (constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified
      ⟨center.1, center.2⟩ rigid)
    hacyc hsimple hcharge alpha ligandLink pointsAt spatial parity writtenParity






theorem referenceState_reader_eq_chiral_of_detectedRigid_derived
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigid input.certified.detectedMultiCenterMolecule
      ⟨center.1, center.2⟩)
    (hacyc : input.certified.moleculeGraph.Acyclic)
    (hsimple : input.certified.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
        some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.certified.localizedOccurrenceRule45TrackedOrder? target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      LocalizedUniversalReference.referenceState input target =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) := by
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    simp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel,
      LocalizedReference.Input.molecule]
  obtain ⟨tracked, trackedComputed, pseudo, descriptorEq⟩ :=
    localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_physicalFrame_derived
      input.certified target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target)
      frame derived center centerReal
      (constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified
        ⟨center.1, center.2⟩ rigid)
      hacyc hsimple hcharge enough pointsAt spatial parity writtenParity
  refine ⟨tracked, trackedComputed, pseudo, ?_⟩
  exact input.certified.localizedCIPModel_reader_eq_chiral_of_rule45_descriptor
    (input.certified.localizedOccurrenceRule45AuxiliarySemantics
      (LocalizedUniversalReference.carrierFuel input))
    (LocalizedUniversalReference.referenceState input)
    (LocalizedUniversalReference.referenceState_bareRule45CIPModel_of_noDoubleRecords
      input noDouble)
    target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target)
    (RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))
    rfl descriptorEq

/-! ## Public kernel guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.canonicalLigandEquiv
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.canonicalLigandEquiv_apply_coe
assert_kernel_only TetraStereo.OneCenter.rootedCutBranchIso_of_actualFrame_constitutionalColumns
assert_kernel_only TetraStereo.OneCenter.priorTieYieldsRootedCutBranchIso_at_actualFrame
assert_kernel_only TetraStereo.OneCenter.constitutionalTieYieldsRootedCutBranchIso_at_actualFrame
assert_kernel_only TetraStereo.OneCenter.exists_ligandPermutation_of_actualFrame
assert_kernel_only TetraStereo.OneCenter.exists_priorTieYieldsRootedCutBranchIso_at_actualFrame
assert_kernel_only TetraStereo.OneCenter.constitutionallySeparatedActualFrameKeys_of_graphRigid
assert_kernel_only TetraStereo.OneCenter.constitutionallySeparatedActualFrameKeys_of_actualFrame
assert_kernel_only TetraStereo.OneCenter.constitutionalCompare_ne_at_actualFrame_of_graphRigid
assert_kernel_only
  TetraStereo.OneCenter.constitutionalCompare_ne_at_actualFrame_of_graphRigid_derived
assert_kernel_only
  TetraStereo.OneCenter.localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_physicalFrame_noInterface
assert_kernel_only
  TetraStereo.OneCenter.localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_physicalFrame_derived
assert_kernel_only
  TetraStereo.OneCenter.localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_detectedRigid_noInterface
assert_kernel_only
  TetraStereo.OneCenter.localizedConstitutionallyRigidFrame_descriptor_eq_chiral_of_detectedRigid_derived
assert_kernel_only
  TetraStereo.OneCenter.referenceState_reader_eq_chiral_of_constitutionallyRigidFrame_noInterface
assert_kernel_only
  TetraStereo.OneCenter.referenceState_reader_eq_chiral_of_detectedRigid_noInterface
assert_kernel_only
  TetraStereo.OneCenter.referenceState_reader_eq_chiral_of_detectedRigid_derived

end TetraStereo.OneCenter
