/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.LocalizedGeneralRigidLabelCovariance
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.OneCenter.LocalizedOuterDigraphActualPriorityFidelity
import TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput















































































































/-! ## A. Actual branch trees of the four frame slots -/







theorem exists_frameSlotBranchTree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (index : Fin 4) :
    ∃ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
      tree.source = frame.cursorAt index ∧
        LocalizedCumulativeTreeTableMatch .rule4a tree
          ((frame.compoundKeyAt input target view derived index).prior.rule4aKey) ∧
          LocalizedCumulativeTreeRealizes input
            (fun cursor => input.localizedDependencyLabel target view cursor) tree := by
  have buildEq :=
    buildLocalizedRerootCompoundRule45Key?_rule4a_of_frame input target view frame derived index
  have withReadEq :
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
          (fun cursor => input.localizedDependencyLabel target view cursor)
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some ((frame.compoundKeyAt input target view derived index).prior.rule4aKey) := by
    rw [buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      input .rule4a target view]
    exact buildEq
  obtain ⟨tree, source, trace⟩ :=
    exists_trace_of_buildWithRead input .rule4a
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) _ withReadEq
  exact ⟨tree, source,
    (LocalizedActualRecursiveSortTrace.fullMatch_of_trace trace).tableMatch,
    LocalizedActualRecursiveSortTrace.realizes_of_trace trace⟩

/-- The actual `.rule4a` branch tree of a frame slot, obtained from `exists_frameSlotBranchTree`.
This is a `Classical.choose` of a *proved* existence statement; no tree, key, sort success or
reader relation is supplied by the caller. -/
noncomputable def frameSlotBranchTree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (index : Fin 4) :
    LocalizedCumulativeDecoratedTree input carrierFuel :=
  Classical.choose (exists_frameSlotBranchTree input target view frame derived index)

/-- The chosen branch tree is rooted at the slot cursor. -/
theorem frameSlotBranchTree_source
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (index : Fin 4) :
    (frameSlotBranchTree input target view frame derived index).source = frame.cursorAt index :=
  (Classical.choose_spec (exists_frameSlotBranchTree input target view frame derived index)).1

/-- The chosen branch tree's three constitutional tables match the slot's actual Rule-4a key. -/
theorem frameSlotBranchTree_tableMatch
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (index : Fin 4) :
    LocalizedCumulativeTreeTableMatch .rule4a
      (frameSlotBranchTree input target view frame derived index)
      ((frame.compoundKeyAt input target view derived index).prior.rule4aKey) :=
  (Classical.choose_spec (exists_frameSlotBranchTree input target view frame derived index)).2.1

/-- The chosen branch tree carries the recursive actual provenance at the actual reader. -/
theorem frameSlotBranchTree_realizes
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (index : Fin 4) :
    LocalizedCumulativeTreeRealizes input
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (frameSlotBranchTree input target view frame derived index) :=
  (Classical.choose_spec (exists_frameSlotBranchTree input target view frame derived index)).2.2

/-- **The original outer root is retained.**  The branch tree of any frame slot is rooted at the
target's own stored root `target.1.root`; no fresh root is substituted.  The frame's slot cursors
are the declared children of `{ occurrence := target, previous? := none }`, so
`localizedRerootChildren_root_eq` gives the equality. -/
theorem frameSlotBranchTree_root
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (index : Fin 4) :
    (frameSlotBranchTree input target view frame derived index).source.occurrence.1.root =
      target.1.root := by
  rw [frameSlotBranchTree_source]
  exact localizedRerootChildren_root_eq input { occurrence := target, previous? := none }
    (frame.cursorAt index) frame.cursors derived.1 (by
      unfold LocalizedOccurrenceFourLigandFrame.cursorAt
      exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index))

/-! ## B. The independent physical rule-major outcome of two frame slots -/






noncomputable def frameSlotPhysicalOutcome
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (outerRoot : input.Atom)
    (left right : Fin 4) (outcome : Ordering) : Prop :=
  physicalRuleMajorOutcome singleBonded acyclic outerRoot
    (frameSlotBranchTree input target view frame derived left)
    (frameSlotBranchTree input target view frame derived right) outcome






theorem frameSlotPhysicalOutcome_iff_constitutionalCompare
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (left right : Fin 4) (outcome : Ordering) :
    OfficialRuleMajorKey.compare
        ((frame.compoundKeyAt input target view derived left).prior.rule4aKey.constitutional)
        ((frame.compoundKeyAt input target view derived right).prior.rule4aKey.constitutional) =
        outcome ↔
      frameSlotPhysicalOutcome input target view frame derived singleBonded acyclic
        target.1.root left right outcome := by
  unfold frameSlotPhysicalOutcome
  exact compare_eq_iff_physicalRuleMajorOutcome
    (singleBonded := singleBonded) (acyclic := acyclic)
    (stage := .rule4a)
    (readLeft := fun cursor => input.localizedDependencyLabel target view cursor)
    (readRight := fun cursor => input.localizedDependencyLabel target view cursor)
    (leftTree := frameSlotBranchTree input target view frame derived left)
    (rightTree := frameSlotBranchTree input target view frame derived right)
    (leftKey := (frame.compoundKeyAt input target view derived left).prior.rule4aKey)
    (rightKey := (frame.compoundKeyAt input target view derived right).prior.rule4aKey)
    (leftMatch := frameSlotBranchTree_tableMatch input target view frame derived left)
    (rightMatch := frameSlotBranchTree_tableMatch input target view frame derived right)
    (realizesLeft := frameSlotBranchTree_realizes input target view frame derived left)
    (realizesRight := frameSlotBranchTree_realizes input target view frame derived right)
    (outerRoot := target.1.root)
    (leftRoot := frameSlotBranchTree_root input target view frame derived left)
    (rightRoot := frameSlotBranchTree_root input target view frame derived right)
    (outcome := outcome)

/-! ## C. Physical strictness is the strict key rank -/








theorem frameSlotPhysicalOutcome_rank_lt_of_gt
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
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (left right : Fin 4) (different : left ≠ right)
    (higher : frameSlotPhysicalOutcome input target view frame derived hsimple hacyc
      target.1.root left right Ordering.gt) :
    input.compoundKeyRank (frame.compoundKeyAt input target view derived) right <
      input.compoundKeyRank (frame.compoundKeyAt input target view derived) left := by
  have separated : ConstitutionallySeparatedActualKeys input
      (frame.compoundKeyAt input target view derived) :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input target view frame derived center
      centerReal rigid hacyc hsimple hcharge enough
  have decisive : ∀ left right : Fin 4, left ≠ right →
      OfficialRuleMajorKey.compare
        ((frame.compoundKeyAt input target view derived left).prior.rule4aKey.constitutional)
        ((frame.compoundKeyAt input target view derived right).prior.rule4aKey.constitutional) ≠
        Ordering.eq :=
    fun left right different =>
      constitutionalCompare_ne_at_actualFrame_of_graphRigid_derived input target view frame derived
        center centerReal rigid hacyc hsimple hcharge enough left right different
  have compared : OfficialRuleMajorKey.compare
      ((frame.compoundKeyAt input target view derived left).prior.rule4aKey.constitutional)
      ((frame.compoundKeyAt input target view derived right).prior.rule4aKey.constitutional) =
      Ordering.gt :=
    (frameSlotPhysicalOutcome_iff_constitutionalCompare input target view frame derived hsimple
      hacyc left right Ordering.gt).mpr higher
  have production :=
    compareLocalizedOccurrenceThroughRule5At?_eq_constitutional input target view frame
      (frame.compoundKeyAt input target view derived)
      (fun index => frame.compoundKeyAt_built input target view derived index)
      separated decisive left right different
  have rank :=
    input.compareLocalizedOccurrenceThroughRule5At?_eq_strictRankComparison target view frame
      (frame.compoundKeyAt input target view derived)
      (fun index => frame.compoundKeyAt_built input target view derived index)
      separated left right different
  have orderingEq : compare
        (input.compoundKeyRank (frame.compoundKeyAt input target view derived) left)
        (input.compoundKeyRank (frame.compoundKeyAt input target view derived) right) =
      OfficialRuleMajorKey.compare
        ((frame.compoundKeyAt input target view derived left).prior.rule4aKey.constitutional)
        ((frame.compoundKeyAt input target view derived right).prior.rule4aKey.constitutional) := by
    have mapped := congrArg
      (Option.map (fun record : ConstitutionalDescriptorHierarchyComparison => record.ordering))
      (rank.symm.trans production)
    simpa [strictRankComparison] using mapped
  rw [compared] at orderingEq
  exact Nat.compare_eq_gt.mp orderingEq

/-- **Strictly smaller key rank implies physical seniority.**  The converse of
`frameSlotPhysicalOutcome_rank_lt_of_gt`.  This direction needs no distinctness hypothesis: a
strict rank inequality already forces the two slots to differ. -/
theorem frameSlotPhysicalOutcome_gt_of_rank_lt
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
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (left right : Fin 4)
    (higher : input.compoundKeyRank (frame.compoundKeyAt input target view derived) right <
      input.compoundKeyRank (frame.compoundKeyAt input target view derived) left) :
    frameSlotPhysicalOutcome input target view frame derived hsimple hacyc
      target.1.root left right Ordering.gt := by
  have different : left ≠ right := by
    intro same
    rw [same] at higher
    exact Nat.lt_irrefl _ higher
  have separated : ConstitutionallySeparatedActualKeys input
      (frame.compoundKeyAt input target view derived) :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input target view frame derived center
      centerReal rigid hacyc hsimple hcharge enough
  have decisive : ∀ left right : Fin 4, left ≠ right →
      OfficialRuleMajorKey.compare
        ((frame.compoundKeyAt input target view derived left).prior.rule4aKey.constitutional)
        ((frame.compoundKeyAt input target view derived right).prior.rule4aKey.constitutional) ≠
        Ordering.eq :=
    fun left right different =>
      constitutionalCompare_ne_at_actualFrame_of_graphRigid_derived input target view frame derived
        center centerReal rigid hacyc hsimple hcharge enough left right different
  have production :=
    compareLocalizedOccurrenceThroughRule5At?_eq_constitutional input target view frame
      (frame.compoundKeyAt input target view derived)
      (fun index => frame.compoundKeyAt_built input target view derived index)
      separated decisive left right different
  have rank :=
    input.compareLocalizedOccurrenceThroughRule5At?_eq_strictRankComparison target view frame
      (frame.compoundKeyAt input target view derived)
      (fun index => frame.compoundKeyAt_built input target view derived index)
      separated left right different
  have orderingEq : compare
        (input.compoundKeyRank (frame.compoundKeyAt input target view derived) left)
        (input.compoundKeyRank (frame.compoundKeyAt input target view derived) right) =
      OfficialRuleMajorKey.compare
        ((frame.compoundKeyAt input target view derived left).prior.rule4aKey.constitutional)
        ((frame.compoundKeyAt input target view derived right).prior.rule4aKey.constitutional) := by
    have mapped := congrArg
      (Option.map (fun record : ConstitutionalDescriptorHierarchyComparison => record.ordering))
      (rank.symm.trans production)
    simpa [strictRankComparison] using mapped
  have compared : OfficialRuleMajorKey.compare
      ((frame.compoundKeyAt input target view derived left).prior.rule4aKey.constitutional)
      ((frame.compoundKeyAt input target view derived right).prior.rule4aKey.constitutional) =
      Ordering.gt := by
    rw [Nat.compare_eq_gt.mpr higher] at orderingEq
    exact orderingEq.symm
  exact (frameSlotPhysicalOutcome_iff_constitutionalCompare input target view frame derived hsimple
    hacyc left right Ordering.gt).mp compared




theorem frameSlotPhysicalOutcome_total_of_ne
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
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (left right : Fin 4) (different : left ≠ right) :
    frameSlotPhysicalOutcome input target view frame derived hsimple hacyc
        target.1.root left right Ordering.gt ∨
      frameSlotPhysicalOutcome input target view frame derived hsimple hacyc
        target.1.root left right Ordering.lt := by
  have decisive :=
    constitutionalCompare_ne_at_actualFrame_of_graphRigid_derived input target view frame derived
      center centerReal rigid hacyc hsimple hcharge enough left right different
  cases compared : OfficialRuleMajorKey.compare
      ((frame.compoundKeyAt input target view derived left).prior.rule4aKey.constitutional)
      ((frame.compoundKeyAt input target view derived right).prior.rule4aKey.constitutional) with
  | lt =>
      exact Or.inr ((frameSlotPhysicalOutcome_iff_constitutionalCompare input target view frame
        derived hsimple hacyc left right Ordering.lt).mp compared)
  | eq => exact absurd compared decisive
  | gt =>
      exact Or.inl ((frameSlotPhysicalOutcome_iff_constitutionalCompare input target view frame
        derived hsimple hacyc left right Ordering.gt).mp compared)

/-! ## D. The independent highest-first order -/

/-- **The independent highest-first order of the four physical neighbours.**  The list is a
permutation of the four slots and every earlier slot is physically senior to every later one, for
the independent physical rule-major outcome at the retained outer root `target.1.root`.

The definition mentions neither `tracked.highestFirst` nor any executable sorter, key, rank or
permutation output. -/
def IndependentPhysicalHighestFirst
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (order : List (Fin 4)) : Prop :=
  order.Perm (List.finRange 4) ∧
    order.Pairwise (fun left right =>
      frameSlotPhysicalOutcome input target view frame derived singleBonded acyclic
        target.1.root left right Ordering.gt)

/-- **Existence from actual admissibility.**  The actual tracked order produced by
`exists_trackedOrder_of_constitutionallySeparatedActualKeys` is a permutation of the four slots and
is strictly descending for the actual compound rank; the rank equivalence
`frameSlotPhysicalOutcome_gt_of_rank_lt` turns that strictness into independent physical seniority.
No desired order, sorting success or reader correspondence is assumed. -/
theorem exists_independentPhysicalHighestFirst
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
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel) :
    ∃ order : List (Fin 4),
      IndependentPhysicalHighestFirst input target view frame derived hsimple hacyc order := by
  have separated : ConstitutionallySeparatedActualKeys input
      (frame.compoundKeyAt input target view derived) :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input target view frame derived center
      centerReal rigid hacyc hsimple hcharge enough
  obtain ⟨tracked, _trackedComputed, permutation, strict, _pseudo⟩ :=
    input.exists_trackedOrder_of_constitutionallySeparatedActualKeys target view frame derived
      (frame.compoundKeyAt input target view derived)
      (fun index => frame.compoundKeyAt_built input target view derived index) separated
  refine ⟨tracked.highestFirst, permutation, ?_⟩
  exact strict.imp (fun {left right} higher =>
    frameSlotPhysicalOutcome_gt_of_rank_lt input target view frame derived center centerReal rigid
      hacyc hsimple hcharge enough left right higher)

/-- **Strict sorted permutation uniqueness.**  If two permutations of the four slots are both
strictly descending for the actual compound rank, they are the same list.  Antisymmetry on the
union comes from injectivity of the rank, which is derived from the separated actual keys. -/
theorem eq_of_pairwise_rank_strict
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
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {first second : List (Fin 4)}
    (permutationFirst : first.Perm (List.finRange 4))
    (permutationSecond : second.Perm (List.finRange 4))
    (strictFirst : first.Pairwise (fun left right =>
      input.compoundKeyRank (frame.compoundKeyAt input target view derived) right <
        input.compoundKeyRank (frame.compoundKeyAt input target view derived) left))
    (strictSecond : second.Pairwise (fun left right =>
      input.compoundKeyRank (frame.compoundKeyAt input target view derived) right <
        input.compoundKeyRank (frame.compoundKeyAt input target view derived) left)) :
    first = second := by
  have separated : ConstitutionallySeparatedActualKeys input
      (frame.compoundKeyAt input target view derived) :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input target view frame derived center
      centerReal rigid hacyc hsimple hcharge enough
  have offDiagonal : input.CompoundKeyOffDiagonalStrict
      (frame.compoundKeyAt input target view derived) :=
    input.compoundKeyOffDiagonalStrict_of_priorSeparated
      (frame.compoundKeyAt input target view derived) separated
  have injective : Function.Injective
      (input.compoundKeyRank (frame.compoundKeyAt input target view derived)) :=
    input.compoundKeyRank_injective (frame.compoundKeyAt input target view derived) offDiagonal
  have permutationTransport : List.Perm first second :=
    permutationFirst.trans permutationSecond.symm
  refine List.Perm.eq_of_pairwise
    (le := fun left right => ¬
      input.compoundKeyRank (frame.compoundKeyAt input target view derived) left <
        input.compoundKeyRank (frame.compoundKeyAt input target view derived) right)
    ?_ ?_ ?_ permutationTransport
  · intro left right _ _ notLeft notRight
    exact injective (le_antisymm (Nat.le_of_not_lt notRight) (Nat.le_of_not_lt notLeft))
  · exact strictFirst.imp (fun {left right} higher => Nat.not_lt_of_ge (Nat.le_of_lt higher))
  · exact strictSecond.imp (fun {left right} higher => Nat.not_lt_of_ge (Nat.le_of_lt higher))

/-- **Physical pairwise descent implies strict rank descent.**  A `Nodup` list that is pairwise
physically senior is pairwise strictly descending for the actual compound rank.  The distinctness
required by `frameSlotPhysicalOutcome_rank_lt_of_gt` comes from the `Nodup` hypothesis at the head
of the list. -/
theorem pairwise_rank_of_pairwise_physical
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
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (order : List (Fin 4)) :
    order.Pairwise (fun left right =>
        frameSlotPhysicalOutcome input target view frame derived hsimple hacyc
          target.1.root left right Ordering.gt) →
      order.Nodup →
        order.Pairwise (fun left right =>
          input.compoundKeyRank (frame.compoundKeyAt input target view derived) right <
            input.compoundKeyRank (frame.compoundKeyAt input target view derived) left) := by
  induction order with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      intro physical nodup
      cases physical with
      | cons headRel tailRel =>
          refine List.Pairwise.cons ?_ (inductionHypothesis tailRel nodup.of_cons)
          intro member memberOf
          have notMem : head ∉ tail := (List.nodup_cons.mp nodup).1
          have different : head ≠ member := fun same => notMem (same.symm ▸ memberOf)
          exact frameSlotPhysicalOutcome_rank_lt_of_gt input target view frame derived center
            centerReal rigid hacyc hsimple hcharge enough head member different
            (headRel member memberOf)

/-- **The independent order is exactly the actual tracked order.**  The physical pairwise
strictness of an independent order is converted to strict compound-rank descent (using the
original-root branch trees and the derived rank equivalence), and strict sorted permutation
uniqueness identifies it with `tracked.highestFirst`. -/
theorem trackedHighestFirst_eq_independent
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
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (order : List (Fin 4))
    (independent : IndependentPhysicalHighestFirst input target view frame derived hsimple hacyc
      order)
    (tracked : TrackedLocalizedLigandOrder)
    (trackedPermutation : tracked.highestFirst.Perm (List.finRange 4))
    (trackedStrict : tracked.highestFirst.Pairwise (fun left right =>
      input.compoundKeyRank (frame.compoundKeyAt input target view derived) right <
        input.compoundKeyRank (frame.compoundKeyAt input target view derived) left)) :
    tracked.highestFirst = order := by
  have permutation : order.Perm (List.finRange 4) := independent.1
  have physicalPairwise : order.Pairwise (fun left right =>
      frameSlotPhysicalOutcome input target view frame derived hsimple hacyc
        target.1.root left right Ordering.gt) := independent.2
  have nodup : order.Nodup :=
    (List.nodup_finRange 4).perm permutation.symm
  have orderStrict : order.Pairwise (fun left right =>
      input.compoundKeyRank (frame.compoundKeyAt input target view derived) right <
        input.compoundKeyRank (frame.compoundKeyAt input target view derived) left) :=
    pairwise_rank_of_pairwise_physical input target view frame derived center centerReal rigid
      hacyc hsimple hcharge enough order physicalPairwise nodup
  exact (eq_of_pairwise_rank_strict input target view frame derived center centerReal rigid hacyc
    hsimple hcharge enough permutation trackedPermutation orderStrict trackedStrict).symm

/-! ## E. The rational tetrahedral descriptor is determined by the geometry -/

/-- **Descriptor uniqueness.**  For a fixed ordered point list at most one `R/S` descriptor can
satisfy the rational tetrahedral criterion: a negative and a positive oriented volume cannot
coexist. -/
theorem rationalTetrahedralDescriptor_unique
    {points : List CartesianPoint3} {first second : RS}
    (left : CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor points first)
    (right : CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor points second) :
    first = second := by
  cases first with
  | R =>
      cases second with
      | R => rfl
      | S =>
          obtain ⟨f, s, t, fo, pointsEq, negative⟩ := left
          obtain ⟨f', s', t', fo', pointsEq', positive⟩ := right
          have components : [f, s, t, fo] = [f', s', t', fo'] := pointsEq.symm.trans pointsEq'
          simp only [List.cons.injEq, List.nil_eq, and_true] at components
          obtain ⟨rfl, rfl, rfl, rfl⟩ := components
          exact absurd positive (not_lt.mpr (le_of_lt negative))
  | S =>
      cases second with
      | R =>
          obtain ⟨f, s, t, fo, pointsEq, positive⟩ := left
          obtain ⟨f', s', t', fo', pointsEq', negative⟩ := right
          have components : [f, s, t, fo] = [f', s', t', fo'] := pointsEq.symm.trans pointsEq'
          simp only [List.cons.injEq, List.nil_eq, and_true] at components
          obtain ⟨rfl, rfl, rfl, rfl⟩ := components
          exact absurd positive (not_lt.mpr (le_of_lt negative))
      | S => rfl

/-! ## F. The independent absolute auxiliary `R/S` label -/



private theorem map_eq_ofFn_getElem {α β : Type} (list : List α) (function : α → β) :
    list.map function =
      List.ofFn (fun index : Fin list.length => function (list[index])) :=
  (List.ofFn_getElem_eq_map list function).symm










theorem rationalTetrahedralDescriptor_of_independentOrder
    (pointsAt : Fin 4 → CartesianPoint3)
    (order : List (Fin 4))
    (permutation : order.Perm (List.finRange 4))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor (order.map pointsAt)
      (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven (order.map Fin.val))) := by
  have lengthEq : order.length = 4 := by
    simpa using permutation.length_eq
  let positions : List Nat := order.map Fin.val
  have positionsPermutation : positions.Perm (List.range 4) := by
    have mapped := permutation.map Fin.val
    simpa [positions, List.map_coe_finRange_eq_range] using mapped
  let ordering : Equiv.Perm (Fin 4) :=
    Rule6HandednessSemantics.finFourEquivOfPermutationList positions positionsPermutation
  have orderingList : Rule6HandednessSemantics.finFourPermutationList ordering = positions :=
    Rule6HandednessSemantics.finFourPermutationList_equivOfPermutationList
      positions positionsPermutation
  let getAt : Fin 4 → Fin 4 := fun index => order[Fin.cast lengthEq.symm index]
  have orderingEq : ∀ index : Fin 4, ordering index = getAt index := by
    intro index
    apply Fin.ext
    have functionsEq : (fun position : Fin 4 => (ordering position).val) =
        (fun position : Fin 4 => (getAt position).val) := by
      apply List.ofFn_inj.mp
      calc List.ofFn (fun position : Fin 4 => (ordering position).val)
          = Rule6HandednessSemantics.finFourPermutationList ordering := rfl
        _ = positions := orderingList
        _ = order.map Fin.val := rfl
        _ = List.ofFn (fun position : Fin order.length => (order[position]).val) :=
            map_eq_ofFn_getElem order Fin.val
        _ = List.ofFn (fun position : Fin 4 => (getAt position).val) := by
            simpa [getAt] using List.ofFn_congr lengthEq
              (fun position : Fin order.length => (order[position]).val)
    exact congrFun functionsEq index
  have pointVectorEq : ∀ index : Fin 4,
      RationalTetrahedralPermutation.pointVector
        (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) index = pointsAt index := by
    intro index
    fin_cases index <;> rfl
  have permutedEq : RationalTetrahedralPermutation.permutedPoints
        (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ordering =
      List.ofFn (fun index : Fin 4 =>
        RationalTetrahedralPermutation.pointVector
          (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) (ordering index)) := by
    simp [RationalTetrahedralPermutation.permutedPoints, List.ofFn_succ]
  have bridge : order.map pointsAt =
      RationalTetrahedralPermutation.permutedPoints
        (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ordering := by
    calc order.map pointsAt
        = List.ofFn (fun index : Fin 4 => pointsAt (getAt index)) := by
          rw [map_eq_ofFn_getElem order pointsAt]
          simpa [getAt] using List.ofFn_congr lengthEq
            (fun position : Fin order.length => pointsAt (order[position]))
      _ = List.ofFn (fun index : Fin 4 =>
            RationalTetrahedralPermutation.pointVector
              (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) (ordering index)) := by
          apply List.ofFn_inj.mpr
          funext index
          rw [orderingEq index]
          exact (pointVectorEq (getAt index)).symm
      _ = RationalTetrahedralPermutation.permutedPoints
            (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ordering :=
          permutedEq.symm
  obtain ⟨first, second, third, fourth, writtenEq, volume⟩ := writtenParity
  have splitFirst : pointsAt 0 = first ∧
      [pointsAt 1, pointsAt 2, pointsAt 3] = [second, third, fourth] :=
    (List.cons.injEq _ _ _ _).mp writtenEq
  have splitSecond : pointsAt 1 = second ∧
      [pointsAt 2, pointsAt 3] = [third, fourth] :=
    (List.cons.injEq _ _ _ _).mp splitFirst.2
  have splitThird : pointsAt 2 = third ∧ [pointsAt 3] = [fourth] :=
    (List.cons.injEq _ _ _ _).mp splitSecond.2
  have firstEq : pointsAt 0 = first := splitFirst.1
  have secondEq : pointsAt 1 = second := splitSecond.1
  have thirdEq : pointsAt 2 = third := splitThird.1
  have fourthEq : pointsAt 3 = fourth :=
    ((List.cons.injEq _ _ _ _).mp splitThird.2).1
  have pointsEqPermuted : RationalTetrahedralPermutation.permutedPoints
        (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ordering =
      RationalTetrahedralPermutation.permutedPoints
        first second third fourth ordering := by
    simp [RationalTetrahedralPermutation.permutedPoints,
      firstEq, secondEq, thirdEq, fourthEq]
  have labelEq : RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven
          (Rule6HandednessSemantics.finFourPermutationList ordering)) =
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven positions) := by
    rw [orderingList]
  rw [bridge, pointsEqPermuted, ← labelEq]
  exact RationalTetrahedralPermutation.rationalTetrahedralDescriptor_permutedPoints
    first second third fourth ordering parity volume


















theorem referenceState_eq_chiral_iff_physicalDescriptor
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigid input.certified.detectedMultiCenterMolecule
      ⟨center.1, center.2⟩)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
        some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0)
    (order : List (Fin 4))
    (independent : IndependentPhysicalHighestFirst input.certified target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target)
      frame derived singleBonded acyclic order)
    (rs : RS) :
    LocalizedUniversalReference.referenceState input target = some (.chiral rs) ↔
      CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor (order.map pointsAt) rs := by
  let view := input.certified.localizedDependencyView
    (LocalizedUniversalReference.referenceState input) target
  let volume := CartesianPoint3.orientedVolume
    (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3)
  let parity : TetrahedralInputParity := parityOfVolumeSign (rationalVolumeSign volume)
  have writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity :=
    rationalTetrahedralInputParity_parityOfVolumeSign
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) nonzero
  obtain ⟨tracked, trackedComputed, _pseudo, state⟩ :=
    referenceState_reader_eq_chiral_of_detectedRigid_derived (input := input)
      (noDouble := noDouble) (target := target) (frame := frame) (derived := derived)
      (center := center) (centerReal := centerReal) (rigid := rigid)
      (hacyc := acyclic) (hsimple := singleBonded) (hcharge := hcharge)
      (pointsAt := pointsAt) (spatial := spatial) (parity := parity)
      (writtenParity := writtenParity)
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    simp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel,
      LocalizedReference.Input.molecule]
  have rigidGraph : ConstitutionallyRigidGraphAt input.certified.moleculeGraph center.1 :=
    constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified
      ⟨center.1, center.2⟩ rigid
  have separated : ConstitutionallySeparatedActualKeys input.certified
      (frame.compoundKeyAt input.certified target view derived) :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input.certified target view frame
      derived center centerReal rigidGraph acyclic singleBonded hcharge enough
  obtain ⟨tracked', trackedComputed', permutation', strict', _pseudo'⟩ :=
    input.certified.exists_trackedOrder_of_constitutionallySeparatedActualKeys target view frame
      derived (frame.compoundKeyAt input.certified target view derived)
      (fun index => frame.compoundKeyAt_built input.certified target view derived index) separated
  have trackedEq : tracked' = tracked := by
    rw [trackedComputed] at trackedComputed'
    exact (Option.some.inj trackedComputed').symm
  have permutationTracked : tracked.highestFirst.Perm (List.finRange 4) := by
    simpa [trackedEq] using permutation'
  have strictTracked : tracked.highestFirst.Pairwise (fun left right =>
      input.certified.compoundKeyRank
          (frame.compoundKeyAt input.certified target view derived) right <
        input.certified.compoundKeyRank
          (frame.compoundKeyAt input.certified target view derived) left) := by
    simpa [trackedEq] using strict'
  have orderEq : tracked.highestFirst = order :=
    trackedHighestFirst_eq_independent input.certified target view frame derived center centerReal
      rigidGraph acyclic singleBonded hcharge enough order independent tracked permutationTracked
      strictTracked
  have stateOrder : LocalizedUniversalReference.referenceState input target =
      some (.chiral (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven (order.map Fin.val)))) := by
    rw [← orderEq]
    exact state
  have rational : CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor (order.map pointsAt)
      (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven (order.map Fin.val))) :=
    rationalTetrahedralDescriptor_of_independentOrder pointsAt order independent.1 parity
      writtenParity
  constructor
  · intro someEq
    have rsEq : rs = RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven (order.map Fin.val)) := by
      have combined := someEq.symm.trans stateOrder
      simpa using combined
    rw [rsEq]
    exact rational
  · intro descriptor
    have rsEq : rs = RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven (order.map Fin.val)) :=
      rationalTetrahedralDescriptor_unique descriptor rational
    rw [rsEq]
    exact stateOrder






theorem referenceState_eq_none_of_independentPhysicalTwin
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule center) :
    LocalizedUniversalReference.referenceState input target = none :=
  referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic noDouble
    input.certified.detectedMultiCenterMolecule rfl center target targetCurrent
    rootTetrahedral twin






















def ConstitutionalPriorityCorrespondence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (priority : Fin 4 → Fin 4 → Prop) : Prop :=
  ∀ left right : Fin 4, left ≠ right →
    (priority left right ↔
      OfficialRuleMajorKey.compare
        ((frame.compoundKeyAt input target view derived left).prior.rule4aKey.constitutional)
        ((frame.compoundKeyAt input target view derived right).prior.rule4aKey.constitutional) =
        Ordering.gt)

/-- **Highest-first predicate for an arbitrary physical priority relation.**  The list is a
permutation of the four physical slots and every earlier slot is priority-senior to every later
one. -/
def IndependentHighestFirstFor
    (priority : Fin 4 → Fin 4 → Prop) (order : List (Fin 4)) : Prop :=
  order.Perm (List.finRange 4) ∧ order.Pairwise priority





theorem priority_rank_lt_of_priority
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
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (priority : Fin 4 → Fin 4 → Prop)
    (correspondence : ConstitutionalPriorityCorrespondence input target view frame derived priority)
    (left right : Fin 4) (different : left ≠ right) (higher : priority left right) :
    input.compoundKeyRank (frame.compoundKeyAt input target view derived) right <
      input.compoundKeyRank (frame.compoundKeyAt input target view derived) left := by
  have separated : ConstitutionallySeparatedActualKeys input
      (frame.compoundKeyAt input target view derived) :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input target view frame derived center
      centerReal rigid hacyc hsimple hcharge enough
  have decisive : ∀ left right : Fin 4, left ≠ right →
      OfficialRuleMajorKey.compare
        ((frame.compoundKeyAt input target view derived left).prior.rule4aKey.constitutional)
        ((frame.compoundKeyAt input target view derived right).prior.rule4aKey.constitutional) ≠
        Ordering.eq :=
    fun left right different =>
      constitutionalCompare_ne_at_actualFrame_of_graphRigid_derived input target view frame derived
        center centerReal rigid hacyc hsimple hcharge enough left right different
  have compared : OfficialRuleMajorKey.compare
      ((frame.compoundKeyAt input target view derived left).prior.rule4aKey.constitutional)
      ((frame.compoundKeyAt input target view derived right).prior.rule4aKey.constitutional) =
      Ordering.gt :=
    (correspondence left right different).mp higher
  have production :=
    compareLocalizedOccurrenceThroughRule5At?_eq_constitutional input target view frame
      (frame.compoundKeyAt input target view derived)
      (fun index => frame.compoundKeyAt_built input target view derived index)
      separated decisive left right different
  have rank :=
    input.compareLocalizedOccurrenceThroughRule5At?_eq_strictRankComparison target view frame
      (frame.compoundKeyAt input target view derived)
      (fun index => frame.compoundKeyAt_built input target view derived index)
      separated left right different
  have orderingEq : compare
        (input.compoundKeyRank (frame.compoundKeyAt input target view derived) left)
        (input.compoundKeyRank (frame.compoundKeyAt input target view derived) right) =
      OfficialRuleMajorKey.compare
        ((frame.compoundKeyAt input target view derived left).prior.rule4aKey.constitutional)
        ((frame.compoundKeyAt input target view derived right).prior.rule4aKey.constitutional) := by
    have mapped := congrArg
      (Option.map (fun record : ConstitutionalDescriptorHierarchyComparison => record.ordering))
      (rank.symm.trans production)
    simpa [strictRankComparison] using mapped
  rw [compared] at orderingEq
  exact Nat.compare_eq_gt.mp orderingEq

/-- **Priority pairwise descent implies strict rank descent.**  The priority-agnostic counterpart
of `pairwise_rank_of_pairwise_physical`. -/
theorem pairwise_rank_of_pairwise_priority
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
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (priority : Fin 4 → Fin 4 → Prop)
    (correspondence : ConstitutionalPriorityCorrespondence input target view frame derived priority)
    (order : List (Fin 4)) :
    order.Pairwise priority →
      order.Nodup →
        order.Pairwise (fun left right =>
          input.compoundKeyRank (frame.compoundKeyAt input target view derived) right <
            input.compoundKeyRank (frame.compoundKeyAt input target view derived) left) := by
  induction order with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      intro physical nodup
      cases physical with
      | cons headRel tailRel =>
          refine List.Pairwise.cons ?_ (inductionHypothesis tailRel nodup.of_cons)
          intro member memberOf
          have notMem : head ∉ tail := (List.nodup_cons.mp nodup).1
          have different : head ≠ member := fun same => notMem (same.symm ▸ memberOf)
          exact priority_rank_lt_of_priority input target view frame derived center
            centerReal rigid hacyc hsimple hcharge enough priority correspondence head member
            different (headRel member memberOf)

/-- **The priority-ordered list is the actual tracked order.**  The priority-agnostic counterpart
of `trackedHighestFirst_eq_independent`. -/
theorem trackedHighestFirst_eq_priorityOrder
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
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (priority : Fin 4 → Fin 4 → Prop)
    (correspondence : ConstitutionalPriorityCorrespondence input target view frame derived priority)
    (order : List (Fin 4))
    (independent : IndependentHighestFirstFor priority order)
    (tracked : TrackedLocalizedLigandOrder)
    (trackedPermutation : tracked.highestFirst.Perm (List.finRange 4))
    (trackedStrict : tracked.highestFirst.Pairwise (fun left right =>
      input.compoundKeyRank (frame.compoundKeyAt input target view derived) right <
        input.compoundKeyRank (frame.compoundKeyAt input target view derived) left)) :
    tracked.highestFirst = order := by
  have permutation : order.Perm (List.finRange 4) := independent.1
  have priorityPairwise : order.Pairwise priority := independent.2
  have nodup : order.Nodup :=
    (List.nodup_finRange 4).perm permutation.symm
  have orderStrict : order.Pairwise (fun left right =>
      input.compoundKeyRank (frame.compoundKeyAt input target view derived) right <
        input.compoundKeyRank (frame.compoundKeyAt input target view derived) left) :=
    pairwise_rank_of_pairwise_priority input target view frame derived center centerReal rigid
      hacyc hsimple hcharge enough priority correspondence order priorityPairwise nodup
  exact (eq_of_pairwise_rank_strict input target view frame derived center centerReal rigid hacyc
    hsimple hcharge enough permutation trackedPermutation orderStrict trackedStrict).symm









theorem referenceState_eq_chiral_iff_priorityDescriptor
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigid input.certified.detectedMultiCenterMolecule
      ⟨center.1, center.2⟩)
    (priority : Fin 4 → Fin 4 → Prop)
    (correspondence : ConstitutionalPriorityCorrespondence input.certified target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target)
      frame derived priority)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
        some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0)
    (order : List (Fin 4))
    (independent : IndependentHighestFirstFor priority order)
    (rs : RS) :
    LocalizedUniversalReference.referenceState input target = some (.chiral rs) ↔
      CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor (order.map pointsAt) rs := by
  let view := input.certified.localizedDependencyView
    (LocalizedUniversalReference.referenceState input) target
  let volume := CartesianPoint3.orientedVolume
    (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3)
  let parity : TetrahedralInputParity := parityOfVolumeSign (rationalVolumeSign volume)
  have writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity :=
    rationalTetrahedralInputParity_parityOfVolumeSign
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) nonzero
  obtain ⟨tracked, trackedComputed, _pseudo, state⟩ :=
    referenceState_reader_eq_chiral_of_detectedRigid_derived (input := input)
      (noDouble := noDouble) (target := target) (frame := frame) (derived := derived)
      (center := center) (centerReal := centerReal) (rigid := rigid)
      (hacyc := acyclic) (hsimple := singleBonded) (hcharge := hcharge)
      (pointsAt := pointsAt) (spatial := spatial) (parity := parity)
      (writtenParity := writtenParity)
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    simp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel,
      LocalizedReference.Input.molecule]
  have rigidGraph : ConstitutionallyRigidGraphAt input.certified.moleculeGraph center.1 :=
    constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified
      ⟨center.1, center.2⟩ rigid
  have separated : ConstitutionallySeparatedActualKeys input.certified
      (frame.compoundKeyAt input.certified target view derived) :=
    constitutionallySeparatedActualFrameKeys_of_actualFrame input.certified target view frame
      derived center centerReal rigidGraph acyclic singleBonded hcharge enough
  obtain ⟨tracked', trackedComputed', permutation', strict', _pseudo'⟩ :=
    input.certified.exists_trackedOrder_of_constitutionallySeparatedActualKeys target view frame
      derived (frame.compoundKeyAt input.certified target view derived)
      (fun index => frame.compoundKeyAt_built input.certified target view derived index) separated
  have trackedEq : tracked' = tracked := by
    rw [trackedComputed] at trackedComputed'
    exact (Option.some.inj trackedComputed').symm
  have permutationTracked : tracked.highestFirst.Perm (List.finRange 4) := by
    simpa [trackedEq] using permutation'
  have strictTracked : tracked.highestFirst.Pairwise (fun left right =>
      input.certified.compoundKeyRank
          (frame.compoundKeyAt input.certified target view derived) right <
        input.certified.compoundKeyRank
          (frame.compoundKeyAt input.certified target view derived) left) := by
    simpa [trackedEq] using strict'
  have orderEq : tracked.highestFirst = order :=
    trackedHighestFirst_eq_priorityOrder input.certified target view frame derived center
      centerReal rigidGraph acyclic singleBonded hcharge enough priority correspondence order
      independent tracked permutationTracked strictTracked
  have stateOrder : LocalizedUniversalReference.referenceState input target =
      some (.chiral (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven (order.map Fin.val)))) := by
    rw [← orderEq]
    exact state
  have rational : CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor (order.map pointsAt)
      (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven (order.map Fin.val))) :=
    rationalTetrahedralDescriptor_of_independentOrder pointsAt order independent.1 parity
      writtenParity
  constructor
  · intro someEq
    have rsEq : rs = RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven (order.map Fin.val)) := by
      have combined := someEq.symm.trans stateOrder
      simpa using combined
    rw [rsEq]
    exact rational
  · intro descriptor
    have rsEq : rs = RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven (order.map Fin.val)) :=
      rationalTetrahedralDescriptor_unique descriptor rational
    rw [rsEq]
    exact stateOrder

/-! ## Public kernel guards -/

assert_kernel_only TetraStereo.OneCenter.exists_frameSlotBranchTree
assert_kernel_only TetraStereo.OneCenter.frameSlotBranchTree
assert_kernel_only TetraStereo.OneCenter.frameSlotBranchTree_source
assert_kernel_only TetraStereo.OneCenter.frameSlotBranchTree_tableMatch
assert_kernel_only TetraStereo.OneCenter.frameSlotBranchTree_realizes
assert_kernel_only TetraStereo.OneCenter.frameSlotBranchTree_root
assert_kernel_only TetraStereo.OneCenter.frameSlotPhysicalOutcome
assert_kernel_only TetraStereo.OneCenter.frameSlotPhysicalOutcome_iff_constitutionalCompare
assert_kernel_only TetraStereo.OneCenter.frameSlotPhysicalOutcome_rank_lt_of_gt
assert_kernel_only TetraStereo.OneCenter.frameSlotPhysicalOutcome_gt_of_rank_lt
assert_kernel_only TetraStereo.OneCenter.frameSlotPhysicalOutcome_total_of_ne
assert_kernel_only TetraStereo.OneCenter.IndependentPhysicalHighestFirst
assert_kernel_only TetraStereo.OneCenter.exists_independentPhysicalHighestFirst
assert_kernel_only TetraStereo.OneCenter.eq_of_pairwise_rank_strict
assert_kernel_only TetraStereo.OneCenter.pairwise_rank_of_pairwise_physical
assert_kernel_only TetraStereo.OneCenter.trackedHighestFirst_eq_independent
assert_kernel_only TetraStereo.OneCenter.rationalTetrahedralDescriptor_unique
assert_kernel_only TetraStereo.OneCenter.rationalTetrahedralDescriptor_of_independentOrder
assert_kernel_only TetraStereo.OneCenter.referenceState_eq_chiral_iff_physicalDescriptor
assert_kernel_only TetraStereo.OneCenter.referenceState_eq_none_of_independentPhysicalTwin
assert_kernel_only TetraStereo.OneCenter.ConstitutionalPriorityCorrespondence
assert_kernel_only TetraStereo.OneCenter.IndependentHighestFirstFor
assert_kernel_only TetraStereo.OneCenter.priority_rank_lt_of_priority
assert_kernel_only TetraStereo.OneCenter.pairwise_rank_of_pairwise_priority
assert_kernel_only TetraStereo.OneCenter.trackedHighestFirst_eq_priorityOrder
assert_kernel_only TetraStereo.OneCenter.referenceState_eq_chiral_iff_priorityDescriptor

end TetraStereo.OneCenter
