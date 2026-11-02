import TetraStereo.OneCenter.LocalizedFirstSpherePhysicalPriority
import TetraStereo.OneCenter.LocalizedIndependentAuxiliaryRS
import TetraStereo.OneCenter.LocalizedActualOrderedEvaluatorAgreement
import TetraStereo.OneCenter.LocalizedActualOrderedEvaluatorPreservation
import TetraStereo.OneCenter.TrackedLocalizedLigandSortCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# First-sphere priority at an actual occurrence

If a list of frame slots is strictly descending by the atomic number of the actual cursor atom,
then it is an independent physical highest-first list.  The proof uses the production frame-slot
trees and the existing first-sphere physical priority theorem; it does not inspect auxiliary labels
or assume a global physical domain.
-/

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedUniversalReference

noncomputable section

variable (input : LocalizedUniversalReference.Input)
variable {fuel : Nat}

private theorem finRangeMapPermFour (e : Fin 4 ≃ Fin 4) :
    ((List.finRange 4).map e).Perm (List.finRange 4) := by
  have nd : ((List.finRange 4).map e).Nodup := (List.nodup_finRange 4).map e.injective
  apply List.perm_of_nodup_nodup_toFinset_eq nd (List.nodup_finRange 4)
  have h₁ : ((List.finRange 4).map e).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup nd]; simp)
  have h₂ : (List.finRange 4).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup (List.nodup_finRange 4)]; simp)
  rw [h₁, h₂]

private theorem mapMMapOption {α β γ : Type*} (f : β → Option γ) (g : α → β) :
    ∀ l : List α, (l.map g).mapM f = l.mapM (fun a => f (g a))
  | [] => rfl
  | a :: l => by simp [List.mapM_cons, mapMMapOption f g l]

private theorem orderingThen_of_ne {a b : Ordering} (h : a ≠ Ordering.eq) :
    a.then b = a := by
  cases a <;> simp_all [Ordering.then]

/-- First-sphere atomic-number dominance for the actual frame-slot trees. -/
theorem frameSlotPhysicalOutcome_gt_of_slotZ_gt
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame fuel)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    {left right : Fin 4}
    (hZ : input.certified.moleculeGraph.atomZ
      (cursorAtom singleBonded acyclic (frame.cursorAt right)) <
      input.certified.moleculeGraph.atomZ
        (cursorAtom singleBonded acyclic (frame.cursorAt left))) :
    frameSlotPhysicalOutcome input.certified target view frame derived singleBonded acyclic
      target.1.root left right Ordering.gt := by
  let leftTree := frameSlotBranchTree input.certified target view frame derived left
  let rightTree := frameSlotBranchTree input.certified target view frame derived right
  have leftObserved : leftTree.source.occurrence.1.node.current? =
      some (cursorAtom singleBonded acyclic (frame.cursorAt left)) := by
    rw [frameSlotBranchTree_source]
    exact cursorAtom_spec singleBonded acyclic (frame.cursorAt left)
  have rightObserved : rightTree.source.occurrence.1.node.current? =
      some (cursorAtom singleBonded acyclic (frame.cursorAt right)) := by
    rw [frameSlotBranchTree_source]
    exact cursorAtom_spec singleBonded acyclic (frame.cursorAt right)
  have leftAtom := nodeAtom_eq_of_observed singleBonded acyclic leftObserved
  have rightAtom := nodeAtom_eq_of_observed singleBonded acyclic rightObserved
  have leftAtRoot : physicalAtomicNumberAt singleBonded acyclic leftTree [] =
      input.certified.moleculeGraph.atomZ (cursorAtom singleBonded acyclic (frame.cursorAt left)) := by
    simp [physicalAtomicNumberAt, leftAtom]
  have rightAtRoot : physicalAtomicNumberAt singleBonded acyclic rightTree [] =
      input.certified.moleculeGraph.atomZ (cursorAtom singleBonded acyclic (frame.cursorAt right)) := by
    simp [physicalAtomicNumberAt, rightAtom]
  unfold frameSlotPhysicalOutcome
  change physicalRuleMajorOutcome singleBonded acyclic target.1.root leftTree rightTree
    Ordering.gt
  unfold physicalRuleMajorOutcome
  apply Or.inl
  refine ⟨[], ?_, fun earlier h => absurd h (not_hierarchyAddressBefore_nil earlier)⟩
  change DeclarativeCIP.DescendingNatOutcome
    (physicalAtomicNumberAt singleBonded acyclic leftTree [])
    (physicalAtomicNumberAt singleBonded acyclic rightTree []) Ordering.gt
  rw [leftAtRoot, rightAtRoot]
  exact DeclarativeCIP.DescendingNatOutcome.gt hZ

theorem frameSlotPhysicalOutcome_lt_of_slotZ_lt
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame fuel)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    {left right : Fin 4}
    (hZ : input.certified.moleculeGraph.atomZ
      (cursorAtom singleBonded acyclic (frame.cursorAt left)) <
      input.certified.moleculeGraph.atomZ
        (cursorAtom singleBonded acyclic (frame.cursorAt right))) :
    frameSlotPhysicalOutcome input.certified target view frame derived singleBonded acyclic
      target.1.root left right Ordering.lt := by
  let leftTree := frameSlotBranchTree input.certified target view frame derived left
  let rightTree := frameSlotBranchTree input.certified target view frame derived right
  have leftObserved : leftTree.source.occurrence.1.node.current? =
      some (cursorAtom singleBonded acyclic (frame.cursorAt left)) := by
    rw [frameSlotBranchTree_source]
    exact cursorAtom_spec singleBonded acyclic (frame.cursorAt left)
  have rightObserved : rightTree.source.occurrence.1.node.current? =
      some (cursorAtom singleBonded acyclic (frame.cursorAt right)) := by
    rw [frameSlotBranchTree_source]
    exact cursorAtom_spec singleBonded acyclic (frame.cursorAt right)
  have leftAtom := nodeAtom_eq_of_observed singleBonded acyclic leftObserved
  have rightAtom := nodeAtom_eq_of_observed singleBonded acyclic rightObserved
  have leftAtRoot : physicalAtomicNumberAt singleBonded acyclic leftTree [] =
      input.certified.moleculeGraph.atomZ (cursorAtom singleBonded acyclic (frame.cursorAt left)) := by
    simp [physicalAtomicNumberAt, leftAtom]
  have rightAtRoot : physicalAtomicNumberAt singleBonded acyclic rightTree [] =
      input.certified.moleculeGraph.atomZ (cursorAtom singleBonded acyclic (frame.cursorAt right)) := by
    simp [physicalAtomicNumberAt, rightAtom]
  unfold frameSlotPhysicalOutcome
  change physicalRuleMajorOutcome singleBonded acyclic target.1.root leftTree rightTree
    Ordering.lt
  unfold physicalRuleMajorOutcome
  apply Or.inl
  refine ⟨[], ?_, fun earlier h => absurd h (not_hierarchyAddressBefore_nil earlier)⟩
  change DeclarativeCIP.DescendingNatOutcome
    (physicalAtomicNumberAt singleBonded acyclic leftTree [])
    (physicalAtomicNumberAt singleBonded acyclic rightTree []) Ordering.lt
  rw [leftAtRoot, rightAtRoot]
  exact DeclarativeCIP.DescendingNatOutcome.lt hZ

/-- A Rule-1a-resolved physical frame pair is also resolved by the ordered through-Rule-5
comparator, with no pseudo flag. -/
theorem orderedComparison_eq_of_physicalOutcome
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame fuel)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    {left right : Fin 4} {ordering : Ordering}
    (physical : frameSlotPhysicalOutcome input.certified target view frame derived
      singleBonded acyclic target.1.root left right ordering)
    (nonTie : ordering ≠ Ordering.eq) :
    input.certified.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame left right =
      some (localizedOccurrenceRule45ComparisonRecord
        { ordering := ordering, pseudo := false }) := by
  have constitutional := (frameSlotPhysicalOutcome_iff_constitutionalCompare input.certified
    target view frame derived singleBonded acyclic left right ordering).mpr physical
  let leftKey := (frame.compoundKeyAt input.certified target view derived left)
  let rightKey := (frame.compoundKeyAt input.certified target view derived right)
  have rule4a : input.certified.compareLocalizedRerootCumulativeRule45Keys
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey = ordering := by
    unfold leftKey rightKey compareLocalizedRerootCumulativeRule45Keys compareLex Ordering.byKey
    rw [constitutional]
    exact orderingThen_of_ne nonTie
  have rule4aNe : input.certified.compareLocalizedRerootCumulativeRule45Keys
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey ≠ Ordering.eq := by
    rw [rule4a]
    exact nonTie
  have priorCmp : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      leftKey.prior rightKey.prior = ordering := by
    rw [input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
      leftKey.prior rightKey.prior rule4aNe, rule4a]
  have actualThrough : input.certified.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey =
      { ordering := ordering, pseudo := false } := by
    unfold compareLocalizedRerootCompoundThroughRule5
    simp [priorCmp, nonTie]
  have orderedThrough := input.certified.compareThroughRule5_outcomeOrdered45_of_rule4a_ne
    leftKey rightKey rule4aNe
  have builtLeft := frame.compoundKeyAt_built input.certified target view derived left
  have builtRight := frame.compoundKeyAt_built input.certified target view derived right
  rw [input.certified.compareLocalizedOccurrenceThroughRule5OrderedAt?_of_built
    target view frame builtLeft builtRight]
  rw [orderedThrough, actualThrough]

/-- Distinct first-sphere atom numbers fix the ordered comparison, uniformly over every view. -/
theorem orderedComparison_eq_strictRank_of_slotZ
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame fuel)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (slotZ : Fin 4 → Nat)
    (slotZ_eq : ∀ i, input.certified.moleculeGraph.atomZ
      (cursorAtom singleBonded acyclic (frame.cursorAt i)) = slotZ i)
    {left right : Fin 4} (different : slotZ left ≠ slotZ right) :
    input.certified.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame left right =
      strictRankComparison slotZ left right := by
  rcases lt_or_gt_of_ne different with hlt | hgt
  · have physical := frameSlotPhysicalOutcome_lt_of_slotZ_lt input target view frame derived
      singleBonded acyclic (left := left) (right := right) (by
        calc
          input.certified.moleculeGraph.atomZ (cursorAtom singleBonded acyclic (frame.cursorAt left))
              = slotZ left := slotZ_eq left
          _ < slotZ right := hlt
          _ = input.certified.moleculeGraph.atomZ
              (cursorAtom singleBonded acyclic (frame.cursorAt right)) := (slotZ_eq right).symm)
    have result := orderedComparison_eq_of_physicalOutcome input target view frame derived
      singleBonded acyclic physical (by decide : Ordering.lt ≠ Ordering.eq)
    simpa [strictRankComparison, compare_lt_iff_lt.mpr hlt] using result
  · have physical := frameSlotPhysicalOutcome_gt_of_slotZ_gt input target view frame derived
      singleBonded acyclic (left := left) (right := right) (by
        calc
          input.certified.moleculeGraph.atomZ (cursorAtom singleBonded acyclic (frame.cursorAt right))
              = slotZ right := slotZ_eq right
          _ < slotZ left := hgt
          _ = input.certified.moleculeGraph.atomZ
              (cursorAtom singleBonded acyclic (frame.cursorAt left)) := (slotZ_eq left).symm)
    have result := orderedComparison_eq_of_physicalOutcome input target view frame derived
      singleBonded acyclic physical (by decide : Ordering.gt ≠ Ordering.eq)
    simpa [strictRankComparison, compare_gt_iff_gt.mpr hgt] using result

/-- A first-sphere atomic-number order on the actual four frame slots is an independent physical
highest-first order.  `slotZ` is the atomic number of the source atom at each cursor; callers can
obtain it from canonical ligand observations and a frame permutation. -/
theorem independentPhysicalHighestFirst_of_slotZ_order
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame fuel)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (enough : input.certified.certified.input.molecule.atomCount ≤ fuel)
    (slotZ : Fin 4 → Nat)
    (slotZ_eq : ∀ i, input.certified.moleculeGraph.atomZ
      (cursorAtom singleBonded acyclic (frame.cursorAt i)) = slotZ i)
    (order : List (Fin 4))
    (permutation : order.Perm (List.finRange 4))
    (descending : order.Pairwise (fun left right => slotZ right < slotZ left)) :
    IndependentPhysicalHighestFirst input.certified target view frame derived
      singleBonded acyclic order := by
  have physical : ∀ order : List (Fin 4),
      order.Pairwise (fun left right => slotZ right < slotZ left) →
      order.Pairwise (fun left right =>
        frameSlotPhysicalOutcome input.certified target view frame derived singleBonded acyclic
          target.1.root left right Ordering.gt) := by
    intro order horder
    induction order with
    | nil => exact List.Pairwise.nil
    | cons head tail ih =>
      have hcons := List.pairwise_cons.mp horder
      apply List.Pairwise.cons
      · intro right rightMem
        have hZ : input.certified.moleculeGraph.atomZ
            (cursorAtom singleBonded acyclic (frame.cursorAt right)) <
          input.certified.moleculeGraph.atomZ
            (cursorAtom singleBonded acyclic (frame.cursorAt head)) := by
          rw [slotZ_eq right, slotZ_eq head]
          exact hcons.1 right rightMem
        let leftCursor := frame.cursorAt head
        let rightCursor := frame.cursorAt right
        have leftRoot : leftCursor.occurrence.1.root = target.1.root := by
          change (frame.cursorAt head).occurrence.1.root = target.1.root
          exact localizedRerootChildren_root_eq input.certified
            { occurrence := target, previous? := none } (frame.cursorAt head) frame.cursors
            derived.1 (by
              unfold LocalizedOccurrenceFourLigandFrame.cursorAt
              exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm head))
        have rightRoot : rightCursor.occurrence.1.root = target.1.root := by
          change (frame.cursorAt right).occurrence.1.root = target.1.root
          exact localizedRerootChildren_root_eq input.certified
            { occurrence := target, previous? := none } (frame.cursorAt right) frame.cursors
            derived.1 (by
              unfold LocalizedOccurrenceFourLigandFrame.cursorAt
              exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm right))
        obtain ⟨leftKey, rightKey, leftBuilt, rightBuilt, compareIff⟩ :=
          exists_physicalTreeCanonicalOutcome_iff_actualComparison enough
            singleBonded acyclic .rule4a target view target.1.root leftCursor rightCursor
            (frame.cursorAt_valid input.certified target derived head)
            (frame.cursorAt_valid input.certified target derived right) leftRoot rightRoot
        let cmp := OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional
        have canonicalAtCmp : PhysicalTreeCanonicalOutcome input.certified.moleculeGraph
            target.1.root
            (leftCursor.previous?.bind fun p => p.1.node.current?)
            (rightCursor.previous?.bind fun p => p.1.node.current?)
            (cursorAtom singleBonded acyclic leftCursor)
            (cursorAtom singleBonded acyclic rightCursor) cmp :=
          (compareIff cmp).mp rfl
        have canonical : PhysicalTreeCanonicalOutcome input.certified.moleculeGraph
            target.1.root
            (leftCursor.previous?.bind fun p => p.1.node.current?)
            (rightCursor.previous?.bind fun p => p.1.node.current?)
            (cursorAtom singleBonded acyclic leftCursor)
            (cursorAtom singleBonded acyclic rightCursor) Ordering.gt :=
          physicalTreeCanonicalOutcome_gt_of_atomZ_gt input.certified.moleculeGraph
            target.1.root canonicalAtCmp hZ
        have compare : OfficialRuleMajorKey.compare leftKey.constitutional
            rightKey.constitutional = Ordering.gt :=
          (physicalTreeCanonicalOutcome_eq_gt_of_atomZ_gt input.certified.moleculeGraph
            target.1.root canonicalAtCmp hZ)
        have leftKeyEq : leftKey =
            (frame.compoundKeyAt input.certified target view derived head).prior.rule4aKey := by
          have builtFrame := buildLocalizedRerootCompoundRule45Key?_rule4a_of_frame
            input.certified target view frame derived head
          rw [show localizedOccurrenceRerootEvaluationFuel fuel = 2 * (fuel + 1) by rfl] at builtFrame
          rw [leftBuilt] at builtFrame
          exact Option.some.inj builtFrame
        have rightKeyEq : rightKey =
            (frame.compoundKeyAt input.certified target view derived right).prior.rule4aKey := by
          have builtFrame := buildLocalizedRerootCompoundRule45Key?_rule4a_of_frame
            input.certified target view frame derived right
          rw [show localizedOccurrenceRerootEvaluationFuel fuel = 2 * (fuel + 1) by rfl] at builtFrame
          rw [rightBuilt] at builtFrame
          exact Option.some.inj builtFrame
        have compareFrame : OfficialRuleMajorKey.compare
            ((frame.compoundKeyAt input.certified target view derived head).prior.rule4aKey).constitutional
            ((frame.compoundKeyAt input.certified target view derived right).prior.rule4aKey).constitutional =
              Ordering.gt := by
          simpa [leftKeyEq, rightKeyEq] using compare
        have actual := (frameSlotPhysicalOutcome_iff_constitutionalCompare input.certified
          target view frame derived singleBonded acyclic head right Ordering.gt).mp compareFrame
        exact actual
      · exact ih hcons.2
  exact ⟨permutation, physical order descending⟩

/-- The ordered fixed point assigns the descriptor of a strictly priority-ranked coordinate list
when the actual ordered comparison callback agrees with that injective numeric priority. The
target and frame are arbitrary; no global physical domain or reference-state view equality is
required. `spatialCorrespondence` ties actual frame-slot reads to the canonical ligand enumeration.
-/
theorem orderedReferenceState_eq_chiral_of_strictPriorityCallback
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame fuel)
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target = some frame)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (slotEquiv : Fin 4 ≃ Fin 4)
    (priority : Fin 4 → Nat)
    (priorityInjective : Function.Injective priority)
    (priorityOrder : ∀ ℓ m, ℓ ≠ m →
      input.certified.compareLocalizedOccurrenceThroughRule5OrderedAt? target
        (input.certified.localizedDependencyView
          (input.certified.orderedReferenceState fuel) target)
        frame (slotEquiv.symm ℓ) (slotEquiv.symm m) =
          strictRankComparison (fun i => priority (slotEquiv i))
            (slotEquiv.symm ℓ) (slotEquiv.symm m))
    (order : List (Fin 4))
    (permutation : order.Perm (List.finRange 4))
    (sorted : order.Pairwise fun a b => priority b < priority a)
    (points : List CartesianPoint3)
    (spatialCorrespondence : ∀ index,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
        input.certified.spatialPointAt?
          (input.certified.canonicalLigandAtom center (slotEquiv index)))
    (canonicalPoints : order.mapM (fun ℓ => input.certified.spatialPointAt?
      (input.certified.canonicalLigandAtom center ℓ)) = some points)
    (raw : RS)
    (geometry : descriptorOfPriorityOrderedPoints? points = some raw) :
    input.certified.orderedReferenceState fuel target = some (.chiral raw) := by
  let view := input.certified.localizedDependencyView
    (input.certified.orderedReferenceState fuel) target
  let q : Fin 4 → Nat := fun i => priority (slotEquiv i)
  have qinj : Function.Injective q := priorityInjective.comp slotEquiv.injective
  have compared : ∀ i j, i ≠ j →
      input.certified.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame i j =
        strictRankComparison q i j := by
    intro i j hij
    have hℓm : slotEquiv.symm i ≠ slotEquiv.symm j :=
      fun h => hij (slotEquiv.symm.injective h)
    simpa [view, q] using priorityOrder (slotEquiv i) (slotEquiv j)
      (fun h => hij (slotEquiv.injective h))
  obtain ⟨tracked, hsort, hperm, hdesc, hzero⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne q qinj _ compared
  have hsafe : input.certified.safeLocalizedOccurrenceRule45TrackedOrderOrdered? target view
      frame = some tracked := by
    unfold safeLocalizedOccurrenceRule45TrackedOrderOrdered? safeTrackedOrderOf
    rw [hsort]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [if_pos]
    rw [orderCoherentOf_eq_true_iff]
    refine hdesc.imp ?_
    intro i j hij
    have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    refine ⟨_, compared i j hne, ?_⟩
    show compare (q i) (q j) = .gt
    exact compare_gt_iff_gt.2 hij
  have hcenter : input.certified.localizedOccurrenceDescriptorCenter? target = some center :=
    (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).2 centerReal
  have hmapEq : tracked.highestFirst.map slotEquiv = order := by
    haveI : Std.Antisymm fun a b : Fin 4 => priority b < priority a :=
      ⟨fun a b hab hba => absurd (hab.trans hba) (lt_irrefl _)⟩
    exact List.Perm.eq_of_pairwise' (List.pairwise_map.2 hdesc) sorted
      ((hperm.map slotEquiv).trans ((finRangeMapPermFour slotEquiv).trans permutation.symm))
  have hpoints' : tracked.highestFirst.mapM (fun index =>
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index)) = some points := by
    rw [← hmapEq, mapMMapOption] at canonicalPoints
    rw [← canonicalPoints]
    congr 1
    funext index
    exact spatialCorrespondence index
  rw [← input.certified.orderedReferenceState_fixed fuel target]
  unfold localizedOccurrenceRule45DescriptorOrdered? localizedOccurrenceRule45SpatialEvidenceOrdered?
  rw [hcenter]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [frameComputed]
  simp only [Option.bind_some]
  rw [hsafe]
  simp only [Option.bind_some]
  rw [hpoints']
  simp only [Option.bind_some, geometry, hzero]
  simp [classifyTetrahedralRSPseudo]

end
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.independentPhysicalHighestFirst_of_slotZ_order
assert_kernel_only TetraStereo.OneCenter.frameSlotPhysicalOutcome_gt_of_slotZ_gt
assert_kernel_only TetraStereo.OneCenter.orderedReferenceState_eq_chiral_of_strictPriorityCallback
