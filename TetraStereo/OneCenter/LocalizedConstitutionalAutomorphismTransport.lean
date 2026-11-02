import TetraStereo.OneCenter.LocalizedAcyclicAutomorphismCursorTransport
import TetraStereo.OneCenter.LocalizedCumulativeCursorTransport
import TetraStereo.OneCenter.LocalizedCumulativeConstitutionalCoherence
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness

set_option autoImplicit false

















































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## The empty dependency view reads nothing -/

/-- **The empty view reads `none`.**  A dependency view that answers `none` at every strict
dependency makes the actual production dependency label `none` at every cursor.  This is the only
label-side fact used below, and it mentions no auxiliary state. -/
theorem localizedDependencyLabel_eq_none_of_view_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (viewNone : ∀ source dependency, view source dependency = none)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.localizedDependencyLabel target view cursor = none := by
  dsimp only [CertifiedLocalizedCIPInput.localizedDependencyLabel]
  by_cases dependency : input.LocalizedDepthDependency cursor.occurrence target
  · rw [dif_pos dependency]
    exact viewNone _ _
  · rw [dif_neg dependency]






/-- Official atom-label clause at an actual automorphism-correspondence pair. -/
theorem localizedAutCorrespondence_atomLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    {x y : input.LocalizedRerootCursor carrierFuel}
    (correspondence : LocalizedAutCursorCorrespondence input e root x y) :
    input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node := by
  obtain ⟨a, xCurrent⟩ := input.occurrence_current_exists x.occurrence
  obtain ⟨b, yCurrent⟩ := input.occurrence_current_exists y.occurrence
  exact input.officialNodeAtomLabel_eq_of_correspondence singleBonded acyclic
    correspondence xCurrent yCurrent

/-- Stored Rule-1b root-distance clause at an actual automorphism-correspondence pair.  The
original root is fixed by the automorphism; no depth preservation is assumed. -/
theorem localizedAutCorrespondence_rootDistance
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    (rootFixed : (e : Equiv.Perm input.Atom) root = root)
    {x y : input.LocalizedRerootCursor carrierFuel}
    (correspondence : LocalizedAutCursorCorrespondence input e root x y) :
    x.occurrence.1.node.rule1bRootDistance =
      y.occurrence.1.node.rule1bRootDistance := by
  obtain ⟨a, xCurrent⟩ := input.occurrence_current_exists x.occurrence
  obtain ⟨b, yCurrent⟩ := input.occurrence_current_exists y.occurrence
  exact input.rule1bRootDistance_eq_of_correspondence singleBonded acyclic rootFixed
    correspondence xCurrent yCurrent






theorem exists_leftPermuted_relatedChildren_of_correspondence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    {x y : input.LocalizedRerootCursor carrierFuel}
    (correspondence : LocalizedAutCursorCorrespondence input e root x y) :
    ∃ relatedChildren,
      (input.executableLocalizedRerootChildren x).Perm relatedChildren ∧
        List.Forall₂ (LocalizedAutCursorCorrespondence input e root)
          relatedChildren (input.executableLocalizedRerootChildren y) := by
  classical
  obtain ⟨image, imagePerm, forall₂⟩ :=
    input.exists_permuted_children_forall₂_of_correspondence singleBonded acyclic enough
      correspondence
      (input.localizedRerootChildren?_eq_some_executable x)
      (input.localizedRerootChildren?_eq_some_executable y)
  have composed : Relation.Comp
      (List.Forall₂ (LocalizedAutCursorCorrespondence input e root)) List.Perm
      (input.executableLocalizedRerootChildren x)
      (input.executableLocalizedRerootChildren y) :=
    ⟨image, forall₂, imagePerm⟩
  have reoriented : Relation.Comp List.Perm
      (List.Forall₂ (LocalizedAutCursorCorrespondence input e root))
      (input.executableLocalizedRerootChildren x)
      (input.executableLocalizedRerootChildren y) := by
    rw [← List.forall₂_comp_perm_eq_perm_comp_forall₂]
    exact composed
  exact reoriented

/-! ## Covariance of the dummy `none`-reader cumulative builds -/









theorem buildLocalizedRerootCumulativeRule45Key?_noneObservable_eq_of_correspondence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    (rootFixed : (e : Equiv.Perm input.Atom) root = root)
    (targetL targetR : input.LocalizedCIPOccurrence carrierFuel) :
    ∀ (fuel : Nat) (x y : input.LocalizedRerootCursor carrierFuel),
      LocalizedAutCursorCorrespondence input e root x y →
      (input.buildLocalizedRerootCumulativeRule45Key? .rule4a targetL
          (fun _ _ => (none : Option LocalizedAuxiliaryLabel)) fuel x).map
          (input.localizedRerootCumulativeRule45Observable) =
        (input.buildLocalizedRerootCumulativeRule45Key? .rule4a targetR
          (fun _ _ => (none : Option LocalizedAuxiliaryLabel)) fuel y).map
          (input.localizedRerootCumulativeRule45Observable) :=
  input.buildLocalizedRerootCumulativeRule45Key?_map_observable_eq_of_related
    .rule4a .rule4a
    targetL (fun _ _ => (none : Option LocalizedAuxiliaryLabel))
    targetR (fun _ _ => (none : Option LocalizedAuxiliaryLabel))
    (LocalizedAutCursorCorrespondence input e root)
    (fun x y related =>
      input.localizedAutCorrespondence_atomLabel singleBonded acyclic related)
    (fun x y related =>
      input.localizedAutCorrespondence_rootDistance singleBonded acyclic rootFixed related)
    (fun x y related =>
      input.exists_leftPermuted_relatedChildren_of_correspondence
        singleBonded acyclic enough related)
    (fun x y _related => by
      rw [input.localizedDependencyLabel_eq_none_of_view_eq_none targetL
            (fun _ _ => (none : Option LocalizedAuxiliaryLabel)) (fun _ _ => rfl) x,
        input.localizedDependencyLabel_eq_none_of_view_eq_none targetR
            (fun _ _ => (none : Option LocalizedAuxiliaryLabel)) (fun _ _ => rfl) y])

/-! ## The production endpoint -/











theorem constitutional_observable_eq_of_automorphism_correspondence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    (rootFixed : (e : Equiv.Perm input.Atom) root = root)
    {x y : input.LocalizedRerootCursor carrierFuel}
    (correspondence : LocalizedAutCursorCorrespondence input e root x y)
    (xValid : input.LocalizedRerootCursorValid x)
    (yValid : input.LocalizedRerootCursorValid y)
    (stageL : LocalizedCumulativeRule45Stage)
    (targetL : input.LocalizedCIPOccurrence carrierFuel)
    (viewL : input.LocalizedDependencyView targetL)
    (stageR : LocalizedCumulativeRule45Stage)
    (targetR : input.LocalizedCIPOccurrence carrierFuel)
    (viewR : input.LocalizedDependencyView targetR) :
    ∃ leftKey rightKey : input.LocalizedRerootCumulativeRule45Key,
      input.buildLocalizedRerootCumulativeRule45Key? stageL targetL viewL
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) x = some leftKey ∧
        input.buildLocalizedRerootCumulativeRule45Key? stageR targetR viewR
            (localizedOccurrenceRerootEvaluationFuel carrierFuel) y = some rightKey ∧
          constitutionalObservable leftKey.constitutional =
            constitutionalObservable rightKey.constitutional := by
  classical
  -- The two dummy builds are total, because the evaluation fuel is the proved reroot bound.
  have noneLeftTotal : ∃ key, input.buildLocalizedRerootCumulativeRule45Key? .rule4a targetL
      (fun _ _ => (none : Option LocalizedAuxiliaryLabel))
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) x = some key := by
    simpa only [localizedOccurrenceRerootEvaluationFuel] using
      input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice .rule4a targetL
        (fun _ _ => (none : Option LocalizedAuxiliaryLabel)) x xValid
  have noneRightTotal : ∃ key, input.buildLocalizedRerootCumulativeRule45Key? .rule4a targetR
      (fun _ _ => (none : Option LocalizedAuxiliaryLabel))
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) y = some key := by
    simpa only [localizedOccurrenceRerootEvaluationFuel] using
      input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice .rule4a targetR
        (fun _ _ => (none : Option LocalizedAuxiliaryLabel)) y yValid
  obtain ⟨noneLeftKey, noneLeftComputed⟩ := noneLeftTotal
  obtain ⟨noneRightKey, noneRightComputed⟩ := noneRightTotal
  -- The two actual builds are total for the same reason.
  have leftTotal : ∃ key, input.buildLocalizedRerootCumulativeRule45Key? stageL targetL viewL
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) x = some key := by
    simpa only [localizedOccurrenceRerootEvaluationFuel] using
      input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice stageL targetL viewL
        x xValid
  have rightTotal : ∃ key, input.buildLocalizedRerootCumulativeRule45Key? stageR targetR viewR
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) y = some key := by
    simpa only [localizedOccurrenceRerootEvaluationFuel] using
      input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice stageR targetR viewR
        y yValid
  obtain ⟨leftKey, leftComputed⟩ := leftTotal
  obtain ⟨rightKey, rightComputed⟩ := rightTotal
  refine ⟨leftKey, rightKey, leftComputed, rightComputed, ?_⟩
  -- Observable covariance of the two dummy builds.
  have transported :=
    input.buildLocalizedRerootCumulativeRule45Key?_noneObservable_eq_of_correspondence
      singleBonded acyclic enough rootFixed targetL targetR
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) x y correspondence
  rw [noneLeftComputed, noneRightComputed] at transported
  have noneObservable :
      input.localizedRerootCumulativeRule45Observable noneLeftKey =
        input.localizedRerootCumulativeRule45Observable noneRightKey := by
    simpa using transported
  have noneConstitutional :
      constitutionalObservable noneLeftKey.constitutional =
        constitutionalObservable noneRightKey.constitutional :=
    congrArg
      (fun observed : LocalizedCumulativeRule45Observable =>
        ({ rule1a := observed.rule1a
           rule1b := observed.rule1b
           rule2 := observed.rule2 } : LocalizedConstitutionalObservable))
      noneObservable
  -- Same-cursor coherence on each side identifies the arbitrary build with the dummy one.
  have leftCoherence :
      constitutionalObservable leftKey.constitutional =
        constitutionalObservable noneLeftKey.constitutional :=
    input.cumulative_builds_constitutional_observable_equal x leftComputed noneLeftComputed
  have rightCoherence :
      constitutionalObservable noneRightKey.constitutional =
        constitutionalObservable rightKey.constitutional :=
    input.cumulative_builds_constitutional_observable_equal y noneRightComputed rightComputed
  exact leftCoherence.trans (noneConstitutional.trans rightCoherence)

/-- **Constitutional covariance for arbitrary successful builds.**  The production endpoint with
its derived success replaced by explicit success hypotheses at arbitrary, possibly different,
recursion budgets.  This is the integration form for callers that already hold successful builds;
the constitutional verdict still depends only on the cursor correspondence. -/
theorem constitutional_observable_eq_of_builds_of_correspondence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    (rootFixed : (e : Equiv.Perm input.Atom) root = root)
    {x y : input.LocalizedRerootCursor carrierFuel}
    (correspondence : LocalizedAutCursorCorrespondence input e root x y)
    (xValid : input.LocalizedRerootCursorValid x)
    (yValid : input.LocalizedRerootCursorValid y)
    {leftFuel rightFuel : Nat}
    {stageL : LocalizedCumulativeRule45Stage}
    {targetL : input.LocalizedCIPOccurrence carrierFuel}
    {viewL : input.LocalizedDependencyView targetL}
    {stageR : LocalizedCumulativeRule45Stage}
    {targetR : input.LocalizedCIPOccurrence carrierFuel}
    {viewR : input.LocalizedDependencyView targetR}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftComputed : input.buildLocalizedRerootCumulativeRule45Key?
      stageL targetL viewL leftFuel x = some leftKey)
    (rightComputed : input.buildLocalizedRerootCumulativeRule45Key?
      stageR targetR viewR rightFuel y = some rightKey) :
    constitutionalObservable leftKey.constitutional =
      constitutionalObservable rightKey.constitutional := by
  obtain ⟨productionLeft, productionRight, productionLeftComputed,
    productionRightComputed, transported⟩ :=
    input.constitutional_observable_eq_of_automorphism_correspondence
      singleBonded acyclic enough rootFixed correspondence xValid yValid
      stageL targetL viewL stageR targetR viewR
  have leftCoherence :
      constitutionalObservable leftKey.constitutional =
        constitutionalObservable productionLeft.constitutional :=
    input.cumulative_builds_constitutional_observable_equal x leftComputed
      productionLeftComputed
  have rightCoherence :
      constitutionalObservable productionRight.constitutional =
        constitutionalObservable rightKey.constitutional :=
    input.cumulative_builds_constitutional_observable_equal y
      productionRightComputed rightComputed
  exact leftCoherence.trans (transported.trans rightCoherence)

/-! ## Comparison congruence across a pair of corresponding ligands -/

/-- **Pairwise comparison congruence.**  Two pairs of actual cursors, each pair related by the same
root-fixing physical automorphism correspondence, produce production cumulative keys whose
`OfficialRuleMajorKey.compare` verdict is the same on both sides.  The four descriptor stages,
targets and views are independent, so this is a statement about the constitutional priority order
of corresponding ligands alone, and it needs no auxiliary label covariance. -/
theorem compare_eq_of_automorphism_correspondence_pair
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    (rootFixed : (e : Equiv.Perm input.Atom) root = root)
    {firstLeft firstRight secondLeft secondRight :
      input.LocalizedRerootCursor carrierFuel}
    (firstCorrespondence :
      LocalizedAutCursorCorrespondence input e root firstLeft firstRight)
    (secondCorrespondence :
      LocalizedAutCursorCorrespondence input e root secondLeft secondRight)
    (firstLeftValid : input.LocalizedRerootCursorValid firstLeft)
    (firstRightValid : input.LocalizedRerootCursorValid firstRight)
    (secondLeftValid : input.LocalizedRerootCursorValid secondLeft)
    (secondRightValid : input.LocalizedRerootCursorValid secondRight)
    (firstLeftStage : LocalizedCumulativeRule45Stage)
    (firstLeftTarget : input.LocalizedCIPOccurrence carrierFuel)
    (firstLeftView : input.LocalizedDependencyView firstLeftTarget)
    (firstRightStage : LocalizedCumulativeRule45Stage)
    (firstRightTarget : input.LocalizedCIPOccurrence carrierFuel)
    (firstRightView : input.LocalizedDependencyView firstRightTarget)
    (secondLeftStage : LocalizedCumulativeRule45Stage)
    (secondLeftTarget : input.LocalizedCIPOccurrence carrierFuel)
    (secondLeftView : input.LocalizedDependencyView secondLeftTarget)
    (secondRightStage : LocalizedCumulativeRule45Stage)
    (secondRightTarget : input.LocalizedCIPOccurrence carrierFuel)
    (secondRightView : input.LocalizedDependencyView secondRightTarget) :
    ∃ firstLeftKey secondLeftKey firstRightKey secondRightKey :
        input.LocalizedRerootCumulativeRule45Key,
      input.buildLocalizedRerootCumulativeRule45Key?
          firstLeftStage firstLeftTarget firstLeftView
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) firstLeft = some firstLeftKey ∧
        input.buildLocalizedRerootCumulativeRule45Key?
            secondLeftStage secondLeftTarget secondLeftView
            (localizedOccurrenceRerootEvaluationFuel carrierFuel) secondLeft =
          some secondLeftKey ∧
          input.buildLocalizedRerootCumulativeRule45Key?
              firstRightStage firstRightTarget firstRightView
              (localizedOccurrenceRerootEvaluationFuel carrierFuel) firstRight =
            some firstRightKey ∧
            input.buildLocalizedRerootCumulativeRule45Key?
                secondRightStage secondRightTarget secondRightView
                (localizedOccurrenceRerootEvaluationFuel carrierFuel) secondRight =
              some secondRightKey ∧
              OfficialRuleMajorKey.compare
                  firstLeftKey.constitutional secondLeftKey.constitutional =
                OfficialRuleMajorKey.compare
                  firstRightKey.constitutional secondRightKey.constitutional := by
  obtain ⟨firstLeftKey, firstRightKey, firstLeftComputed, firstRightComputed,
    firstTransported⟩ :=
    input.constitutional_observable_eq_of_automorphism_correspondence
      singleBonded acyclic enough rootFixed firstCorrespondence firstLeftValid firstRightValid
      firstLeftStage firstLeftTarget firstLeftView
      firstRightStage firstRightTarget firstRightView
  obtain ⟨secondLeftKey, secondRightKey, secondLeftComputed, secondRightComputed,
    secondTransported⟩ :=
    input.constitutional_observable_eq_of_automorphism_correspondence
      singleBonded acyclic enough rootFixed secondCorrespondence secondLeftValid secondRightValid
      secondLeftStage secondLeftTarget secondLeftView
      secondRightStage secondRightTarget secondRightView
  exact ⟨firstLeftKey, secondLeftKey, firstRightKey, secondRightKey,
    firstLeftComputed, secondLeftComputed, firstRightComputed, secondRightComputed,
    ruleMajor_compare_congr firstLeftKey.constitutional secondLeftKey.constitutional
      firstRightKey.constitutional secondRightKey.constitutional
      firstTransported secondTransported⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

Every exported declaration is closed by kernel reduction alone; the guards below reject project
axioms, `sorryAx` and native/compiler trust. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDependencyLabel_eq_none_of_view_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedAutCorrespondence_atomLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedAutCorrespondence_rootDistance
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_leftPermuted_relatedChildren_of_correspondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_noneObservable_eq_of_correspondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.constitutional_observable_eq_of_automorphism_correspondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.constitutional_observable_eq_of_builds_of_correspondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compare_eq_of_automorphism_correspondence_pair
