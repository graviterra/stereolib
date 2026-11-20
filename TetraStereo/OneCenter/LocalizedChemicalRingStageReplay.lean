import TetraStereo.OneCenter.LocalizedChemicalRingStageShape
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Current rule-major rebuilding along decoded occurrence correspondences

The recurrence is the actual compiler, including its rule-major sort. Related child frames
may be permuted and source atoms may differ. Only comparison-visible root observations are
preserved. This generic theorem is instantiated below with the correspondence decoded from
fully tied comparison keys; it does not require acyclic molecular graphs.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingStageReplay

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree
open LocalizedChemicalRingDecodedRelation LocalizedChemicalRingStageObservable LocalizedChemicalRingStageShape

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

private theorem terminal_eq (stage : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (x y : input.LocalizedRerootCursor carrierFuel)
    (atom : input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node)
    (distance : x.occurrence.1.node.rule1bRootDistance = y.occurrence.1.node.rule1bRootDistance)
    (priority : localizedCumulativeRule45Priority stage (readL x) =
      localizedCumulativeRule45Priority stage (readR y)) :
    input.localizedRerootCumulativeRule45Observable
        (localizedCumulativeRule45TerminalKey input stage x (readL x)) =
      input.localizedRerootCumulativeRule45Observable
        (localizedCumulativeRule45TerminalKey input stage y (readR y)) := by
  simp only [localizedRerootCumulativeRule45Observable,
    MoleculeGraph.officialRuleMajorRootKey, atom, distance, priority]

private theorem terminal_iff {α : Type*} {R : α → α → Prop} {left middle right : List α}
    (perm : left.Perm middle) (related : List.Forall₂ R middle right) : left = [] ↔ right = [] := by
  have length := perm.length_eq.trans related.length_eq
  constructor
  · intro h
    apply List.length_eq_zero_iff.mp
    rw [← length, h]
    rfl
  · intro h
    apply List.length_eq_zero_iff.mp
    rw [length, h]
    rfl

private theorem mapM_shaped (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) (fuel : Nat)
    {cursors : List (input.LocalizedRerootCursor carrierFuel)}
    {keys : List input.LocalizedRerootCumulativeRule45Key}
    (built : cursors.mapM (input.buildRuleMajorCumulativeWithRead? stage read fuel) = some keys) :
    ∀ key ∈ keys, Shaped (ruleMajorStageWidth stage) key.descriptor := by
  have paired := (mapM_eq_some_iff_forall₂ _ _ _).mp built
  clear built
  induction paired with
  | nil => simp
  | cons head tail ih =>
      intro key member
      rcases List.mem_cons.mp member with rfl | member
      · exact build_shaped input stage read fuel _ _ head
      · exact ih key member

/-- Successful current-stage builds at related occurrences have exactly equal comparison-visible
tables. Sorting and the fixed vector width are derived from the actual builds. -/
theorem replay_of_related
    (stage : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (R : input.LocalizedRerootCursor carrierFuel → input.LocalizedRerootCursor carrierFuel → Prop)
    (atom : ∀ x y, R x y → input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node)
    (distance : ∀ x y, R x y → x.occurrence.1.node.rule1bRootDistance =
      y.occurrence.1.node.rule1bRootDistance)
    (children : ∀ x y, R x y → ∃ frame,
      (input.executableLocalizedRerootChildren x).Perm frame ∧
        List.Forall₂ R frame (input.executableLocalizedRerootChildren y))
    (priority : ∀ x y, R x y → localizedCumulativeRule45Priority stage (readL x) =
      localizedCumulativeRule45Priority stage (readR y)) :
    ∀ fuel x y, R x y → ∀ keyL keyR,
      input.buildRuleMajorCumulativeWithRead? stage readL fuel x = some keyL →
      input.buildRuleMajorCumulativeWithRead? stage readR fuel y = some keyR →
      input.localizedRerootCumulativeRule45Observable keyL =
        input.localizedRerootCumulativeRule45Observable keyR := by
  intro fuel
  induction fuel with
  | zero =>
      intro x y related keyL keyR builtL builtR
      unfold buildRuleMajorCumulativeWithRead? at builtL builtR
      rw [input.localizedRerootChildren?_eq_some_executable] at builtL builtR
      obtain ⟨frame, perm, aligned⟩ := children x y related
      by_cases empty : input.executableLocalizedRerootChildren x = []
      · have emptyR := (terminal_iff perm aligned).mp empty
        simp only [Option.bind_eq_bind, Option.bind_some, empty, emptyR, if_true,
          Option.some.injEq] at builtL builtR
        rw [← builtL, ← builtR]
        exact terminal_eq stage readL readR x y (atom x y related) (distance x y related)
          (priority x y related)
      · simp [empty] at builtL
  | succ fuel ih =>
      intro x y related keyL keyR builtL builtR
      unfold buildRuleMajorCumulativeWithRead? at builtL builtR
      rw [input.localizedRerootChildren?_eq_some_executable] at builtL builtR
      obtain ⟨frame, perm, aligned⟩ := children x y related
      by_cases empty : input.executableLocalizedRerootChildren x = []
      · have emptyR := (terminal_iff perm aligned).mp empty
        simp only [Option.bind_eq_bind, Option.bind_some, empty, emptyR, if_true,
          Option.some.injEq] at builtL builtR
        rw [← builtL, ← builtR]
        exact terminal_eq stage readL readR x y (atom x y related) (distance x y related)
          (priority x y related)
      · have nonemptyR : input.executableLocalizedRerootChildren y ≠ [] :=
          fun h => empty ((terminal_iff perm aligned).mpr h)
        simp only [Option.bind_eq_bind, Option.bind_some, if_neg empty, if_neg nonemptyR] at builtL builtR
        obtain ⟨leftKeys, leftBuilt, leftEq⟩ := Option.bind_eq_some_iff.mp builtL
        obtain ⟨rightKeys, rightBuilt, rightEq⟩ := Option.bind_eq_some_iff.mp builtR
        have leftEq' := Option.some.inj leftEq
        have rightEq' := Option.some.inj rightEq
        obtain ⟨relatedKeys, relatedBuilt, keysPerm⟩ := exists_mapM_some_of_perm _ perm leftBuilt
        have keyRelations := forall₂_of_mapM_some
          (fun a b h ka kb ha hb => ih a b h ka kb ha hb) aligned relatedBuilt rightBuilt
        have equal : relatedKeys.map input.localizedRerootCumulativeRule45Observable =
            rightKeys.map input.localizedRerootCumulativeRule45Observable := by
          clear rightBuilt rightEq rightEq' relatedBuilt keysPerm
          induction keyRelations with
          | nil => rfl
          | cons h _ ih => simp only [List.map_cons, h, ih]
        have sorted := sorted_observables_eq (ruleMajorStageWidth stage) (stageWidth_positive stage)
          leftKeys rightKeys (mapM_shaped stage readL fuel leftBuilt) (mapM_shaped stage readR fuel rightBuilt)
          ((keysPerm.map input.localizedRerootCumulativeRule45Observable).trans (List.Perm.of_eq equal))
        rw [← leftEq', ← rightEq']
        apply input.localizedRerootCumulativeRule45Observable_assemble_eq
        · simp only [MoleculeGraph.officialRuleMajorRootKey, atom x y related]
        · simp only [MoleculeGraph.officialRuleMajorRootKey, distance x y related]
        · simp only [MoleculeGraph.officialRuleMajorRootKey, atom x y related]
        · rw [priority x y related]
        · exact sorted

/-- The relation needed by replay, including reader agreement, is derived from decoded decorated
observations. Ring duplicates are included. The shared stage can be chosen arbitrarily. -/
theorem replay_of_observations
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    (same : observation left = observation right)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (realL : LocalizedCumulativeTreeRealizes input readL left)
    (realR : LocalizedCumulativeTreeRealizes input readR right)
    (stage : LocalizedCumulativeRule45Stage) (fuel : Nat)
    (x y : input.LocalizedRerootCursor carrierFuel)
    (related : ShapePositionCursorRelation (shape_eq_of_observation_eq left right same) x y)
    (keyL keyR : input.LocalizedRerootCumulativeRule45Key)
    (builtL : input.buildRuleMajorCumulativeWithRead? stage readL fuel x = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stage readR fuel y = some keyR) :
    input.localizedRerootCumulativeRule45Observable keyL =
      input.localizedRerootCumulativeRule45Observable keyR := by
  let hs := shape_eq_of_observation_eq left right same
  exact replay_of_related stage readL readR (ShapePositionCursorRelation hs)
    (fun _ _ h => related_atomLabel hs realL realR h)
    (fun _ _ h => shapePositionCursorRelation_rootDistance hs realL realR h)
    (fun _ _ h => shapePositionCursorRelation_children hs realL realR h)
    (fun _ _ h => congrArg (localizedCumulativeRule45Priority stage) (related_readers same realL realR h))
    fuel x y related keyL keyR builtL builtR

end TetraStereo.OneCenter.LocalizedChemicalRingStageReplay

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStageReplay.replay_of_related
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStageReplay.replay_of_observations
