import TetraStereo.OneCenter.CIPAuthoritativeSourceAlignment

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace RawMolecule

/-!
# Sparse-key comparison on a common semantic schedule

The production key is nested by sphere and then parent-slot path.  This file proves, without
executing examples, that matching path supports turn that nested sparse comparison into ordinary
lexicographic comparison of observations on the flattened semantic schedule.  It also proves that
a sparse comparison can return equality only when its two path supports match.
-/

private theorem compareCanonicalPath_self (path : List ℕ) :
    compareCanonicalPath path path = .eq := by
  induction path with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [compareCanonicalPath, List.compareLex]

theorem compareSparseCanonicalEntry_samePath
    {α : Type*} (compareLabel : α → α → Ordering)
    (path : List ℕ) (left right : α) :
    compareSparseCanonicalEntry compareLabel (path, left) (path, right) =
      compareLabel left right := by
  simp [compareSparseCanonicalEntry, compareLex, Ordering.byKey,
    compareCanonicalPath_self, flip]

/-- Equal-length prefixes can be compared before their remaining tails. -/
theorem compareLex_append_of_length_eq
    {α : Type*} (compareValue : α → α → Ordering) :
    ∀ left right leftTail rightTail,
    left.length = right.length →
      List.compareLex compareValue (left ++ leftTail) (right ++ rightTail) =
        (List.compareLex compareValue left right).then
          (List.compareLex compareValue leftTail rightTail)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, lengthEq => by simp at lengthEq
  | _ :: _, [], _, _, lengthEq => by simp at lengthEq
  | leftHead :: left, rightHead :: right, leftTail, rightTail, lengthEq => by
      simp only [List.length_cons, Nat.succ.injEq] at lengthEq
      simp only [List.cons_append, List.compareLex]
      cases compareValue leftHead rightHead with
      | lt => rfl
      | gt => rfl
      | eq =>
          exact compareLex_append_of_length_eq compareValue
            left right leftTail rightTail lengthEq

/-- On the same ordered paths, one sparse layer compares exactly the observation lists. -/
theorem compareSparseCanonicalLayer_mapSource_eq_compareLex
    {Source Value : Type*} (compareValue : Value → Value → Ordering)
    (leftValue rightValue : Source → Value) :
    ∀ left right : List (List ℕ × Source),
    left.map Prod.fst = right.map Prod.fst →
      compareSparseCanonicalLayer compareValue
          (left.map fun entry => (entry.1, leftValue entry.2))
          (right.map fun entry => (entry.1, rightValue entry.2)) =
        List.compareLex compareValue (left.map (leftValue ∘ Prod.snd))
          (right.map (rightValue ∘ Prod.snd))
  | [], [], _ => rfl
  | [], _ :: _, paths => by simp at paths
  | _ :: _, [], paths => by simp at paths
  | (leftPath, leftSource) :: left,
      (rightPath, rightSource) :: right, paths => by
      simp only [List.map_cons, List.cons.injEq] at paths
      rw [← paths.1]
      simp only [compareSparseCanonicalLayer, List.map_cons, List.compareLex,
        Function.comp_apply]
      rw [compareSparseCanonicalEntry_samePath]
      have tail := compareSparseCanonicalLayer_mapSource_eq_compareLex
        compareValue leftValue rightValue left right paths.2
      cases compareValue (leftValue leftSource) (rightValue rightSource) with
      | lt => rfl
      | gt => rfl
      | eq => exact tail

/-- Matching sphere/path supports collapse nested sparse comparison to a single sphere-major
lexicographic comparison. -/
theorem compareSparseCanonicalLayers_mapSource_eq_compareLex_flatten
    {Source Value : Type*} (compareValue : Value → Value → Ordering)
    (leftValue rightValue : Source → Value) :
    ∀ left right : List (List (List ℕ × Source)),
    left.map (List.map Prod.fst) = right.map (List.map Prod.fst) →
      compareSparseCanonicalLayers compareValue
          (left.map fun layer => layer.map fun entry => (entry.1, leftValue entry.2))
          (right.map fun layer => layer.map fun entry => (entry.1, rightValue entry.2)) =
        List.compareLex compareValue
          (left.flatten.map (leftValue ∘ Prod.snd))
          (right.flatten.map (rightValue ∘ Prod.snd))
  | [], [], _ => rfl
  | [], _ :: _, paths => by simp at paths
  | _ :: _, [], paths => by simp at paths
  | leftLayer :: left, rightLayer :: right, paths => by
      simp only [List.map_cons, List.cons.injEq] at paths
      have layerCompared := compareSparseCanonicalLayer_mapSource_eq_compareLex
        compareValue leftValue rightValue leftLayer rightLayer paths.1
      have tailCompared := compareSparseCanonicalLayers_mapSource_eq_compareLex_flatten
        compareValue leftValue rightValue left right paths.2
      have layerLength :
          (leftLayer.map (leftValue ∘ Prod.snd)).length =
            (rightLayer.map (rightValue ∘ Prod.snd)).length := by
        simpa using congrArg List.length paths.1
      simp only [compareSparseCanonicalLayers, List.map_cons, List.compareLex,
        List.flatten_cons, List.map_append]
      unfold compareSparseCanonicalLayers at tailCompared
      rw [layerCompared]
      rw [compareLex_append_of_length_eq compareValue
        (leftLayer.map (leftValue ∘ Prod.snd))
        (rightLayer.map (rightValue ∘ Prod.snd))
        (left.flatten.map (leftValue ∘ Prod.snd))
        (right.flatten.map (rightValue ∘ Prod.snd)) layerLength]
      cases List.compareLex compareValue
          (leftLayer.map (leftValue ∘ Prod.snd))
          (rightLayer.map (rightValue ∘ Prod.snd)) with
      | lt => rfl
      | gt => rfl
      | eq => exact tailCompared

theorem compareCanonicalPath_eq_iff : ∀ left right : List ℕ,
    compareCanonicalPath left right = .eq ↔ left = right
  | [], [] => by simp [compareCanonicalPath, List.compareLex]
  | [], _ :: _ => by simp [compareCanonicalPath, List.compareLex]
  | _ :: _, [] => by simp [compareCanonicalPath, List.compareLex]
  | leftHead :: left, rightHead :: right => by
      simp only [compareCanonicalPath, List.compareLex]
      by_cases headEq : leftHead = rightHead
      · subst rightHead
        simp
      · have comparedNe : compare leftHead rightHead ≠ .eq := by
          simpa using headEq
        cases compared : compare leftHead rightHead <;> simp_all

/-- Equality of a sparse entry comparison forces equality of its semantic path, independently of
the label comparator. -/
theorem compareSparseCanonicalEntry_eq_implies_path_eq
    {α : Type*} (compareLabel : α → α → Ordering)
    (left right : List ℕ × α)
    (equal : compareSparseCanonicalEntry compareLabel left right = .eq) :
    left.1 = right.1 := by
  unfold compareSparseCanonicalEntry compareLex at equal
  have parts :
      Ordering.byKey Prod.fst (flip compareCanonicalPath) left right = .eq ∧
        Ordering.byKey Prod.snd compareLabel left right = .eq := by
    simpa only [Ordering.then_eq_eq] using equal
  have pathEqual := parts.1
  change compareCanonicalPath right.1 left.1 = .eq at pathEqual
  exact (compareCanonicalPath_eq_iff right.1 left.1).mp pathEqual |>.symm

/-- Equality of a sparse layer comparison forces identical path support in that sphere. -/
theorem compareSparseCanonicalLayer_eq_implies_paths_eq
    {α : Type*} (compareLabel : α → α → Ordering) :
    ∀ left right : List (List ℕ × α),
    compareSparseCanonicalLayer compareLabel left right = .eq →
      left.map Prod.fst = right.map Prod.fst
  | [], [], _ => rfl
  | [], _ :: _, equal => by
      simp [compareSparseCanonicalLayer, List.compareLex] at equal
  | _ :: _, [], equal => by
      simp [compareSparseCanonicalLayer, List.compareLex] at equal
  | leftHead :: left, rightHead :: right, equal => by
      simp only [compareSparseCanonicalLayer, List.compareLex] at equal
      cases entryCompared : compareSparseCanonicalEntry compareLabel leftHead rightHead with
      | lt => simp [entryCompared] at equal
      | gt => simp [entryCompared] at equal
      | eq =>
          simp only [entryCompared] at equal
          simp [compareSparseCanonicalEntry_eq_implies_path_eq
              compareLabel leftHead rightHead entryCompared,
            compareSparseCanonicalLayer_eq_implies_paths_eq
              compareLabel left right equal]

/-- Equality of a whole sparse hierarchy comparison forces identical sphere/path support. -/
theorem compareSparseCanonicalLayers_eq_implies_paths_eq
    {α : Type*} (compareLabel : α → α → Ordering) :
    ∀ left right : List (List (List ℕ × α)),
    compareSparseCanonicalLayers compareLabel left right = .eq →
      left.map (List.map Prod.fst) = right.map (List.map Prod.fst)
  | [], [], _ => rfl
  | [], _ :: _, equal => by
      simp [compareSparseCanonicalLayers, List.compareLex] at equal
  | _ :: _, [], equal => by
      simp [compareSparseCanonicalLayers, List.compareLex] at equal
  | leftHead :: left, rightHead :: right, equal => by
      simp only [compareSparseCanonicalLayers, List.compareLex] at equal
      cases layerCompared : compareSparseCanonicalLayer compareLabel leftHead rightHead with
      | lt => simp [layerCompared] at equal
      | gt => simp [layerCompared] at equal
      | eq =>
          simp only [layerCompared] at equal
          simp [compareSparseCanonicalLayer_eq_implies_paths_eq
              compareLabel leftHead rightHead layerCompared,
            compareSparseCanonicalLayers_eq_implies_paths_eq
              compareLabel left right equal]

theorem mapCanonicalSourceLayers_paths
    {α : Type*} (observe : CanonicalBranchNode → α)
    (layers : List (List CanonicalSourceEntry)) :
    (mapCanonicalSourceLayers observe layers).map (List.map Prod.fst) =
      layers.map (List.map Prod.fst) := by
  simp [mapCanonicalSourceLayers, List.map_map, Function.comp_def]

/-- A Rule-1a tie between source-aligned keys proves that their complete constitutional source
supports coincide, sphere by sphere and slot by slot. -/
theorem CanonicalBranchKey.AuthoritativeSourceAligned.sourcePaths_eq_of_rule1a_tie
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey)
    (leftAligned : leftKey.AuthoritativeSourceAligned mol)
    (rightAligned : rightKey.AuthoritativeSourceAligned mol)
    (rule1aTie : compareSparseCanonicalLayers compareCIPAtomicLabel
      leftKey.rule1a rightKey.rule1a = .eq) :
    leftKey.sourceNodes.map (List.map Prod.fst) =
      rightKey.sourceNodes.map (List.map Prod.fst) := by
  have paths := compareSparseCanonicalLayers_eq_implies_paths_eq
    compareCIPAtomicLabel leftKey.rule1a rightKey.rule1a rule1aTie
  rw [leftAligned.1, rightAligned.1] at paths
  simpa only [mapCanonicalSourceLayers_paths] using paths

/-- Consequently the two flattened semantic schedules are literally the same list. -/
theorem CanonicalBranchKey.AuthoritativeSourceAligned.sourceAddressSchedule_eq_of_rule1a_tie
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey)
    (leftAligned : leftKey.AuthoritativeSourceAligned mol)
    (rightAligned : rightKey.AuthoritativeSourceAligned mol)
    (rule1aTie : compareSparseCanonicalLayers compareCIPAtomicLabel
      leftKey.rule1a rightKey.rule1a = .eq) :
    leftKey.sourceAddressSchedule = rightKey.sourceAddressSchedule := by
  have paths :=
    CanonicalBranchKey.AuthoritativeSourceAligned.sourcePaths_eq_of_rule1a_tie
      mol leftKey rightKey leftAligned rightAligned rule1aTie
  unfold CanonicalBranchKey.sourceAddressSchedule
  simpa only [List.map_flatten] using congrArg List.flatten paths

/-- Rule 1b on aligned keys with a Rule-1a tie is ordinary lexicographic observation comparison
on their now-common semantic address schedule. -/
theorem compareRule1b_eq_compareLex_sourceSchedule_of_rule1a_tie
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey)
    (leftAligned : leftKey.AuthoritativeSourceAligned mol)
    (rightAligned : rightKey.AuthoritativeSourceAligned mol)
    (rule1aTie : compareSparseCanonicalLayers compareCIPAtomicLabel
      leftKey.rule1a rightKey.rule1a = .eq) :
    compareSparseCanonicalLayers compareRule1bRootDistance
        leftKey.rule1b rightKey.rule1b =
      List.compareLex compareRule1bRootDistance
        (leftKey.sourceNodes.flatten.map
          (CanonicalBranchNode.rule1bCode ∘ Prod.snd))
        (rightKey.sourceNodes.flatten.map
          (CanonicalBranchNode.rule1bCode ∘ Prod.snd)) := by
  rw [leftAligned.2.1, rightAligned.2.1]
  exact compareSparseCanonicalLayers_mapSource_eq_compareLex_flatten
    compareRule1bRootDistance CanonicalBranchNode.rule1bCode
      CanonicalBranchNode.rule1bCode leftKey.sourceNodes rightKey.sourceNodes
      (CanonicalBranchKey.AuthoritativeSourceAligned.sourcePaths_eq_of_rule1a_tie
        mol leftKey rightKey leftAligned rightAligned rule1aTie)

/-- Rule 2 has the analogous common-schedule form after the earlier support-establishing tie. -/
theorem compareRule2_eq_compareLex_sourceSchedule_of_rule1a_tie
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey)
    (leftAligned : leftKey.AuthoritativeSourceAligned mol)
    (rightAligned : rightKey.AuthoritativeSourceAligned mol)
    (rule1aTie : compareSparseCanonicalLayers compareCIPAtomicLabel
      leftKey.rule1a rightKey.rule1a = .eq) :
    compareSparseCanonicalLayers compare leftKey.rule2 rightKey.rule2 =
      List.compareLex compare
        (leftKey.sourceNodes.flatten.map (mol.canonicalRule2Mass ∘ Prod.snd))
        (rightKey.sourceNodes.flatten.map (mol.canonicalRule2Mass ∘ Prod.snd)) := by
  rw [leftAligned.2.2, rightAligned.2.2]
  exact compareSparseCanonicalLayers_mapSource_eq_compareLex_flatten
    compare mol.canonicalRule2Mass mol.canonicalRule2Mass
      leftKey.sourceNodes rightKey.sourceNodes
      (CanonicalBranchKey.AuthoritativeSourceAligned.sourcePaths_eq_of_rule1a_tie
        mol leftKey rightKey leftAligned rightAligned rule1aTie)

end RawMolecule

end TetraStereo.OneCenter
