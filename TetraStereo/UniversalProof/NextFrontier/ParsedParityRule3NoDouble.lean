import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3CanonicalFrame

set_option autoImplicit false









namespace TetraStereo.OneCenter.AuthoritativeChemicalInput

private theorem exceptNodeOutcome_eq_none_of_noDouble
    (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {outcome : Option source.AromaticCanonicalRule3SpatialNodeResult}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialNodeExceptOutcome
      excluded node outcome) :
    outcome = none := by
  cases derived with
  | structuralNonunit => rfl
  | excludedUnit => rfl
  | @retainedGeometry result observed freshIdentity =>
      rcases observed with ⟨_real, _current, _parent, ordinary, _unit⟩
      exact (noDouble result.left result.right ordinary).elim

private theorem foldl_max_rule3_lengths_eq_zero
    {source : AuthoritativeChemicalInput}
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (empty : ∀ key ∈ keys, key.rule3 = []) :
    keys.foldl (fun longest child => max longest child.rule3.length) 0 = 0 := by
  induction keys with
  | nil => rfl
  | cons head tail ih =>
      have headEmpty := empty head (by simp)
      simp [headEmpty]
      exact ih (fun key present => empty key (by simp [present]))

private theorem mergeRule3PriorityChildren_eq_nil
    {source : AuthoritativeChemicalInput}
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (empty : ∀ key ∈ keys, key.rule3 = []) :
    mergeAromaticCanonicalRule3PriorityChildren keys = [] := by
  unfold mergeAromaticCanonicalRule3PriorityChildren
  rw [show aromaticCanonicalRule3PriorityChildLayerCount keys = 0 by
    exact foldl_max_rule3_lengths_eq_zero keys empty]
  rfl

/-- Every key in an actual common-exclusion derivation has empty Rule-3 priority layers
when the source has no ordinary double bonds, for any exclusion set and rule fuel. -/
theorem declarativeRule3SpatialKeyExceptList_rule3_eq_nil_of_noDouble
    (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    {carrierFuel fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded fuel cursors keys) :
    ∀ key ∈ keys, key.rule3 = [] := by
  refine DeclarativeAromaticCanonicalRule3SpatialKeyExceptList.rec
    (motive_1 := fun _fuel _cursor key _derived => key.rule3 = [])
    (motive_2 := fun _fuel _cursors keys _derived =>
      ∀ key ∈ keys, key.rule3 = [])
    ?_ ?_ ?_ ?_ ?_ derived
  · intro cursor children observation frame terminal observed
    have observationEmpty :=
      source.exceptNodeOutcome_eq_none_of_noDouble noDouble observed
    subst observation
    rfl
  · intro fuel cursor children observation frame terminal observed
    have observationEmpty :=
      source.exceptNodeOutcome_eq_none_of_noDouble noDouble observed
    subst observation
    rfl
  · intro fuel cursor children observation childKeys sorted frame nonterminal observed
      childrenDerived permutation descending childrenEmpty
    have observationEmpty :=
      source.exceptNodeOutcome_eq_none_of_noDouble noDouble observed
    subst observation
    simp only [aromaticCanonicalRule3RootPriorities, List.nil_append]
    apply mergeRule3PriorityChildren_eq_nil sorted
    intro child present
    exact childrenEmpty child (permutation.mem_iff.mp present)
  · intro fuel
    simp
  · intro fuel cursor cursors headKey tailKeys head tail headEmpty tailEmpty key present
    simp only [List.mem_cons] at present
    rcases present with rfl | present
    · exact headEmpty
    · exact tailEmpty key present

/-- A single actual common-exclusion key has empty Rule-3 priority layers on a source
without ordinary double bonds. The actual derivation supplies the key. -/
theorem declarativeRule3SpatialKeyExcept_rule3_eq_nil_of_noDouble
    (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    {carrierFuel fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept
      excluded fuel cursor key) :
    key.rule3 = [] := by
  have singleton : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded fuel [cursor] [key] := .cons derived (.nil fuel)
  exact source.declarativeRule3SpatialKeyExceptList_rule3_eq_nil_of_noDouble
    noDouble singleton key (by simp)

end TetraStereo.OneCenter.AuthoritativeChemicalInput
