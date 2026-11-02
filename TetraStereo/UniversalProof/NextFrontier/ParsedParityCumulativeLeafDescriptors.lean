import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCumulativeRule45Exact

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Generic actual cumulative descriptor projection for a three-terminal branch. Child
sorting remains the real canonical sort, but identical terminal descriptor arrays make its
order immaterial to this projection. No constitutional-source equality is asserted. -/

namespace TetraStereo.UniversalProof.NextFrontier.ParsedParityCumulativeLeafDescriptors

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Terminal actual cumulative keys have exactly the node's actual label priority. -/
theorem canonical_terminal_descriptor (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalCumulativeRule45Key)
    (derived : source.CanonicalAromaticCanonicalCumulativeRule45Key stage target view fuel cursor key)
    (terminal : source.aromaticCanonicalRerootChildren cursor = []) :
    key.descriptor = [[([], localizedCumulativeRule45Priority stage
      (source.aromaticCanonicalDependencyLabel target view cursor))]] := by
  cases derived with
  | terminal frame empty observed =>
      rw [(source.aromaticCanonicalDependencyLabel_eq_iff target view cursor _).mpr observed]
  | branch frame nonempty observed childDerivations ranking =>
      have actual := (source.aromaticCanonicalRerootChildren?_eq_some_iff _ _).mpr frame
      simp only [aromaticCanonicalRerootChildren?, Option.some.injEq] at actual
      exact False.elim (nonempty (actual.symm.trans terminal))

private theorem canonical_list_pointwise {source : AuthoritativeChemicalInput}
    {carrierFuel fuel : Nat} {stage : LocalizedCumulativeRule45Stage}
    {target : source.AromaticCanonicalOccurrence carrierFuel}
    {view : source.AromaticCanonicalDependencyView target}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalCumulativeRule45Key}
    (derived : source.CanonicalAromaticCanonicalCumulativeRule45KeyList stage target view fuel cursors keys) :
    List.Forall₂ (source.CanonicalAromaticCanonicalCumulativeRule45Key stage target view fuel)
      cursors keys :=
  match derived with
  | .nil _ => .nil
  | .cons head tail => .cons head (canonical_list_pointwise tail)

private theorem terminal_list_descriptors (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalCumulativeRule45Key}
    (derived : source.CanonicalAromaticCanonicalCumulativeRule45KeyList stage target view fuel cursors keys)
    (terminal : ∀ child ∈ cursors, source.aromaticCanonicalRerootChildren child = [])
    (absent : ∀ child ∈ cursors, source.aromaticCanonicalDependencyLabel target view child = none) :
    ∀ key ∈ keys, key.descriptor = [[([], localizedCumulativeRule45Priority stage none)]] := by
  have pointwise := canonical_list_pointwise derived
  clear derived
  revert terminal absent
  induction pointwise with
  | nil => intro terminal absent; simp
  | @cons cursor key cursors keys head tail ih =>
      intro terminal absent selected member
      rcases List.mem_cons.mp member with rfl | retained
      · rw [canonical_terminal_descriptor source stage target view cursor selected head
          (terminal cursor List.mem_cons_self), absent cursor List.mem_cons_self]
      · exact ih (fun child member => terminal child (List.mem_cons_of_mem _ member))
          (fun child member => absent child (List.mem_cons_of_mem _ member)) selected retained

/-- Exact complete descriptor layers of an actual branch with three unlabeled terminal children.
The root's label is read from the supplied genuine dependency view, never postulated as an output. -/
theorem canonical_three_leaf_descriptor (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalCumulativeRule45Key)
    (derived : source.CanonicalAromaticCanonicalCumulativeRule45Key stage target view fuel cursor key)
    (count : (source.aromaticCanonicalRerootChildren cursor).length = 3)
    (terminal : ∀ child ∈ source.aromaticCanonicalRerootChildren cursor,
      source.aromaticCanonicalRerootChildren child = [])
    (absent : ∀ child ∈ source.aromaticCanonicalRerootChildren cursor,
      source.aromaticCanonicalDependencyLabel target view child = none) :
    key.descriptor =
      [[([], localizedCumulativeRule45Priority stage
        (source.aromaticCanonicalDependencyLabel target view cursor))],
       [([0], localizedCumulativeRule45Priority stage none),
        ([1], localizedCumulativeRule45Priority stage none),
        ([2], localizedCumulativeRule45Priority stage none)]] := by
  cases derived with
  | terminal frame empty observed =>
      have actual := (source.aromaticCanonicalRerootChildren?_eq_some_iff _ _).mpr frame
      simp only [aromaticCanonicalRerootChildren?, Option.some.injEq] at actual
      rw [actual, empty] at count
      contradiction
  | @branch depth cursor children label childKeys sorted frame nonempty observed childrenDerived ranking =>
      have actual : source.aromaticCanonicalRerootChildren cursor = children := by
        have computed := (source.aromaticCanonicalRerootChildren?_eq_some_iff _ _).mpr frame
        simpa only [aromaticCanonicalRerootChildren?, Option.some.injEq] using computed
      have sortedEq := (source.sortAromaticCanonicalCumulativeRule45Keys_eq_iff_canonical
        childKeys sorted).mpr ranking
      have permutation : sorted.Perm childKeys := by
        rw [← sortedEq]
        exact sortAromaticCanonicalCumulativeRule45Keys_perm _ _
      have childValues := terminal_list_descriptors source stage target view childrenDerived
        (fun child member => terminal child (by rw [actual]; exact member))
        (fun child member => absent child (by rw [actual]; exact member))
      have sortedValues : ∀ key ∈ sorted,
          key.descriptor = [[([], localizedCumulativeRule45Priority stage none)]] := by
        intro selected member
        exact childValues selected (permutation.mem_iff.mp member)
      have length : sorted.length = 3 := by
        rw [permutation.length_eq, ← (canonical_list_pointwise childrenDerived).length_eq, ← actual]
        exact count
      obtain ⟨k0, k1, k2, sortedList⟩ := List.length_eq_three.mp length
      clear sortedEq
      subst sorted
      have d0 := sortedValues k0 (by simp)
      have d1 := sortedValues k1 (by simp)
      have d2 := sortedValues k2 (by simp)
      have labelEq := (source.aromaticCanonicalDependencyLabel_eq_iff target view cursor _).mpr observed
      simp [mergeAromaticCanonicalDescriptorChildren, aromaticCanonicalDescriptorChildLayerCount,
        OfficialRuleMajorKey.prefixLayer, d0, d1, d2, labelEq, List.range_succ]

end TetraStereo.UniversalProof.NextFrontier.ParsedParityCumulativeLeafDescriptors
