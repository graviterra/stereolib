import TetraStereo.OneCenter.CIPAuthoritativeMoleculeCursorRanking
import TetraStereo.OneCenter.ProductionCIPBranchingOccurrenceComparatorCompleteness
import TetraStereo.OneCenter.ProductionCIPRule1aGeneralSoundness

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.UniversalProof.ProductionPrunedFrontierCapacityProofs

/-!
# Molecule-derived branching cursor termination ranking

This module constructs an actual `BranchingCursorTerminationRanking` instance from molecular
structure, rather than repackaging an assumed `BranchingCursorSupport` premise.  Every field of the
ranking is derived:

* `eligible` is canonical reachability (`CanonicalCenterRerootCursor`) from one molecular center;
* `height` is the existing molecule-derived `moleculeCursorHeight`;
* `zero_terminal` and `child_decreases` are the already proved `moleculeCursorHeight_zero_terminal`
  and `moleculeCursorHeight_child_lt`;
* `child_eligible` is closure of the canonical domain under forward reroot children;
* the two genuinely source-sensitive fields are exposed as explicit hypotheses:
  - `local_width` needs the **ternary branching width** condition: the uncut canonical neighborhood
    of every generated node has at most four occurrences, so deleting the incoming occurrence leaves
    at most three forward children.  This is the tetrahedral (four-ligand) scope.  Its numerical bound is more restrictive than the authoritative bonding-number-six condition; molecules whose
    center carries a fifth or sixth occurrence (for example a P-92 bonding-number-six center) are
    **excluded** and are covered only by the cap-free authoritative path.  We therefore never claim
    universal totality of this branching scope.
  - `label` needs production Rule-1a label totality for the `multipleBondDuplicate` observation,
    which delegates to `mancudeRule1aLabel?`.  This is discharged from the refreshed production
    label-totality module (`ProductionCIPRule1aGeneralSoundness`), where the maximum-matching
    support condition makes the production dispatcher total at localized attached duplicates.

The frontier width cap (`defaultBranchWidthCap`) is deliberately kept *separate*: the height bound is
a molecule-size fact (`2 * atomCount + 1`) with no reference to the operational cap, and the cap is
applied only through the frontier-budget hypothesis of `BranchingFrontierSupport`.

## Production dependency

`productionMancudeRule1aSupported_of_localizedMaximum` uses the integrated production theorem
`RawMolecule.mancudeRule1aLabel?_exists_of_localized_maximum` from
`TetraStereo.OneCenter.ProductionCIPRule1aGeneralSoundness`.
-/

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.OneCenter.ProductionCIPRerootComparatorLaws
open TetraStereo.OneCenter.ProductionCIPBranchingOccurrenceComparatorCompleteness

noncomputable section

/-! ## Local ternary branching width -/

/-- Local ternary branching scope: after deleting the incoming cursor occurrence, a generated node
has at most three forward children.  Equivalently the uncut canonical neighborhood has at most four
occurrences.  This is a local four-occurrence envelope and has a smaller numerical bound than the
authoritative bonding-number-six boundary `CanonicalCenterBondingNumberSix`. -/
def CanonicalCenterBranchingWidth (mol : RawMolecule) (center : Nat) : Prop :=
  ∀ node : CanonicalBranchNode, CanonicalCenterTreeNode mol center node →
    (canonicalOriginalParent? node).toList.length + (mol.canonicalChildren node).length ≤ 4

/-- The ternary branching scope is contained in the authoritative bonding-number-six scope.  This theorem proves inclusion; it does not establish a strict-inclusion witness or the reverse
implication. The two numerical bounds must not be silently interchanged. -/
theorem CanonicalCenterBondingNumberSix_of_branchingWidth
    {mol : RawMolecule} {center : Nat}
    (branching : CanonicalCenterBranchingWidth mol center) :
    CanonicalCenterBondingNumberSix mol center := by
  intro node generated
  exact le_trans (branching node generated) (by norm_num)

/-- Deleting the remembered incoming occurrence from a ternary-width neighborhood leaves at most
three forward children.  This is the `≤ 3` local-width field of `BranchingCursorTerminationRanking`,
proved from the molecule-level scope predicate rather than assumed. -/
theorem canonicalCenterRerootCursor_local_width_three
    {mol : RawMolecule} {center : Nat}
    (branching : CanonicalCenterBranchingWidth mol center)
    (cursor : CanonicalRerootCursor)
    (eligible : CanonicalCenterRerootCursor mol center cursor) :
    (cursor.children mol).length ≤ 3 := by
  rcases eligible.previous_mem_neighbors with ⟨previous, previousEq, previousMember⟩
  have nodeGenerated : CanonicalCenterTreeNode mol center cursor.node := by
    cases eligible with
    | descending parentGenerated nodeMember => exact .child parentGenerated nodeMember
    | ascending nodeGenerated childMember => exact nodeGenerated
  by_cases leaf : cursor.node.forcedLeaf = true
  · simp [CanonicalRerootCursor.children, leaf]
  · have notLeaf : cursor.node.forcedLeaf = false := Bool.eq_false_of_not_eq_true leaf
    have previousMember' : previous ∈ cursor.neighbors mol := by
      simpa [CanonicalRerootCursor.neighbors] using previousMember
    have neighborBound : (cursor.neighbors mol).length ≤ 4 := by
      simpa [CanonicalRerootCursor.neighbors] using branching cursor.node nodeGenerated
    have dropped :
        ((cursor.neighbors mol).filterMap
          (fun neighbor =>
            if neighbor == previous then none
            else some ({ node := neighbor, previous? := some cursor.node } :
              CanonicalRerootCursor))).length <
          (cursor.neighbors mol).length := by
      apply length_filterMap_lt_of_mem_eq_none _ previousMember'
      simp
    rw [CanonicalRerootCursor.children, notLeaf]
    simp only [Bool.false_eq_true, ↓reduceIte, previousEq]
    omega

/-! ## Production Rule-1a label totality -/

/-- Production-side mancude support: `mancudeRule1aLabel?` returns a label at every in-range
attached--duplicate pair.  This is the production analogue of the authoritative
`MancudeRule1aSupported`, stated over `Fin mol.atomCount` so it can be discharged directly by the
refreshed production label-totality theorem. -/
def ProductionMancudeRule1aSupported (mol : RawMolecule) : Prop :=
  ∀ (attached duplicated : Fin mol.atomCount), ∃ label,
    mol.mancudeRule1aLabel? attached.val duplicated.val = some label

/-- Molecule-level form of the maximum-matching support condition: the written noncumulative double
bonds of every localized mancude component form a maximum-cardinality matching of that component.
This is the exact hypothesis of the refreshed production totality theorem
`mancudeRule1aLabel?_exists_of_localized_maximum`. -/
def LocalizedMancudeComponentsMaximum (mol : RawMolecule) : Prop :=
  ∀ attached : Fin mol.atomCount, IsMaximumMancudeEdgeMatching
    ((mol.localizedMancudeComponentEdges attached.val).filter
      fun edge => mol.bondOrder edge.1 edge.2 == 2)
    (mol.localizedMancudeComponentEdges attached.val)

/-- Exact derivable support theorem: a well-formed molecule with unique bond records whose localized
mancude components carry written maximum matchings satisfies production Rule-1a label totality.  The
localized case is discharged by the refreshed general-branch totality theorem; the non-localized
case is total by construction of `mancudeRule1aLabel?`. -/
theorem productionMancudeRule1aSupported_of_localizedMaximum
    (mol : RawMolecule) (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (maximum : LocalizedMancudeComponentsMaximum mol) :
    ProductionMancudeRule1aSupported mol := by
  intro attached duplicated
  by_cases localized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true
  · exact mol.mancudeRule1aLabel?_exists_of_localized_maximum wellFormed unique
      attached duplicated localized (maximum attached)
  · refine ⟨{ numerator := mol.atomZAt duplicated.val, denominator := 1 }, ?_⟩
    unfold RawMolecule.mancudeRule1aLabel?
    rw [Bool.eq_false_of_not_eq_true localized]
    simp

/-! ## Range facts for generated canonical nodes -/

/-- Every atom occurrence generated from a bounded center is in range. -/
theorem CanonicalCenterTreeNode.atom_lt_atomCount
    {mol : RawMolecule} {center : Nat} (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed) {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol center node) :
    node.atom < mol.atomCount := by
  cases generated with
  | root => simpa [canonicalCenterRoot] using centerBound
  | @child parent child parentGenerated member =>
      exact child_atom_lt_atomCount wellFormed member

/-- Every generated child remembers its immediate parent's atom. -/
theorem canonicalChild_parent_eq {mol : RawMolecule}
    {parent child : CanonicalBranchNode}
    (member : child ∈ mol.canonicalChildren parent) :
    child.parent = parent.atom := by
  unfold RawMolecule.canonicalChildren at member
  by_cases leaf : parent.forcedLeaf
  · simp [leaf] at member
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    rcases member with ⟨copy, _copyMember, rfl⟩
    rfl

/-- The remembered parent slot of a generated canonical node is in range.  For the root it is the
center; for a child it is the atom of the generated parent. -/
theorem CanonicalCenterTreeNode.parent_lt_atomCount
    {mol : RawMolecule} {center : Nat} (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed) {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol center node) :
    node.parent < mol.atomCount := by
  cases generated with
  | root => simpa [canonicalCenterRoot] using centerBound
  | child parentGenerated member =>
      rw [canonicalChild_parent_eq member]
      exact CanonicalCenterTreeNode.atom_lt_atomCount centerBound wellFormed parentGenerated

/-- Production Rule-1a label totality for generated canonical nodes.  Real atoms, ring duplicates
and phantoms are total by construction; the `multipleBondDuplicate` case uses production mancude
support at the in-range attached--duplicate pair. -/
theorem CanonicalCenterTreeNode.canonicalRule1aLabel?_exists
    {mol : RawMolecule} {center : Nat} (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed)
    (supported : ProductionMancudeRule1aSupported mol)
    {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol center node) :
    ∃ value, mol.canonicalRule1aLabel? node = some value := by
  cases provenanceEq : node.provenance with
  | realAtom => exact ⟨{ numerator := mol.atomZAt node.atom, denominator := 1 },
      by simp [RawMolecule.canonicalRule1aLabel?, provenanceEq]⟩
  | multipleBondDuplicate distance =>
      rcases supported
          ⟨node.parent, CanonicalCenterTreeNode.parent_lt_atomCount centerBound wellFormed generated⟩
          ⟨node.atom, CanonicalCenterTreeNode.atom_lt_atomCount centerBound wellFormed generated⟩ with
        ⟨label, observed⟩
      exact ⟨label, by simp [RawMolecule.canonicalRule1aLabel?, provenanceEq, observed]⟩
  | ringDuplicate distance => exact ⟨{ numerator := mol.atomZAt node.atom, denominator := 1 },
      by simp [RawMolecule.canonicalRule1aLabel?, provenanceEq]⟩
  | phantom distance => exact ⟨{ numerator := 0, denominator := 1 },
      by simp [RawMolecule.canonicalRule1aLabel?, provenanceEq]⟩

/-! ## The molecule-derived ranking instance -/

/-- A molecule-derived `BranchingCursorTerminationRanking` for the canonical center tree.  No field
is assumed: `eligible` is canonical reachability, `height` is `moleculeCursorHeight`, termination and
child decrease are the existing molecule proofs, local width is the ternary branching scope, and the
label field is discharged from production mancude support. -/
def moleculeBranchingCursorTerminationRanking
    (mol : RawMolecule) (center : Nat) (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed)
    (branching : CanonicalCenterBranchingWidth mol center)
    (supported : ProductionMancudeRule1aSupported mol) :
    BranchingCursorTerminationRanking mol where
  eligible := CanonicalCenterRerootCursor mol center
  height := moleculeCursorHeight mol
  label := fun cursor eligible => by
    have generated : CanonicalCenterTreeNode mol center cursor.node := by
      cases eligible with
      | descending parentGenerated nodeMember => exact .child parentGenerated nodeMember
      | ascending nodeGenerated childMember => exact nodeGenerated
    exact CanonicalCenterTreeNode.canonicalRule1aLabel?_exists centerBound wellFormed supported generated
  zero_terminal := fun cursor eligible heightZero =>
    moleculeCursorHeight_zero_terminal centerBound wellFormed cursor eligible heightZero
  local_width := fun cursor eligible =>
    canonicalCenterRerootCursor_local_width_three branching cursor eligible
  child_eligible := fun _cursor _child eligible member => eligible.child member
  child_decreases := fun _cursor _child eligible member =>
    moleculeCursorHeight_child_lt centerBound wellFormed eligible member

/-- Every eligible branching cursor fits the uniform molecule-size height bound, with no reference to
the operational frontier cap. -/
theorem moleculeBranchingCursorTerminationRanking_height_le
    (mol : RawMolecule) (center : Nat) (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed)
    (_branching : CanonicalCenterBranchingWidth mol center)
    (_supported : ProductionMancudeRule1aSupported mol)
    {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol center cursor) :
    moleculeCursorHeight mol cursor ≤ 2 * mol.atomCount + 1 :=
  moleculeCursorHeight_le_two_mul_atomCount_add_one centerBound wellFormed eligible

/-- The constructed ranking supplies recursive `BranchingCursorSupport` at any covering fuel. -/
theorem moleculeBranchingCursorSupport_of_eligible
    (mol : RawMolecule) (center : Nat) (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed)
    (branching : CanonicalCenterBranchingWidth mol center)
    (supported : ProductionMancudeRule1aSupported mol)
    (fuel : Nat) {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol center cursor)
    (covered : moleculeCursorHeight mol cursor ≤ fuel) :
    BranchingCursorSupport mol fuel cursor :=
  (moleculeBranchingCursorTerminationRanking mol center centerBound wellFormed branching
    supported).branchingSupport_of_height_le fuel cursor eligible covered

/-- Molecule-derived branching support at the uniform `2 * atomCount + 1` depth. -/
theorem moleculeBranchingCursorSupport_uniform
    (mol : RawMolecule) (center : Nat) (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed)
    (branching : CanonicalCenterBranchingWidth mol center)
    (supported : ProductionMancudeRule1aSupported mol)
    {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol center cursor) :
    BranchingCursorSupport mol (2 * mol.atomCount + 1) cursor :=
  moleculeBranchingCursorSupport_of_eligible mol center centerBound wellFormed branching supported
    (2 * mol.atomCount + 1) eligible
    (moleculeCursorHeight_le_two_mul_atomCount_add_one centerBound wellFormed eligible)

/-- Fully molecule-derived branching support: no support hypothesis remains beyond the explicit
ternary-width scope, the localized-maximum condition, well-formedness and unique bond records. -/
theorem moleculeBranchingCursorSupport_uniform_of_localizedMaximum
    (mol : RawMolecule) (center : Nat) (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (branching : CanonicalCenterBranchingWidth mol center)
    (maximum : LocalizedMancudeComponentsMaximum mol)
    {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol center cursor) :
    BranchingCursorSupport mol (2 * mol.atomCount + 1) cursor :=
  moleculeBranchingCursorSupport_uniform mol center centerBound wellFormed branching
    (productionMancudeRule1aSupported_of_localizedMaximum mol wellFormed unique maximum)
    eligible

/-! ## Frontier cap budget, kept separate -/

/-- A single supported pair at a depth covered by the certified height, below the operational
frontier cap, forms a supported frontier.  The ternary envelope `3 ^ fuel ≤ defaultBranchWidthCap` is
an independent hypothesis: the height bound above is a molecule-size fact and does not imply it. -/
theorem moleculeBranchingFrontierSupport_singleton
    (mol : RawMolecule) (center : Nat) (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed)
    (branching : CanonicalCenterBranchingWidth mol center)
    (supported : ProductionMancudeRule1aSupported mol)
    (fuel : Nat) {left right : CanonicalRerootCursor}
    (envelope : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap)
    (leftEligible : CanonicalCenterRerootCursor mol center left)
    (rightEligible : CanonicalCenterRerootCursor mol center right)
    (leftCovered : moleculeCursorHeight mol left ≤ fuel)
    (rightCovered : moleculeCursorHeight mol right ≤ fuel) :
    BranchingFrontierSupport mol fuel [(left, right)] :=
  branchingFrontierSupport_singleton mol fuel left right envelope
    (moleculeBranchingCursorSupport_of_eligible mol center centerBound wellFormed branching
      supported fuel leftEligible leftCovered)
    (moleculeBranchingCursorSupport_of_eligible mol center centerBound wellFormed branching
      supported fuel rightEligible rightCovered)

end

end TetraStereo.UniversalProof.ProductionPrunedFrontierCapacityProofs
