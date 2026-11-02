import TetraStereo.OneCenter.RawFramedGeneratedFuelInterface
import TetraStereo.OneCenter.CIPAuthoritativeMancudeTotality
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.OneCenter.CanonicalComparisonFrame
open TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission
open TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability
open TetraStereo.OneCenter.AuthoritativeCIPMancudeTotality
open TetraStereo.OneCenter.AuthoritativeCIPCursorSupport
open TetraStereo.OneCenter.RawFramedConstitutionalFuelClosure
open TetraStereo.OneCenter.RawFramedGeneratedFuelInterface

/-!
# Runtime Rule-1a availability on the generated-mancude (Kekulé) domain

`GeneratedDuplicateAtomicLabelAvailability` isolates the exact executable refusal boundary of the
authoritative Rule-1a node label: a `.multipleBondDuplicate` node whose attached edge is a localized
mancude edge fails only when both the simple-cycle shortcut and the exhaustive maximum-matching
average fail.  Its sufficient scope `NonMancudeGeneratedDuplicates` excludes *every* generated
multiple-bond duplicate on a localized edge.

That scope is unnecessarily narrow.  `CIPAuthoritativeMancudeTotality` already proves an independent
chemical condition under which the exhaustive branch cannot fail:

```lean
LocalizedMancudeKekuleAdmissible mol
```

says that, in every localized component, the written noncumulative double bonds form a
maximum-cardinality matching of the complete finite localized edge graph.  From `mol.WellFormed`,
`mol.BondRecordsUnique` and this condition, the existing theorem
`mancudeRule1aSupported_of_localizedKekuleAdmissible` derives `MancudeRule1aSupported mol`, i.e.
`mancudeRule1aLabelAuthoritative?` is total.  This module consumes that theorem; it does not
reimplement matching enumeration.

## Honest domain statement

The broader domain used below is the explicit hypothesis

```lean
KekuleGeneratedDomain mol :=
  mol.WellFormed ∧ mol.BondRecordsUnique ∧ LocalizedMancudeKekuleAdmissible mol
```

This is *not* a claim that every molecule is Kekulé admissible, and it is not universal molecular
admissibility.  The matching premise remains an independent chemical hypothesis supplied by the
caller, exactly as it is in `CIPAuthoritativeMancudeTotality`.  What changes relative to
`NonMancudeGeneratedDuplicates` is only the scope of the runtime availability results: generated
multiple-bond duplicates on localized mancude edges are now admitted whenever the written double
bonds already form a maximum matching, even though no "off-mancude" assumption holds.

No production definition is changed and no second comparator is introduced.  The labels returned
are the actual executable `canonicalRule1aLabelAuthoritative?` values (`CIPAtomicLabel` numerator /
denominator pairs); the exact refusal boundary of the old module is re-exported unchanged, so
outside the domain an absent label still means exactly what it meant before.

## Main results

* `generated_rule1a_label_available_of_kekule` — every actually generated node has an
  authoritative Rule-1a label on the Kekulé domain;
* `generated_rule1a_label_exact_of_kekule` — the three total provenance classes keep their exact
  rational labels and the multiple-bond class is exactly the mancude dispatch, with no substitution;
* `multipleBondDuplicate_label_none_iff_refusal` — the original refusal boundary, re-exported
  verbatim (under a non-shadowing name);
* `generated_label_none_refuted_of_kekule` — on the domain no generated node refuses;
* `profile?_rule1a_label_available_of_kekule` — the actual `Profile` produced by
  `profile?_complete` carries labels and observations on every generated member;
* `interface_of_generated_profile_of_kekule` — the `FrameObserved` / `FrameLabelAvailable`
  interface of `RawFramedGeneratedFuelInterface` is discharged from the actual admitted profile,
  without the archived all-real gate;
* `frameRuntime_label?_rule1a_available_of_kekule` — the shipped `FrameRuntime.label?` returns a
  Rule-1a ordering for actual cursor pairs on the projected profile;
* `failClosed_uniform_of_interface` and `main_uniform_of_interface` — a *single* ordering at
  `2 * atomCount + 2` that is the same ordering at every larger fuel (fuel is quantified inside
  the scope of the existential ordering, so this is genuine uniform stability, not a per-fuel
  existential);
* `generated_profile_failClosed_uniform_of_kekule` and
  `generated_profile_main_uniform_of_kekule` — the shipped fail-closed candidate and the stable
  MAIN constitutional comparator for actual ligand cursors on the Kekulé domain;
* `generated_profile_failClosed_uniform_of_nonMancude` and
  `generated_profile_main_uniform_of_nonMancude` — the same uniform endpoints on the earlier
  `NonMancudeGeneratedDuplicates` domain, exported so that both scopes have the stronger form.

The generic fuel recursion is owned by `RawFramedGeneratedFuelInterface`; this module only
discharges its interface on the broader domain and composes the final results.
-/

/-! ## The broader generated-mancude domain -/

/-- The explicit generated-mancude domain: well-formed finite bond records, unique bond records,
and the independent written-matching (Kekulé) condition on every localized component.

This bundles hypotheses already consumed by `CIPAuthoritativeMancudeTotality`.  It is a premise,
not a theorem about all molecules. -/
def KekuleGeneratedDomain (mol : RawMolecule) : Prop :=
  mol.WellFormed ∧ mol.BondRecordsUnique ∧ LocalizedMancudeKekuleAdmissible mol

/-- The well-formedness component of the domain. -/
theorem KekuleGeneratedDomain.wellFormed {mol : RawMolecule}
    (domain : KekuleGeneratedDomain mol) : mol.WellFormed :=
  domain.1

/-- The unique-finite-bond-record component of the domain. -/
theorem KekuleGeneratedDomain.bondRecordsUnique {mol : RawMolecule}
    (domain : KekuleGeneratedDomain mol) : mol.BondRecordsUnique :=
  domain.2.1

/-- The independent maximum-written-matching component of the domain.  This is the chemical
premise, not a consequence of well-formedness. -/
theorem KekuleGeneratedDomain.kekuleAdmissible {mol : RawMolecule}
    (domain : KekuleGeneratedDomain mol) : LocalizedMancudeKekuleAdmissible mol :=
  domain.2.2

/-- The existing chemical totality theorem, restated on the bundled domain.  No matching
enumeration is re-proved here. -/
theorem mancudeRule1aSupported_of_kekuleDomain (mol : RawMolecule)
    (domain : KekuleGeneratedDomain mol) :
    MancudeRule1aSupported mol :=
  mancudeRule1aSupported_of_localizedKekuleAdmissible mol
    domain.wellFormed domain.bondRecordsUnique domain.kekuleAdmissible

/-! ## Every generated node has its exact authoritative label -/

/-- Every actually generated node receives the executable authoritative Rule-1a label on the
Kekulé domain.  The `.realAtom`, `.ringDuplicate` and `.phantom` branches are total by
construction; the `.multipleBondDuplicate` branch is covered by the existing chemical totality
theorem, not by a new matching argument.

The generated-relation premise is retained so that this is an availability statement about the
actual `canonicalChildren` tree, not about arbitrary hand-built nodes. -/
theorem generated_rule1a_label_available_of_kekule
    (mol : RawMolecule) (root : Nat) (domain : KekuleGeneratedDomain mol)
    (node : CanonicalBranchNode)
    (_generated : CanonicalCenterTreeNode mol root node) :
    ∃ label, mol.canonicalRule1aLabelAuthoritative? node = some label :=
  canonicalRule1aLabelAuthoritative?_exists mol
    (mancudeRule1aSupported_of_kekuleDomain mol domain) node

/-- The exact label values are retained.  Real and ring duplicates keep the plain atomic-number
label `atomZAt / 1`, a phantom keeps `0 / 1`, and a multiple-bond duplicate is exactly the
authoritative mancude dispatch `mancudeRule1aLabelAuthoritative?` — no default and no atomic-number
substitution is introduced for the mancude branch. -/
theorem generated_rule1a_label_exact_of_kekule
    (mol : RawMolecule) (root : Nat) (domain : KekuleGeneratedDomain mol)
    (node : CanonicalBranchNode) (generated : CanonicalCenterTreeNode mol root node) :
    (∃ label : CIPAtomicLabel, mol.canonicalRule1aLabelAuthoritative? node = some label) ∧
    (node.provenance = .realAtom →
      mol.canonicalRule1aLabelAuthoritative? node =
        some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel)) ∧
    (∀ stored, node.provenance = .ringDuplicate stored →
      mol.canonicalRule1aLabelAuthoritative? node =
        some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel)) ∧
    (∀ stored, node.provenance = .phantom stored →
      mol.canonicalRule1aLabelAuthoritative? node =
        some ({ numerator := 0, denominator := 1 } : CIPAtomicLabel)) ∧
    (∀ stored, node.provenance = .multipleBondDuplicate stored →
      mol.canonicalRule1aLabelAuthoritative? node =
        mol.mancudeRule1aLabelAuthoritative? node.parent node.atom) := by
  refine ⟨generated_rule1a_label_available_of_kekule mol root domain node generated,
    ?_, ?_, ?_, ?_⟩
  · intro real
    exact GeneratedDuplicateAtomicLabelAvailability.realAtom_label mol node real
  · intro stored ring
    exact GeneratedDuplicateAtomicLabelAvailability.ringDuplicate_label mol node stored ring
  · intro stored phantom
    exact GeneratedDuplicateAtomicLabelAvailability.phantom_label mol node stored phantom
  · intro stored multiple
    simp [RawMolecule.canonicalRule1aLabelAuthoritative?, multiple]

/-! ## The original refusal boundary is unchanged -/

/-- The exact refusal boundary of `GeneratedDuplicateAtomicLabelAvailability`, re-exported
verbatim.  It needs no domain hypothesis: outside the Kekulé domain an absent label still means a
localized mancude multiple-bond duplicate whose simple-cycle shortcut and exhaustive matching
average both fail.  This module never totalizes that case. -/
theorem multipleBondDuplicate_label_none_iff_refusal (mol : RawMolecule)
    (node : CanonicalBranchNode)
    (stored : Nat) (provenance : node.provenance = .multipleBondDuplicate stored) :
    mol.canonicalRule1aLabelAuthoritative? node = none ↔
      containsUndirectedEdge mol.localizedMancudeEdges node.parent node.atom = true ∧
      mol.simpleMancudeCycle? node.parent node.atom = none ∧
      mol.generalMancudeRule1aLabelAuthoritative? node.parent node.atom = none :=
  GeneratedDuplicateAtomicLabelAvailability.multipleBondDuplicate_label_none_iff mol node stored
    provenance

/-- On the Kekulé domain no actually generated node can take the refusal branch.  This is the
concrete "availability" content: `none` is excluded on the domain, while the unconditional boundary
above still describes it outside the domain. -/
theorem generated_label_none_refuted_of_kekule
    (mol : RawMolecule) (root : Nat) (domain : KekuleGeneratedDomain mol)
    (node : CanonicalBranchNode) (generated : CanonicalCenterTreeNode mol root node)
    (absent : mol.canonicalRule1aLabelAuthoritative? node = none) : False := by
  obtain ⟨label, present⟩ :=
    generated_rule1a_label_available_of_kekule mol root domain node generated
  rw [present] at absent
  simp at absent

/-! ## Availability on the actual admitted profile -/

/-- For every actually generated center, the actual uncapped profile succeeds and every member of
its actual generated list has an authoritative Rule-1a label, a defined observation, and the
admission invariants (duplicate coordinates bounded, no phantom provenance), provided the molecule
lies in the Kekulé generated-mancude domain.

Nothing about profile success or label success is assumed: the profile is produced by
`CanonicalGeneratedProfileAdmission.profile?_complete` from `mol.WellFormed`, the root bound, and
the actual generation relation. -/
theorem profile?_rule1a_label_available_of_kekule
    (mol : RawMolecule) (root : Nat) (domain : KekuleGeneratedDomain mol)
    (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.root = root ∧
      p.center = center ∧
      center ∈ p.generated ∧
      (∀ node ∈ p.generated,
        ∃ label, mol.canonicalRule1aLabelAuthoritative? node = some label) ∧
      (∀ node ∈ p.generated, (observeNode p.frame node).isSome = true) ∧
      (∀ node ∈ p.generated,
        (∀ stored, node.provenance = .multipleBondDuplicate stored →
          stored + 1 ≤ node.history.tail.length) ∧
        (∀ stored, node.provenance = .ringDuplicate stored →
          stored + 1 ≤ node.history.tail.length) ∧
        (∀ stored, node.provenance ≠ .phantom stored)) := by
  obtain ⟨p, hprofile, hroot, hcenter, _hframe, hgenerated, hmember, _hpath, hadmission⟩ :=
    CanonicalGeneratedProfileAdmission.profile?_complete mol root domain.wellFormed rootBound
      center centerGenerated
  refine ⟨p, hprofile, hroot, hcenter, hmember, ?_, ?_, ?_⟩
  · intro node nodeMember
    rw [hgenerated] at nodeMember
    exact generated_rule1a_label_available_of_kekule mol root domain node
      (CanonicalGeneratedComparisonProfile.prefixTree_generated mol root (mol.atomCount + 1)
        0 node nodeMember)
  · intro node nodeMember
    exact (hadmission node nodeMember).2.2.2
  · intro node nodeMember
    exact ⟨(hadmission node nodeMember).1, (hadmission node nodeMember).2.1,
      (hadmission node nodeMember).2.2.1⟩

/-- The admitted comparison center itself has its exact authoritative label on the Kekulé domain. -/
theorem profile?_center_rule1a_available_of_kekule
    (mol : RawMolecule) (root : Nat) (domain : KekuleGeneratedDomain mol)
    (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.center = center ∧
      ∃ label, mol.canonicalRule1aLabelAuthoritative? p.center = some label := by
  obtain ⟨p, hprofile, _hroot, hcenter, hmember, labels, _observed, _bounds⟩ :=
    profile?_rule1a_label_available_of_kekule mol root domain rootBound center centerGenerated
  refine ⟨p, hprofile, hcenter, ?_⟩
  rw [hcenter]
  exact labels center hmember

/-! ## The runtime interface on the projected actual profile -/

/-- Discharge of `RawFramedGeneratedFuelInterface.FrameObserved` and `FrameLabelAvailable` from the
*actual* general profile produced by `CanonicalGeneratedComparisonProfile.profile?`.  The archived
all-real admission gate is not used; observation comes from the actual generated relation and
labels come from the Kekulé domain.

The profile and its success are produced by `profile?_complete`, so neither the collector nor any
label is assumed. -/
theorem interface_of_generated_profile_of_kekule
    (mol : RawMolecule) (root : Nat) (domain : KekuleGeneratedDomain mol)
    (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.root = root ∧
      FrameObserved mol (toFrameProfile p) p.root ∧
      FrameLabelAvailable mol p.root := by
  obtain ⟨p, hprofile, hpRoot, _hpCenter, _hpFrame, hpGenerated, _hcenterMem, _hpath,
    _hadmission⟩ :=
    CanonicalGeneratedProfileAdmission.profile?_complete mol root domain.wellFormed rootBound
      center centerGenerated
  have memberOfGenerated : ∀ {node : CanonicalBranchNode},
      CanonicalCenterTreeNode mol root node → node ∈ p.generated := by
    intro node generated
    exact mem_generated_of_tree domain.wellFormed rootBound hpGenerated generated
  refine ⟨p, hprofile, hpRoot, ?_, ?_⟩
  · intro cursor eligible
    have eligibleRoot : CanonicalCenterRerootCursor mol root cursor := by
      rw [hpRoot] at eligible
      exact eligible
    have nodeGenerated : CanonicalCenterTreeNode mol root cursor.node :=
      CanonicalCenterRerootCursor.node_generated eligibleRoot
    have nodeMem : cursor.node ∈ p.generated := memberOfGenerated nodeGenerated
    have previousGenerated : ∀ previous, cursor.previous? = some previous →
        previous ∈ p.generated := by
      intro previous hprevious
      exact memberOfGenerated
        (CanonicalCenterRerootCursor.previous_generated eligibleRoot previous hprevious)
    have previousNeighbor : ∀ previous, cursor.previous? = some previous →
        previous ∈ cursor.neighbors mol :=
      CanonicalCenterRerootCursor.previous_mem_neighbors eligibleRoot
    have observedNode : (observeNode (toFrameProfile p).frame cursor.node).isSome = true :=
      CanonicalGeneratedProfileAdmission.observe_isSome_of_generated mol root
        (toFrameProfile p).frame nodeGenerated
    exact GeneratedDuplicateAtomicLabelAvailability.cursor?_actual_of_membership mol
      (toFrameProfile p)
      (by simpa [toFrameProfile] using nodeMem)
      (fun previous hprevious => by
        simpa [toFrameProfile] using previousGenerated previous hprevious)
      previousNeighbor observedNode
  · intro cursor eligible
    have eligibleRoot : CanonicalCenterRerootCursor mol root cursor := by
      rw [hpRoot] at eligible
      exact eligible
    exact generated_rule1a_label_available_of_kekule mol root domain cursor.node
      (CanonicalCenterRerootCursor.node_generated eligibleRoot)

/-! ## Shipped Rule-1a runtime on actual cursors -/

/-- On the Kekulé domain the shipped `FrameRuntime.label?` with `authoritative := true` returns a
Rule-1a ordering for every pair of genuine oriented centre-tree cursors of an actual generated
centre.  The profile is the actual admitted general profile, projected to `FrameRuntime.Profile`;
observations and labels come from `FrameObserved` and `FrameLabelAvailable`.

The ordering is the comparison of the exact authoritative `CIPAtomicLabel` values; no default label
is inserted. -/
theorem frameRuntime_label?_rule1a_available_of_kekule
    (mol : RawMolecule) (root : Nat) (domain : KekuleGeneratedDomain mol)
    (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.root = root ∧
      ∃ ordering,
        FrameRuntime.label? mol (toFrameProfile p) true .rule1a
          (.actual left) (.actual right) = some ordering := by
  obtain ⟨p, hprofile, hpRoot, observed, labels⟩ :=
    interface_of_generated_profile_of_kekule mol root domain rootBound center centerGenerated
  refine ⟨p, hprofile, hpRoot, ?_⟩
  have observedRoot : FrameObserved mol (toFrameProfile p) root := by
    simpa [hpRoot] using observed
  have labelsRoot : FrameLabelAvailable mol root := by
    simpa [hpRoot] using labels
  have leftHeight : moleculeCursorHeight mol left ≤ 2 * mol.atomCount + 2 := by
    have bounded := moleculeCursorHeight_le_two_mul_atomCount_add_one rootBound
      domain.wellFormed leftEligible
    omega
  have rightHeight : moleculeCursorHeight mol right ≤ 2 * mol.atomCount + 2 := by
    have bounded := moleculeCursorHeight_le_two_mul_atomCount_add_one rootBound
      domain.wellFormed rightEligible
    omega
  have leftSupport : FramedCursorSupport mol (toFrameProfile p) root
      (2 * mol.atomCount + 2) (.actual left) :=
    .actual _ left leftEligible leftHeight
  have rightSupport : FramedCursorSupport mol (toFrameProfile p) root
      (2 * mol.atomCount + 2) (.actual right) :=
    .actual _ right rightEligible rightHeight
  exact label?_exists_of_interface mol (toFrameProfile p) root (2 * mol.atomCount + 2)
    observedRoot labelsRoot .rule1a (.actual left) (.actual right) leftSupport rightSupport

/-! ## Uniform stability on the structural interface -/

/-- **One fail-closed ordering at the explicit bound, stable verbatim at every larger fuel.**

The existential ordering is fixed first, and the fuel quantifier is inside its scope.  This is
uniform stability, not a family of independently chosen per-fuel orderings.  The only inputs are the
accepted interface of `RawFramedGeneratedFuelInterface` and the finite-graph bounds. -/
theorem failClosed_uniform_of_interface
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (root : Nat)
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (observedEligible : FrameObserved mol profile root)
    (labelEligible : FrameLabelAvailable mol root)
    {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right) :
    ∃ ordering,
      RawFramedFailClosedFuelBase.failClosedCompareBranch? mol profile true
          (2 * mol.atomCount + 2) .rule2 (.actual left) (.actual right) = some ordering ∧
      ∀ fuel, 2 * mol.atomCount + 2 ≤ fuel →
        RawFramedFailClosedFuelBase.failClosedCompareBranch? mol profile true
          fuel .rule2 (.actual left) (.actual right) = some ordering := by
  obtain ⟨ordering, computed⟩ :=
    failClosed_compareBranch_rule2_fuel_bound_of_interface mol profile root centerBound
      wellFormed bonding observedEligible labelEligible leftEligible rightEligible
  exact ⟨ordering, computed, fun fuel fuelBound =>
    RawFramedFailClosedFuelBase.failClosed_success_mono mol profile true .rule2 computed
      fuelBound⟩

/-- **One MAIN ordering at the explicit bound, stable verbatim at every larger fuel.**

The fail-closed candidate ordering obtained above is fixed once; every larger fuel returns the
same ordering through `failClosed_success_mono`, and `failClosed_refines_main` transports that same
ordering to the shipped `FrameRuntime.compareBranch?`. -/
theorem main_uniform_of_interface
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (root : Nat)
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (observedEligible : FrameObserved mol profile root)
    (labelEligible : FrameLabelAvailable mol root)
    {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right) :
    ∃ ordering,
      FrameRuntime.compareBranch? mol profile true
          (2 * mol.atomCount + 2) .rule2 (.actual left) (.actual right) = some ordering ∧
      ∀ fuel, 2 * mol.atomCount + 2 ≤ fuel →
        FrameRuntime.compareBranch? mol profile true
          fuel .rule2 (.actual left) (.actual right) = some ordering := by
  obtain ⟨ordering, atBound, stable⟩ :=
    failClosed_uniform_of_interface mol profile root centerBound wellFormed bonding
      observedEligible labelEligible leftEligible rightEligible
  refine ⟨ordering, ?_, ?_⟩
  · exact RawFramedFailClosedFuelBase.failClosed_refines_main mol profile true .rule2
      (2 * mol.atomCount + 2) (.actual left) (.actual right) ordering atBound
  · intro fuel fuelBound
    exact RawFramedFailClosedFuelBase.failClosed_refines_main mol profile true .rule2 fuel
      (.actual left) (.actual right) ordering (stable fuel fuelBound)

/-! ## Uniform stability on the Kekulé generated-mancude domain -/

/-- **Fail-closed uniform stability on the broader Kekulé domain.**  For an actual generated
centre and actual ligand cursors, there is one ordering produced at fuel `2 * atomCount + 2` and
the same ordering is produced at every larger fuel.  The profile is the actual admitted general
profile, projected to the runtime record; no archived all-real admission and no `nonMancude` scope
is used. -/
theorem generated_profile_failClosed_uniform_of_kekule
    (mol : RawMolecule) (root : Nat) (domain : KekuleGeneratedDomain mol)
    (rootBound : root < mol.atomCount)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.root = root ∧
      ∃ ordering,
        RawFramedFailClosedFuelBase.failClosedCompareBranch? mol (toFrameProfile p) true
            (2 * mol.atomCount + 2) .rule2 (.actual left) (.actual right) = some ordering ∧
        ∀ fuel, 2 * mol.atomCount + 2 ≤ fuel →
          RawFramedFailClosedFuelBase.failClosedCompareBranch? mol (toFrameProfile p) true
            fuel .rule2 (.actual left) (.actual right) = some ordering := by
  obtain ⟨p, hprofile, hpRoot, observed, labels⟩ :=
    interface_of_generated_profile_of_kekule mol root domain rootBound center centerGenerated
  refine ⟨p, hprofile, hpRoot, ?_⟩
  have observedRoot : FrameObserved mol (toFrameProfile p) root := by
    simpa [hpRoot] using observed
  have labelsRoot : FrameLabelAvailable mol root := by
    simpa [hpRoot] using labels
  have leftEligible : CanonicalCenterRerootCursor mol root left :=
    occurrenceLigandCursor_eligible centerGenerated leftMember
  have rightEligible : CanonicalCenterRerootCursor mol root right :=
    occurrenceLigandCursor_eligible centerGenerated rightMember
  exact failClosed_uniform_of_interface mol (toFrameProfile p) root rootBound
    domain.wellFormed bonding observedRoot labelsRoot leftEligible rightEligible

/-- **MAIN uniform stability on the broader Kekulé domain.**  The shipped
`FrameRuntime.compareBranch?` produces the same ordering at the explicit bound and at every larger
fuel.  The production comparator is unchanged. -/
theorem generated_profile_main_uniform_of_kekule
    (mol : RawMolecule) (root : Nat) (domain : KekuleGeneratedDomain mol)
    (rootBound : root < mol.atomCount)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.root = root ∧
      ∃ ordering,
        FrameRuntime.compareBranch? mol (toFrameProfile p) true
            (2 * mol.atomCount + 2) .rule2 (.actual left) (.actual right) = some ordering ∧
        ∀ fuel, 2 * mol.atomCount + 2 ≤ fuel →
          FrameRuntime.compareBranch? mol (toFrameProfile p) true
            fuel .rule2 (.actual left) (.actual right) = some ordering := by
  obtain ⟨p, hprofile, hpRoot, observed, labels⟩ :=
    interface_of_generated_profile_of_kekule mol root domain rootBound center centerGenerated
  refine ⟨p, hprofile, hpRoot, ?_⟩
  have observedRoot : FrameObserved mol (toFrameProfile p) root := by
    simpa [hpRoot] using observed
  have labelsRoot : FrameLabelAvailable mol root := by
    simpa [hpRoot] using labels
  have leftEligible : CanonicalCenterRerootCursor mol root left :=
    occurrenceLigandCursor_eligible centerGenerated leftMember
  have rightEligible : CanonicalCenterRerootCursor mol root right :=
    occurrenceLigandCursor_eligible centerGenerated rightMember
  exact main_uniform_of_interface mol (toFrameProfile p) root rootBound
    domain.wellFormed bonding observedRoot labelsRoot leftEligible rightEligible

/-! ## Uniform stability on the earlier non-mancude domain -/

/-- **Fail-closed uniform stability on `NonMancudeGeneratedDuplicates`.**  The interface of
`RawFramedGeneratedFuelInterface` is reused unchanged; only the stronger existential shape is new,
so both domains expose the same uniform endpoint. -/
theorem generated_profile_failClosed_uniform_of_nonMancude
    (mol : RawMolecule) (root : Nat)
    (wellFormed : mol.WellFormed) (rootBound : root < mol.atomCount)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.root = root ∧
      ∃ ordering,
        RawFramedFailClosedFuelBase.failClosedCompareBranch? mol (toFrameProfile p) true
            (2 * mol.atomCount + 2) .rule2 (.actual left) (.actual right) = some ordering ∧
        ∀ fuel, 2 * mol.atomCount + 2 ≤ fuel →
          RawFramedFailClosedFuelBase.failClosedCompareBranch? mol (toFrameProfile p) true
            fuel .rule2 (.actual left) (.actual right) = some ordering := by
  obtain ⟨p, hprofile, hpRoot, observed, labels⟩ :=
    interface_of_generated_profile mol root wellFormed rootBound center centerGenerated nonMancude
  refine ⟨p, hprofile, hpRoot, ?_⟩
  have observedRoot : FrameObserved mol (toFrameProfile p) root := by
    simpa [hpRoot] using observed
  have labelsRoot : FrameLabelAvailable mol root := by
    simpa [hpRoot] using labels
  have leftEligible : CanonicalCenterRerootCursor mol root left :=
    occurrenceLigandCursor_eligible centerGenerated leftMember
  have rightEligible : CanonicalCenterRerootCursor mol root right :=
    occurrenceLigandCursor_eligible centerGenerated rightMember
  exact failClosed_uniform_of_interface mol (toFrameProfile p) root rootBound
    wellFormed bonding observedRoot labelsRoot leftEligible rightEligible

/-- **MAIN uniform stability on `NonMancudeGeneratedDuplicates`.** -/
theorem generated_profile_main_uniform_of_nonMancude
    (mol : RawMolecule) (root : Nat)
    (wellFormed : mol.WellFormed) (rootBound : root < mol.atomCount)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.root = root ∧
      ∃ ordering,
        FrameRuntime.compareBranch? mol (toFrameProfile p) true
            (2 * mol.atomCount + 2) .rule2 (.actual left) (.actual right) = some ordering ∧
        ∀ fuel, 2 * mol.atomCount + 2 ≤ fuel →
          FrameRuntime.compareBranch? mol (toFrameProfile p) true
            fuel .rule2 (.actual left) (.actual right) = some ordering := by
  obtain ⟨p, hprofile, hpRoot, observed, labels⟩ :=
    interface_of_generated_profile mol root wellFormed rootBound center centerGenerated nonMancude
  refine ⟨p, hprofile, hpRoot, ?_⟩
  have observedRoot : FrameObserved mol (toFrameProfile p) root := by
    simpa [hpRoot] using observed
  have labelsRoot : FrameLabelAvailable mol root := by
    simpa [hpRoot] using labels
  have leftEligible : CanonicalCenterRerootCursor mol root left :=
    occurrenceLigandCursor_eligible centerGenerated leftMember
  have rightEligible : CanonicalCenterRerootCursor mol root right :=
    occurrenceLigandCursor_eligible centerGenerated rightMember
  exact main_uniform_of_interface mol (toFrameProfile p) root rootBound
    wellFormed bonding observedRoot labelsRoot leftEligible rightEligible

end TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability

/-! ## Kernel-authority guards (core) -/

assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.KekuleGeneratedDomain
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.KekuleGeneratedDomain.wellFormed
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.KekuleGeneratedDomain.bondRecordsUnique
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.KekuleGeneratedDomain.kekuleAdmissible
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.mancudeRule1aSupported_of_kekuleDomain
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.generated_rule1a_label_available_of_kekule
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.generated_rule1a_label_exact_of_kekule
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.multipleBondDuplicate_label_none_iff_refusal
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.generated_label_none_refuted_of_kekule
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.profile?_rule1a_label_available_of_kekule
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.profile?_center_rule1a_available_of_kekule
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.interface_of_generated_profile_of_kekule
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.frameRuntime_label?_rule1a_available_of_kekule
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.failClosed_uniform_of_interface
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.main_uniform_of_interface
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.generated_profile_failClosed_uniform_of_kekule
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.generated_profile_main_uniform_of_kekule
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.generated_profile_failClosed_uniform_of_nonMancude
assert_kernel_only
  TetraStereo.OneCenter.GeneratedMancudeRuntimeAvailability.generated_profile_main_uniform_of_nonMancude
