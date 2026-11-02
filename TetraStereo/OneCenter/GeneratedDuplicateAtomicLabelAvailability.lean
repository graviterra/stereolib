import TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission
import TetraStereo.OneCenter.CIPAuthoritativeBranchComparator
import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.OneCenter.CanonicalComparisonFrame

/-!
# Exact Rule-1a label availability on the actual generated duplicate domain

The uncapped authoritative Rule-1a node label

```lean
mol.canonicalRule1aLabelAuthoritative? node
```

is total on `.realAtom`, `.ringDuplicate` and `.phantom` nodes by construction.  The only
refusing constructor is `.multipleBondDuplicate`: it delegates to

```lean
mol.mancudeRule1aLabelAuthoritative? node.parent node.atom
```

which can return `none` only after the edge guard
`containsUndirectedEdge mol.localizedMancudeEdges node.parent node.atom` is *true* and both the
simple-cycle shortcut and the exhaustive matching average fail.

This module isolates, on the actual `canonicalChildren` generation relation:

* the exact executable refusal boundary
  (`multipleBondDuplicate_label_none_iff`);
* the sufficient executable non-mancude scope that removes the refusing branch for every actually
  generated duplicate: no generated multiple-bond duplicate lies on a localized mancude edge
  (`NonMancudeGeneratedDuplicates`).  Ring duplicates, ordinary (non-conjugated) multiple-bond
  duplicates, real atoms and the empty phantom case all remain inside the domain.  This condition
  is sufficient, not necessary: a mancude duplicate can still receive a label from the simple-cycle
  shortcut or from the exhaustive matching average, as the exact boundary theorem records;
* availability of the actual authoritative label for every member of the actual generated profile
  returned by `CanonicalGeneratedComparisonProfile.profile?`, using the already proved admission
  theorem rather than assuming a successful key or profile;
* the structural coordinates of a generated multiple-bond duplicate, keeping the stored attachment
  depth `parent.depth` explicitly separate from the comparison frame's represented coordinate.

Nothing here totalizes a refusal: a `.multipleBondDuplicate` whose edge *is* mancude still returns
whatever `mancudeRule1aLabelAuthoritative?` returns, including `none`, and
`multipleBondDuplicate_label_none_iff` states that refusal exactly.
-/

/-! ## The executable domain condition -/

/-- No actually generated multiple-bond duplicate is attached across a localized mancude edge.

This is an executable Bool condition about the same `localizedMancudeEdges` list consumed by
`mancudeRule1aLabelAuthoritative?`.  It is not a claim that a label exists, and it does not include
any cycle/matching success hypothesis.  It is a sufficient scope, not a necessary one: mancude
duplicates whose simple-cycle shortcut or exhaustive matching average succeeds are still labelled,
and this predicate deliberately says nothing about them. -/
def NonMancudeGeneratedDuplicates (mol : RawMolecule) (root : Nat) : Prop :=
  ∀ node, CanonicalCenterTreeNode mol root node →
    ∀ stored, node.provenance = .multipleBondDuplicate stored →
      containsUndirectedEdge mol.localizedMancudeEdges node.parent node.atom = false

/-! ## Exact labels of the three total provenance classes -/

/-- A real occurrence receives its plain atomic-number label. -/
theorem realAtom_label (mol : RawMolecule) (node : CanonicalBranchNode)
    (real : node.provenance = .realAtom) :
    mol.canonicalRule1aLabelAuthoritative? node =
      some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) := by
  simp [RawMolecule.canonicalRule1aLabelAuthoritative?, real]

/-- A ring duplicate receives its plain atomic-number label: the authoritative implementation does
not run the mancude average for ring closures. -/
theorem ringDuplicate_label (mol : RawMolecule) (node : CanonicalBranchNode) (stored : Nat)
    (ring : node.provenance = .ringDuplicate stored) :
    mol.canonicalRule1aLabelAuthoritative? node =
      some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) := by
  simp [RawMolecule.canonicalRule1aLabelAuthoritative?, ring]

/-- A raw phantom occurrence receives the zero label. -/
theorem phantom_label (mol : RawMolecule) (node : CanonicalBranchNode) (stored : Nat)
    (phantom : node.provenance = .phantom stored) :
    mol.canonicalRule1aLabelAuthoritative? node =
      some ({ numerator := 0, denominator := 1 } : CIPAtomicLabel) := by
  simp [RawMolecule.canonicalRule1aLabelAuthoritative?, phantom]

/-! ## The refusing constructor -/

/-- A multiple-bond duplicate off the localized mancude graph receives the plain atomic-number
label.  This is the only branch of `canonicalRule1aLabelAuthoritative?` whose success depends on
molecular data, and this is the exact condition that skips it. -/
theorem multipleBondDuplicate_label_of_nonMancude (mol : RawMolecule)
    (node : CanonicalBranchNode) (stored : Nat)
    (provenance : node.provenance = .multipleBondDuplicate stored)
    (nonMancude : containsUndirectedEdge mol.localizedMancudeEdges node.parent node.atom = false) :
    mol.canonicalRule1aLabelAuthoritative? node =
      some ({ numerator := mol.atomZAt node.atom, denominator := 1 } : CIPAtomicLabel) := by
  simp [RawMolecule.canonicalRule1aLabelAuthoritative?, provenance,
    RawMolecule.mancudeRule1aLabelAuthoritative?, nonMancude]

/-- A simple localized cycle duplicate receives the exact simple-cycle label. -/
theorem multipleBondDuplicate_label_of_simpleCycle (mol : RawMolecule)
    (node : CanonicalBranchNode) (stored : Nat) (cycle : List Nat) (alternate : Nat)
    (provenance : node.provenance = .multipleBondDuplicate stored)
    (localized : containsUndirectedEdge mol.localizedMancudeEdges node.parent node.atom = true)
    (cycleEq : mol.simpleMancudeCycle? node.parent node.atom = some (cycle, alternate)) :
    mol.canonicalRule1aLabelAuthoritative? node =
      some (mol.simpleMancudeCycleLabel node.atom alternate cycle) := by
  simp [RawMolecule.canonicalRule1aLabelAuthoritative?, provenance,
    RawMolecule.mancudeRule1aLabelAuthoritative?, localized, cycleEq]

/-- **Exact refusal boundary.**  The authoritative Rule-1a label of a multiple-bond duplicate is
absent if and only if the duplicated atom is attached by a localized mancude edge and both the
simple-cycle shortcut and the exhaustive matching average fail.

The right-hand side is the actual executable refusal predicate; no aromatic or unresolved case is
reinterpreted as an atomic label. -/
theorem multipleBondDuplicate_label_none_iff (mol : RawMolecule) (node : CanonicalBranchNode)
    (stored : Nat) (provenance : node.provenance = .multipleBondDuplicate stored) :
    mol.canonicalRule1aLabelAuthoritative? node = none ↔
      containsUndirectedEdge mol.localizedMancudeEdges node.parent node.atom = true ∧
      mol.simpleMancudeCycle? node.parent node.atom = none ∧
      mol.generalMancudeRule1aLabelAuthoritative? node.parent node.atom = none := by
  constructor
  · intro absent
    by_cases localized : containsUndirectedEdge mol.localizedMancudeEdges
        node.parent node.atom = true
    · refine ⟨localized, ?_, ?_⟩
      · cases cycleEq : mol.simpleMancudeCycle? node.parent node.atom with
        | none => rfl
        | some cycleData =>
            obtain ⟨cycle, alternate⟩ := cycleData
            have present := multipleBondDuplicate_label_of_simpleCycle mol node stored cycle
              alternate provenance localized cycleEq
            rw [present] at absent
            cases absent
      · cases generalEq : mol.generalMancudeRule1aLabelAuthoritative? node.parent node.atom with
        | none => rfl
        | some label =>
            have simpleNone : mol.simpleMancudeCycle? node.parent node.atom = none := by
              by_contra notNone
              cases cycleEq : mol.simpleMancudeCycle? node.parent node.atom with
              | none => exact notNone cycleEq
              | some cycleData =>
                  obtain ⟨cycle, alternate⟩ := cycleData
                  have present := multipleBondDuplicate_label_of_simpleCycle mol node stored
                    cycle alternate provenance localized cycleEq
                  rw [present] at absent
                  cases absent
            have present : mol.canonicalRule1aLabelAuthoritative? node = some label := by
              simp [RawMolecule.canonicalRule1aLabelAuthoritative?, provenance,
                RawMolecule.mancudeRule1aLabelAuthoritative?, localized, simpleNone, generalEq]
            rw [present] at absent
            cases absent
    · have nonMancude : containsUndirectedEdge mol.localizedMancudeEdges
          node.parent node.atom = false := Bool.eq_false_of_not_eq_true localized
      have present := multipleBondDuplicate_label_of_nonMancude mol node stored provenance
        nonMancude
      rw [present] at absent
      cases absent
  · intro ⟨localized, simpleNone, generalNone⟩
    simp [RawMolecule.canonicalRule1aLabelAuthoritative?, provenance,
      RawMolecule.mancudeRule1aLabelAuthoritative?, localized, simpleNone, generalNone]

/-! ## Availability on the generated relation -/

/-- Every actually generated node has an authoritative Rule-1a label under the non-mancude
generated-duplicate domain.  The `.realAtom`, `.ringDuplicate` and `.phantom` cases are total by
construction; the multiple-bond case is the non-mancude branch above. -/
theorem generated_rule1a_label_available_of_nonMancude (mol : RawMolecule) (root : Nat)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    (node : CanonicalBranchNode)
    (generated : CanonicalCenterTreeNode mol root node) :
    ∃ label, mol.canonicalRule1aLabelAuthoritative? node = some label := by
  cases provenance : node.provenance with
  | realAtom =>
      exact ⟨_, realAtom_label mol node provenance⟩
  | multipleBondDuplicate stored =>
      exact ⟨_, multipleBondDuplicate_label_of_nonMancude mol node stored provenance
        (nonMancude node generated stored provenance)⟩
  | ringDuplicate stored =>
      exact ⟨_, ringDuplicate_label mol node stored provenance⟩
  | phantom stored =>
      exact ⟨_, phantom_label mol node stored provenance⟩

/-- If a generated node has no authoritative Rule-1a label, it must be an actual multiple-bond
duplicate whose attached edge is a localized mancude edge.  This is the necessity direction: an
unavailable label is never reinterpreted as an atomic value. -/
theorem generated_label_none_imp_multipleBond_mancude (mol : RawMolecule) (root : Nat)
    (node : CanonicalBranchNode) (_generated : CanonicalCenterTreeNode mol root node)
    (absent : mol.canonicalRule1aLabelAuthoritative? node = none) :
    ∃ stored, node.provenance = .multipleBondDuplicate stored ∧
      containsUndirectedEdge mol.localizedMancudeEdges node.parent node.atom = true := by
  cases provenance : node.provenance with
  | realAtom =>
      have present := realAtom_label mol node provenance
      rw [present] at absent
      cases absent
  | multipleBondDuplicate stored =>
      have boundary := (multipleBondDuplicate_label_none_iff mol node stored provenance).1 absent
      exact ⟨stored, rfl, boundary.1⟩
  | ringDuplicate stored =>
      have present := ringDuplicate_label mol node stored provenance
      rw [present] at absent
      cases absent
  | phantom stored =>
      have present := phantom_label mol node stored provenance
      rw [present] at absent
      cases absent

/-! ## Structural coordinates of a generated multiple-bond duplicate -/

/-- The stored multiple-bond coordinate is exactly the attachment depth `parent.depth`, while the
observable comparison coordinate is the framed duplicate distance.  These are two separate facts;
the attachment depth is not identified with any represented-atom 2013 distance. -/
theorem generated_multipleBondDuplicate_coordinates (mol : RawMolecule) {root : Nat}
    {parent child : CanonicalBranchNode}
    (parentGenerated : CanonicalCenterTreeNode mol root parent)
    (childMember : child ∈ mol.canonicalChildren parent)
    (stored : Nat)
    (provenance : child.provenance = .multipleBondDuplicate stored) :
    stored = parent.depth ∧
      (∀ frame : CanonicalComparisonFrame.Frame,
        observeNode frame child = some (frame.duplicateDistance child stored)) := by
  refine ⟨mol.canonicalChildren_multipleBondDuplicate_distance parent child childMember stored
    provenance, ?_⟩
  intro frame
  have bounds := CanonicalGeneratedProfileAdmission.child_duplicate_bound mol parentGenerated
    childMember
  exact multiple_observation frame child stored provenance (bounds.1 stored provenance)

/-! ## Availability on the actual admitted profile -/

/-- For every actually generated center, the actual uncapped profile succeeds and every member of
its actual generated list has an authoritative Rule-1a label and a defined observation, provided the
generated multiple-bond duplicates are non-mancude.

No success of the profile, of the collector, or of any label is assumed: the profile is produced by
`CanonicalGeneratedProfileAdmission.profile?_complete` from `mol.WellFormed`, the root bound, and the
actual generation relation. -/
theorem profile?_rule1a_label_available_of_nonMancude (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (nonMancude : NonMancudeGeneratedDuplicates mol root) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.root = root ∧
      p.center = center ∧
      center ∈ p.generated ∧
      (∀ node ∈ p.generated,
        ∃ label, mol.canonicalRule1aLabelAuthoritative? node = some label) ∧
      (∀ node ∈ p.generated, (observeNode p.frame node).isSome = true) := by
  obtain ⟨p, hprofile, hroot, hcenter, _hframe, hgenerated, hmember, _hpath, hadmission⟩ :=
    CanonicalGeneratedProfileAdmission.profile?_complete mol root well rootBound center
      centerGenerated
  refine ⟨p, hprofile, hroot, hcenter, hmember, ?_, ?_⟩
  · intro node nodeMember
    rw [hgenerated] at nodeMember
    exact generated_rule1a_label_available_of_nonMancude mol root nonMancude node
      (CanonicalGeneratedComparisonProfile.prefixTree_generated mol root
        (mol.atomCount + 1) 0 node nodeMember)
  · intro node nodeMember
    exact (hadmission node nodeMember).2.2.2

/-- The admitted comparison center itself has an authoritative Rule-1a label. -/
theorem profile?_center_rule1a_available_of_nonMancude (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (nonMancude : NonMancudeGeneratedDuplicates mol root) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.center = center ∧
      ∃ label, mol.canonicalRule1aLabelAuthoritative? p.center = some label := by
  obtain ⟨p, hprofile, _hroot, hcenter, hmember, labels, _observed⟩ :=
    profile?_rule1a_label_available_of_nonMancude mol root well rootBound center
      centerGenerated nonMancude
  refine ⟨p, hprofile, hcenter, ?_⟩
  rw [hcenter]
  exact labels center hmember

/-! ## Reusing the archived runtime profile type

`FrameRuntime.Profile` is the archived triple `⟨center, frame, generated⟩`, while the new
generated profile also keeps the original root coordinate.  Rather than defining a second
comparator, the new profile is projected onto the archived type, and the exact interface consumed
by the shipped `FrameRuntime.label?` on Rule 1a is stated explicitly: both actual cursors are
observed by the profile, and both original nodes have an authoritative Rule-1a label. -/

/-- Projection of the actual generated profile onto the archived runtime profile type.  This is a
plain field selection: the archived type has no separate root coordinate. -/
def toRuntimeProfile (p : CanonicalGeneratedComparisonProfile.Profile) : FrameRuntime.Profile :=
  ⟨p.center, p.frame, p.generated⟩

@[simp] theorem toRuntimeProfile_center (p : CanonicalGeneratedComparisonProfile.Profile) :
    (toRuntimeProfile p).center = p.center := rfl

@[simp] theorem toRuntimeProfile_frame (p : CanonicalGeneratedComparisonProfile.Profile) :
    (toRuntimeProfile p).frame = p.frame := rfl

@[simp] theorem toRuntimeProfile_generated (p : CanonicalGeneratedComparisonProfile.Profile) :
    (toRuntimeProfile p).generated = p.generated := rfl

/-- The node of an oriented center-tree cursor is generated from the center. -/
theorem CanonicalCenterRerootCursor.node_generated {mol : RawMolecule} {center : Nat}
    {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol center cursor) :
    CanonicalCenterTreeNode mol center cursor.node := by
  cases eligible with
  | @descending parent node parentGenerated member =>
      exact .child parentGenerated member
  | @ascending node child nodeGenerated member => exact nodeGenerated

/-- The remembered previous node of an oriented center-tree cursor is generated from the center. -/
theorem CanonicalCenterRerootCursor.previous_generated {mol : RawMolecule} {center : Nat}
    {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol center cursor) :
    ∀ previous, cursor.previous? = some previous →
      CanonicalCenterTreeNode mol center previous := by
  cases eligible with
  | @descending parent node parentGenerated member =>
      intro previous hprevious
      have same : parent = previous := by simpa using hprevious
      rw [← same]
      exact parentGenerated
  | @ascending node child nodeGenerated member =>
      intro previous hprevious
      have same : child = previous := by simpa using hprevious
      rw [← same]
      exact .child nodeGenerated member

/-- The remembered previous node of an oriented center-tree cursor is an actual neighbor of the
cursor node, hence passes the shipped incoming-edge guard. -/
theorem CanonicalCenterRerootCursor.previous_mem_neighbors {mol : RawMolecule} {center : Nat}
    {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol center cursor) :
    ∀ previous, cursor.previous? = some previous →
      previous ∈ cursor.neighbors mol := by
  cases eligible with
  | @descending parent node parentGenerated member =>
      intro previous hprevious
      have same : parent = previous := by simpa using hprevious
      rw [← same]
      have recovered := canonicalOriginalParent?_eq_some_of_child parentGenerated member
      simp [CanonicalRerootCursor.neighbors, recovered]
  | @ascending node child nodeGenerated member =>
      intro previous hprevious
      have same : child = previous := by simpa using hprevious
      rw [← same]
      simp [CanonicalRerootCursor.neighbors, member]

/-- A genuine actual cursor passes the shipped `FrameRuntime.cursor?` guards whenever its node and
remembered previous node are members of the profile's generated list and the node is observed.

This is the structural cursor step used by the runtime: it does not assume that `cursor?` succeeds,
and it does not replace the shipped definition. -/
theorem cursor?_actual_of_membership (mol : RawMolecule) (profile : FrameRuntime.Profile)
    {cursor : CanonicalRerootCursor}
    (nodeMember : cursor.node ∈ profile.generated)
    (previousGenerated : ∀ previous, cursor.previous? = some previous →
      previous ∈ profile.generated)
    (previousNeighbor : ∀ previous, cursor.previous? = some previous →
      previous ∈ cursor.neighbors mol)
    (observed : (observeNode profile.frame cursor.node).isSome = true) :
    ∃ distance, FrameRuntime.cursor? mol profile (.actual cursor) = some distance := by
  have observedSome : ∃ distance, observeNode profile.frame cursor.node = some distance := by
    cases value : observeNode profile.frame cursor.node with
    | none => simp [value] at observed
    | some distance => exact ⟨distance, rfl⟩
  obtain ⟨distance, observedEq⟩ := observedSome
  have nodeContains : profile.generated.contains cursor.node = true := by
    rw [List.contains_eq_mem, decide_eq_true_eq]
    exact nodeMember
  cases previousEq : cursor.previous? with
  | none =>
      refine ⟨distance, ?_⟩
      change (if !profile.generated.contains cursor.node then none else
        if !(cursor.previous?.all fun previous =>
            profile.generated.contains previous && (cursor.neighbors mol).contains previous)
          then none else
        observeNode profile.frame cursor.node) = some distance
      rw [nodeContains, previousEq]
      simp [observedEq]
  | some previous =>
      have previousMember := previousGenerated previous previousEq
      have neighbor := previousNeighbor previous previousEq
      refine ⟨distance, ?_⟩
      change (if !profile.generated.contains cursor.node then none else
        if !(cursor.previous?.all fun previous =>
            profile.generated.contains previous && (cursor.neighbors mol).contains previous)
          then none else
        observeNode profile.frame cursor.node) = some distance
      rw [nodeContains, previousEq]
      simp [previousMember, neighbor, observedEq]

/-- The exact interface consumed by the shipped `FrameRuntime.label?` on Rule 1a: both actual
cursors are observed by the profile, and both original nodes have an authoritative Rule-1a label.
Nothing about a comparison result or a key is assumed. -/
def Rule1aRuntimeInterface (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (left right : CanonicalRerootCursor) : Prop :=
  (∃ leftDistance,
      FrameRuntime.cursor? mol profile (.actual left) = some leftDistance) ∧
  (∃ rightDistance,
      FrameRuntime.cursor? mol profile (.actual right) = some rightDistance) ∧
  (∃ leftLabel, mol.canonicalRule1aLabelAuthoritative? left.node = some leftLabel) ∧
  (∃ rightLabel, mol.canonicalRule1aLabelAuthoritative? right.node = some rightLabel)

/-- The interface above is exactly sufficient for the shipped `FrameRuntime.label?` to return a
Rule-1a ordering.  The proof unfolds the shipped definition; no second comparator is introduced. -/
theorem label?_rule1a_of_interface (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (left right : CanonicalRerootCursor)
    (interface : Rule1aRuntimeInterface mol profile left right) :
    ∃ ordering, FrameRuntime.label? mol profile true .rule1a
      (.actual left) (.actual right) = some ordering := by
  obtain ⟨⟨leftDistance, leftObserved⟩, ⟨rightDistance, rightObserved⟩,
    ⟨leftLabel, leftLabelEq⟩, ⟨rightLabel, rightLabelEq⟩⟩ := interface
  refine ⟨compareCIPAtomicLabel leftLabel rightLabel, ?_⟩
  simp [FrameRuntime.label?, leftObserved, rightObserved, FrameRuntime.Cursor.original,
    RawMolecule.compareCanonicalNodeRuleAuthoritative?, leftLabelEq, rightLabelEq]

/-! ## The shipped Rule-1a comparison on actual generated cursors -/

/-- On the non-mancude generated-duplicate domain, the shipped `FrameRuntime.label?` with
`authoritative := true` returns a Rule-1a ordering for every pair of genuine oriented center-tree
cursors of an actual generated center.

The profile is produced by the actual admission theorem; the cursor guards and the label
availability are derived, not assumed. -/
theorem frameRuntime_label?_rule1a_available_of_nonMancude (mol : RawMolecule) (root : Nat)
    (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    (left right : CanonicalRerootCursor)
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      ∃ ordering,
        FrameRuntime.label? mol (toRuntimeProfile p) true .rule1a
          (.actual left) (.actual right) = some ordering := by
  obtain ⟨p, hprofile, hroot, _hcenter, _hframe, hgenerated, _hmember, _hpath, hadmission⟩ :=
    CanonicalGeneratedProfileAdmission.profile?_complete mol root well rootBound center
      centerGenerated
  have complete : ∀ node, CanonicalCenterTreeNode mol p.root node → node ∈ p.generated := by
    intro node generatedNode
    rw [hroot] at generatedNode
    rw [hgenerated]
    exact (CanonicalGeneratedComparisonProfile.complete_tree_member_iff mol root
      (mol.atomCount + 1) well rootBound (Nat.le_refl _) node).2 generatedNode
  have observedOn : ∀ node ∈ p.generated, (observeNode p.frame node).isSome = true :=
    fun node nodeMember => (hadmission node nodeMember).2.2.2
  have labelsOn : ∀ node ∈ p.generated,
      ∃ label, mol.canonicalRule1aLabelAuthoritative? node = some label := by
    intro node nodeMember
    rw [hgenerated] at nodeMember
    exact generated_rule1a_label_available_of_nonMancude mol root nonMancude node
      (CanonicalGeneratedComparisonProfile.prefixTree_generated mol root (mol.atomCount + 1)
        0 node nodeMember)
  have leftGenerated : CanonicalCenterTreeNode mol root left.node :=
    CanonicalCenterRerootCursor.node_generated leftEligible
  have rightGenerated : CanonicalCenterTreeNode mol root right.node :=
    CanonicalCenterRerootCursor.node_generated rightEligible
  have leftMember : left.node ∈ p.generated :=
    complete left.node (by simpa [hroot] using leftGenerated)
  have rightMember : right.node ∈ p.generated :=
    complete right.node (by simpa [hroot] using rightGenerated)
  have leftPreviousGenerated : ∀ previous, left.previous? = some previous →
      previous ∈ p.generated := by
    intro previous hprevious
    exact complete previous (by
      simpa [hroot] using
        CanonicalCenterRerootCursor.previous_generated leftEligible previous hprevious)
  have rightPreviousGenerated : ∀ previous, right.previous? = some previous →
      previous ∈ p.generated := by
    intro previous hprevious
    exact complete previous (by
      simpa [hroot] using
        CanonicalCenterRerootCursor.previous_generated rightEligible previous hprevious)
  have leftPreviousNeighbor : ∀ previous, left.previous? = some previous →
      previous ∈ left.neighbors mol :=
    CanonicalCenterRerootCursor.previous_mem_neighbors leftEligible
  have rightPreviousNeighbor : ∀ previous, right.previous? = some previous →
      previous ∈ right.neighbors mol :=
    CanonicalCenterRerootCursor.previous_mem_neighbors rightEligible
  obtain ⟨leftDistance, leftCursor⟩ := cursor?_actual_of_membership mol (toRuntimeProfile p)
    leftMember leftPreviousGenerated leftPreviousNeighbor (observedOn left.node leftMember)
  obtain ⟨rightDistance, rightCursor⟩ := cursor?_actual_of_membership mol (toRuntimeProfile p)
    rightMember rightPreviousGenerated rightPreviousNeighbor (observedOn right.node rightMember)
  obtain ⟨leftLabel, leftLabelEq⟩ := labelsOn left.node leftMember
  obtain ⟨rightLabel, rightLabelEq⟩ := labelsOn right.node rightMember
  have interface : Rule1aRuntimeInterface mol (toRuntimeProfile p) left right :=
    ⟨⟨leftDistance, leftCursor⟩, ⟨rightDistance, rightCursor⟩,
      ⟨leftLabel, leftLabelEq⟩, ⟨rightLabel, rightLabelEq⟩⟩
  obtain ⟨ordering, hordering⟩ :=
    label?_rule1a_of_interface mol (toRuntimeProfile p) left right interface
  exact ⟨p, hprofile, ordering, hordering⟩

/-- The same shipped Rule-1a comparison on the actual center occurrence itself, whose actual
cursor has no remembered previous node.  This is the concrete constructor case: membership and
observation come from the admitted profile, and the label comes from the non-mancude domain. -/
theorem frameRuntime_center_label?_rule1a_available_of_nonMancude (mol : RawMolecule)
    (root : Nat) (well : mol.WellFormed) (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (nonMancude : NonMancudeGeneratedDuplicates mol root) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.center = center ∧
      ∃ ordering,
        FrameRuntime.label? mol (toRuntimeProfile p) true .rule1a
          (.actual ({ node := center, previous? := none } : CanonicalRerootCursor))
          (.actual ({ node := center, previous? := none } : CanonicalRerootCursor)) =
            some ordering := by
  obtain ⟨p, hprofile, _hroot, hcenter, hmember, labels, observed⟩ :=
    profile?_rule1a_label_available_of_nonMancude mol root well rootBound center centerGenerated
      nonMancude
  have cursorMember : (⟨center, none⟩ : CanonicalRerootCursor).node ∈ p.generated := by
    simpa using hmember
  have noPrevious : ∀ previous, (⟨center, none⟩ : CanonicalRerootCursor).previous? =
      some previous → previous ∈ p.generated := by
    intro previous hprevious
    simp at hprevious
  have noPreviousNeighbor : ∀ previous,
      (⟨center, none⟩ : CanonicalRerootCursor).previous? = some previous →
        previous ∈ (⟨center, none⟩ : CanonicalRerootCursor).neighbors mol := by
    intro previous hprevious
    simp at hprevious
  obtain ⟨distance, cursorObserved⟩ := cursor?_actual_of_membership mol (toRuntimeProfile p)
    cursorMember noPrevious noPreviousNeighbor (observed center hmember)
  obtain ⟨label, labelEq⟩ := labels center hmember
  have interface : Rule1aRuntimeInterface mol (toRuntimeProfile p)
      (⟨center, none⟩ : CanonicalRerootCursor) (⟨center, none⟩ : CanonicalRerootCursor) :=
    ⟨⟨distance, cursorObserved⟩, ⟨distance, cursorObserved⟩,
      ⟨label, labelEq⟩, ⟨label, labelEq⟩⟩
  obtain ⟨ordering, hordering⟩ :=
    label?_rule1a_of_interface mol (toRuntimeProfile p)
      (⟨center, none⟩ : CanonicalRerootCursor) (⟨center, none⟩ : CanonicalRerootCursor)
      interface
  exact ⟨p, hprofile, hcenter, ordering, hordering⟩

end TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.NonMancudeGeneratedDuplicates
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.realAtom_label
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.ringDuplicate_label
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.phantom_label
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.multipleBondDuplicate_label_of_nonMancude
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.multipleBondDuplicate_label_of_simpleCycle
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.multipleBondDuplicate_label_none_iff
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.generated_rule1a_label_available_of_nonMancude
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.generated_label_none_imp_multipleBond_mancude
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.generated_multipleBondDuplicate_coordinates
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.profile?_rule1a_label_available_of_nonMancude
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.profile?_center_rule1a_available_of_nonMancude
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.toRuntimeProfile
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.toRuntimeProfile_center
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.toRuntimeProfile_frame
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.toRuntimeProfile_generated
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.CanonicalCenterRerootCursor.node_generated
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.CanonicalCenterRerootCursor.previous_generated
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.CanonicalCenterRerootCursor.previous_mem_neighbors
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.cursor?_actual_of_membership
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.Rule1aRuntimeInterface
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.label?_rule1a_of_interface
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.frameRuntime_label?_rule1a_available_of_nonMancude
assert_kernel_only
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.frameRuntime_center_label?_rule1a_available_of_nonMancude
