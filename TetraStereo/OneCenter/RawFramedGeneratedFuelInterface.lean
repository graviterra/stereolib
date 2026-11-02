import TetraStereo.OneCenter.RawFramedConstitutionalFuelClosure
import TetraStereo.OneCenter.RawFramedFailClosedFuelBase
import TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-!
# Fuel stability of the framed comparator on generated actual profiles

The archived `FrameRuntime.Profile` is the all-real record
`CanonicalTreeProfile.Profile = ⟨center, frame, generated⟩`.  The runtime comparator reads only
`frame` and `generated`.  Consequently the general actual occurrence profile
`CanonicalGeneratedComparisonProfile.Profile = ⟨root, center, frame, generated⟩` can be projected
to the archived record (`toFrameProfile`) without changing any runtime step, even though the
archived executable admission gate `CanonicalTreeProfile.profile?` rejects ring and multiple-bond
duplicates and hence does not accept the projected record.

The archived totality proofs consume an admitted-profile premise only through two derived facts
about the observed cursors:

* every eligible actual cursor is observed by `FrameRuntime.cursor?`;
* every eligible actual cursor's node carries an authoritative Rule-1a label.

This module isolates those as the structural interface `FrameObserved` and `FrameLabelAvailable`,
proves the fail-closed recursive totality chain over an arbitrary `FrameRuntime.Profile` from that
interface (plus `root < atomCount`, `mol.WellFormed` and the P-92 width premise), and discharges
the interface from the *general* actual profile produced by
`CanonicalGeneratedComparisonProfile.profile?`.

The final results concern the shipped fail-closed candidate and the shipped actual comparator on
the projected actual profile, at the explicit fuel `2 * atomCount + 2` and at every larger fuel.
No second comparator is introduced, no archived admission premise is assumed, and the multiple-bond
mancude refusal is preserved as the explicit domain condition `NonMancudeGeneratedDuplicates`.

## Main results

* `label?_exists_of_interface`, `pairLabels?_exists_of_interface`, `ranked?_exists_of_interface`,
  `nextPairs?_exists_of_interface`, `compareRule?_exists_of_interface` — the recursive Rule
  totality chain over the structural interface;
* `failClosed_compareBranch_exists_of_interface` — fail-closed candidate totality at every fuel;
* `failClosed_compareBranch_rule2_fuel_bound_of_interface` — the explicit `2 * atomCount + 2`
  bound;
* `interface_of_generated_profile` — interface discharge, with the profile *constructed* by the
  actual admission theorem `CanonicalGeneratedProfileAdmission.profile?_complete`;
* `generated_profile_failClosed_compareBranch_rule2` and
  `generated_profile_main_compareBranch_rule2` — candidate and actual runtime totality on the
  projected actual profile;
* `generated_profile_failClosed_compareBranch_rule2_ge` and
  `generated_profile_main_compareBranch_rule2_ge` — the same results at every larger fuel.
-/

namespace TetraStereo.OneCenter

namespace RawFramedGeneratedFuelInterface

open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.FrameRuntime
open TetraStereo.OneCenter.RawFramedConstitutionalFuelClosure
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.OneCenter.CanonicalGeneratedComparisonProfile
open TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability
open TetraStereo.OneCenter.CanonicalComparisonFrame

/-! ## The minimal structural interface -/

/-- Every actual cursor eligible in the centre tree rooted at `root` is observed by the runtime on
the supplied profile.  This is the only profile-dependent input to `cursor?` totality used by the
archived proof. -/
def FrameObserved (mol : RawMolecule) (profile : FrameRuntime.Profile) (root : Nat) : Prop :=
  ∀ cursor : CanonicalRerootCursor,
    CanonicalCenterRerootCursor mol root cursor →
      ∃ distance, FrameRuntime.cursor? mol profile (.actual cursor) = some distance

/-- Every actual cursor eligible in the centre tree rooted at `root` carries an authoritative
Rule-1a label.  This is the only profile-dependent input to `label?` totality used by the archived
proof. -/
def FrameLabelAvailable (mol : RawMolecule) (root : Nat) : Prop :=
  ∀ cursor : CanonicalRerootCursor,
    CanonicalCenterRerootCursor mol root cursor →
      ∃ label, mol.canonicalRule1aLabelAuthoritative? cursor.node = some label

/-! ## Supported-cursor observation and labels -/

/-- A supported cursor is observed whenever every eligible actual cursor is. -/
theorem framedsupport_observed_of_interface
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (root : Nat)
    (observedEligible : FrameObserved mol profile root) :
    ∀ (fuel : Nat) (cursor : FrameRuntime.Cursor),
      FramedCursorSupport mol profile root fuel cursor →
      ∃ distance, FrameRuntime.cursor? mol profile cursor = some distance := by
  intro fuel cursor support
  cases support with
  | padding parent parentObserved =>
      rcases parentObserved with ⟨distance, distanceEq⟩
      exact ⟨distance + 1, by simp [FrameRuntime.cursor?, distanceEq]⟩
  | actual cursor eligible _ =>
      exact observedEligible cursor eligible

/-- A supported cursor's original node carries an authoritative Rule-1a label.  Padding nodes are
phantom nodes with the fixed zero label; actual nodes use the interface. -/
theorem cursor_rule1a_label_of_support
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (root : Nat)
    (labelEligible : FrameLabelAvailable mol root) :
    ∀ (fuel : Nat) (cursor : FrameRuntime.Cursor),
      FramedCursorSupport mol profile root fuel cursor →
      ∃ label, mol.canonicalRule1aLabelAuthoritative?
        (FrameRuntime.Cursor.original mol cursor).node = some label := by
  intro fuel cursor support
  cases support with
  | padding parent _ =>
      refine ⟨{ numerator := 0, denominator := 1 }, ?_⟩
      simp [FrameRuntime.Cursor.original, canonicalPhantom,
        canonicalRule1aLabelAuthoritative?]
  | actual cursor eligible _ =>
      simpa [FrameRuntime.Cursor.original] using labelEligible cursor eligible

/-! ## Totality of the recursive runtime over the interface -/

/-- `FrameRuntime.label?` is total for every supported cursor pair. -/
theorem label?_exists_of_interface
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (root : Nat) (fuel : Nat)
    (observedEligible : FrameObserved mol profile root)
    (labelEligible : FrameLabelAvailable mol root) :
    ∀ (rule : CanonicalRuleStage) (left right : FrameRuntime.Cursor),
      FramedCursorSupport mol profile root fuel left →
      FramedCursorSupport mol profile root fuel right →
      ∃ ordering, FrameRuntime.label? mol profile true rule left right = some ordering := by
  intro rule left right leftSupport rightSupport
  have hld := framedsupport_observed_of_interface mol profile root observedEligible
    fuel left leftSupport
  have hrd := framedsupport_observed_of_interface mol profile root observedEligible
    fuel right rightSupport
  rcases hld with ⟨ld, ldEq⟩
  rcases hrd with ⟨rd, rdEq⟩
  cases rule with
  | rule1a =>
      rcases cursor_rule1a_label_of_support mol profile root labelEligible fuel left
          leftSupport with ⟨ll, hll⟩
      rcases cursor_rule1a_label_of_support mol profile root labelEligible fuel right
          rightSupport with ⟨rl, hrl⟩
      exact ⟨compareCIPAtomicLabel ll rl, by
        simp [FrameRuntime.label?, ldEq, rdEq, hll, hrl,
          compareCanonicalNodeRuleAuthoritative?]⟩
  | rule1b =>
      exact ⟨(if ld < rd then Ordering.gt else if rd < ld then Ordering.lt else Ordering.eq), by
        simp [FrameRuntime.label?, ldEq, rdEq]⟩
  | rule2 =>
      exact ⟨mol.compareCanonicalNodeRule .rule2 (FrameRuntime.Cursor.original mol left).node
        (FrameRuntime.Cursor.original mol right).node, by
        simp [FrameRuntime.label?, ldEq, rdEq, compareCanonicalNodeRuleAuthoritative?]⟩

/-- `FrameRuntime.pairLabels?` is total for every supported frontier. -/
theorem pairLabels?_exists_of_interface
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (root : Nat) (fuel : Nat)
    (observedEligible : FrameObserved mol profile root)
    (labelEligible : FrameLabelAvailable mol root)
    (rule : CanonicalRuleStage) :
    ∀ pairs, FramedFrontierSupport mol profile root fuel pairs →
      ∃ ordering, FrameRuntime.pairLabels? mol profile true rule pairs = some ordering
  | [], _ => ⟨Ordering.eq, by simp [FrameRuntime.pairLabels?]⟩
  | (left, right) :: pairs, support => by
      have head := support (left, right) (by simp)
      have tail : FramedFrontierSupport mol profile root fuel pairs := by
        intro pair member
        exact support pair (by simp [member])
      rcases label?_exists_of_interface mol profile root fuel observedEligible labelEligible
          rule left right head.1 head.2 with ⟨cmp, hcmp⟩
      rcases pairLabels?_exists_of_interface mol profile root fuel observedEligible labelEligible
          rule pairs tail with ⟨rest, hrest⟩
      cases cmp with
      | lt => exact ⟨.lt, by simp [FrameRuntime.pairLabels?, hcmp]⟩
      | gt => exact ⟨.gt, by simp [FrameRuntime.pairLabels?, hcmp]⟩
      | eq => exact ⟨rest, by simp [FrameRuntime.pairLabels?, hcmp, hrest]⟩

/-- `FrameRuntime.ranked?` is total and lowers the support fuel, under the P-92 width bound and the
cursor-observation interface. -/
theorem ranked?_exists_of_interface
    (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) (fuel : Nat)
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (observedEligible : FrameObserved mol profile root)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (beforeTotal : ∀ left right,
      FramedCursorSupport mol profile root fuel left →
      FramedCursorSupport mol profile root fuel right →
      ∃ ordering, before left right = some ordering) :
    ∀ cursor, FramedCursorSupport mol profile root (fuel + 1) cursor →
      ∃ ranked, FrameRuntime.ranked? mol profile true before cursor = some ranked ∧
        ∀ child, child ∈ ranked → FramedCursorSupport mol profile root fuel child := by
  intro cursor support
  cases support with
  | padding parent parentObserved =>
      have paddingObserved : ∃ d,
          FrameRuntime.cursor? mol profile (.padding parent) = some d := by
        rcases parentObserved with ⟨d, hd⟩
        exact ⟨d + 1, by simp [FrameRuntime.cursor?, hd]⟩
      have rankedEq : FrameRuntime.ranked? mol profile true before (.padding parent) =
          some (List.replicate RawMolecule.authoritativeChildSlots
            (.padding (.padding parent))) := by
        rcases parentObserved with ⟨d, hd⟩
        simp [FrameRuntime.ranked?, FrameRuntime.cursor?, FrameRuntime.Cursor.original,
          canonicalPhantom, hd, CanonicalRerootCursor.children, CanonicalBranchNode.forcedLeaf,
          FrameRuntime.sort?]
      refine ⟨List.replicate RawMolecule.authoritativeChildSlots
        (.padding (.padding parent)), rankedEq, ?_⟩
      intro child member
      have childEq : child = .padding (.padding parent) := List.eq_of_mem_replicate member
      subst child
      exact .padding fuel (.padding parent) paddingObserved
  | actual cursor eligible heightLe =>
      have ownObserved : ∃ distance,
          FrameRuntime.cursor? mol profile (.actual cursor) = some distance :=
        observedEligible cursor eligible
      have width : ((cursor.children mol).map FrameRuntime.Cursor.actual).length ≤
          RawMolecule.authoritativeChildSlots := by
        simpa using canonicalCenterRerootCursor_local_width bonding cursor eligible
      have width' : (cursor.children mol).length ≤
          RawMolecule.authoritativeChildSlots := by
        simpa using width
      have childrenSupported : ∀ child,
          child ∈ (cursor.children mol).map FrameRuntime.Cursor.actual →
          FramedCursorSupport mol profile root fuel child := by
        intro child member
        rw [List.mem_map] at member
        rcases member with ⟨under, underMember, rfl⟩
        have childEligible : CanonicalCenterRerootCursor mol root under :=
          CanonicalCenterRerootCursor.child eligible underMember
        have heightLt : moleculeCursorHeight mol under < moleculeCursorHeight mol cursor :=
          moleculeCursorHeight_child_lt centerBound wellFormed eligible underMember
        have heightLe' : moleculeCursorHeight mol under ≤ fuel := by omega
        exact .actual fuel under childEligible heightLe'
      have childrenObserved : ∀ child,
          child ∈ (cursor.children mol).map FrameRuntime.Cursor.actual →
          ∃ d, FrameRuntime.cursor? mol profile child = some d := by
        intro child member
        exact framedsupport_observed_of_interface mol profile root observedEligible fuel child
          (childrenSupported child member)
      rcases mapM_exists_of_all_observed (FrameRuntime.cursor? mol profile)
          ((cursor.children mol).map FrameRuntime.Cursor.actual) childrenObserved with
        ⟨validated, validatedEq⟩
      rcases sort?_exists_of_supported mol profile root fuel before beforeTotal
          ((cursor.children mol).map FrameRuntime.Cursor.actual) childrenSupported with
        ⟨sorted, sortedEq, sortedSupport, sortedLength⟩
      rcases ownObserved with ⟨distance, hdistance⟩
      refine ⟨sorted ++ List.replicate
          (RawMolecule.authoritativeChildSlots - sorted.length) (.padding (.actual cursor)),
        ?_, ?_⟩
      · simp [FrameRuntime.ranked?, FrameRuntime.Cursor.original, hdistance,
          validatedEq, sortedEq]
        exact width'
      · intro child member
        rcases List.mem_append.mp member with inSorted | inPadding
        · exact sortedSupport child inSorted
        · have childEq : child = .padding (.actual cursor) := List.eq_of_mem_replicate inPadding
          subst child
          exact .padding fuel (.actual cursor) ⟨distance, hdistance⟩

/-- `FrameRuntime.nextPairs?` exists and lowers the support fuel. -/
theorem nextPairs?_exists_of_interface
    (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat) (fuel : Nat)
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (observedEligible : FrameObserved mol profile root)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (beforeTotal : ∀ left right,
      FramedCursorSupport mol profile root fuel left →
      FramedCursorSupport mol profile root fuel right →
      ∃ ordering, before left right = some ordering) :
    ∀ pairs, FramedFrontierSupport mol profile root (fuel + 1) pairs →
      ∃ next, FrameRuntime.nextPairs? mol profile true before pairs = some next ∧
        FramedFrontierSupport mol profile root fuel next := by
  intro pairs
  induction pairs with
  | nil =>
      intro _
      refine ⟨[], by simp [FrameRuntime.nextPairs?], ?_⟩
      intro pair member
      simp at member
  | cons pair rest ih =>
      intro support
      have head := support pair (by simp)
      have tail : FramedFrontierSupport mol profile root (fuel + 1) rest := by
        intro candidate member
        exact support candidate (by simp [member])
      rcases ih tail with ⟨restResult, restEq, restSupport⟩
      by_cases bothTerminal : FrameRuntime.terminal mol pair.1 = true ∧
          FrameRuntime.terminal mol pair.2 = true
      · refine ⟨restResult, by simp [FrameRuntime.nextPairs?, restEq, bothTerminal],
          restSupport⟩
      · rcases ranked?_exists_of_interface mol profile root fuel centerBound wellFormed bonding
            observedEligible before beforeTotal pair.1 head.1 with
          ⟨left, leftEq, leftSupport⟩
        rcases ranked?_exists_of_interface mol profile root fuel centerBound wellFormed bonding
            observedEligible before beforeTotal pair.2 head.2 with
          ⟨right, rightEq, rightSupport⟩
        refine ⟨left.zip right ++ restResult, ?_, ?_⟩
        · simp [FrameRuntime.nextPairs?, restEq, bothTerminal, leftEq, rightEq]
        · intro candidate member
          rcases List.mem_append.mp member with zipped | inRest
          · have components := List.of_mem_zip zipped
            exact ⟨leftSupport candidate.1 components.1,
              rightSupport candidate.2 components.2⟩
          · exact restSupport candidate inRest

/-- `FrameRuntime.compareRule?` is total on supported frontiers within the recursive fuel budget. -/
theorem compareRule?_exists_of_interface
    (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (root : Nat)
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (observedEligible : FrameObserved mol profile root)
    (labelEligible : FrameLabelAvailable mol root)
    (rankFuel : Nat)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (beforeTotal : ∀ left right,
      FramedCursorSupport mol profile root rankFuel left →
      FramedCursorSupport mol profile root rankFuel right →
      ∃ ordering, before left right = some ordering)
    (rule : CanonicalRuleStage) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 → FramedFrontierSupport mol profile root fuel pairs →
      ∃ ordering, FrameRuntime.compareRule? mol profile true before rule fuel pairs =
        some ordering := by
  intro fuel
  induction fuel with
  | zero =>
      intro pairs _ support
      rcases pairLabels?_exists_of_interface mol profile root 0 observedEligible labelEligible
          rule pairs support with ⟨labels, labelsEq⟩
      have capFalse : (!(true : Bool) && RawMolecule.defaultBranchWidthCap < pairs.length) =
          false := by simp
      cases labels with
      | lt =>
          refine ⟨.lt, ?_⟩
          rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq]
          simp
      | gt =>
          refine ⟨.gt, ?_⟩
          rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq]
          simp
      | eq =>
          have nextEq : FrameRuntime.nextPairs? mol profile true before pairs = some [] :=
            nextPairs?_zero_eq_nil mol profile root centerBound wellFormed before pairs support
          refine ⟨.eq, ?_⟩
          rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq, nextEq]
          simp
  | succ fuel ih =>
      intro pairs fuelLe support
      have lowerLe : fuel ≤ rankFuel := by omega
      have localTotal : ∀ left right,
          FramedCursorSupport mol profile root fuel left →
          FramedCursorSupport mol profile root fuel right →
          ∃ ordering, before left right = some ordering := by
        intro left right leftSupport rightSupport
        exact beforeTotal left right (leftSupport.mono lowerLe) (rightSupport.mono lowerLe)
      rcases pairLabels?_exists_of_interface mol profile root (fuel + 1) observedEligible
          labelEligible rule pairs support with ⟨labels, labelsEq⟩
      have capFalse : (!(true : Bool) && RawMolecule.defaultBranchWidthCap < pairs.length) =
          false := by simp
      cases labels with
      | lt =>
          refine ⟨.lt, ?_⟩
          rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq]
          simp
      | gt =>
          refine ⟨.gt, ?_⟩
          rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq]
          simp
      | eq =>
          rcases nextPairs?_exists_of_interface mol profile root fuel centerBound wellFormed
              bonding observedEligible before localTotal pairs support with
            ⟨next, nextEq, nextSupport⟩
          cases next with
          | nil =>
              refine ⟨.eq, ?_⟩
              rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq, nextEq]
              simp
          | cons pair rest =>
              rcases ih (pair :: rest) (by omega) nextSupport with ⟨decision, decisionEq⟩
              refine ⟨decision, ?_⟩
              rw [FrameRuntime.compareRule?, if_neg (by simp), labelsEq, nextEq]
              show FrameRuntime.compareRule? mol profile true before rule fuel (pair :: rest) =
                some decision
              exact decisionEq

/-! ## Fail-closed candidate totality over the interface -/

/-- The exact successor schedule of the shipped fail-closed candidate, with the recursive callback
written out.  This is an unfolding definition, not a comparator. -/
private def failClosedSchedule? (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    (fuel : Nat) (stage : CanonicalRuleStage)
    (left right : FrameRuntime.Cursor) : Option Ordering :=
  (FrameRuntime.compareRule? mol profile authoritative before .rule1a fuel [(left, right)]) >>= fun first =>
    if first != Ordering.eq || stage == .rule1a then some first else
    (FrameRuntime.compareRule? mol profile authoritative before .rule1b fuel [(left, right)]) >>= fun distance =>
      if distance != Ordering.eq || stage == .rule1b then some distance else
      FrameRuntime.compareRule? mol profile authoritative before .rule2 fuel [(left, right)]

/-- The positive-fuel branch of the shipped fail-closed candidate is the explicit schedule with
the candidate itself as its own callback. -/
private theorem failClosed_succ_eq (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage)
    (left right : FrameRuntime.Cursor) :
    RawFramedFailClosedFuelBase.failClosedCompareBranch? mol profile authoritative
        (Nat.succ fuel) stage left right =
      failClosedSchedule? mol profile authoritative
        (RawFramedFailClosedFuelBase.failClosedCompareBranch? mol profile authoritative fuel stage)
        (Nat.succ fuel) stage left right := rfl

/-- At fuel `0`, supported pairs are runtime-terminal and the shipped fail-closed candidate succeeds
on the structural interface. -/
theorem failClosed_zero_exists_of_interface
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (root : Nat)
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (observedEligible : FrameObserved mol profile root)
    (labelEligible : FrameLabelAvailable mol root) :
    ∀ (stage : CanonicalRuleStage) (left right : FrameRuntime.Cursor),
      FramedCursorSupport mol profile root 0 left →
      FramedCursorSupport mol profile root 0 right →
      ∃ ordering,
        RawFramedFailClosedFuelBase.failClosedCompareBranch? mol profile true 0 stage left right =
          some ordering := by
  intro stage left right leftSupport rightSupport
  have hleft := FramedCursorSupport.zero_terminal centerBound wellFormed left leftSupport
  have hright := FramedCursorSupport.zero_terminal centerBound wellFormed right rightSupport
  rw [RawFramedFailClosedFuelBase.failClosed_zero_eq_throughLabels_of_terminal mol profile true
    stage left right hleft hright]
  have h1a := label?_exists_of_interface mol profile root 0 observedEligible labelEligible .rule1a
    left right leftSupport rightSupport
  have h1b := label?_exists_of_interface mol profile root 0 observedEligible labelEligible .rule1b
    left right leftSupport rightSupport
  have h2 := label?_exists_of_interface mol profile root 0 observedEligible labelEligible .rule2
    left right leftSupport rightSupport
  exact RawFramedFailClosedFuelBase.throughLabels?_exists mol profile true stage left right
    h1a h1b h2

/-- **Fail-closed candidate totality on the structural interface, at every fuel.**  The induction
is the shipped fail-closed schedule; the only substitutions are the interface-backed `label?` and
`compareRule?` totality lemmas.  No archived all-real profile admission is used. -/
theorem failClosed_compareBranch_exists_of_interface
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (root : Nat)
    (centerBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (observedEligible : FrameObserved mol profile root)
    (labelEligible : FrameLabelAvailable mol root) :
    ∀ (fuel : Nat) (stage : CanonicalRuleStage) (left right : FrameRuntime.Cursor),
      FramedCursorSupport mol profile root fuel left →
      FramedCursorSupport mol profile root fuel right →
      ∃ ordering,
        RawFramedFailClosedFuelBase.failClosedCompareBranch? mol profile true fuel stage left right =
          some ordering := by
  intro fuel
  induction fuel with
  | zero =>
      intro stage left right leftSupport rightSupport
      exact failClosed_zero_exists_of_interface mol profile root centerBound wellFormed
        observedEligible labelEligible stage left right leftSupport rightSupport
  | succ fuel ih =>
      intro stage left right leftSupport rightSupport
      let before := RawFramedFailClosedFuelBase.failClosedCompareBranch? mol profile true fuel stage
      have beforeTotal : ∀ left right,
          FramedCursorSupport mol profile root fuel left →
          FramedCursorSupport mol profile root fuel right →
          ∃ ordering, before left right = some ordering := by
        intro left right leftSupport rightSupport
        exact ih stage left right leftSupport rightSupport
      have frontier : FramedFrontierSupport mol profile root (fuel + 1) [(left, right)] := by
        intro pair member
        have pairEq : pair = (left, right) := by simpa using member
        subst pair
        exact ⟨leftSupport, rightSupport⟩
      rcases compareRule?_exists_of_interface mol profile root centerBound wellFormed bonding
          observedEligible labelEligible fuel before beforeTotal .rule1a (fuel + 1)
          [(left, right)] (by omega) frontier with ⟨first, firstEq⟩
      cases first with
      | lt =>
          refine ⟨.lt, ?_⟩
          rw [failClosed_succ_eq]
          simp only [failClosedSchedule?]
          rw [firstEq]
          simp
      | gt =>
          refine ⟨.gt, ?_⟩
          rw [failClosed_succ_eq]
          simp only [failClosedSchedule?]
          rw [firstEq]
          simp
      | eq =>
          cases stage with
          | rule1a =>
              refine ⟨.eq, ?_⟩
              rw [failClosed_succ_eq]
              simp only [failClosedSchedule?]
              rw [firstEq]
              simp
          | rule1b =>
              rcases compareRule?_exists_of_interface mol profile root centerBound wellFormed
                  bonding observedEligible labelEligible fuel before beforeTotal .rule1b (fuel + 1)
                  [(left, right)] (by omega) frontier with ⟨distance, distanceEq⟩
              cases distance with
              | lt =>
                  refine ⟨.lt, ?_⟩
                  rw [failClosed_succ_eq]
                  simp only [failClosedSchedule?]
                  rw [firstEq, distanceEq]
                  simp
              | gt =>
                  refine ⟨.gt, ?_⟩
                  rw [failClosed_succ_eq]
                  simp only [failClosedSchedule?]
                  rw [firstEq, distanceEq]
                  simp
              | eq =>
                  refine ⟨.eq, ?_⟩
                  rw [failClosed_succ_eq]
                  simp only [failClosedSchedule?]
                  rw [firstEq, distanceEq]
                  simp
          | rule2 =>
              rcases compareRule?_exists_of_interface mol profile root centerBound wellFormed
                  bonding observedEligible labelEligible fuel before beforeTotal .rule1b (fuel + 1)
                  [(left, right)] (by omega) frontier with ⟨distance, distanceEq⟩
              cases distance with
              | lt =>
                  refine ⟨.lt, ?_⟩
                  rw [failClosed_succ_eq]
                  simp only [failClosedSchedule?]
                  rw [firstEq, distanceEq]
                  simp
              | gt =>
                  refine ⟨.gt, ?_⟩
                  rw [failClosed_succ_eq]
                  simp only [failClosedSchedule?]
                  rw [firstEq, distanceEq]
                  simp
              | eq =>
                  rcases compareRule?_exists_of_interface mol profile root centerBound wellFormed
                      bonding observedEligible labelEligible fuel before beforeTotal .rule2
                      (fuel + 1) [(left, right)] (by omega) frontier with ⟨mass, massEq⟩
                  refine ⟨mass, ?_⟩
                  rw [failClosed_succ_eq]
                  simp only [failClosedSchedule?]
                  rw [firstEq, distanceEq, massEq]
                  simp

/-- **Fail-closed structural fuel bound.**  The shipped fail-closed comparator is total at fuel
`2 * atomCount + 2` on every eligible pair, from the two structural interface facts and the
finite-graph bounds. -/
theorem failClosed_compareBranch_rule2_fuel_bound_of_interface
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
        (2 * mol.atomCount + 2) .rule2 (.actual left) (.actual right) = some ordering := by
  have leftHeight : moleculeCursorHeight mol left ≤ 2 * mol.atomCount + 1 :=
    moleculeCursorHeight_le_two_mul_atomCount_add_one centerBound wellFormed leftEligible
  have rightHeight : moleculeCursorHeight mol right ≤ 2 * mol.atomCount + 1 :=
    moleculeCursorHeight_le_two_mul_atomCount_add_one centerBound wellFormed rightEligible
  have leftSupport : FramedCursorSupport mol profile root (2 * mol.atomCount + 2)
      (.actual left) :=
    .actual (2 * mol.atomCount + 2) left leftEligible (by omega)
  have rightSupport : FramedCursorSupport mol profile root (2 * mol.atomCount + 2)
      (.actual right) :=
    .actual (2 * mol.atomCount + 2) right rightEligible (by omega)
  exact failClosed_compareBranch_exists_of_interface mol profile root centerBound wellFormed
    bonding observedEligible labelEligible (2 * mol.atomCount + 2) .rule2 (.actual left)
    (.actual right) leftSupport rightSupport

/-! ## Projection of the general actual profile to the runtime record -/

/-- The archived runtime record projected from a general actual occurrence profile.  This reuses
the shared projection `GeneratedDuplicateAtomicLabelAvailability.toRuntimeProfile` (so there is a
single projection in the repository): the runtime reads only `frame` and `generated`, both
preserved exactly, while the archived `center` field is carried along but never consulted by
`cursor?`, `label?`, `compareRule?`, `throughLabels?` or `compareBranch?`. -/
def toFrameProfile (p : CanonicalGeneratedComparisonProfile.Profile) : FrameRuntime.Profile :=
  TetraStereo.OneCenter.GeneratedDuplicateAtomicLabelAvailability.toRuntimeProfile p

@[simp] theorem toFrameProfile_center (p : CanonicalGeneratedComparisonProfile.Profile) :
    (toFrameProfile p).center = p.center := rfl

@[simp] theorem toFrameProfile_frame (p : CanonicalGeneratedComparisonProfile.Profile) :
    (toFrameProfile p).frame = p.frame := rfl

@[simp] theorem toFrameProfile_generated (p : CanonicalGeneratedComparisonProfile.Profile) :
    (toFrameProfile p).generated = p.generated := rfl

/-! ## Discharging the interface from the general profile gate -/

/-- A node generated from the centre root lies in the collected inventory.

The profile is *constructed* by the actual admission theorem, so its `generated` field is the
complete canonical prefix tree rather than an assumed collector success. -/
theorem mem_generated_of_tree
    {mol : RawMolecule} {root : Nat}
    (wellFormed : mol.WellFormed) (rootBound : root < mol.atomCount)
    {p : CanonicalGeneratedComparisonProfile.Profile}
    (generatedEq : p.generated =
      CanonicalGeneratedComparisonProfile.prefixTree mol root 0 (mol.atomCount + 1))
    {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root node) :
    node ∈ p.generated := by
  rw [generatedEq]
  exact CanonicalGeneratedComparisonProfile.generated_mem_complete_tree mol root
    (mol.atomCount + 1) wellFormed rootBound (Nat.le_refl _) node generated

/-- **Interface discharge from the actual general profile.**  Given a well-formed molecule, an
in-range root, an actually generated centre and the non-mancude generated-duplicate domain, the
actual profile gate succeeds on a profile whose projection observes every eligible actual cursor
and exposes an authoritative Rule-1a label on every eligible actual node.

The profile and its success are produced by
`CanonicalGeneratedProfileAdmission.profile?_complete`; neither the profile, the collector, nor
any label is assumed. -/
theorem interface_of_generated_profile
    (mol : RawMolecule) (root : Nat)
    (wellFormed : mol.WellFormed) (rootBound : root < mol.atomCount)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (nonMancude : NonMancudeGeneratedDuplicates mol root) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.root = root ∧
      FrameObserved mol (toFrameProfile p) p.root ∧
      FrameLabelAvailable mol p.root := by
  obtain ⟨p, hprofile, hpRoot, _hpCenter, _hpFrame, hpGenerated, _hcenterMem, _hpath,
    _hadmission⟩ :=
    CanonicalGeneratedProfileAdmission.profile?_complete mol root wellFormed rootBound center
      centerGenerated
  have memberOfGenerated : ∀ {node : CanonicalBranchNode},
      CanonicalCenterTreeNode mol root node → node ∈ p.generated := by
    intro node generated
    exact mem_generated_of_tree wellFormed rootBound hpGenerated generated
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
    exact cursor?_actual_of_membership mol (toFrameProfile p)
      (by simpa [toFrameProfile] using nodeMem)
      (fun previous hprevious => by
        simpa [toFrameProfile] using previousGenerated previous hprevious)
      previousNeighbor observedNode
  · intro cursor eligible
    have eligibleRoot : CanonicalCenterRerootCursor mol root cursor := by
      rw [hpRoot] at eligible
      exact eligible
    exact generated_rule1a_label_available_of_nonMancude mol root nonMancude cursor.node
      (CanonicalCenterRerootCursor.node_generated eligibleRoot)

/-! ## Totality and stability on the projected actual profile -/

/-- **Fail-closed candidate totality on the projected actual profile.**  For a general actual
profile produced by `CanonicalGeneratedComparisonProfile.profile?`, on the non-mancude
generated-duplicate domain, the shipped fail-closed candidate applied to the projected record is
total on every eligible ligand pair at fuel `2 * atomCount + 2`.

The profile gate success is derived from `mol.WellFormed`, the root bound and the actual
generation relation; no admission of the projected record is assumed (and in general it fails for
duplicate-bearing profiles). -/
theorem generated_profile_failClosed_compareBranch_rule2
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
          (2 * mol.atomCount + 2) .rule2 (.actual left) (.actual right) = some ordering := by
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
  exact failClosed_compareBranch_rule2_fuel_bound_of_interface mol (toFrameProfile p) root
    rootBound wellFormed bonding observedRoot labelsRoot leftEligible rightEligible

/-- **Actual comparator totality on the projected actual profile.**  The shipped
`FrameRuntime.compareBranch?` is total at stage `.rule2` and fuel `2 * atomCount + 2` on the same
projected actual profile.  This is obtained from candidate totality together with the existing
success-refinement theorem `failClosed_refines_main`; the production comparator is unchanged. -/
theorem generated_profile_main_compareBranch_rule2
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
          (2 * mol.atomCount + 2) .rule2 (.actual left) (.actual right) = some ordering := by
  obtain ⟨p, hprofile, hpRoot, ordering, computed⟩ :=
    generated_profile_failClosed_compareBranch_rule2 mol root wellFormed rootBound bonding
      center centerGenerated nonMancude leftMember rightMember
  refine ⟨p, hprofile, hpRoot, ordering, ?_⟩
  exact RawFramedFailClosedFuelBase.failClosed_refines_main mol (toFrameProfile p) true .rule2
    (2 * mol.atomCount + 2) (.actual left) (.actual right) ordering computed

/-- **Fail-closed candidate totality at every larger fuel.**  The result at the explicit bound is
transported to every `fuel ≥ 2 * atomCount + 2` by the unconditional successful-fuel monotonicity
`failClosed_success_mono`, preserving the same ordering. -/
theorem generated_profile_failClosed_compareBranch_rule2_ge
    (mol : RawMolecule) (root : Nat)
    (wellFormed : mol.WellFormed) (rootBound : root < mol.atomCount)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center)
    (fuel : Nat) (fuelBound : 2 * mol.atomCount + 2 ≤ fuel) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.root = root ∧
      ∃ ordering,
        RawFramedFailClosedFuelBase.failClosedCompareBranch? mol (toFrameProfile p) true
          fuel .rule2 (.actual left) (.actual right) = some ordering := by
  obtain ⟨p, hprofile, hpRoot, ordering, computed⟩ :=
    generated_profile_failClosed_compareBranch_rule2 mol root wellFormed rootBound bonding
      center centerGenerated nonMancude leftMember rightMember
  refine ⟨p, hprofile, hpRoot, ordering, ?_⟩
  exact RawFramedFailClosedFuelBase.failClosed_success_mono mol (toFrameProfile p) true .rule2
    computed fuelBound

/-- **Actual comparator totality at every larger fuel.**  The explicit-bound answer is stable at
every `fuel ≥ 2 * atomCount + 2`: successful-fuel monotonicity of the candidate and the existing
refinement into `FrameRuntime.compareBranch?` preserve the same ordering. -/
theorem generated_profile_main_compareBranch_rule2_ge
    (mol : RawMolecule) (root : Nat)
    (wellFormed : mol.WellFormed) (rootBound : root < mol.atomCount)
    (bonding : CanonicalCenterBondingNumberSix mol root)
    (center : CanonicalBranchNode)
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (nonMancude : NonMancudeGeneratedDuplicates mol root)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center)
    (fuel : Nat) (fuelBound : 2 * mol.atomCount + 2 ≤ fuel) :
    ∃ p : CanonicalGeneratedComparisonProfile.Profile,
      CanonicalGeneratedComparisonProfile.profile? mol center = some p ∧
      p.root = root ∧
      ∃ ordering,
        FrameRuntime.compareBranch? mol (toFrameProfile p) true
          fuel .rule2 (.actual left) (.actual right) = some ordering := by
  obtain ⟨p, hprofile, hpRoot, ordering, computed⟩ :=
    generated_profile_failClosed_compareBranch_rule2_ge mol root wellFormed rootBound bonding
      center centerGenerated nonMancude leftMember rightMember fuel fuelBound
  refine ⟨p, hprofile, hpRoot, ordering, ?_⟩
  exact RawFramedFailClosedFuelBase.failClosed_refines_main mol (toFrameProfile p) true .rule2
    fuel (.actual left) (.actual right) ordering computed

end RawFramedGeneratedFuelInterface

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.FrameObserved
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.FrameLabelAvailable
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.framedsupport_observed_of_interface
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.cursor_rule1a_label_of_support
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.label?_exists_of_interface
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.pairLabels?_exists_of_interface
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.ranked?_exists_of_interface
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.nextPairs?_exists_of_interface
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.compareRule?_exists_of_interface
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.failClosed_zero_exists_of_interface
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.failClosed_compareBranch_exists_of_interface
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.failClosed_compareBranch_rule2_fuel_bound_of_interface
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.toFrameProfile
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.toFrameProfile_center
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.toFrameProfile_frame
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.toFrameProfile_generated
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.mem_generated_of_tree
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.interface_of_generated_profile
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.generated_profile_failClosed_compareBranch_rule2
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.generated_profile_main_compareBranch_rule2
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.generated_profile_failClosed_compareBranch_rule2_ge
assert_kernel_only
  TetraStereo.OneCenter.RawFramedGeneratedFuelInterface.generated_profile_main_compareBranch_rule2_ge
