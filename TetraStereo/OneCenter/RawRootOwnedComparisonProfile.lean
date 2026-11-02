import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.OneCenter.ConstitutionalRootStageAvailability
import TetraStereo.KernelOnly





















































set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace RawRootOwnedComparisonProfile

open RawMolecule
open TetraStereo.OneCenter.ConstitutionalRootStageAvailability

/-! ## Root-owned profile and policy seam -/

/-- Extract the original root from the actual comparison owner's retained history. -/
def extractedRoot (profile : CanonicalTreeProfile.Profile) : Option ℕ :=
  profile.center.history.getLast?

/-- Candidate root-owned profile: the comparison owner and generated inventory are preserved;
only the distance origin is replaced by the singleton original root. -/
def rootOwnedProfile (profile : CanonicalTreeProfile.Profile) (root : ℕ) :
    CanonicalTreeProfile.Profile :=
  { center := profile.center
    frame := ⟨[root]⟩
    generated := profile.generated }

/-- Executable root-owned profile.  A centre history without a root is refused, not totalized. -/
def rootOwnedProfile? (profile : CanonicalTreeProfile.Profile) :
    Option CanonicalTreeProfile.Profile :=
  (extractedRoot profile).map fun root => rootOwnedProfile profile root

/-- Explicit policy seam between the deployed centre-owned frame and the candidate
original-root frame.  This module never changes the deployed policy. -/
inductive ComparisonOriginPolicy where
  | centerOwned
  | originalRoot
  deriving DecidableEq, Repr

/-- Apply a comparison-origin policy to an accepted profile. -/
def policyProfile? : ComparisonOriginPolicy → CanonicalTreeProfile.Profile →
    Option CanonicalTreeProfile.Profile
  | .centerOwned, profile => some profile
  | .originalRoot, profile => rootOwnedProfile? profile

theorem rootOwnedProfile_center (profile : CanonicalTreeProfile.Profile) (root : ℕ) :
    (rootOwnedProfile profile root).center = profile.center := rfl

theorem rootOwnedProfile_generated (profile : CanonicalTreeProfile.Profile) (root : ℕ) :
    (rootOwnedProfile profile root).generated = profile.generated := rfl

/-- The comparison owner and the distance origin are distinct fields of the root-owned profile. -/
theorem rootOwnedProfile_separates_owner_and_origin
    (profile : CanonicalTreeProfile.Profile) (root : ℕ) :
    (rootOwnedProfile profile root).center = profile.center ∧
      (rootOwnedProfile profile root).frame = (⟨[root]⟩ : CanonicalComparisonFrame.Frame) :=
  ⟨rfl, rfl⟩

theorem rootOwnedProfile?_eq_some {profile : CanonicalTreeProfile.Profile} {root : ℕ}
    (hroot : profile.center.history.getLast? = some root) :
    rootOwnedProfile? profile = some (rootOwnedProfile profile root) := by
  simp [rootOwnedProfile?, extractedRoot, hroot]

theorem rootOwnedProfile?_eq_none_iff (profile : CanonicalTreeProfile.Profile) :
    rootOwnedProfile? profile = none ↔ profile.center.history.getLast? = none := by
  cases hroot : profile.center.history.getLast? <;>
    simp [rootOwnedProfile?, extractedRoot, hroot]

theorem policyProfile?_centerOwned (profile : CanonicalTreeProfile.Profile) :
    policyProfile? .centerOwned profile = some profile := rfl

theorem policyProfile?_originalRoot (profile : CanonicalTreeProfile.Profile) :
    policyProfile? .originalRoot profile = rootOwnedProfile? profile := rfl

/-! ## Acceptance facts of a successful executable profile -/

/-- The exact generated-node gate used by `CanonicalTreeProfile.profile?`. -/
def acceptedNodeCheck (mol : RawMolecule) (root : ℕ) (node : CanonicalBranchNode) : Bool :=
  node.provenance == .realAtom && node.history.head? == some node.atom &&
  node.history.getLast? == some root && !node.history.isEmpty &&
  decide node.history.Nodup && node.history.all (fun atom => decide (atom < mol.atomCount))

/-- Unpack the executable gate into the actual history/provenance/bound facts. -/
theorem acceptedNodeCheck_facts {mol : RawMolecule} {root : ℕ} {node : CanonicalBranchNode}
    (h : acceptedNodeCheck mol root node = true) :
    node.provenance = .realAtom ∧ node.history.head? = some node.atom ∧
      node.history.getLast? = some root ∧ node.history ≠ [] ∧
      node.history.Nodup ∧ ∀ atom ∈ node.history, atom < mol.atomCount := by
  unfold acceptedNodeCheck at h
  -- `&&` is left-associative; peel the rightmost conjunct each time.
  obtain ⟨hleft₁, hbounds⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hleft₂, hnodup⟩ := Bool.and_eq_true_iff.mp hleft₁
  obtain ⟨hleft₃, hnonempty⟩ := Bool.and_eq_true_iff.mp hleft₂
  obtain ⟨hleft₄, hlast⟩ := Bool.and_eq_true_iff.mp hleft₃
  obtain ⟨hreal, hhead⟩ := Bool.and_eq_true_iff.mp hleft₄
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [beq_iff_eq] using hreal
  · simpa [beq_iff_eq] using hhead
  · simpa [beq_iff_eq] using hlast
  · have hempty : node.history.isEmpty = false := by
      cases hb : node.history.isEmpty <;> simp_all
    exact List.isEmpty_eq_false_iff.mp hempty
  · exact of_decide_eq_true hnodup
  · intro atom member
    have bounded : decide (atom < mol.atomCount) = true := by
      simpa using List.all_eq_true.mp hbounds atom member
    exact of_decide_eq_true bounded

/-- Every successful profile has a real extracted root and every generated node passes the
actual acceptance gate at that root. -/
theorem profile?_accepted {mol : RawMolecule} {center : CanonicalBranchNode}
    {profile : CanonicalTreeProfile.Profile}
    (h : CanonicalTreeProfile.profile? mol center = some profile) :
    ∃ root, center.history.getLast? = some root ∧ root < mol.atomCount ∧
      profile.generated.all (acceptedNodeCheck mol root) = true := by
  cases hroot : center.history.getLast? with
  | none =>
      unfold CanonicalTreeProfile.profile? at h
      simp only [hroot, Bind.bind, Option.bind] at h
      cases h
  | some root =>
      unfold CanonicalTreeProfile.profile? at h
      simp only [hroot, Bind.bind, Option.bind] at h
      split at h
      · cases h
      · rename_i hnotadm
        cases hgenerated : CanonicalTreeProfile.collect (mol.atomCount + 1) mol.atomCount mol
            [{ atom := root, parent := root, history := [root],
               provenance := CanonicalNodeProvenance.realAtom }] with
        | none =>
            simp only [hgenerated] at h
            cases h
        | some generated =>
            simp only [hgenerated] at h
            split at h
            · cases h
            · rename_i _hnotcontains
              split at h
              · cases h
              · rename_i hnotall
                have hall : (generated.all fun node =>
                    node.provenance == CanonicalNodeProvenance.realAtom &&
                    node.history.head? == some node.atom &&
                    node.history.getLast? == some root && !node.history.isEmpty &&
                    decide node.history.Nodup &&
                    node.history.all (fun atom => decide (atom < mol.atomCount))) = true := by
                  cases ha : (generated.all fun node =>
                      node.provenance == CanonicalNodeProvenance.realAtom &&
                      node.history.head? == some node.atom &&
                      node.history.getLast? == some root && !node.history.isEmpty &&
                      decide node.history.Nodup &&
                      node.history.all (fun atom => decide (atom < mol.atomCount))) with
                  | true => rfl
                  | false => exact absurd (by rw [ha]; rfl) hnotall
                have hbound : root < mol.atomCount := by
                  by_contra hnot
                  have hdec : decide (root < mol.atomCount) = false := by
                    rw [decide_eq_false_iff_not]
                    exact hnot
                  exact hnotadm (by rw [hdec]; rfl)
                have hp : profile = ⟨center, ⟨center.history⟩, generated⟩ :=
                  (Option.some.inj h).symm
                refine ⟨root, rfl, hbound, ?_⟩
                rw [hp]
                simpa only [acceptedNodeCheck] using hall

/-- Component form: the extracted root is in bounds. -/
theorem profile?_getLast? {mol : RawMolecule} {center : CanonicalBranchNode}
    {profile : CanonicalTreeProfile.Profile}
    (h : CanonicalTreeProfile.profile? mol center = some profile) :
    ∃ root, center.history.getLast? = some root ∧ root < mol.atomCount := by
  obtain ⟨root, hroot, hbound, _⟩ := profile?_accepted h
  exact ⟨root, hroot, hbound⟩

/-- A successful profile is exactly its centre, centre history frame, and retained inventory. -/
theorem profile?_eq_self {mol : RawMolecule} {center : CanonicalBranchNode}
    {profile : CanonicalTreeProfile.Profile}
    (h : CanonicalTreeProfile.profile? mol center = some profile) :
    profile = ⟨center, ⟨center.history⟩, profile.generated⟩ := by
  cases hroot : center.history.getLast? with
  | none =>
      unfold CanonicalTreeProfile.profile? at h
      simp only [hroot, Bind.bind, Option.bind] at h
      cases h
  | some root =>
      unfold CanonicalTreeProfile.profile? at h
      simp only [hroot, Bind.bind, Option.bind] at h
      split at h
      · cases h
      · cases hgenerated : CanonicalTreeProfile.collect (mol.atomCount + 1) mol.atomCount mol
            [{ atom := root, parent := root, history := [root],
               provenance := CanonicalNodeProvenance.realAtom }] with
        | none =>
            simp only [hgenerated] at h
            cases h
        | some generated =>
            simp only [hgenerated] at h
            split at h
            · cases h
            · split at h
              · cases h
              · have hprofile : profile = ⟨center, ⟨center.history⟩, generated⟩ :=
                  (Option.some.inj h).symm
                subst profile
                rfl

theorem profile?_center_eq {mol : RawMolecule} {center : CanonicalBranchNode}
    {profile : CanonicalTreeProfile.Profile}
    (h : CanonicalTreeProfile.profile? mol center = some profile) :
    profile.center = center := by
  rw [profile?_eq_self h]

theorem profile?_frame_eq {mol : RawMolecule} {center : CanonicalBranchNode}
    {profile : CanonicalTreeProfile.Profile}
    (h : CanonicalTreeProfile.profile? mol center = some profile) :
    profile.frame = (⟨center.history⟩ : CanonicalComparisonFrame.Frame) := by
  rw [profile?_eq_self h]

/-- Per-node acceptance facts for every node of a successful profile.  These are derived from
the executable acceptance gate, not supplied by the caller. -/
theorem profile?_node_facts {mol : RawMolecule} {center : CanonicalBranchNode}
    {profile : CanonicalTreeProfile.Profile} {root : ℕ} {node : CanonicalBranchNode}
    (h : CanonicalTreeProfile.profile? mol center = some profile)
    (hroot : center.history.getLast? = some root)
    (hmember : node ∈ profile.generated) :
    node.provenance = .realAtom ∧ node.history.head? = some node.atom ∧
      node.history.getLast? = some root ∧ node.history ≠ [] ∧
      node.history.Nodup ∧ ∀ atom ∈ node.history, atom < mol.atomCount := by
  obtain ⟨root', hroot', _hbound, hcheck⟩ := profile?_accepted h
  rw [hroot] at hroot'
  have hrootEq : root' = root := (Option.some.inj hroot').symm
  have hnodeCheck : acceptedNodeCheck mol root node = true := by
    have memberCheck := (List.all_eq_true.mp hcheck) node hmember
    simpa [hrootEq] using memberCheck
  exact acceptedNodeCheck_facts hnodeCheck

theorem profile?_node_real {mol : RawMolecule} {center : CanonicalBranchNode}
    {profile : CanonicalTreeProfile.Profile} {root : ℕ} {node : CanonicalBranchNode}
    (h : CanonicalTreeProfile.profile? mol center = some profile)
    (hroot : center.history.getLast? = some root)
    (hmember : node ∈ profile.generated) :
    node.provenance = .realAtom :=
  (profile?_node_facts h hroot hmember).1

theorem profile?_node_getLast {mol : RawMolecule} {center : CanonicalBranchNode}
    {profile : CanonicalTreeProfile.Profile} {root : ℕ} {node : CanonicalBranchNode}
    (h : CanonicalTreeProfile.profile? mol center = some profile)
    (hroot : center.history.getLast? = some root)
    (hmember : node ∈ profile.generated) :
    node.history.getLast? = some root :=
  (profile?_node_facts h hroot hmember).2.2.1

/-! ## Singleton-origin frame metric -/

/-- A history that actually ends at `root` has frame distance `depth` from the singleton
origin `[root]`. -/
theorem frameDistance_singleton_of_getLast? {root : ℕ} {history : List ℕ}
    (hlast : history.getLast? = some root) :
    CanonicalComparisonFrame.frameDistance [root] history = history.length - 1 := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  simp [CanonicalComparisonFrame.frameDistance, CanonicalComparisonFrame.pathDistance,
    CanonicalComparisonFrame.commonPrefixLength]
  omega

/-- **Observer bridge.**  On a real node whose actual retained history ends at the extracted
root, the root-owned frame observer returns exactly the legacy stored Rule-1b distance. -/
theorem observeNode_rootOwned_eq_rule1bRootDistance
    (profile : CanonicalTreeProfile.Profile) (root : ℕ) (node : CanonicalBranchNode)
    (hreal : node.provenance = .realAtom)
    (hlast : node.history.getLast? = some root) :
    CanonicalComparisonFrame.observeNode (rootOwnedProfile profile root).frame node =
      some node.rule1bRootDistance := by
  rw [CanonicalComparisonFrame.real_observation _ node hreal]
  simp only [rootOwnedProfile, CanonicalComparisonFrame.Frame.realDistance]
  rw [frameDistance_singleton_of_getLast? hlast]
  simp [CanonicalBranchNode.rule1bRootDistance, CanonicalBranchNode.depth, hreal]

/-- Accepted-profile form: the provenance and rooted-history premises are derived from the
executable profile success and actual membership, never assumed. -/
theorem profile?_observeNode_rootOwned_eq_rule1bRootDistance
    {mol : RawMolecule} {center : CanonicalBranchNode}
    {profile : CanonicalTreeProfile.Profile} {root : ℕ} {node : CanonicalBranchNode}
    (h : CanonicalTreeProfile.profile? mol center = some profile)
    (hroot : center.history.getLast? = some root)
    (hmember : node ∈ profile.generated) :
    CanonicalComparisonFrame.observeNode (rootOwnedProfile profile root).frame node =
      some node.rule1bRootDistance := by
  obtain ⟨hreal, _hhead, hlast, _hnonempty, _hnodup, _hbounds⟩ :=
    profile?_node_facts h hroot hmember
  exact observeNode_rootOwned_eq_rule1bRootDistance profile root node hreal hlast

/-! ## Runtime cursor bridge -/

/-- **Runtime cursor bridge (checks explicit).**  The existing generated-node and
previous-neighbour guards are preserved; when they pass, `FrameRuntime.cursor?` on the
root-owned profile reports exactly the legacy stored Rule-1b distance of a validated real node. -/
theorem cursor?_actual_rootOwned_eq_rule1bRootDistance_of_checks
    (mol : RawMolecule) (profile : CanonicalTreeProfile.Profile) (root : ℕ)
    (cursor : CanonicalRerootCursor)
    (hgenerated : (rootOwnedProfile profile root).generated.contains cursor.node = true)
    (hprevious : (cursor.previous?.all fun previous =>
      (rootOwnedProfile profile root).generated.contains previous &&
        (cursor.neighbors mol).contains previous) = true)
    (hreal : cursor.node.provenance = .realAtom)
    (hlast : cursor.node.history.getLast? = some root) :
    FrameRuntime.cursor? mol (rootOwnedProfile profile root) (.actual cursor) =
      some cursor.node.rule1bRootDistance := by
  simp only [FrameRuntime.cursor?]
  rw [hgenerated]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [hprevious]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  exact observeNode_rootOwned_eq_rule1bRootDistance profile root cursor.node hreal hlast

/-- **Runtime cursor bridge (accepted profile).**  Membership in the accepted inventory
supplies the generated guard; the rooted-history and real-provenance facts are derived from the
executable profile acceptance.  The previous-neighbour guard remains an explicit hypothesis. -/
theorem profile?_cursor?_actual_rootOwned_eq_rule1bRootDistance
    {mol : RawMolecule} {center : CanonicalBranchNode}
    {profile : CanonicalTreeProfile.Profile} {root : ℕ}
    (cursor : CanonicalRerootCursor)
    (h : CanonicalTreeProfile.profile? mol center = some profile)
    (hroot : center.history.getLast? = some root)
    (hmember : cursor.node ∈ profile.generated)
    (hprevious : (cursor.previous?.all fun previous =>
      profile.generated.contains previous && (cursor.neighbors mol).contains previous) = true) :
    FrameRuntime.cursor? mol (rootOwnedProfile profile root) (.actual cursor) =
      some cursor.node.rule1bRootDistance := by
  obtain ⟨hreal, _hhead, hlast, _hnonempty, _hnodup, _hbounds⟩ :=
    profile?_node_facts h hroot hmember
  have hgenerated : (rootOwnedProfile profile root).generated.contains cursor.node = true := by
    change profile.generated.contains cursor.node = true
    rw [List.contains_eq_mem, decide_eq_true_iff]
    exact hmember
  have hprevious' : (cursor.previous?.all fun previous =>
      (rootOwnedProfile profile root).generated.contains previous &&
        (cursor.neighbors mol).contains previous) = true := by
    simpa only [rootOwnedProfile] using hprevious
  exact cursor?_actual_rootOwned_eq_rule1bRootDistance_of_checks mol profile root cursor
    hgenerated hprevious' hreal hlast

/-- Padding is the existing parent sidecar step: no coordinate is invented for the phantom. -/
theorem cursor?_padding_rootOwned_eq_map
    (mol : RawMolecule) (profile : CanonicalTreeProfile.Profile) (root : ℕ)
    (parent : FrameRuntime.Cursor) :
    FrameRuntime.cursor? mol (rootOwnedProfile profile root) (.padding parent) =
      (FrameRuntime.cursor? mol (rootOwnedProfile profile root) parent).map
        (fun distance => distance + 1) := rfl

/-- On a validated real parent, padding observes exactly the parent's legacy distance plus one. -/
theorem cursor?_padding_actual_rootOwned_eq_rule1bRootDistance
    (mol : RawMolecule) (profile : CanonicalTreeProfile.Profile) (root : ℕ)
    (cursor : CanonicalRerootCursor)
    (hparent : FrameRuntime.cursor? mol (rootOwnedProfile profile root) (.actual cursor) =
      some cursor.node.rule1bRootDistance) :
    FrameRuntime.cursor? mol (rootOwnedProfile profile root) (.padding (.actual cursor)) =
      some (cursor.node.rule1bRootDistance + 1) := by
  rw [cursor?_padding_rootOwned_eq_map, hparent]
  rfl

/-- The observed padding distance is exactly the Rule-1b distance stored on the production
padding node recomputed by `FrameRuntime.Cursor.original`, i.e. the exact legacy value. -/
theorem cursor?_padding_actual_rootOwned_eq_original_rule1bRootDistance
    (mol : RawMolecule) (profile : CanonicalTreeProfile.Profile) (root : ℕ)
    (cursor : CanonicalRerootCursor)
    (hparent : FrameRuntime.cursor? mol (rootOwnedProfile profile root) (.actual cursor) =
      some cursor.node.rule1bRootDistance) :
    FrameRuntime.cursor? mol (rootOwnedProfile profile root) (.padding (.actual cursor)) =
      some (FrameRuntime.Cursor.original mol (.padding (.actual cursor))).node.rule1bRootDistance := by
  rw [cursor?_padding_actual_rootOwned_eq_rule1bRootDistance mol profile root cursor hparent]
  rfl

/-! ## Policy coincidence at an original-root centre -/

/-- When the comparison owner already is the original root, the candidate and deployed policies
produce the same profile.  This is the structural C2-unchanged statement. -/
theorem policyProfile?_agree_at_original_root
    {profile : CanonicalTreeProfile.Profile} {root : ℕ}
    (hroot : profile.center.history.getLast? = some root)
    (hframe : profile.frame = (⟨[root]⟩ : CanonicalComparisonFrame.Frame)) :
    policyProfile? .originalRoot profile = policyProfile? .centerOwned profile := by
  rw [policyProfile?_originalRoot, policyProfile?_centerOwned,
    rootOwnedProfile?_eq_some hroot]
  congr 1
  cases profile with
  | mk center frame generated =>
      simp only [rootOwnedProfile]
      rw [← hframe]

/-! ## Actual C0 fixture: legacy `(0, 2)` restored -/

/-- The C0 profile's actual centre history ends at the original root C2. -/
theorem c0_root_extracted :
    c0Profile.center.history.getLast? = some c2Atom := by
  have hcenter : c0Profile.center = c0Node := profile?_center_eq profiles_resolve.2
  rw [hcenter]
  decide

/-- The C2 profile's actual centre history also ends at C2 (it is the original root). -/
theorem c2_root_extracted :
    c2Profile.center.history.getLast? = some c2Atom := by
  have hcenter : c2Profile.center = c2Root := profile?_center_eq profiles_resolve.1
  rw [hcenter]
  decide

/-- The current deployed C0 frame still observes the centre-owned distances `(1, 1)`; the
fixture is unchanged by this module. -/
theorem c0_current_frame_observations_unchanged :
    CanonicalComparisonFrame.observeNode c0Profile.frame c2Root = some 1 ∧
      CanonicalComparisonFrame.observeNode c0Profile.frame c3Node = some 1 := by
  constructor <;> decide

/-- **C0 legacy restoration.**  The root-owned C0 frame observes the original-root legacy
distances `(0, 2)` for the C2 parent arm and the outward C3 arm. -/
theorem c0_rootOwned_observes_legacy_distances :
    CanonicalComparisonFrame.observeNode (rootOwnedProfile c0Profile c2Atom).frame c2Root =
        some 0 ∧
      CanonicalComparisonFrame.observeNode (rootOwnedProfile c0Profile c2Atom).frame c3Node =
        some 2 := by
  constructor
  · rw [observeNode_rootOwned_eq_rule1bRootDistance c0Profile c2Atom c2Root
      (by decide) (by decide)]
    decide
  · rw [observeNode_rootOwned_eq_rule1bRootDistance c0Profile c2Atom c3Node
      (by decide) (by decide)]
    decide

/-- Paired form of the restored legacy profile. -/
theorem c0_rootOwned_legacy_pair :
    (CanonicalComparisonFrame.observeNode (rootOwnedProfile c0Profile c2Atom).frame c2Root,
     CanonicalComparisonFrame.observeNode (rootOwnedProfile c0Profile c2Atom).frame c3Node) =
      (some 0, some 2) := by
  rw [c0_rootOwned_observes_legacy_distances.1,
    c0_rootOwned_observes_legacy_distances.2]

/-- **C2 unchanged.**  At the original-root centre, the root-owned profile is the deployed
accepted profile. -/
theorem c2_rootOwned_eq_current :
    rootOwnedProfile c2Profile c2Atom = c2Profile := by
  have hp : c2Profile = ⟨c2Root, ⟨c2Root.history⟩, c2Profile.generated⟩ :=
    profile?_eq_self profiles_resolve.1
  rw [hp]
  rfl

theorem c2_rootOwned_frame_eq_current :
    (rootOwnedProfile c2Profile c2Atom).frame = c2Profile.frame := by
  rw [c2_rootOwned_eq_current]

/-- The candidate and deployed policies agree on the actual C2 profile. -/
theorem c2_policies_agree :
    policyProfile? .originalRoot c2Profile = policyProfile? .centerOwned c2Profile := by
  apply policyProfile?_agree_at_original_root
  · exact c2_root_extracted
  · rw [profile?_frame_eq profiles_resolve.1]
    rfl

/-- Consequently every runtime cursor observation at C2 is unchanged by the candidate policy. -/
theorem c2_cursor?_rootOwned_eq_current (cursor : FrameRuntime.Cursor) :
    FrameRuntime.cursor? mol (rootOwnedProfile c2Profile c2Atom) cursor =
      FrameRuntime.cursor? mol c2Profile cursor := by
  rw [c2_rootOwned_eq_current]

end RawRootOwnedComparisonProfile
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.rootOwnedProfile_center
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.rootOwnedProfile_generated
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.rootOwnedProfile_separates_owner_and_origin
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.rootOwnedProfile?_eq_some
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.rootOwnedProfile?_eq_none_iff
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.policyProfile?_centerOwned
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.policyProfile?_originalRoot
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.acceptedNodeCheck_facts
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.profile?_accepted
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.profile?_getLast?
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.profile?_eq_self
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.profile?_center_eq
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.profile?_frame_eq
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.profile?_node_facts
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.profile?_node_real
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.profile?_node_getLast
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.frameDistance_singleton_of_getLast?
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.observeNode_rootOwned_eq_rule1bRootDistance
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.profile?_observeNode_rootOwned_eq_rule1bRootDistance
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.cursor?_actual_rootOwned_eq_rule1bRootDistance_of_checks
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.profile?_cursor?_actual_rootOwned_eq_rule1bRootDistance
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.cursor?_padding_rootOwned_eq_map
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.cursor?_padding_actual_rootOwned_eq_rule1bRootDistance
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.cursor?_padding_actual_rootOwned_eq_original_rule1bRootDistance
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.policyProfile?_agree_at_original_root
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.c0_root_extracted
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.c2_root_extracted
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.c0_current_frame_observations_unchanged
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.c0_rootOwned_observes_legacy_distances
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.c0_rootOwned_legacy_pair
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.c2_rootOwned_eq_current
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.c2_rootOwned_frame_eq_current
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.c2_policies_agree
assert_kernel_only
  TetraStereo.OneCenter.RawRootOwnedComparisonProfile.c2_cursor?_rootOwned_eq_current
