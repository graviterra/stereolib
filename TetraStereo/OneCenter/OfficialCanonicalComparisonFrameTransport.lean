






























































import TetraStereo.OneCenter.CanonicalComparisonFrame
import TetraStereo.OneCenter.RawLocalizedChildNodeTransport
import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo
namespace OneCenter
namespace OfficialCanonicalComparisonFrameTransport

open TetraStereo.OneCenter.RawLocalizedChildNodeTransport

variable {V : Type*} [DecidableEq V]

/-! ## Official observation -/

/-- The actual rootward prefix used for a duplicate observation: the mapped node history, with the
current atom removed, reversed from the root, and truncated at the stored duplicate distance.  This
is the official counterpart of `CanonicalComparisonFrame.duplicateRootwardCoordinate`. -/
def officialHistoryCoordinate (toRaw : V → ℕ) (history : List V)
    (storedDistance : ℕ) : List ℕ :=
  (history.map toRaw).tail.reverse.take (storedDistance + 1)

/-- Node-level actual duplicate rootward coordinate. -/
def officialDuplicateRootwardCoordinate (toRaw : V → ℕ) (node : OfficialCIPNode V)
    (storedDistance : ℕ) : List ℕ :=
  officialHistoryCoordinate toRaw node.history storedDistance

/-- The actual truncation bound for the official duplicate coordinate.  This is an `abbrev` so
that the executable `if` in the guarded observation can synthesize its `Decidable` instance. -/
abbrev officialHistoryBound (toRaw : V → ℕ) (history : List V) (storedDistance : ℕ) : Prop :=
  storedDistance + 1 ≤ (history.map toRaw).tail.length

/-- Node-level actual duplicate bound. -/
abbrev officialDuplicateBound (toRaw : V → ℕ) (node : OfficialCIPNode V)
    (storedDistance : ℕ) : Prop :=
  officialHistoryBound toRaw node.history storedDistance

/-- Guarded duplicate observation: an out-of-bound stored coordinate is refused (`none`), never
totalized. -/
def officialDuplicateObservationOfHistory? (toRaw : V → ℕ)
    (frame : CanonicalComparisonFrame.Frame) (history : List V)
    (storedDistance : ℕ) : Option ℕ :=
  if officialHistoryBound toRaw history storedDistance then
    some (CanonicalComparisonFrame.pathDistance frame.originHistory.reverse
      (officialHistoryCoordinate toRaw history storedDistance))
  else none

/-- The official Option-valued observer, reading provenance and the *actual* mapped history.  Real
atoms use the frame metric on the full history; ring and multiple-bond duplicates use the actual
duplicate rootward coordinate and bound; explicit placeholders are refused. -/
def observeOfficialProvenance? (toRaw : V → ℕ)
    (frame : CanonicalComparisonFrame.Frame) (provenance : OfficialCIPNodeProvenance)
    (history : List V) : Option ℕ :=
  match provenance with
  | .realAtom =>
      some (CanonicalComparisonFrame.frameDistance frame.originHistory (history.map toRaw))
  | .multipleBondDuplicate stored =>
      officialDuplicateObservationOfHistory? toRaw frame history stored
  | .ringDuplicate stored =>
      officialDuplicateObservationOfHistory? toRaw frame history stored
  | .placeholder _ _ => none

/-- Official observation of a node under an arbitrary fixed frame. -/
def observeOfficialWith? (toRaw : V → ℕ) (frame : CanonicalComparisonFrame.Frame)
    (node : OfficialCIPNode V) : Option ℕ :=
  observeOfficialProvenance? toRaw frame node.provenance node.history

/-- Official observation whose origin history is the *actual* target history mapped by `toRaw`.
No caller-supplied origin and no caller-supplied distance are accepted. -/
def observeOfficialAtTarget? (toRaw : V → ℕ) (target : OfficialCIPNode V)
    (node : OfficialCIPNode V) : Option ℕ :=
  observeOfficialWith? toRaw ⟨target.history.map toRaw⟩ node

/-- Production observer on `Fin` atoms: the origin is the actual target history mapped by
`Fin.val`. -/
def observeOfficial? {n : ℕ} (target node : OfficialCIPNode (Fin n)) : Option ℕ :=
  observeOfficialAtTarget? (fun atom : Fin n => atom.val) target node

/-! ## Canonical value-level observer -/

/-- Value-level presentation of `CanonicalComparisonFrame.observeNode` that takes provenance and
history explicitly, so provenance can be destructed as an ordinary variable in transport proofs. -/
def canonicalDuplicateObservation? (frame : CanonicalComparisonFrame.Frame)
    (history : List ℕ) (storedDistance : ℕ) : Option ℕ :=
  if storedDistance + 1 ≤ history.tail.length then
    some (CanonicalComparisonFrame.pathDistance frame.originHistory.reverse
      (history.tail.reverse.take (storedDistance + 1)))
  else none

/-- Canonical value-level observer. -/
def observeCanonicalProvenance? (frame : CanonicalComparisonFrame.Frame)
    (provenance : RawMolecule.CanonicalNodeProvenance) (history : List ℕ) : Option ℕ :=
  match provenance with
  | .realAtom => some (CanonicalComparisonFrame.frameDistance frame.originHistory history)
  | .multipleBondDuplicate stored => canonicalDuplicateObservation? frame history stored
  | .ringDuplicate stored => canonicalDuplicateObservation? frame history stored
  | .phantom _ => none

/-- The value-level canonical observer is definitionally the frame observer. -/
theorem observeNode_eq_observeCanonicalProvenance? (frame : CanonicalComparisonFrame.Frame)
    (node : RawMolecule.CanonicalBranchNode) :
    CanonicalComparisonFrame.observeNode frame node =
      observeCanonicalProvenance? frame node.provenance node.history := by
  rcases node with ⟨atom, parent, history, provenance⟩
  cases provenance <;> rfl

/-! ## Observation transport -/

/-- Corresponding provenances, mapped histories and origin histories give the same Option-valued
observation.  The proof destructs the provenance correspondence; no stored-distance equality is
assumed. -/
theorem observeOfficialProvenance?_eq
    (toRaw : V → ℕ) (originO originC : List ℕ)
    (provenanceO : OfficialCIPNodeProvenance)
    (provenanceC : RawMolecule.CanonicalNodeProvenance)
    (historyO : List V) (historyC : List ℕ)
    (horigin : originO = originC)
    (hhistory : historyO.map toRaw = historyC)
    (hprov : NodeProvenanceCorresponds provenanceO provenanceC) :
    observeOfficialProvenance? toRaw ⟨originO⟩ provenanceO historyO =
      observeCanonicalProvenance? ⟨originC⟩ provenanceC historyC := by
  cases hprov with
  | realAtom =>
      simp only [observeOfficialProvenance?, observeCanonicalProvenance?, horigin, hhistory]
  | multipleBondDuplicate distance =>
      simp only [observeOfficialProvenance?, observeCanonicalProvenance?,
        officialDuplicateObservationOfHistory?, canonicalDuplicateObservation?,
        officialHistoryBound, officialHistoryCoordinate, horigin, hhistory]
  | ringDuplicate distance =>
      simp only [observeOfficialProvenance?, observeCanonicalProvenance?,
        officialDuplicateObservationOfHistory?, canonicalDuplicateObservation?,
        officialHistoryBound, officialHistoryCoordinate, horigin, hhistory]

/-- **Core observation transport.**  For corresponding official target/node and canonical
target/node, the official observation computed from the *actual* official target history agrees
with `CanonicalComparisonFrame.observeNode` at the canonical frame
`{ originHistory := targetC.history }`. -/
theorem observeOfficialAtTarget?_eq_observeNode
    (toRaw : V → ℕ)
    {targetO nodeO : OfficialCIPNode V}
    {targetC nodeC : RawMolecule.CanonicalBranchNode}
    (htarget : NodeCorresponds toRaw targetO targetC)
    (hnode : NodeCorresponds toRaw nodeO nodeC) :
    observeOfficialAtTarget? toRaw targetO nodeO =
      CanonicalComparisonFrame.observeNode ⟨targetC.history⟩ nodeC := by
  unfold observeOfficialAtTarget? observeOfficialWith?
  rw [observeNode_eq_observeCanonicalProvenance?]
  exact observeOfficialProvenance?_eq toRaw (targetO.history.map toRaw) targetC.history
    nodeO.provenance nodeC.provenance nodeO.history nodeC.history
    htarget.history hnode.history hnode.provenance

/-- **Production observation transport (mapped `Fin.val`).** -/
theorem observeOfficial?_eq_observeNode
    {n : ℕ} {targetO nodeO : OfficialCIPNode (Fin n)}
    {targetC nodeC : RawMolecule.CanonicalBranchNode}
    (htarget : NodeCorresponds (fun atom : Fin n => atom.val) targetO targetC)
    (hnode : NodeCorresponds (fun atom : Fin n => atom.val) nodeO nodeC) :
    observeOfficial? targetO nodeO =
      CanonicalComparisonFrame.observeNode ⟨targetC.history⟩ nodeC := by
  unfold observeOfficial?
  exact observeOfficialAtTarget?_eq_observeNode (fun atom : Fin n => atom.val) htarget hnode

/-- Option refusal is preserved: the official observation is `none` exactly when the canonical
observation is `none`. -/
theorem observeOfficial?_eq_none_iff
    {n : ℕ} {targetO nodeO : OfficialCIPNode (Fin n)}
    {targetC nodeC : RawMolecule.CanonicalBranchNode}
    (htarget : NodeCorresponds (fun atom : Fin n => atom.val) targetO targetC)
    (hnode : NodeCorresponds (fun atom : Fin n => atom.val) nodeO nodeC) :
    observeOfficial? targetO nodeO = none ↔
      CanonicalComparisonFrame.observeNode ⟨targetC.history⟩ nodeC = none := by
  rw [observeOfficial?_eq_observeNode htarget hnode]

/-- Option refusal is preserved (generic form). -/
theorem observeOfficialAtTarget?_eq_none_iff
    (toRaw : V → ℕ)
    {targetO nodeO : OfficialCIPNode V}
    {targetC nodeC : RawMolecule.CanonicalBranchNode}
    (htarget : NodeCorresponds toRaw targetO targetC)
    (hnode : NodeCorresponds toRaw nodeO nodeC) :
    observeOfficialAtTarget? toRaw targetO nodeO = none ↔
      CanonicalComparisonFrame.observeNode ⟨targetC.history⟩ nodeC = none := by
  rw [observeOfficialAtTarget?_eq_observeNode toRaw htarget hnode]

/-! ### Actual duplicate coordinate, bound and refusal -/

/-- The official duplicate rootward coordinate is exactly the canonical one after transporting the
mapped history. -/
theorem officialDuplicateRootwardCoordinate_eq
    (toRaw : V → ℕ)
    {nodeO : OfficialCIPNode V} {nodeC : RawMolecule.CanonicalBranchNode}
    (h : NodeCorresponds toRaw nodeO nodeC) (storedDistance : ℕ) :
    officialDuplicateRootwardCoordinate toRaw nodeO storedDistance =
      CanonicalComparisonFrame.duplicateRootwardCoordinate nodeC storedDistance := by
  unfold officialDuplicateRootwardCoordinate officialHistoryCoordinate
    CanonicalComparisonFrame.duplicateRootwardCoordinate
  rw [h.history]

/-- The actual official truncation bound is exactly the canonical bound. -/
theorem officialDuplicateBound_iff
    (toRaw : V → ℕ)
    {nodeO : OfficialCIPNode V} {nodeC : RawMolecule.CanonicalBranchNode}
    (h : NodeCorresponds toRaw nodeO nodeC) (storedDistance : ℕ) :
    officialDuplicateBound toRaw nodeO storedDistance ↔
      storedDistance + 1 ≤ nodeC.history.tail.length := by
  unfold officialDuplicateBound officialHistoryBound
  rw [h.history]

/-- Explicit placeholder nodes are refused by the official observer. -/
theorem observeOfficialWith?_placeholder (toRaw : V → ℕ)
    (frame : CanonicalComparisonFrame.Frame) (node : OfficialCIPNode V)
    (kind : OfficialPhantomNodeKind) (storedDistance : ℕ)
    (placeholder : node.provenance = .placeholder kind storedDistance) :
    observeOfficialWith? toRaw frame node = none := by
  simp [observeOfficialWith?, observeOfficialProvenance?, placeholder]

/-- An out-of-bound multiple-bond duplicate coordinate is refused, never totalized. -/
theorem observeOfficialWith?_multipleBondDuplicate_refusal (toRaw : V → ℕ)
    (frame : CanonicalComparisonFrame.Frame) (node : OfficialCIPNode V)
    (storedDistance : ℕ)
    (kind : node.provenance = .multipleBondDuplicate storedDistance)
    (invalid : ¬ officialDuplicateBound toRaw node storedDistance) :
    observeOfficialWith? toRaw frame node = none := by
  have hinvalid : ¬ officialHistoryBound toRaw node.history storedDistance := by
    simpa only [officialDuplicateBound] using invalid
  unfold observeOfficialWith? observeOfficialProvenance?
  rw [kind]
  change officialDuplicateObservationOfHistory? toRaw frame node.history storedDistance = none
  unfold officialDuplicateObservationOfHistory?
  exact if_neg hinvalid

/-- An out-of-bound ring duplicate coordinate is refused, never totalized. -/
theorem observeOfficialWith?_ringDuplicate_refusal (toRaw : V → ℕ)
    (frame : CanonicalComparisonFrame.Frame) (node : OfficialCIPNode V)
    (storedDistance : ℕ)
    (kind : node.provenance = .ringDuplicate storedDistance)
    (invalid : ¬ officialDuplicateBound toRaw node storedDistance) :
    observeOfficialWith? toRaw frame node = none := by
  have hinvalid : ¬ officialHistoryBound toRaw node.history storedDistance := by
    simpa only [officialDuplicateBound] using invalid
  unfold observeOfficialWith? observeOfficialProvenance?
  rw [kind]
  change officialDuplicateObservationOfHistory? toRaw frame node.history storedDistance = none
  unfold officialDuplicateObservationOfHistory?
  exact if_neg hinvalid

/-- A real atom is observed with the frame metric on the actual mapped history. -/
theorem observeOfficialWith?_real (toRaw : V → ℕ)
    (frame : CanonicalComparisonFrame.Frame) (node : OfficialCIPNode V)
    (real : node.provenance = .realAtom) :
    observeOfficialWith? toRaw frame node =
      some (CanonicalComparisonFrame.frameDistance frame.originHistory
        (node.history.map toRaw)) := by
  simp [observeOfficialWith?, observeOfficialProvenance?, real]

/-! ## Padding through the parent sidecar -/

/-- Padding is observed through its parent, with the same `.map (fun d => d + 1)` step as
`CanonicalComparisonFrame.PaddingSidecar.distance?`.  The parent observation may itself refuse. -/
theorem cursor?_padding_eq_sidecar
    (mol : RawMolecule) (profile : CanonicalTreeProfile.Profile)
    (frame : CanonicalComparisonFrame.Frame)
    (parent : FrameRuntime.Cursor) (parentC : RawMolecule.CanonicalBranchNode)
    (storedDistance : ℕ)
    (hparent : FrameRuntime.cursor? mol profile parent =
      CanonicalComparisonFrame.observeNode frame parentC) :
    FrameRuntime.cursor? mol profile (.padding parent) =
      (CanonicalComparisonFrame.paddingSidecar frame parentC storedDistance).distance? := by
  rw [CanonicalComparisonFrame.padding_from_parent]
  rw [show FrameRuntime.cursor? mol profile (.padding parent) =
      (FrameRuntime.cursor? mol profile parent).map (fun distance => distance + 1) from rfl,
    hparent]

/-! ## Successful profile frame and runtime cursor agreement -/

/-- A successful `CanonicalTreeProfile.profile?` fixes the frame origin to the actual centre
history. -/
theorem profile?_frame_eq (mol : RawMolecule) (center : RawMolecule.CanonicalBranchNode)
    (profile : CanonicalTreeProfile.Profile)
    (h : CanonicalTreeProfile.profile? mol center = some profile) :
    profile.frame = (⟨center.history⟩ : CanonicalComparisonFrame.Frame) := by
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
               provenance := RawMolecule.CanonicalNodeProvenance.realAtom }] with
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

/-- A successful profile contains its own centre in the generated list. -/
theorem profile?_generated_contains_center (mol : RawMolecule)
    (center : RawMolecule.CanonicalBranchNode)
    (profile : CanonicalTreeProfile.Profile)
    (h : CanonicalTreeProfile.profile? mol center = some profile) :
    profile.generated.contains center = true := by
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
               provenance := RawMolecule.CanonicalNodeProvenance.realAtom }] with
        | none =>
            simp only [hgenerated] at h
            cases h
        | some generated =>
            simp only [hgenerated] at h
            split at h
            · cases h
            · rename_i hnotcontains
              split at h
              · cases h
              · have hprofile : profile = ⟨center, ⟨center.history⟩, generated⟩ :=
                  (Option.some.inj h).symm
                subst profile
                have hb : generated.contains center = true := by
                  cases hc : generated.contains center with
                  | true => rfl
                  | false => exact absurd (by rw [hc]; rfl) hnotcontains
                exact hb

/-- Membership in the generated list yields the executable `contains` check. -/
theorem generated_contains_of_mem (profile : CanonicalTreeProfile.Profile)
    {node : RawMolecule.CanonicalBranchNode} (member : node ∈ profile.generated) :
    profile.generated.contains node = true := by
  simpa [List.contains_eq_mem] using member

/-- **Runtime cursor agreement (checks explicit).**  When the existing generated-node and previous
neighbour checks pass, `FrameRuntime.cursor?` observes the canonical frame observer at that node. -/
theorem cursor?_actual_eq_observeNode_of_checks
    (mol : RawMolecule) (profile : CanonicalTreeProfile.Profile)
    (frame : CanonicalComparisonFrame.Frame)
    (cursor : CanonicalRerootCursor)
    (hframe : profile.frame = frame)
    (hgenerated : profile.generated.contains cursor.node = true)
    (hprevious : (cursor.previous?.all fun previous =>
      profile.generated.contains previous && (cursor.neighbors mol).contains previous) = true) :
    FrameRuntime.cursor? mol profile (.actual cursor) =
      CanonicalComparisonFrame.observeNode frame cursor.node := by
  simp only [FrameRuntime.cursor?]
  rw [hgenerated]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [hprevious]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, hframe]

/-- **Runtime cursor agreement (successful profile).**  The profile success supplies the frame
origin; the existing generated/neighbour checks remain explicit hypotheses. -/
theorem profile?_cursor?_actual_eq_observeNode
    (mol : RawMolecule) (center : RawMolecule.CanonicalBranchNode)
    (profile : CanonicalTreeProfile.Profile)
    (cursor : CanonicalRerootCursor)
    (hprofile : CanonicalTreeProfile.profile? mol center = some profile)
    (hgenerated : profile.generated.contains cursor.node = true)
    (hprevious : (cursor.previous?.all fun previous =>
      profile.generated.contains previous && (cursor.neighbors mol).contains previous) = true) :
    FrameRuntime.cursor? mol profile (.actual cursor) =
      CanonicalComparisonFrame.observeNode ⟨center.history⟩ cursor.node := by
  rw [cursor?_actual_eq_observeNode_of_checks mol profile ⟨center.history⟩ cursor
    (profile?_frame_eq mol center profile hprofile) hgenerated hprevious]

/-- **Runtime cursor agreement (membership-derived check).**  The generated-node check is derived
from actual membership in the profile's generated list, not dropped. -/
theorem profile?_cursor?_actual_eq_observeNode_of_mem
    (mol : RawMolecule) (center : RawMolecule.CanonicalBranchNode)
    (profile : CanonicalTreeProfile.Profile)
    (cursor : CanonicalRerootCursor)
    (hprofile : CanonicalTreeProfile.profile? mol center = some profile)
    (hmember : cursor.node ∈ profile.generated)
    (hprevious : (cursor.previous?.all fun previous =>
      profile.generated.contains previous && (cursor.neighbors mol).contains previous) = true) :
    FrameRuntime.cursor? mol profile (.actual cursor) =
      CanonicalComparisonFrame.observeNode ⟨center.history⟩ cursor.node :=
  profile?_cursor?_actual_eq_observeNode mol center profile cursor hprofile
    (generated_contains_of_mem profile hmember) hprevious

/-- The centre cursor is observed, with the generated check derived from profile success. -/
theorem profile?_cursor?_center_eq
    (mol : RawMolecule) (center : RawMolecule.CanonicalBranchNode)
    (profile : CanonicalTreeProfile.Profile)
    (hprofile : CanonicalTreeProfile.profile? mol center = some profile) :
    FrameRuntime.cursor? mol profile
        (.actual ({ node := center } : CanonicalRerootCursor)) =
      CanonicalComparisonFrame.observeNode ⟨center.history⟩ center := by
  rw [profile?_cursor?_actual_eq_observeNode mol center profile
    ({ node := center } : CanonicalRerootCursor) hprofile
    (profile?_generated_contains_center mol center profile hprofile) (by simp)]

/-- **Combined endpoint.**  If the canonical target is the profile centre and the runtime cursor
observes a node corresponding to the official node, then the runtime cursor observation equals the
official observation computed from the actual official target history.  The existing runtime
checks are explicit (`hprevious`); the generated check is derived from `cursor.node = center`. -/
theorem profile?_cursor?_actual_eq_observeOfficial?
    {n : ℕ} (mol : RawMolecule) (center : RawMolecule.CanonicalBranchNode)
    (profile : CanonicalTreeProfile.Profile)
    (cursor : CanonicalRerootCursor)
    {targetO nodeO : OfficialCIPNode (Fin n)}
    (hprofile : CanonicalTreeProfile.profile? mol center = some profile)
    (hcenter : cursor.node = center)
    (htarget : NodeCorresponds (fun atom : Fin n => atom.val) targetO center)
    (hnode : NodeCorresponds (fun atom : Fin n => atom.val) nodeO cursor.node)
    (hprevious : (cursor.previous?.all fun previous =>
      profile.generated.contains previous && (cursor.neighbors mol).contains previous) = true) :
    FrameRuntime.cursor? mol profile (.actual cursor) = observeOfficial? targetO nodeO := by
  have hgenerated : profile.generated.contains cursor.node = true := by
    rw [hcenter]
    exact profile?_generated_contains_center mol center profile hprofile
  rw [profile?_cursor?_actual_eq_observeNode mol center profile cursor hprofile hgenerated hprevious]
  exact (observeOfficial?_eq_observeNode htarget hnode).symm

end OfficialCanonicalComparisonFrameTransport
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.observeNode_eq_observeCanonicalProvenance?
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.observeOfficialProvenance?_eq
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?_eq_observeNode
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.observeOfficial?_eq_observeNode
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.observeOfficial?_eq_none_iff
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?_eq_none_iff
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.officialDuplicateRootwardCoordinate_eq
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.officialDuplicateBound_iff
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.observeOfficialWith?_placeholder
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.observeOfficialWith?_multipleBondDuplicate_refusal
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.observeOfficialWith?_ringDuplicate_refusal
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.observeOfficialWith?_real
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.cursor?_padding_eq_sidecar
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.profile?_frame_eq
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.profile?_generated_contains_center
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.generated_contains_of_mem
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.cursor?_actual_eq_observeNode_of_checks
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.profile?_cursor?_actual_eq_observeNode
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.profile?_cursor?_actual_eq_observeNode_of_mem
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.profile?_cursor?_center_eq
assert_kernel_only
  TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport.profile?_cursor?_actual_eq_observeOfficial?
