import TetraStereo.OneCenter.LocalizedMarkedRawCarrierBridge
import TetraStereo.OneCenter.LocalizedMarkedUncappedOperations
import TetraStereo.OneCenter.CanonicalGeneratedProfileAdmission
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Executable root-specific lookup of raw occurrences in the certified carrier

The lookup recovers the original root from the raw history, checks its bound, and searches only
that root's existing official occurrence enumeration. It never enumerates all molecular roots.
Its test checks every field of `NodeCorresponds`, including duplicate provenance and distance;
unsupported placeholders refuse. The returned subtype carries actual carrier membership, whose
proof is erased from execution. No choice operation is used in the executable definitions.

For every reached raw occurrence under the stated finite single-bond intake conditions, the
unbounded transport theorem constructs a matching enumerated witness and proves lookup success.
No carrier, address, comparison result, descriptor, or expected output is supplied by the caller.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedCarrierLookup

open CertifiedLocalizedCIPInput RawLocalizedChildNodeTransport
open LocalizedMarkedRawCarrierBridge LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedUncappedOperations (generated_of_reachedFrom)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- The exact provenance relation already used by raw/certified node transport. -/
def rawProvenance? : OfficialCIPNodeProvenance → Option RawMolecule.CanonicalNodeProvenance
  | .realAtom => some .realAtom
  | .multipleBondDuplicate distance => some (.multipleBondDuplicate distance)
  | .ringDuplicate distance => some (.ringDuplicate distance)
  | .placeholder _ _ => none

theorem rawProvenance?_eq_some_iff (official : OfficialCIPNodeProvenance)
    (raw : RawMolecule.CanonicalNodeProvenance) :
    rawProvenance? official = some raw ↔ NodeProvenanceCorresponds official raw := by
  constructor
  · intro matched
    cases official with
    | realAtom =>
        have same : RawMolecule.CanonicalNodeProvenance.realAtom = raw := Option.some.inj matched
        subst raw
        exact .realAtom
    | multipleBondDuplicate distance =>
        have same : RawMolecule.CanonicalNodeProvenance.multipleBondDuplicate distance = raw :=
          Option.some.inj matched
        subst raw
        exact .multipleBondDuplicate distance
    | ringDuplicate distance =>
        have same : RawMolecule.CanonicalNodeProvenance.ringDuplicate distance = raw :=
          Option.some.inj matched
        subst raw
        exact .ringDuplicate distance
    | placeholder _ _ => cases matched
  · intro corresponds
    cases corresponds <;> rfl

/-- Computable full node correspondence, not an atom-only or history-only lookup predicate. -/
def nodeMatches (input : CertifiedLocalizedCIPInput) (official : OfficialCIPNode input.Atom)
    (raw : Node) : Bool :=
  official.current?.map (fun atom => atom.val) == some raw.atom &&
    official.history.map (fun atom => atom.val) == raw.history &&
    official.history.head? == official.current? &&
    rawProvenance? official.provenance == some raw.provenance &&
    official.parent?.map (fun atom => atom.val) ==
      (if raw.parent = raw.atom then none else some raw.parent)

theorem nodeMatches_iff (input : CertifiedLocalizedCIPInput)
    (official : OfficialCIPNode input.Atom) (raw : Node) :
    nodeMatches input official raw = true ↔
      NodeCorresponds (fun atom : input.Atom => atom.val) official raw := by
  simp only [nodeMatches, Bool.and_eq_true, beq_iff_eq, rawProvenance?_eq_some_iff, and_assoc]
  constructor
  · rintro ⟨current, history, head, provenance, parent⟩
    exact ⟨current, history, head, provenance, parent⟩
  · intro corresponds
    exact ⟨corresponds.current, corresponds.history, corresponds.head,
      corresponds.provenance, corresponds.parent⟩

/-- Only one rooted enumeration is executed. Global membership is an erased proof attached to
each rooted frame, not a second search or an all-roots runtime check. -/
def rootedCarrier (input : CertifiedLocalizedCIPInput) (fuel : Nat) (root : input.Atom) :
    List (input.LocalizedCIPOccurrence fuel) :=
  (input.localizedOccurrencesAtAtom fuel root).attach.map fun entry =>
    ⟨entry.1, by
      unfold localizedOccurrences
      rw [List.mem_dedup, List.mem_flatMap]
      exact ⟨root, by simp, entry.2⟩⟩

theorem mem_rootedCarrier_iff (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.Atom) (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence ∈ rootedCarrier input fuel root ↔
      occurrence.1 ∈ input.localizedOccurrencesAtAtom fuel root := by
  constructor
  · intro member
    obtain ⟨entry, _, same⟩ := List.mem_map.mp member
    have valueEq := congrArg Subtype.val same
    rw [← valueEq]
    exact entry.2
  · intro member
    apply List.mem_map.mpr
    refine ⟨⟨occurrence.1, member⟩, by simp, ?_⟩
    exact Subtype.ext rfl

def lookupAtRoot? (input : CertifiedLocalizedCIPInput) (root : input.Atom) (raw : Node) :
    Option (input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1)) :=
  (rootedCarrier input (input.certified.input.molecule.atomCount + 1) root).find?
    (fun occurrence => nodeMatches input occurrence.1.node raw)

/-- Malformed empty or out-of-range roots refuse before the selected-root enumeration. -/
def lookup? (input : CertifiedLocalizedCIPInput) (raw : Node) :
    Option (input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1)) :=
  match raw.history.getLast? with
  | none => none
  | some root =>
      if bounded : root < input.certified.input.molecule.atomCount then
        lookupAtRoot? input ⟨root, bounded⟩ raw
      else none

theorem lookupAtRoot?_sound (input : CertifiedLocalizedCIPInput) (root : input.Atom)
    (raw : Node)
    (occurrence : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (found : lookupAtRoot? input root raw = some occurrence) :
    occurrence.1.root = root ∧
      NodeCorresponds (fun atom : input.Atom => atom.val) occurrence.1.node raw := by
  have member := List.mem_of_find?_eq_some found
  have rooted := (mem_rootedCarrier_iff input _ root occurrence).mp member
  have derived := (input.mem_localizedOccurrencesAtAtom_iff _ root occurrence.1).mp rooted
  have tested := List.find?_some found
  exact ⟨input.declarativeLocalizedOccurrenceSubtree_root_eq derived,
    (nodeMatches_iff input occurrence.1.node raw).mp tested⟩

theorem lookup?_sound (input : CertifiedLocalizedCIPInput) (raw : Node)
    (occurrence : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (found : lookup? input raw = some occurrence) :
    NodeCorresponds (fun atom : input.Atom => atom.val) occurrence.1.node raw := by
  unfold lookup? at found
  split at found
  · contradiction
  · split at found
    · exact (lookupAtRoot?_sound input _ raw occurrence found).2
    · contradiction

/-- Actual raw reachability constructs a matching rooted search witness at the universal depth.
The search's returned result, rather than a chosen witness, is bound to the original raw root. -/
theorem lookup?_exists_of_reachedFrom
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : SingleBonded mol) (root : Nat) (valid : root < mol.atomCount)
    (node : Node) (reached : ReachedFrom mol root node) :
    ∃ occurrence : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1),
      lookup? input node = some occurrence ∧
      occurrence.1.root = localizedIndexOf mol input agreement ⟨root, valid⟩ ∧
      NodeCorresponds (fun atom : input.Atom => atom.val) occurrence.1.node node := by
  obtain ⟨address, official, path, corresponds⟩ := reachedFrom_unbounded_corresponds mol input
    agreement wellFormed unique supported single root valid node reached
  let rootAtom := localizedIndexOf mol input agreement ⟨root, valid⟩
  let witness := input.localizedUnboundedOccurrenceAtAtom rootAtom path
  have rooted : witness.1 ∈ input.localizedOccurrencesAtAtom
      (input.certified.input.molecule.atomCount + 1) rootAtom :=
    input.localizedOccurrenceUniversalDepth_covers_atom rootAtom path
  have member := (mem_rootedCarrier_iff input _ rootAtom witness).mpr rooted
  have matched : nodeMatches input witness.1.node node = true :=
    (nodeMatches_iff input witness.1.node node).mpr corresponds
  have existsResult : (lookupAtRoot? input rootAtom node).isSome :=
    List.find?_isSome.mpr ⟨witness, member, matched⟩
  obtain ⟨occurrence, found⟩ := Option.isSome_iff_exists.mp existsResult
  have sound := lookupAtRoot?_sound input rootAtom node occurrence found
  have last := CanonicalGeneratedProfileAdmission.generated_history_getLast mol root
    (generated_of_reachedFrom mol root node reached)
  have bounded : root < input.certified.input.molecule.atomCount := rootAtom.isLt
  refine ⟨occurrence, ?_, sound.1, sound.2⟩
  simpa only [lookup?, last, dif_pos bounded] using found

end TetraStereo.OneCenter.LocalizedMarkedCarrierLookup

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCarrierLookup.rawProvenance?
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCarrierLookup.rawProvenance?_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCarrierLookup.nodeMatches
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCarrierLookup.nodeMatches_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCarrierLookup.rootedCarrier
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCarrierLookup.mem_rootedCarrier_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCarrierLookup.lookupAtRoot?
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCarrierLookup.lookup?
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCarrierLookup.lookupAtRoot?_sound
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCarrierLookup.lookup?_sound
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCarrierLookup.lookup?_exists_of_reachedFrom
