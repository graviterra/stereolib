import TetraStereo.OneCenter.IR9PolyhedralSemantics
import TetraStereo.OneCenter.OrganicStereoInteractionRoles
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo.OneCenter

open RedBookIR9

/-!
# Source-bound donor-occurrence encoding for IR-9.3.5

`RedBookIR9.DonorOccurrence` records a base priority number, a ligand identity and kind, a
coordinating-fragment identity and kind, and an *arbitrary* `isPolydentate : Prop`.  It therefore
cannot, on its own, say which actual source atom donates, which actual source interaction carries
the coordination, or why one occurrence is polydentate.  This module supplies that missing
molecule-bound layer.

Levels are kept explicitly separate, matching IR-9.3.5.3:

* **Ligand level.** `IsPolydentate ledger ligandGroup` is *derived* from the number of distinct
  recorded donor atoms bound to one centre inside one ligand occurrence
  (`recordedLigandDenticity`).  It is **not** the fragment count and **not** an arbitrary
  proposition.  Two donor fragments of one ligand therefore both receive the true ligand-level
  flag even when each fragment records exactly one donor; the two-fragment bidentate example
  `two_fragment_bidentate_example` states this.
* **Fragment level.** `recordedFragmentKappa ledger fragmentGroup` is ordinary atom-donor
  κ-denticity *within* one coordinating fragment.  It is not used for the old record's
  `isPolydentate` field; it is the atom-count diagnostic.

Everything computed here is **recorded** denticity: it counts the incidences actually present in
the supplied ledger.  No completeness of a physical donor set is claimed.  A caller that has a
finite, independently supplied donor set can pass `LigandDonorSupportCertificate`, which then
proves that the recorded cardinality equals that supplied cardinality
(`recordedLigandDenticity_eq_card_of_certificate`).

Other boundaries:

* `DonorIncidence` binds one donor atom and one metal centre to a concrete, separately indexed
  `Fin molecule.interactions.length` source interaction.  The direction and source-support
  evidence come from the companion interaction-role layer
  (`InteractionRoles.DirectedEnrichment`); this module does not re-derive them.
* `encode` is the **membership-checked recorded encoding**: its only premise is that the
  incidence is a member of the ledger.  It does not assert donor-support membership or physical
  completeness; the resulting `isPolydentate` flag is the derived **recorded** ligand-level
  condition.  `encodeRaw` is the raw metadata projection; the occurrence list stores raw
  metadata, and `occurrences_get_encode` shows that each stored occurrence is the encoding of
  the incidence at the same position.
* `PhysicalDonorOccurrence` strengthens `encode` with explicit finite ligand and fragment donor
  supports, identity agreement with those supports, and membership of the donor atom in the
  fragment support.  It still carries **no** completeness certificate, so its denticity flag
  also remains **recorded** denticity: it is *not* a claim that the recorded donor set is the
  full physical donor set.
* Only `LigandDonorSupportCertificate` — both subset directions between a supplied finite
  ligand donor support and the recorded donor set — identifies the recorded ligand denticity
  with the cardinality of that supplied support
  (`recordedLigandDenticity_eq_card_of_certificate`).  No theorem here claims physical
  completeness of any grouping or of any denticity number without such an explicit certificate.
* Donor atom identities are deliberately **not** part of the old record, so encoding is not
  injective (`encode_not_injective_of_donor_ne`, `no_donor_identity_recovery`, and the concrete
  witness `witness_encode_not_injective`).  Only the complete enriched `DonorLedger` round-trips.
* Priorities are supplied input numbers (`basePriority`).  Nothing here derives a CIP ranking.
* Hapticity η belongs to `InteractionRoles.HapticLigand.eta` and is *not* κ.  This module contains
  no η definition and never converts a haptic donor support into independent κ donors.
* This is a representation layer, not a chemical-admissibility oracle.
-/

namespace DonorOccurrenceEncoding

variable {LigandId LigandKind FragmentId FragmentKind : Type*}
variable [DecidableEq LigandId] [DecidableEq LigandKind]
variable [DecidableEq FragmentId] [DecidableEq FragmentKind]

/-! ## Ligand-level and fragment-level occurrence groups -/

/-- The identity of one coordinating-fragment occurrence around one metal centre. -/
structure FragmentGroup (LigandId LigandKind FragmentId FragmentKind : Type*) (atomCount : Nat) where
  ligand : LigandId
  ligandKind : LigandKind
  fragment : FragmentId
  fragmentKind : FragmentKind
  centre : Fin atomCount
  deriving DecidableEq

/-- The identity of one ligand occurrence around one metal centre.  IR-9.3.5.3 judges
polydenticity at this level, so fragment identities are deliberately absent. -/
structure LigandGroup (LigandId LigandKind : Type*) (atomCount : Nat) where
  ligand : LigandId
  ligandKind : LigandKind
  centre : Fin atomCount
  deriving DecidableEq

namespace FragmentGroup

variable {atomCount : Nat}

/-- The ligand-level group of a fragment occurrence. -/
def toLigandGroup (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind atomCount) :
    LigandGroup LigandId LigandKind atomCount :=
  { ligand := group.ligand
    ligandKind := group.ligandKind
    centre := group.centre }

@[simp] theorem toLigandGroup_ligand
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind atomCount) :
    group.toLigandGroup.ligand = group.ligand := rfl

@[simp] theorem toLigandGroup_ligandKind
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind atomCount) :
    group.toLigandGroup.ligandKind = group.ligandKind := rfl

@[simp] theorem toLigandGroup_centre
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind atomCount) :
    group.toLigandGroup.centre = group.centre := rfl

end FragmentGroup

/-! ## Source-bound donor incidences -/

/-- One donor incidence.  The `index` is a concrete position in the source interaction list, so two
literally equal source interactions remain separately addressable.  The `evidence` field is the
explicit physical direction (`donor → acceptor`) together with the proof that the source
interaction at `index` has exactly this two-atom support, length two and `coordinate` kind. -/
structure DonorIncidence (molecule : SemanticMolecule)
    (LigandId LigandKind FragmentId FragmentKind : Type*) where
  index : Fin molecule.interactions.length
  ligand : LigandId
  ligandKind : LigandKind
  fragment : FragmentId
  fragmentKind : FragmentKind
  /-- Caller-supplied base priority number.  This module performs no CIP derivation. -/
  basePriority : Nat
  evidence : InteractionRoles.DirectedEnrichment molecule index

namespace DonorIncidence

variable {molecule : SemanticMolecule}

/-- The donor atom of the incidence, as an actual source atom. -/
def donor (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    Fin molecule.atomCount :=
  inc.evidence.coordination.donor

/-- The metal centre of the incidence, as an actual source atom. -/
def centre (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    Fin molecule.atomCount :=
  inc.evidence.coordination.acceptor

/-- The fragment-level occurrence group of the incidence. -/
def fragmentGroup (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount :=
  { ligand := inc.ligand
    ligandKind := inc.ligandKind
    fragment := inc.fragment
    fragmentKind := inc.fragmentKind
    centre := inc.centre }

/-- The ligand-level occurrence group of the incidence. -/
def ligandGroup (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    LigandGroup LigandId LigandKind molecule.atomCount :=
  inc.fragmentGroup.toLigandGroup

@[simp] theorem donor_def (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.donor = inc.evidence.coordination.donor := rfl

@[simp] theorem centre_def (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.centre = inc.evidence.coordination.acceptor := rfl

@[simp] theorem fragmentGroup_ligand
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.fragmentGroup.ligand = inc.ligand := rfl

@[simp] theorem fragmentGroup_ligandKind
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.fragmentGroup.ligandKind = inc.ligandKind := rfl

@[simp] theorem fragmentGroup_fragment
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.fragmentGroup.fragment = inc.fragment := rfl

@[simp] theorem fragmentGroup_fragmentKind
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.fragmentGroup.fragmentKind = inc.fragmentKind := rfl

@[simp] theorem fragmentGroup_centre
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.fragmentGroup.centre = inc.centre := rfl

@[simp] theorem ligandGroup_ligand
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.ligandGroup.ligand = inc.ligand := rfl

@[simp] theorem ligandGroup_ligandKind
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.ligandGroup.ligandKind = inc.ligandKind := rfl

@[simp] theorem ligandGroup_centre
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.ligandGroup.centre = inc.centre := rfl

/-- Donor and centre are distinct source atoms. -/
theorem donor_ne_centre (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.donor ≠ inc.centre :=
  inc.evidence.coordination.distinct

/-- The source interaction index really lies in the finite source interaction list. -/
theorem index_isLt (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.index.val < molecule.interactions.length :=
  inc.index.isLt

/-- The donor atom is a bounded source atom. -/
theorem donor_isLt (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.donor.val < molecule.atomCount :=
  inc.donor.isLt

/-- The metal centre is a bounded source atom. -/
theorem centre_isLt (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.centre.val < molecule.atomCount :=
  inc.centre.isLt

/-- The source interaction at the recorded index is a `coordinate` interaction. -/
theorem source_kind (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    (molecule.interactions.get inc.index).kind = SemanticInteractionKind.coordinate :=
  inc.evidence.kind_coordinate

/-- The source interaction at the recorded index has exactly two participants.  This is the
structural reason why a multi-atom haptic interaction is never a κ donor incidence. -/
theorem source_participants_length
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    (molecule.interactions.get inc.index).participants.length = 2 :=
  inc.evidence.length_two

/-- The donor atom actually occurs in the participants of the source interaction at the recorded
index.  This is the "donor indices are source-bound" property. -/
theorem donor_mem_source_participants
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.donor.val ∈ (molecule.interactions.get inc.index).participants := by
  have hmem : inc.donor.val ∈ (molecule.interactions.get inc.index).participants.toFinset := by
    rw [inc.evidence.support]
    simp [DonorIncidence.donor]
  simpa using hmem

/-- All source-boundness facts bundled. -/
theorem sourceBound
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    inc.index.val < molecule.interactions.length ∧
      inc.donor.val < molecule.atomCount ∧
      inc.centre.val < molecule.atomCount ∧
      inc.donor.val ∈ (molecule.interactions.get inc.index).participants ∧
      (molecule.interactions.get inc.index).kind = SemanticInteractionKind.coordinate ∧
      (molecule.interactions.get inc.index).participants.length = 2 :=
  ⟨inc.index_isLt, inc.donor_isLt, inc.centre_isLt, inc.donor_mem_source_participants,
    inc.source_kind, inc.source_participants_length⟩

/-- Two incidences with the same ligand/fragment identity data and the same centre lie in the same
fragment occurrence group. -/
theorem fragmentGroup_eq_of_fields
    (left right : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (hLigand : left.ligand = right.ligand)
    (hLigandKind : left.ligandKind = right.ligandKind)
    (hFragment : left.fragment = right.fragment)
    (hFragmentKind : left.fragmentKind = right.fragmentKind)
    (hCentre : left.centre = right.centre) :
    left.fragmentGroup = right.fragmentGroup := by
  simp only [DonorIncidence.fragmentGroup]
  rw [hLigand, hLigandKind, hFragment, hFragmentKind, hCentre]

end DonorIncidence

/-! ## Grouping predicates and recorded donor sets -/

/-- Fragment-level grouping: all fragment identity fields and the centre agree. -/
def SameFragmentGroup {molecule : SemanticMolecule}
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount) : Prop :=
  inc.ligand = group.ligand ∧ inc.ligandKind = group.ligandKind ∧
    inc.fragment = group.fragment ∧ inc.fragmentKind = group.fragmentKind ∧
      inc.centre = group.centre

/-- Ligand-level grouping: ligand identity, ligand kind and centre agree.  Fragment identity is
deliberately excluded. -/
def SameLigandGroup {molecule : SemanticMolecule}
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (group : LigandGroup LigandId LigandKind molecule.atomCount) : Prop :=
  inc.ligand = group.ligand ∧ inc.ligandKind = group.ligandKind ∧ inc.centre = group.centre

/-- A fragment-level group is contained in its ligand-level group. -/
theorem sameLigandGroup_of_sameFragmentGroup {molecule : SemanticMolecule}
    {inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind}
    {group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount}
    (same : SameFragmentGroup inc group) : SameLigandGroup inc group.toLigandGroup := by
  rcases same with ⟨hLigand, hLigandKind, _hFragment, _hFragmentKind, hCentre⟩
  exact ⟨hLigand, hLigandKind, hCentre⟩

/-- Executable fragment-level grouping predicate. -/
def fragmentGroupBool {molecule : SemanticMolecule}
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount) : Bool :=
  decide (inc.ligand = group.ligand) && decide (inc.ligandKind = group.ligandKind) &&
    decide (inc.fragment = group.fragment) && decide (inc.fragmentKind = group.fragmentKind) &&
      decide (inc.centre = group.centre)

/-- Executable ligand-level grouping predicate. -/
def ligandGroupBool {molecule : SemanticMolecule}
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (group : LigandGroup LigandId LigandKind molecule.atomCount) : Bool :=
  decide (inc.ligand = group.ligand) && decide (inc.ligandKind = group.ligandKind) &&
    decide (inc.centre = group.centre)

@[simp] theorem fragmentGroupBool_eq_true_iff {molecule : SemanticMolecule}
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount) :
    fragmentGroupBool inc group = true ↔ SameFragmentGroup inc group := by
  simp [fragmentGroupBool, SameFragmentGroup, and_assoc]

@[simp] theorem ligandGroupBool_eq_true_iff {molecule : SemanticMolecule}
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (group : LigandGroup LigandId LigandKind molecule.atomCount) :
    ligandGroupBool inc group = true ↔ SameLigandGroup inc group := by
  simp [ligandGroupBool, SameLigandGroup, and_assoc]

/-- Fragment-group incidences, in ledger order. -/
def fragmentIncidences {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount) :
    List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :=
  ledger.filter fun inc => fragmentGroupBool inc group

/-- Ligand-group incidences, in ledger order. -/
def ligandIncidences {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : LigandGroup LigandId LigandKind molecule.atomCount) :
    List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :=
  ledger.filter fun inc => ligandGroupBool inc group

@[simp] theorem mem_fragmentIncidences {molecule : SemanticMolecule}
    {ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)}
    {group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount}
    {inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind} :
    inc ∈ fragmentIncidences ledger group ↔ inc ∈ ledger ∧ SameFragmentGroup inc group := by
  simp [fragmentIncidences]

@[simp] theorem mem_ligandIncidences {molecule : SemanticMolecule}
    {ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)}
    {group : LigandGroup LigandId LigandKind molecule.atomCount}
    {inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind} :
    inc ∈ ligandIncidences ledger group ↔ inc ∈ ledger ∧ SameLigandGroup inc group := by
  simp [ligandIncidences]

/-- Recorded donor atoms of one fragment group. -/
def fragmentDonors {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount) :
    Finset (Fin molecule.atomCount) :=
  ((fragmentIncidences ledger group).map DonorIncidence.donor).toFinset

/-- Recorded donor atoms of one ligand group (all fragments included). -/
def ligandDonors {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : LigandGroup LigandId LigandKind molecule.atomCount) :
    Finset (Fin molecule.atomCount) :=
  ((ligandIncidences ledger group).map DonorIncidence.donor).toFinset

@[simp] theorem mem_fragmentDonors {molecule : SemanticMolecule}
    {ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)}
    {group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount}
    {atom : Fin molecule.atomCount} :
    atom ∈ fragmentDonors ledger group ↔
      ∃ inc, inc ∈ ledger ∧ SameFragmentGroup inc group ∧ inc.donor = atom := by
  simp [fragmentDonors, and_assoc]

@[simp] theorem mem_ligandDonors {molecule : SemanticMolecule}
    {ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)}
    {group : LigandGroup LigandId LigandKind molecule.atomCount}
    {atom : Fin molecule.atomCount} :
    atom ∈ ligandDonors ledger group ↔
      ∃ inc, inc ∈ ledger ∧ SameLigandGroup inc group ∧ inc.donor = atom := by
  simp [ligandDonors, and_assoc]

/-- **Recorded fragment κ-denticity**: the number of distinct donor atoms recorded inside one
coordinating fragment. -/
def recordedFragmentKappa {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount) : Nat :=
  (fragmentDonors ledger group).card

/-- **Recorded ligand denticity**: the number of distinct donor atoms recorded for one ligand
occurrence around one centre, counting all of its fragments.  IR-9.3.5.3 polydenticity is derived
from this number, not from the fragment count. -/
def recordedLigandDenticity {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : LigandGroup LigandId LigandKind molecule.atomCount) : Nat :=
  (ligandDonors ledger group).card

/-- Derived polydenticity of one ligand occurrence: at least two distinct recorded donor atoms.
This replaces the arbitrary `isPolydentate : Prop` field of the old record. -/
def IsPolydentate {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : LigandGroup LigandId LigandKind molecule.atomCount) : Prop :=
  2 ≤ recordedLigandDenticity ledger group

@[simp] theorem recordedFragmentKappa_def {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount) :
    recordedFragmentKappa ledger group = (fragmentDonors ledger group).card := rfl

@[simp] theorem recordedLigandDenticity_def {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : LigandGroup LigandId LigandKind molecule.atomCount) :
    recordedLigandDenticity ledger group = (ligandDonors ledger group).card := rfl

theorem isPolydentate_iff_two_le_recordedLigandDenticity {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : LigandGroup LigandId LigandKind molecule.atomCount) :
    IsPolydentate ledger group ↔ 2 ≤ recordedLigandDenticity ledger group :=
  Iff.rfl

/-- Fragment κ never exceeds ligand denticity: a fragment's donors are among its ligand's donors. -/
theorem fragmentDonors_subset_ligandDonors {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount) :
    fragmentDonors ledger group ⊆ ligandDonors ledger group.toLigandGroup := by
  intro atom member
  rw [mem_fragmentDonors] at member
  obtain ⟨inc, incMem, same, rfl⟩ := member
  rw [mem_ligandDonors]
  exact ⟨inc, incMem, sameLigandGroup_of_sameFragmentGroup same, rfl⟩

/-- Fragment κ is bounded by ligand denticity. -/
theorem recordedFragmentKappa_le_recordedLigandDenticity {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount) :
    recordedFragmentKappa ledger group ≤
      recordedLigandDenticity ledger group.toLigandGroup := by
  unfold recordedFragmentKappa recordedLigandDenticity
  exact Finset.card_le_card (fragmentDonors_subset_ligandDonors ledger group)

/-- κ is the number of *distinct* donor atoms: repeated or equal interaction entries cannot create
a second κ donor.  Stated at fragment level. -/
theorem two_le_recordedFragmentKappa_iff_exists_two_distinct_donors
    {molecule : SemanticMolecule}
    {ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)}
    {group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount} :
    2 ≤ recordedFragmentKappa ledger group ↔
      ∃ first, first ∈ ledger ∧ SameFragmentGroup first group ∧
        ∃ second, second ∈ ledger ∧ SameFragmentGroup second group ∧
          first.donor ≠ second.donor := by
  unfold recordedFragmentKappa
  rw [show 2 ≤ (fragmentDonors ledger group).card ↔
      1 < (fragmentDonors ledger group).card from
    ⟨fun h => Nat.lt_of_succ_le h, fun h => Nat.succ_le_of_lt h⟩]
  rw [Finset.one_lt_card]
  constructor
  · rintro ⟨first, firstMem, second, secondMem, different⟩
    rw [mem_fragmentDonors] at firstMem secondMem
    obtain ⟨firstInc, firstIn, firstGroup, rfl⟩ := firstMem
    obtain ⟨secondInc, secondIn, secondGroup, rfl⟩ := secondMem
    exact ⟨firstInc, firstIn, firstGroup, secondInc, secondIn, secondGroup, different⟩
  · rintro ⟨first, firstIn, firstGroup, second, secondIn, secondGroup, different⟩
    exact ⟨first.donor, mem_fragmentDonors.mpr ⟨first, firstIn, firstGroup, rfl⟩,
      second.donor, mem_fragmentDonors.mpr ⟨second, secondIn, secondGroup, rfl⟩, different⟩

/-- Ligand-level derived polydenticity is exactly the existence of two distinct recorded donor
atoms for the ligand occurrence. -/
theorem two_le_recordedLigandDenticity_iff_exists_two_distinct_donors
    {molecule : SemanticMolecule}
    {ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)}
    {group : LigandGroup LigandId LigandKind molecule.atomCount} :
    2 ≤ recordedLigandDenticity ledger group ↔
      ∃ first, first ∈ ledger ∧ SameLigandGroup first group ∧
        ∃ second, second ∈ ledger ∧ SameLigandGroup second group ∧
          first.donor ≠ second.donor := by
  unfold recordedLigandDenticity
  rw [show 2 ≤ (ligandDonors ledger group).card ↔
      1 < (ligandDonors ledger group).card from
    ⟨fun h => Nat.lt_of_succ_le h, fun h => Nat.succ_le_of_lt h⟩]
  rw [Finset.one_lt_card]
  constructor
  · rintro ⟨first, firstMem, second, secondMem, different⟩
    rw [mem_ligandDonors] at firstMem secondMem
    obtain ⟨firstInc, firstIn, firstGroup, rfl⟩ := firstMem
    obtain ⟨secondInc, secondIn, secondGroup, rfl⟩ := secondMem
    exact ⟨firstInc, firstIn, firstGroup, secondInc, secondIn, secondGroup, different⟩
  · rintro ⟨first, firstIn, firstGroup, second, secondIn, secondGroup, different⟩
    exact ⟨first.donor, mem_ligandDonors.mpr ⟨first, firstIn, firstGroup, rfl⟩,
      second.donor, mem_ligandDonors.mpr ⟨second, secondIn, secondGroup, rfl⟩, different⟩

/-- Derived polydenticity at ligand level is the two-distinct-donor existence condition. -/
theorem isPolydentate_iff_exists_two_distinct_donors {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : LigandGroup LigandId LigandKind molecule.atomCount) :
    IsPolydentate ledger group ↔
      ∃ first, first ∈ ledger ∧ SameLigandGroup first group ∧
        ∃ second, second ∈ ledger ∧ SameLigandGroup second group ∧
          first.donor ≠ second.donor :=
  (isPolydentate_iff_two_le_recordedLigandDenticity ledger group).trans
    two_le_recordedLigandDenticity_iff_exists_two_distinct_donors

/-- Recorded fragment κ is bounded by the number of ledger entries. -/
theorem recordedFragmentKappa_le_length {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount) :
    recordedFragmentKappa ledger group ≤ ledger.length := by
  unfold recordedFragmentKappa fragmentDonors
  calc ((fragmentIncidences ledger group).map DonorIncidence.donor).toFinset.card
      ≤ ((fragmentIncidences ledger group).map DonorIncidence.donor).length :=
        List.toFinset_card_le _
    _ = (fragmentIncidences ledger group).length := by simp
    _ ≤ ledger.length := by
        simpa [fragmentIncidences] using
          (List.length_filter_le (fun inc => fragmentGroupBool inc group) ledger)

/-- Recorded ligand denticity is bounded by the number of ledger entries. -/
theorem recordedLigandDenticity_le_length {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (group : LigandGroup LigandId LigandKind molecule.atomCount) :
    recordedLigandDenticity ledger group ≤ ledger.length := by
  unfold recordedLigandDenticity ligandDonors
  calc ((ligandIncidences ledger group).map DonorIncidence.donor).toFinset.card
      ≤ ((ligandIncidences ledger group).map DonorIncidence.donor).length :=
        List.toFinset_card_le _
    _ = (ligandIncidences ledger group).length := by simp
    _ ≤ ledger.length := by
        simpa [ligandIncidences] using
          (List.length_filter_le (fun inc => ligandGroupBool inc group) ledger)

/-- The empty ledger records no donor atoms at all. -/
@[simp] theorem recordedLigandDenticity_nil {molecule : SemanticMolecule}
    (group : LigandGroup LigandId LigandKind molecule.atomCount) :
    recordedLigandDenticity (molecule := molecule)
      ([] : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
      group = 0 := by
  simp [recordedLigandDenticity, ligandDonors, ligandIncidences]

@[simp] theorem recordedFragmentKappa_nil {molecule : SemanticMolecule}
    (group : FragmentGroup LigandId LigandKind FragmentId FragmentKind molecule.atomCount) :
    recordedFragmentKappa (molecule := molecule)
      ([] : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
      group = 0 := by
  simp [recordedFragmentKappa, fragmentDonors, fragmentIncidences]

/-! ## Encoding into the existing `DonorOccurrence` -/

/-- Raw metadata projection to the existing IR-9.3 record.  This constructor does not require
ledger membership and must not be read as a physical-denticity claim.  Use `encode` for the
membership-checked recorded constructor. -/
def encodeRaw {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    DonorOccurrence LigandId LigandKind FragmentId FragmentKind :=
  { basePriority := inc.basePriority
    ligand := inc.fragmentGroup.ligand
    ligandKind := inc.fragmentGroup.ligandKind
    coordinatingFragment := inc.fragmentGroup.fragment
    fragmentKind := inc.fragmentGroup.fragmentKind
    isPolydentate := IsPolydentate ledger inc.fragmentGroup.toLigandGroup }

/-- Membership-checked recorded encoding.  The incidence must be a member of the supplied
ledger; the occurrence identity fields are copied exactly, and polydenticity is the derived
**recorded** ligand-level condition.  This constructor makes no donor-support, grouping-
completeness or physical-denticity claim; use `PhysicalDonorOccurrence.encode` for the supported
variant and `LigandDonorSupportCertificate` for an explicit completeness premise. -/
def encode {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (_member : inc ∈ ledger) :
    DonorOccurrence LigandId LigandKind FragmentId FragmentKind :=
  encodeRaw ledger inc

@[simp] theorem encodeRaw_basePriority {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    (encodeRaw ledger inc).basePriority = inc.basePriority := rfl

@[simp] theorem encodeRaw_ligand {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    (encodeRaw ledger inc).ligand = inc.ligand := rfl

@[simp] theorem encodeRaw_ligandKind {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    (encodeRaw ledger inc).ligandKind = inc.ligandKind := rfl

@[simp] theorem encodeRaw_coordinatingFragment {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    (encodeRaw ledger inc).coordinatingFragment = inc.fragment := rfl

@[simp] theorem encodeRaw_fragmentKind {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    (encodeRaw ledger inc).fragmentKind = inc.fragmentKind := rfl

/-- The old record's `isPolydentate` field is the derived **ligand-level** condition. -/
@[simp] theorem encodeRaw_isPolydentate {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) :
    (encodeRaw ledger inc).isPolydentate ↔ 2 ≤ recordedLigandDenticity ledger inc.ligandGroup :=
  Iff.rfl

/-- Public-constructor versions of the exact-preservation facts. -/
@[simp] theorem encode_ligand {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (member : inc ∈ ledger) :
    (encode ledger inc member).ligand = inc.ligand := rfl

@[simp] theorem encode_ligandKind {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (member : inc ∈ ledger) :
    (encode ledger inc member).ligandKind = inc.ligandKind := rfl

@[simp] theorem encode_coordinatingFragment {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (member : inc ∈ ledger) :
    (encode ledger inc member).coordinatingFragment = inc.fragment := rfl

@[simp] theorem encode_fragmentKind {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (member : inc ∈ ledger) :
    (encode ledger inc member).fragmentKind = inc.fragmentKind := rfl

@[simp] theorem encode_basePriority {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (member : inc ∈ ledger) :
    (encode ledger inc member).basePriority = inc.basePriority := rfl

@[simp] theorem encode_isPolydentate {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (member : inc ∈ ledger) :
    (encode ledger inc member).isPolydentate ↔
      2 ≤ recordedLigandDenticity ledger inc.ligandGroup :=
  Iff.rfl

/-- Exact preservation of every identity field and of the separately supplied priority number,
through the public constructor. -/
theorem encode_preserves_ids {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (member : inc ∈ ledger) :
    (encode ledger inc member).ligand = inc.ligand ∧
      (encode ledger inc member).ligandKind = inc.ligandKind ∧
      (encode ledger inc member).coordinatingFragment = inc.fragment ∧
      (encode ledger inc member).fragmentKind = inc.fragmentKind ∧
      (encode ledger inc member).basePriority = inc.basePriority :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Explicit physical supports and incidence agreement -/

/-- A finite, independently supplied donor support for one ligand occurrence around one centre. -/
structure LigandDonorSupport (molecule : SemanticMolecule)
    (LigandId LigandKind : Type*) where
  ligand : LigandId
  ligandKind : LigandKind
  centre : Fin molecule.atomCount
  donors : Finset (Fin molecule.atomCount)

namespace LigandDonorSupport

variable {molecule : SemanticMolecule}

/-- The ligand-level group described by a supplied support. -/
def toLigandGroup (support : LigandDonorSupport molecule LigandId LigandKind) :
    LigandGroup LigandId LigandKind molecule.atomCount :=
  { ligand := support.ligand
    ligandKind := support.ligandKind
    centre := support.centre }

@[simp] theorem toLigandGroup_ligand
    (support : LigandDonorSupport molecule LigandId LigandKind) :
    support.toLigandGroup.ligand = support.ligand := rfl

@[simp] theorem toLigandGroup_ligandKind
    (support : LigandDonorSupport molecule LigandId LigandKind) :
    support.toLigandGroup.ligandKind = support.ligandKind := rfl

@[simp] theorem toLigandGroup_centre
    (support : LigandDonorSupport molecule LigandId LigandKind) :
    support.toLigandGroup.centre = support.centre := rfl

end LigandDonorSupport

/-- A finite, independently supplied donor support for one coordinating fragment, inside a supplied
ligand support. -/
structure FragmentDonorSupport (molecule : SemanticMolecule)
    (LigandId LigandKind FragmentId FragmentKind : Type*) where
  ligandSupport : LigandDonorSupport molecule LigandId LigandKind
  fragment : FragmentId
  fragmentKind : FragmentKind
  donors : Finset (Fin molecule.atomCount)
  subset_ligand : donors ⊆ ligandSupport.donors

/-- Explicit completeness certificate for one ligand support: the recorded donor set and the
supplied finite physical donor set are the same set.  This is the only way in which a recorded
cardinality is identified with a physical donor count; nothing here recognises physical donors
automatically. -/
structure LigandDonorSupportCertificate {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (support : LigandDonorSupport molecule LigandId LigandKind) where
  recorded_subset : ligandDonors ledger support.toLigandGroup ⊆ support.donors
  supplied_subset : support.donors ⊆ ligandDonors ledger support.toLigandGroup

/-- With an explicit completeness certificate, the recorded ligand denticity is exactly the
cardinality of the supplied finite donor support. -/
theorem recordedLigandDenticity_eq_card_of_certificate {molecule : SemanticMolecule}
    {ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)}
    {support : LigandDonorSupport molecule LigandId LigandKind}
    (certificate : LigandDonorSupportCertificate ledger support) :
    recordedLigandDenticity ledger support.toLigandGroup = support.donors.card := by
  have same : ligandDonors ledger support.toLigandGroup = support.donors :=
    Finset.Subset.antisymm certificate.recorded_subset certificate.supplied_subset
  unfold recordedLigandDenticity
  rw [same]

/-- The supported recorded occurrence constructor.  It requires (i) membership of the incidence in
the supplied ledger, (ii) explicit finite ligand and fragment donor supports, and (iii) agreement
of the incidence identity with those supports together with membership of the donor atom in the
fragment support.  These supports certify source-atom membership and identity agreement only;
they are **not** a completeness certificate.  Consequently the `isPolydentate` flag obtained
through this constructor is still **recorded** denticity.  To identify recorded ligand denticity
with the cardinality of a supplied support, use `LigandDonorSupportCertificate`. -/
structure PhysicalDonorOccurrence (molecule : SemanticMolecule)
    (LigandId LigandKind FragmentId FragmentKind : Type*)
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)) where
  inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind
  member : inc ∈ ledger
  ligandSupport : LigandDonorSupport molecule LigandId LigandKind
  fragmentSupport : FragmentDonorSupport molecule LigandId LigandKind FragmentId FragmentKind
  ligand_eq : ligandSupport.ligand = inc.ligand
  ligandKind_eq : ligandSupport.ligandKind = inc.ligandKind
  centre_eq : ligandSupport.centre = inc.centre
  fragment_eq : fragmentSupport.fragment = inc.fragment
  fragmentKind_eq : fragmentSupport.fragmentKind = inc.fragmentKind
  ligandSupport_eq : fragmentSupport.ligandSupport = ligandSupport
  donor_mem_fragment : inc.donor ∈ fragmentSupport.donors

namespace PhysicalDonorOccurrence

variable {molecule : SemanticMolecule}
variable {ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)}

/-- The supported recorded encoding of an occurrence. -/
def encode (data : PhysicalDonorOccurrence molecule LigandId LigandKind FragmentId FragmentKind
    ledger) : DonorOccurrence LigandId LigandKind FragmentId FragmentKind :=
  DonorOccurrenceEncoding.encode ledger data.inc data.member

/-- The donor atom lies in the supplied ligand support as well. -/
theorem donor_mem_ligand (data : PhysicalDonorOccurrence molecule LigandId LigandKind
    FragmentId FragmentKind ledger) :
    data.inc.donor ∈ data.ligandSupport.donors := by
  have member : data.inc.donor ∈ data.fragmentSupport.donors := data.donor_mem_fragment
  have subset : data.fragmentSupport.donors ⊆ data.ligandSupport.donors := by
    rw [← data.ligandSupport_eq]
    exact data.fragmentSupport.subset_ligand
  exact subset member

/-- The supported constructor preserves all identity fields exactly. -/
theorem encode_preserves_ids (data : PhysicalDonorOccurrence molecule LigandId LigandKind
    FragmentId FragmentKind ledger) :
    data.encode.ligand = data.inc.ligand ∧
      data.encode.ligandKind = data.inc.ligandKind ∧
      data.encode.coordinatingFragment = data.inc.fragment ∧
      data.encode.fragmentKind = data.inc.fragmentKind ∧
      data.encode.basePriority = data.inc.basePriority := by
  unfold encode
  exact DonorOccurrenceEncoding.encode_preserves_ids ledger data.inc data.member

/-- The supported constructor's polydenticity flag is the derived **recorded** ligand-level
condition.  Even with finite supports present, this is not a physical-completeness claim. -/
theorem encode_isPolydentate (data : PhysicalDonorOccurrence molecule LigandId LigandKind
    FragmentId FragmentKind ledger) :
    data.encode.isPolydentate ↔
      2 ≤ recordedLigandDenticity ledger data.inc.ligandGroup := by
  unfold encode
  exact DonorOccurrenceEncoding.encode_isPolydentate ledger data.inc data.member

end PhysicalDonorOccurrence

/-! ## Source-level repeated relations and their exact correspondence -/

/-- Source-level "two occurrences belong to different polydentate ligands of one kind": the
`isPolydentate` premises are the derived ligand-level conditions, and the kind / identity
comparisons are on the actual incidence data. -/
def SourceRepeatedPolydentateLigand {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (left right : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) : Prop :=
  IsPolydentate ledger left.ligandGroup ∧ IsPolydentate ledger right.ligandGroup ∧
    left.ligandKind = right.ligandKind ∧ left.ligand ≠ right.ligand

/-- Source-level "two occurrences belong to different coordinating fragments of one kind inside one
polydentate ligand".  Both occurrences are in the same ligand, so both ligand-level flags are the
same derived condition; distinct fragment identities are what makes the relation hold. -/
def SourceRepeatedCoordinatingFragment {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (left right : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind) : Prop :=
  IsPolydentate ledger left.ligandGroup ∧ IsPolydentate ledger right.ligandGroup ∧
    left.ligand = right.ligand ∧ left.fragmentKind = right.fragmentKind ∧
      left.fragment ≠ right.fragment

/-- Encoding preserves the IR-9.3.5.3 repeated-polydentate-ligand relation exactly. -/
theorem repeatedPolydentateLigand_encode_iff {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (left right : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (leftMem : left ∈ ledger) (rightMem : right ∈ ledger) :
    RepeatedPolydentateLigand (encode ledger left leftMem) (encode ledger right rightMem) ↔
      SourceRepeatedPolydentateLigand ledger left right := by
  constructor <;> intro h <;> exact h

/-- Encoding preserves the IR-9.3.5.3 repeated-coordinating-fragment relation exactly. -/
theorem repeatedCoordinatingFragment_encode_iff {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (left right : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (leftMem : left ∈ ledger) (rightMem : right ∈ ledger) :
    RepeatedCoordinatingFragment (encode ledger left leftMem) (encode ledger right rightMem) ↔
      SourceRepeatedCoordinatingFragment ledger left right := by
  constructor <;> intro h <;> exact h

/-- The exact two-way applicability boundary of IR-9.3.5.3 is likewise preserved. -/
theorem needsPrimeGrouping_encode_iff {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (left right : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (leftMem : left ∈ ledger) (rightMem : right ∈ ledger) :
    NeedsPrimeGrouping (encode ledger left leftMem) (encode ledger right rightMem) ↔
      (SourceRepeatedPolydentateLigand ledger left right ∨
        SourceRepeatedCoordinatingFragment ledger left right) := by
  constructor <;> intro h <;> exact h

/-! ## The complete enriched ledger -/

/-- The complete enriched data: the source molecule-bound incidence list.  Erasing it to
`DonorOccurrence` values loses the donor atoms, centres and source indices. -/
structure DonorLedger (molecule : SemanticMolecule)
    (LigandId LigandKind FragmentId FragmentKind : Type*) where
  incidences : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)

namespace DonorLedger

variable {molecule : SemanticMolecule}

/-- The old-style occurrence list obtained by raw metadata projection of every incidence. -/
def occurrences (ledger : DonorLedger molecule LigandId LigandKind FragmentId FragmentKind) :
    List (DonorOccurrence LigandId LigandKind FragmentId FragmentKind) :=
  ledger.incidences.map (encodeRaw ledger.incidences)

@[simp] theorem occurrences_length
    (ledger : DonorLedger molecule LigandId LigandKind FragmentId FragmentKind) :
    ledger.occurrences.length = ledger.incidences.length := by
  simp [occurrences]

/-- The index of a source incidence, transported to the occurrence list. -/
def occurrenceIndex (ledger : DonorLedger molecule LigandId LigandKind FragmentId FragmentKind)
    (index : Fin ledger.incidences.length) : Fin ledger.occurrences.length :=
  ⟨index.val, by simp⟩

/-- Each stored occurrence is the raw projection of the incidence at the same position. -/
theorem occurrences_get_raw
    (ledger : DonorLedger molecule LigandId LigandKind FragmentId FragmentKind)
    (index : Fin ledger.incidences.length) :
    ledger.occurrences.get (ledger.occurrenceIndex index) =
      encodeRaw ledger.incidences (ledger.incidences.get index) := by
  simp [occurrences, occurrenceIndex]

/-- Each stored occurrence is the membership-checked recorded encoding of the incidence at the
same position, using its actual membership proof. -/
theorem occurrences_get_encode
    (ledger : DonorLedger molecule LigandId LigandKind FragmentId FragmentKind)
    (index : Fin ledger.incidences.length) :
    ledger.occurrences.get (ledger.occurrenceIndex index) =
      encode ledger.incidences (ledger.incidences.get index)
        (List.get_mem ledger.incidences index) := by
  rw [occurrences_get_raw]
  rfl

/-- Position-by-position exactness of the identity data and the derived ligand-level polydenticity
flag. -/
theorem occurrence_preserves_identities
    (ledger : DonorLedger molecule LigandId LigandKind FragmentId FragmentKind)
    (index : Fin ledger.incidences.length) :
    let occurrence := ledger.occurrences.get (ledger.occurrenceIndex index)
    let inc := ledger.incidences.get index
    occurrence.basePriority = inc.basePriority ∧
      occurrence.ligand = inc.ligand ∧
      occurrence.ligandKind = inc.ligandKind ∧
      occurrence.coordinatingFragment = inc.fragment ∧
      occurrence.fragmentKind = inc.fragmentKind ∧
      (occurrence.isPolydentate ↔
        2 ≤ recordedLigandDenticity ledger.incidences inc.ligandGroup) := by
  dsimp only
  rw [occurrences_get_encode]
  exact ⟨rfl, rfl, rfl, rfl, rfl, Iff.rfl⟩

/-- Every incidence of the complete ledger is source bound in the actual molecule. -/
theorem incidences_sourceBound
    (ledger : DonorLedger molecule LigandId LigandKind FragmentId FragmentKind)
    {inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind}
    (_membership : inc ∈ ledger.incidences) :
    inc.index.val < molecule.interactions.length ∧
      inc.donor.val < molecule.atomCount ∧
      inc.centre.val < molecule.atomCount ∧
      inc.donor.val ∈ (molecule.interactions.get inc.index).participants :=
  ⟨inc.index_isLt, inc.donor_isLt, inc.centre_isLt, inc.donor_mem_source_participants⟩

/-- The separately indexed source interactions are retained, in ledger order. -/
def sourceInteractionIndices
    (ledger : DonorLedger molecule LigandId LigandKind FragmentId FragmentKind) :
    List (Fin molecule.interactions.length) :=
  ledger.incidences.map DonorIncidence.index

@[simp] theorem sourceInteractionIndices_length
    (ledger : DonorLedger molecule LigandId LigandKind FragmentId FragmentKind) :
    ledger.sourceInteractionIndices.length = ledger.incidences.length := by
  simp [sourceInteractionIndices]

/-- Equal-valued source interactions at distinct indices remain separately addressable: the index
is part of the ledger data, so two incidences over different positions are different entries even
when their source interactions happen to be equal. -/
theorem index_separates_equal_source_entries
    {first second : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind}
    (_sameSource : molecule.interactions.get first.index = molecule.interactions.get second.index)
    (differentIndex : first.index ≠ second.index) :
    first ≠ second := by
  intro equal
  exact differentIndex (congrArg DonorIncidence.index equal)

end DonorLedger

/-! ## Erasure is not injective: donor identities are lost -/

/-- Two incidences with the same fragment identity data and the same supplied priority encode to
the same old-style occurrence, regardless of which source atom donates. -/
theorem encode_eq_of_identity_eq {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (left right : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (leftMem : left ∈ ledger) (rightMem : right ∈ ledger)
    (identityEq : left.fragmentGroup = right.fragmentGroup)
    (priorityEq : left.basePriority = right.basePriority) :
    encode ledger left leftMem = encode ledger right rightMem := by
  unfold encode encodeRaw
  rw [identityEq, priorityEq]

/-- The public encoding is not injective whenever two same-identity incidences differ in their
donor atom: the old record has nowhere to store that atom.  Injectivity is stated on the subtype of
ledger members, matching the public constructor's membership requirement. -/
theorem encode_not_injective_of_donor_ne {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (left right : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (leftMem : left ∈ ledger) (rightMem : right ∈ ledger)
    (identityEq : left.fragmentGroup = right.fragmentGroup)
    (priorityEq : left.basePriority = right.basePriority)
    (donorNe : left.donor ≠ right.donor) :
    ¬ Function.Injective
        (fun pair : {inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind //
            inc ∈ ledger} => encode ledger pair.1 pair.2) := by
  intro injective
  have equal : (⟨left, leftMem⟩ : {inc : DonorIncidence molecule LigandId LigandKind
        FragmentId FragmentKind // inc ∈ ledger}) = ⟨right, rightMem⟩ :=
    injective (encode_eq_of_identity_eq ledger left right leftMem rightMem identityEq priorityEq)
  exact donorNe (congrArg DonorIncidence.donor (congrArg Subtype.val equal))

/-- No function of the old-style occurrence can recover the source-bound incidence (and hence the
donor atom) from the encoded value. -/
theorem no_donor_identity_recovery {molecule : SemanticMolecule}
    (ledger : List (DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind))
    (left right : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind)
    (leftMem : left ∈ ledger) (rightMem : right ∈ ledger)
    (identityEq : left.fragmentGroup = right.fragmentGroup)
    (priorityEq : left.basePriority = right.basePriority)
    (donorNe : left.donor ≠ right.donor) :
    ¬ ∃ recover : DonorOccurrence LigandId LigandKind FragmentId FragmentKind →
        {inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind // inc ∈ ledger},
        ∀ pair, recover (encode ledger pair.1 pair.2) = pair := by
  rintro ⟨recover, recovers⟩
  have same :=
    encode_eq_of_identity_eq ledger left right leftMem rightMem identityEq priorityEq
  have leftEq := recovers ⟨left, leftMem⟩
  rw [same] at leftEq
  have equal : left = right := congrArg Subtype.val
    (leftEq.symm.trans (recovers ⟨right, rightMem⟩))
  exact donorNe (congrArg DonorIncidence.donor equal)

/-! ## Concrete witnesses -/

/-- Three-atom source with two distinct two-centre `coordinate` interactions that share centre `2`
and are otherwise equal-valued. -/
def witnessMolecule : SemanticMolecule :=
  { atoms :=
      [InteractionRoles.carbonAtom, InteractionRoles.carbonAtom, InteractionRoles.carbonAtom]
    interactions :=
      [ { participants := [0, 2], kind := SemanticInteractionKind.coordinate },
        { participants := [1, 2], kind := SemanticInteractionKind.coordinate } ] }

/-- Directed-coordination evidence for source interaction `0`: atom `0` donates to centre `2`. -/
def witnessEvidence0 :
    InteractionRoles.DirectedEnrichment witnessMolecule ⟨0, by decide⟩ :=
  { coordination :=
      { donor := ⟨0, by decide⟩, acceptor := ⟨2, by decide⟩, distinct := by decide }
    support := rfl
    length_two := rfl
    kind_coordinate := rfl }

/-- Directed-coordination evidence for source interaction `1`: atom `1` donates to centre `2`. -/
def witnessEvidence1 :
    InteractionRoles.DirectedEnrichment witnessMolecule ⟨1, by decide⟩ :=
  { coordination :=
      { donor := ⟨1, by decide⟩, acceptor := ⟨2, by decide⟩, distinct := by decide }
    support := rfl
    length_two := rfl
    kind_coordinate := rfl }

/-- First incidence in the same-fragment non-injectivity pair. -/
def witnessIncidence0 : DonorIncidence witnessMolecule Nat Nat Nat Nat :=
  { index := ⟨0, by decide⟩
    ligand := 0
    ligandKind := 0
    fragment := 0
    fragmentKind := 0
    basePriority := 0
    evidence := witnessEvidence0 }

/-- Second incidence in the same-fragment non-injectivity pair; only the donor atom and the source
interaction index differ. -/
def witnessIncidence1 : DonorIncidence witnessMolecule Nat Nat Nat Nat :=
  { index := ⟨1, by decide⟩
    ligand := 0
    ligandKind := 0
    fragment := 0
    fragmentKind := 0
    basePriority := 0
    evidence := witnessEvidence1 }

theorem witness_identity_eq :
    witnessIncidence0.fragmentGroup = witnessIncidence1.fragmentGroup := by
  decide

theorem witness_priority_eq :
    witnessIncidence0.basePriority = witnessIncidence1.basePriority := rfl

theorem witness_donor_ne :
    witnessIncidence0.donor ≠ witnessIncidence1.donor := by
  decide

theorem witness_mem0 : witnessIncidence0 ∈ [witnessIncidence0, witnessIncidence1] := by simp

theorem witness_mem1 : witnessIncidence1 ∈ [witnessIncidence0, witnessIncidence1] := by simp

/-- The two distinct source-bound incidences encode to the very same old-style occurrence. -/
theorem witness_encode_eq :
    encode [witnessIncidence0, witnessIncidence1] witnessIncidence0 witness_mem0 =
      encode [witnessIncidence0, witnessIncidence1] witnessIncidence1 witness_mem1 :=
  encode_eq_of_identity_eq _ _ _ _ _ witness_identity_eq witness_priority_eq

/-- Consequently the public encoding is not injective on this concrete source. -/
theorem witness_encode_not_injective :
    ¬ Function.Injective
        (fun pair : {inc : DonorIncidence witnessMolecule Nat Nat Nat Nat //
            inc ∈ [witnessIncidence0, witnessIncidence1]} =>
          encode [witnessIncidence0, witnessIncidence1] pair.1 pair.2) :=
  encode_not_injective_of_donor_ne _ _ _ witness_mem0 witness_mem1
    witness_identity_eq witness_priority_eq witness_donor_ne

/-! ## Two-fragment bidentate example: ligand polydenticity is not fragment κ -/

/-- First fragment incidence of the bidentate ligand: ligand `0`, fragment `0`, donor atom `0`. -/
def bidentateIncidence0 : DonorIncidence witnessMolecule Nat Nat Nat Nat :=
  { index := ⟨0, by decide⟩
    ligand := 0
    ligandKind := 0
    fragment := 0
    fragmentKind := 0
    basePriority := 0
    evidence := witnessEvidence0 }

/-- Second fragment incidence of the same bidentate ligand: ligand `0`, fragment `1`, donor atom
`1`.  The ligand records two donors in two one-donor fragments. -/
def bidentateIncidence1 : DonorIncidence witnessMolecule Nat Nat Nat Nat :=
  { index := ⟨1, by decide⟩
    ligand := 0
    ligandKind := 0
    fragment := 1
    fragmentKind := 0
    basePriority := 0
    evidence := witnessEvidence1 }

theorem bidentate_mem0 : bidentateIncidence0 ∈ [bidentateIncidence0, bidentateIncidence1] := by simp

theorem bidentate_mem1 : bidentateIncidence1 ∈ [bidentateIncidence0, bidentateIncidence1] := by simp

/-- Each fragment records exactly one donor. -/
theorem two_fragment_bidentate_fragment_kappa :
    recordedFragmentKappa [bidentateIncidence0, bidentateIncidence1]
        bidentateIncidence0.fragmentGroup = 1 ∧
      recordedFragmentKappa [bidentateIncidence0, bidentateIncidence1]
        bidentateIncidence1.fragmentGroup = 1 := by
  constructor <;> decide

/-- The ligand records two distinct donor atoms, one in each fragment. -/
theorem two_fragment_bidentate_ligand_denticity :
    recordedLigandDenticity [bidentateIncidence0, bidentateIncidence1]
        bidentateIncidence0.ligandGroup = 2 ∧
      recordedLigandDenticity [bidentateIncidence0, bidentateIncidence1]
        bidentateIncidence1.ligandGroup = 2 := by
  constructor <;> decide

/-- Both occurrences of the bidentate ligand receive the true ligand-level polydenticity flag. -/
theorem two_fragment_bidentate_isPolydentate :
    IsPolydentate [bidentateIncidence0, bidentateIncidence1]
        bidentateIncidence0.ligandGroup ∧
      IsPolydentate [bidentateIncidence0, bidentateIncidence1]
        bidentateIncidence1.ligandGroup := by
  constructor <;> (unfold IsPolydentate; decide)

/-- The two occurrences are repeated coordinating fragments of the same kind in one polydentate
ligand: both derived ligand-level flags are true even though each fragment κ is one. -/
theorem two_fragment_bidentate_repeatedFragment :
    RepeatedCoordinatingFragment
      (encode [bidentateIncidence0, bidentateIncidence1] bidentateIncidence0 bidentate_mem0)
      (encode [bidentateIncidence0, bidentateIncidence1] bidentateIncidence1 bidentate_mem1) := by
  rw [repeatedCoordinatingFragment_encode_iff]
  unfold SourceRepeatedCoordinatingFragment
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · unfold IsPolydentate
    decide
  · unfold IsPolydentate
    decide
  · decide

/-- Bundled statement of the mandatory example: two one-donor fragments give fragment κ = 1 each,
ligand denticity 2, true ligand-level polydenticity for both occurrences, and the repeated-fragment
relation holds. -/
theorem two_fragment_bidentate_example :
    recordedFragmentKappa [bidentateIncidence0, bidentateIncidence1]
        bidentateIncidence0.fragmentGroup = 1 ∧
      recordedFragmentKappa [bidentateIncidence0, bidentateIncidence1]
        bidentateIncidence1.fragmentGroup = 1 ∧
      IsPolydentate [bidentateIncidence0, bidentateIncidence1]
        bidentateIncidence0.ligandGroup ∧
      IsPolydentate [bidentateIncidence0, bidentateIncidence1]
        bidentateIncidence1.ligandGroup ∧
      RepeatedCoordinatingFragment
        (encode [bidentateIncidence0, bidentateIncidence1] bidentateIncidence0 bidentate_mem0)
        (encode [bidentateIncidence0, bidentateIncidence1] bidentateIncidence1 bidentate_mem1) :=
  ⟨two_fragment_bidentate_fragment_kappa.1, two_fragment_bidentate_fragment_kappa.2,
    two_fragment_bidentate_isPolydentate.1, two_fragment_bidentate_isPolydentate.2,
    two_fragment_bidentate_repeatedFragment⟩

/-! ## κ versus η hapticity -/

/-- A source interaction whose participant count is not two cannot carry any donor incidence.
The two-participant condition is part of the interaction-role evidence, so this is not a convention
but a consequence of the source decoration. -/
theorem no_donorIncidence_at_index_of_length_ne_two {molecule : SemanticMolecule}
    {index : Fin molecule.interactions.length}
    (different : (molecule.interactions.get index).participants.length ≠ 2) :
    ¬ ∃ inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind,
        inc.index = index := by
  rintro ⟨inc, rfl⟩
  exact different inc.source_participants_length

/-- A haptic ligand of hapticity at least two has `η + 1 ≥ 3` participants.  Such an interaction
therefore supplies no κ incidence at all: its haptic atoms are not counted as independent donors.
This uses only the interaction-role layer's `eta`; this module defines no hapticity of its own. -/
theorem haptic_support_is_not_a_kappa_incidence {molecule : SemanticMolecule}
    (ligand : InteractionRoles.HapticLigand molecule.atomCount)
    (eta_two : 2 ≤ ligand.eta)
    {index : Fin molecule.interactions.length}
    (supportLength : (molecule.interactions.get index).participants.length = ligand.eta + 1) :
    ¬ ∃ inc : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind,
        inc.index = index := by
  rintro ⟨inc, indexEq⟩
  rw [← indexEq] at supportLength
  have atLeastThree : 3 ≤ ligand.eta + 1 := by
    simpa using Nat.succ_le_succ eta_two
  have three_le : 3 ≤ (molecule.interactions.get inc.index).participants.length := by
    rw [supportLength]
    exact atLeastThree
  rw [inc.source_participants_length] at three_le
  exact absurd three_le (by decide)

/-- A concrete haptic ligand: centre `0` with two donor atoms, so `η = 2`. -/
def hapticExample : InteractionRoles.HapticLigand 3 :=
  { centre := ⟨0, by decide⟩
    donors := [⟨1, by decide⟩, ⟨2, by decide⟩]
    nonempty := by decide
    nodup := by decide
    centreNotMem := by decide }

@[simp] theorem hapticExample_eta : hapticExample.eta = 2 := rfl

/-- η and κ are different notions.  The haptic ligand has `η = 2`, while a ledger with no directed
donor incidences records ligand denticity `0` in every group; nothing in this module equates the
two or converts a haptic support into several κ donors. -/
theorem hapticity_and_denticity_differ (molecule : SemanticMolecule)
    (group : LigandGroup Nat Nat molecule.atomCount) :
    hapticExample.eta = 2 ∧
      recordedLigandDenticity (molecule := molecule)
        ([] : List (DonorIncidence molecule Nat Nat Nat Nat)) group = 0 ∧
      hapticExample.eta ≠
        recordedLigandDenticity (molecule := molecule)
          ([] : List (DonorIncidence molecule Nat Nat Nat Nat)) group := by
  refine ⟨rfl, recordedLigandDenticity_nil group, ?_⟩
  rw [recordedLigandDenticity_nil group]
  decide

end DonorOccurrenceEncoding
end TetraStereo.OneCenter
