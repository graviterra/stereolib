/-
# Source-bound `V`-native donor grouping ingress

`OrganicStereoDonorOccurrenceEncoding.DonorLedger` is a complete, enriched donor ledger over an
arbitrary `SemanticMolecule`: every incidence retains its exact source interaction index, the actual
donor and centre atoms, all four arbitrary metadata label types, the supplied `basePriority` and the
explicit `InteractionRoles.DirectedEnrichment` evidence (binary `coordinate` kind, length two,
exact participants and direction).

This module transports that ledger to the *same* finite atom-labelled hypergraph through the common
certified encoding `graph.certifiedEncoding eV`.  The transported channel is `V`-native: it stores
atom labels of `V` (not `Fin` numerals) while retaining every other datum literally.  The binding
to the encoded molecule is expressed by a proof-only validity predicate
(`NativeChannelValidity`), so the channel itself contains no source molecule, no ledger and no
hidden original payload.

Main results:

* `channelOfLedger` is the actual ingress; its occurrence list is the positional image of the
  ledger's incidence list, so ordering and multiplicity are preserved.
* `nativeValidityOfLedger` obtains the proof-only validity certificate from existing
  `DirectedEnrichment` evidence.  The exact participants condition is stated as the unordered
  participant `Finset` equality used by the existing evidence; direction is carried by the
  separate `donor`/`centre` fields, so reverse participant order is not rejected.
* `decodeLedger_channelOfLedger` recovers the original enriched `DonorLedger.incidences` from the
  channel plus the proof-only certificate.
* `channelOfLedger_injective` follows: the channel is a lossless representation of the enriched
  ledger, unlike the raw `DonorLedger.occurrences` projection.
* Fragment κ and ligand denticity computed natively from the channel agree with the encoded
  ledger's recorded cardinalities, via the explicit atom equivalence `encodedAtomEquiv`; no
  physical donor-support completeness is claimed.
* `relabelChannel e` relabels atoms along any equivalence `e`; the `Fin` encoding is the special
  case `e = eV`, with the two-sided inverse `relabelChannel eV.symm`.

No CIP priority derivation is performed: `basePriority` is copied.  No clustering, hapticity or
support-completeness claim is made.
-/

import TetraStereo.OneCenter.OrganicStereoSourceBoundResidueAssembly
import TetraStereo.OneCenter.OrganicStereoDonorOccurrenceEncoding

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo.OneCenter

open DonorOccurrenceEncoding
open OrganicStereoIndependentElectronicEncoding

namespace DonorGroupingIngress

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {LigandId LigandKind FragmentId FragmentKind : Type*}
variable [DecidableEq LigandId] [DecidableEq LigandKind]
variable [DecidableEq FragmentId] [DecidableEq FragmentKind]
variable {E B : Type*} [Fintype E] [Fintype B]

/-! ## The V-native occurrence and channel -/

/-- One donor occurrence with atom labels taken from `V`.  The interaction index is retained
literally; the labels and the supplied base priority are typed data, never squashed to `Nat`. -/
structure VNativeDonorOccurrence (V : Type*) (LigandId LigandKind FragmentId FragmentKind : Type*)
    (interactionCount : Nat) where
  index : Fin interactionCount
  donor : V
  centre : V
  ligand : LigandId
  ligandKind : LigandKind
  fragment : FragmentId
  fragmentKind : FragmentKind
  basePriority : Nat
  deriving DecidableEq

/-- A `V`-native donor channel.  It stores only the occurrence list; the source molecule and the
validity evidence are supplied separately. -/
structure VNativeDonorChannel (V : Type*) (LigandId LigandKind FragmentId FragmentKind : Type*)
    (interactionCount : Nat) where
  occurrences :
    List (VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind interactionCount)

/-! ## Native grouping, donor sets and recorded denticities -/

/-- Native fragment occurrence group: fragment identity fields plus the actual centre atom. -/
structure NativeFragmentGroup (V : Type*) (LigandId LigandKind FragmentId FragmentKind : Type*)
    where
  ligand : LigandId
  ligandKind : LigandKind
  fragment : FragmentId
  fragmentKind : FragmentKind
  centre : V

/-- Native ligand occurrence group: ligand identity fields plus the actual centre atom. -/
structure NativeLigandGroup (V : Type*) (LigandId LigandKind : Type*) where
  ligand : LigandId
  ligandKind : LigandKind
  centre : V

/-- The ligand-level group of a fragment group. -/
def nativeFragmentGroupToLigandGroup {V : Type*} {LigandId LigandKind FragmentId FragmentKind : Type*}
    (group : NativeFragmentGroup V LigandId LigandKind FragmentId FragmentKind) :
    NativeLigandGroup V LigandId LigandKind :=
  { ligand := group.ligand
    ligandKind := group.ligandKind
    centre := group.centre }

/-- The fragment group of an occurrence. -/
def nativeFragmentGroup {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :
    NativeFragmentGroup V LigandId LigandKind FragmentId FragmentKind :=
  { ligand := occ.ligand
    ligandKind := occ.ligandKind
    fragment := occ.fragment
    fragmentKind := occ.fragmentKind
    centre := occ.centre }

/-- The ligand group of an occurrence. -/
def nativeLigandGroup {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :
    NativeLigandGroup V LigandId LigandKind :=
  { ligand := occ.ligand
    ligandKind := occ.ligandKind
    centre := occ.centre }

/-- Native fragment-level grouping predicate. -/
def SameNativeFragmentGroup {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n)
    (group : NativeFragmentGroup V LigandId LigandKind FragmentId FragmentKind) : Prop :=
  occ.ligand = group.ligand ∧ occ.ligandKind = group.ligandKind ∧
    occ.fragment = group.fragment ∧ occ.fragmentKind = group.fragmentKind ∧
      occ.centre = group.centre

/-- Native ligand-level grouping predicate. -/
def SameNativeLigandGroup {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n)
    (group : NativeLigandGroup V LigandId LigandKind) : Prop :=
  occ.ligand = group.ligand ∧ occ.ligandKind = group.ligandKind ∧ occ.centre = group.centre

/-- Executable native fragment-level grouping predicate. -/
def nativeFragmentGroupBool {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n)
    (group : NativeFragmentGroup V LigandId LigandKind FragmentId FragmentKind) : Bool :=
  decide (occ.ligand = group.ligand) && decide (occ.ligandKind = group.ligandKind) &&
    decide (occ.fragment = group.fragment) && decide (occ.fragmentKind = group.fragmentKind) &&
      decide (occ.centre = group.centre)

/-- Executable native ligand-level grouping predicate. -/
def nativeLigandGroupBool {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n)
    (group : NativeLigandGroup V LigandId LigandKind) : Bool :=
  decide (occ.ligand = group.ligand) && decide (occ.ligandKind = group.ligandKind) &&
    decide (occ.centre = group.centre)

@[simp] theorem nativeFragmentGroupBool_eq_true_iff {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n)
    (group : NativeFragmentGroup V LigandId LigandKind FragmentId FragmentKind) :
    nativeFragmentGroupBool occ group = true ↔ SameNativeFragmentGroup occ group := by
  simp [nativeFragmentGroupBool, SameNativeFragmentGroup, and_assoc]

@[simp] theorem nativeLigandGroupBool_eq_true_iff {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n)
    (group : NativeLigandGroup V LigandId LigandKind) :
    nativeLigandGroupBool occ group = true ↔ SameNativeLigandGroup occ group := by
  simp [nativeLigandGroupBool, SameNativeLigandGroup, and_assoc]

/-- Native fragment-group occurrences, in channel order. -/
def nativeFragmentIncidences {n : Nat}
    (occs : List (VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n))
    (group : NativeFragmentGroup V LigandId LigandKind FragmentId FragmentKind) :
    List (VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :=
  occs.filter fun occ => nativeFragmentGroupBool occ group

/-- Native ligand-group occurrences, in channel order. -/
def nativeLigandIncidences {n : Nat}
    (occs : List (VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n))
    (group : NativeLigandGroup V LigandId LigandKind) :
    List (VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :=
  occs.filter fun occ => nativeLigandGroupBool occ group

/-- Recorded donor atoms of a native fragment group. -/
def nativeFragmentDonors {n : Nat}
    (occs : List (VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n))
    (group : NativeFragmentGroup V LigandId LigandKind FragmentId FragmentKind) : Finset V :=
  ((nativeFragmentIncidences occs group).map fun occ => occ.donor).toFinset

/-- Recorded donor atoms of a native ligand group. -/
def nativeLigandDonors {n : Nat}
    (occs : List (VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n))
    (group : NativeLigandGroup V LigandId LigandKind) : Finset V :=
  ((nativeLigandIncidences occs group).map fun occ => occ.donor).toFinset

/-- Native recorded fragment κ: distinct donor atoms inside one fragment occurrence. -/
def nativeRecordedFragmentKappa {n : Nat}
    (occs : List (VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n))
    (group : NativeFragmentGroup V LigandId LigandKind FragmentId FragmentKind) : Nat :=
  (nativeFragmentDonors occs group).card

/-- Native recorded ligand denticity: distinct donor atoms of one ligand occurrence. -/
def nativeRecordedLigandDenticity {n : Nat}
    (occs : List (VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n))
    (group : NativeLigandGroup V LigandId LigandKind) : Nat :=
  (nativeLigandDonors occs group).card

/-- Derived native polydenticity: at least two distinct recorded donor atoms. -/
def NativeIsPolydentate {n : Nat}
    (occs : List (VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n))
    (group : NativeLigandGroup V LigandId LigandKind) : Prop :=
  2 ≤ nativeRecordedLigandDenticity occs group

/-! ## The ingress from an existing enriched ledger -/

/-- The `V`-native occurrence corresponding to one enriched source incidence.  The exact source
interaction index is transported by its numeral; the donor and centre are transported back through
the single atom equivalence induced by the common enumeration; all metadata is copied literally. -/
def occurrenceOfIncidence (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind
      graph.interactions.length :=
  { index := residueSourceInteractionIndex graph eV inc.index
    donor := sourceAtomOfEncoded graph eV inc.donor
    centre := sourceAtomOfEncoded graph eV inc.centre
    ligand := inc.ligand
    ligandKind := inc.ligandKind
    fragment := inc.fragment
    fragmentKind := inc.fragmentKind
    basePriority := inc.basePriority }

@[simp] theorem occurrenceOfIncidence_index (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (occurrenceOfIncidence graph eV inc).index =
      residueSourceInteractionIndex graph eV inc.index := rfl

@[simp] theorem occurrenceOfIncidence_index_val (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (occurrenceOfIncidence graph eV inc).index.val = inc.index.val := rfl

@[simp] theorem occurrenceOfIncidence_donor (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (occurrenceOfIncidence graph eV inc).donor = sourceAtomOfEncoded graph eV inc.donor := rfl

@[simp] theorem occurrenceOfIncidence_centre (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (occurrenceOfIncidence graph eV inc).centre = sourceAtomOfEncoded graph eV inc.centre := rfl

@[simp] theorem occurrenceOfIncidence_ligand (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (occurrenceOfIncidence graph eV inc).ligand = inc.ligand := rfl

@[simp] theorem occurrenceOfIncidence_ligandKind (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (occurrenceOfIncidence graph eV inc).ligandKind = inc.ligandKind := rfl

@[simp] theorem occurrenceOfIncidence_fragment (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (occurrenceOfIncidence graph eV inc).fragment = inc.fragment := rfl

@[simp] theorem occurrenceOfIncidence_fragmentKind (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (occurrenceOfIncidence graph eV inc).fragmentKind = inc.fragmentKind := rfl

@[simp] theorem occurrenceOfIncidence_basePriority (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (occurrenceOfIncidence graph eV inc).basePriority = inc.basePriority := rfl

/-- The actual ingress: the positional image of the enriched incidence list.  The occurrence order
and multiplicity are exactly those of the supplied ledger. -/
def channelOfLedger (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
      graph.interactions.length :=
  { occurrences := ledger.incidences.map (occurrenceOfIncidence graph eV) }

@[simp] theorem channelOfLedger_occurrences (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (channelOfLedger graph eV ledger).occurrences =
      ledger.incidences.map (occurrenceOfIncidence graph eV) := rfl

theorem channelOfLedger_occurrences_length (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (channelOfLedger graph eV ledger).occurrences.length = ledger.incidences.length := by
  rw [channelOfLedger_occurrences, List.length_map]

/-- Positional exactness, including duplicated entries. -/
theorem channelOfLedger_occurrences_getElem? (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) (index : Nat) :
    (channelOfLedger graph eV ledger).occurrences[index]? =
      (ledger.incidences[index]?).map (occurrenceOfIncidence graph eV) := by
  rw [channelOfLedger_occurrences, List.getElem?_map]

/-- Every incidence of the supplied ledger becomes one native occurrence, with its exact index,
donor, centre, metadata and base priority. -/
theorem channelOfLedger_mem_occurrence (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)
    {inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind} (member : inc ∈ ledger.incidences) :
    occurrenceOfIncidence graph eV inc ∈ (channelOfLedger graph eV ledger).occurrences := by
  rw [channelOfLedger_occurrences]
  exact List.mem_map_of_mem member

/-! ## Proof-only native validity and its derivation from existing evidence -/

/-- Source-bound facts for one native occurrence, relative to the common graph encoding.
The participant condition is the unordered `Finset` equality used by the existing
`DirectedEnrichment`; direction is separately retained by `donor` and `centre`. -/
structure NativeOccurrenceFacts (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind
      interactionCount) : Prop where
  kind_coordinate :
    (graph.interactions.get (Fin.cast count_eq occ.index)).2 =
      SemanticInteractionKind.coordinate
  participants_length :
    (graph.interactions.get (Fin.cast count_eq occ.index)).1.length = 2
  support :
    (graph.interactions.get (Fin.cast count_eq occ.index)).1.toFinset =
      ({occ.donor, occ.centre} : Finset V)
  donor_ne_centre : occ.donor ≠ occ.centre

/-- Proof-only validity of a whole native channel.  No validity is derivable from the raw
occurrence list alone; this predicate is the caller-visible certificate. -/
structure NativeChannelValidity (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
      interactionCount) : Prop where
  facts : ∀ occ, occ ∈ channel.occurrences → NativeOccurrenceFacts graph eV count_eq occ

/-- Direction is retained: the donor is an actual participant of the actual interaction. -/
theorem NativeOccurrenceFacts.donor_mem_participants
    {graph : FiniteAtomInteractionHypergraph V} {eV : V ≃ Fin (Fintype.card V)}
    {interactionCount : Nat} {count_eq : interactionCount = graph.interactions.length}
    {occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind interactionCount}
    (facts : NativeOccurrenceFacts graph eV count_eq occ) :
    occ.donor ∈ (graph.interactions.get (Fin.cast count_eq occ.index)).1 := by
  have hmem : occ.donor ∈
      (graph.interactions.get (Fin.cast count_eq occ.index)).1.toFinset := by
    rw [facts.support]
    simp
  simpa using hmem

/-- Direction is retained: the centre is an actual participant of the actual interaction. -/
theorem NativeOccurrenceFacts.centre_mem_participants
    {graph : FiniteAtomInteractionHypergraph V} {eV : V ≃ Fin (Fintype.card V)}
    {interactionCount : Nat} {count_eq : interactionCount = graph.interactions.length}
    {occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind interactionCount}
    (facts : NativeOccurrenceFacts graph eV count_eq occ) :
    occ.centre ∈ (graph.interactions.get (Fin.cast count_eq occ.index)).1 := by
  have hmem : occ.centre ∈
      (graph.interactions.get (Fin.cast count_eq occ.index)).1.toFinset := by
    rw [facts.support]
    simp
  simpa using hmem

/-- The exact encoded support of the source incidence, transported to `V`. -/
theorem occurrenceFactsOfIncidence (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    NativeOccurrenceFacts graph eV
      (rfl : graph.interactions.length = graph.interactions.length)
      (occurrenceOfIncidence graph eV inc) := by
  have hidx :
      (Fin.cast (rfl : graph.interactions.length = graph.interactions.length)
        (occurrenceOfIncidence graph eV inc).index) =
        residueSourceInteractionIndex graph eV inc.index := rfl
  refine ⟨?kind, ?length, ?support, ?distinct⟩
  · rw [hidx]
    have h := congrArg SemanticInteraction.kind
      (certifiedEncoding_interactions_get graph eV inc.index)
    simpa only [FiniteAtomInteractionHypergraph.encodeInteraction] using
      h.symm.trans inc.evidence.kind_coordinate
  · rw [hidx]
    have h := congrArg
      (fun interaction : SemanticInteraction => interaction.participants.length)
      (certifiedEncoding_interactions_get graph eV inc.index)
    simpa only [FiniteAtomInteractionHypergraph.encodeInteraction, List.length_map] using
      h.symm.trans inc.evidence.length_two
  · rw [hidx]
    have hlen :
        (graph.interactions.get
          (residueSourceInteractionIndex graph eV inc.index)).1.length = 2 := by
      have h := congrArg
        (fun interaction : SemanticInteraction => interaction.participants.length)
        (certifiedEncoding_interactions_get graph eV inc.index)
      simpa only [FiniteAtomInteractionHypergraph.encodeInteraction, List.length_map] using
        h.symm.trans inc.evidence.length_two
    have hdonor : sourceAtomOfEncoded graph eV inc.donor ∈
        (graph.interactions.get
          (residueSourceInteractionIndex graph eV inc.index)).1 :=
      sourceAtomOfEncoded_mem_participants graph eV inc.index inc.donor
        inc.donor_mem_source_participants
    have hcentreEncoded : inc.centre.val ∈
        ((graph.certifiedEncoding eV).input.molecule.interactions.get
          inc.index).participants := by
      have hmem : inc.centre.val ∈
          ((graph.certifiedEncoding eV).input.molecule.interactions.get
            inc.index).participants.toFinset := by
        rw [inc.evidence.support]
        simp [DonorIncidence.centre_def]
      simpa using hmem
    have hcentre : sourceAtomOfEncoded graph eV inc.centre ∈
        (graph.interactions.get
          (residueSourceInteractionIndex graph eV inc.index)).1 :=
      sourceAtomOfEncoded_mem_participants graph eV inc.index inc.centre hcentreEncoded
    have hne :
        sourceAtomOfEncoded graph eV inc.donor ≠
          sourceAtomOfEncoded graph eV inc.centre := by
      intro h
      have h' : inc.donor = inc.centre :=
        (encodedAtomEquiv graph eV).symm.injective h
      exact inc.evidence.coordination.distinct h'
    have hcardPair :
        ({sourceAtomOfEncoded graph eV inc.donor,
          sourceAtomOfEncoded graph eV inc.centre} : Finset V).card = 2 :=
      Finset.card_pair hne
    have hsubset :
        ({sourceAtomOfEncoded graph eV inc.donor,
          sourceAtomOfEncoded graph eV inc.centre} : Finset V) ⊆
          (graph.interactions.get
            (residueSourceInteractionIndex graph eV inc.index)).1.toFinset := by
      intro atom hatom
      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
      rcases hatom with rfl | rfl
      · simpa using hdonor
      · simpa using hcentre
    have hcardLe :
        (graph.interactions.get
          (residueSourceInteractionIndex graph eV inc.index)).1.toFinset.card ≤ 2 := by
      have hle :=
        List.toFinset_card_le
          (l := (graph.interactions.get
            (residueSourceInteractionIndex graph eV inc.index)).1)
      rw [hlen] at hle
      exact hle
    have hEq := Finset.eq_of_subset_of_card_le hsubset
      (by rw [hcardPair]; exact hcardLe)
    exact hEq.symm
  · intro h
    have h' : inc.donor = inc.centre :=
      (encodedAtomEquiv graph eV).symm.injective h
    exact inc.evidence.coordination.distinct h'

/-- Proof-only validity obtained from any existing enriched ledger. -/
def nativeValidityOfLedger (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    NativeChannelValidity graph eV
      (rfl : graph.interactions.length = graph.interactions.length)
      (channelOfLedger graph eV ledger) where
  facts occ member := by
    simp only [channelOfLedger] at member
    obtain ⟨inc, _incMem, rfl⟩ := List.mem_map.mp member
    exact occurrenceFactsOfIncidence graph eV inc

/-! ## Decoding back to the enriched ledger -/

/-- The encoded interaction index corresponding to a native occurrence index. -/
def decodedIndex (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (index : Fin interactionCount) :
    Fin (graph.certifiedEncoding eV).input.molecule.interactions.length :=
  Fin.cast (count_eq.trans (certifiedEncoding_interactions_length graph eV).symm) index

@[simp] theorem decodedIndex_val (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (index : Fin interactionCount) :
    (decodedIndex graph eV count_eq index).val = index.val := rfl

@[simp] theorem residueSourceInteractionIndex_decodedIndex
    (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (index : Fin interactionCount) :
    residueSourceInteractionIndex graph eV (decodedIndex graph eV count_eq index) =
      Fin.cast count_eq index :=
  Fin.ext rfl

/-- Rebuild one enriched incidence from a native occurrence plus the proof-only validity facts.
The direction is explicit: `encodedAtomEquiv` sends the native donor to the donor position and
the native centre to the acceptor position of the encoded incidence. -/
def decodeOccurrence (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind
      interactionCount)
    (facts : NativeOccurrenceFacts graph eV count_eq occ) :
    DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind where
  index := decodedIndex graph eV count_eq occ.index
  ligand := occ.ligand
  ligandKind := occ.ligandKind
  fragment := occ.fragment
  fragmentKind := occ.fragmentKind
  basePriority := occ.basePriority
  evidence :=
    { coordination :=
        { donor := encodedAtomEquiv graph eV occ.donor
          acceptor := encodedAtomEquiv graph eV occ.centre
          distinct := fun h => facts.donor_ne_centre
            ((encodedAtomEquiv graph eV).injective h) }
      support := by
        rw [certifiedEncoding_interactions_get graph eV
          (decodedIndex graph eV count_eq occ.index)]
        rw [residueSourceInteractionIndex_decodedIndex graph eV count_eq]
        simp only [FiniteAtomInteractionHypergraph.encodeInteraction]
        rw [toFinset_map_eq_image]
        rw [facts.support]
        simp
      length_two := by
        rw [certifiedEncoding_interactions_get graph eV
          (decodedIndex graph eV count_eq occ.index)]
        rw [residueSourceInteractionIndex_decodedIndex graph eV count_eq]
        simpa only [FiniteAtomInteractionHypergraph.encodeInteraction, List.length_map] using
          facts.participants_length
      kind_coordinate := by
        rw [certifiedEncoding_interactions_get graph eV
          (decodedIndex graph eV count_eq occ.index)]
        rw [residueSourceInteractionIndex_decodedIndex graph eV count_eq]
        simpa only [FiniteAtomInteractionHypergraph.encodeInteraction] using
          facts.kind_coordinate }

@[simp] theorem decodeOccurrence_index (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind interactionCount)
    (facts : NativeOccurrenceFacts graph eV count_eq occ) :
    (decodeOccurrence graph eV count_eq occ facts).index =
      decodedIndex graph eV count_eq occ.index := rfl

@[simp] theorem decodeOccurrence_donor (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind interactionCount)
    (facts : NativeOccurrenceFacts graph eV count_eq occ) :
    (decodeOccurrence graph eV count_eq occ facts).donor =
      encodedAtomEquiv graph eV occ.donor := rfl

@[simp] theorem decodeOccurrence_centre (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind interactionCount)
    (facts : NativeOccurrenceFacts graph eV count_eq occ) :
    (decodeOccurrence graph eV count_eq occ facts).centre =
      encodedAtomEquiv graph eV occ.centre := rfl

/-- Decoding preserves the exact source interaction kind of the occurrence. -/
theorem decodeOccurrence_source_kind (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind interactionCount)
    (facts : NativeOccurrenceFacts graph eV count_eq occ) :
    ((graph.certifiedEncoding eV).input.molecule.interactions.get
      (decodeOccurrence graph eV count_eq occ facts).index).kind =
      SemanticInteractionKind.coordinate :=
  (decodeOccurrence graph eV count_eq occ facts).source_kind

/-- Decoding preserves the exact encoded participant count of the occurrence. -/
theorem decodeOccurrence_source_length (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind interactionCount)
    (facts : NativeOccurrenceFacts graph eV count_eq occ) :
    ((graph.certifiedEncoding eV).input.molecule.interactions.get
      (decodeOccurrence graph eV count_eq occ facts).index).participants.length = 2 :=
  (decodeOccurrence graph eV count_eq occ facts).source_participants_length

/-- The decoded donor is an actual participant of the exact encoded interaction. -/
theorem decodeOccurrence_donor_mem_source_participants
    (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind interactionCount)
    (facts : NativeOccurrenceFacts graph eV count_eq occ) :
    (decodeOccurrence graph eV count_eq occ facts).donor.val ∈
      ((graph.certifiedEncoding eV).input.molecule.interactions.get
        (decodeOccurrence graph eV count_eq occ facts).index).participants :=
  (decodeOccurrence graph eV count_eq occ facts).donor_mem_source_participants

/-- Decoding preserves the exact supplied base priority. -/
@[simp] theorem decodeOccurrence_basePriority (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind interactionCount)
    (facts : NativeOccurrenceFacts graph eV count_eq occ) :
    (decodeOccurrence graph eV count_eq occ facts).basePriority = occ.basePriority := rfl

/-! ## Structural extensionality of the enriched data -/

theorem directedCoordination_extEq {atomCount : Nat}
    {first second : InteractionRoles.DirectedCoordination atomCount}
    (donor : first.donor = second.donor)
    (acceptor : first.acceptor = second.acceptor) : first = second := by
  obtain ⟨firstDonor, firstAcceptor, firstDistinct⟩ := first
  obtain ⟨secondDonor, secondAcceptor, secondDistinct⟩ := second
  dsimp only at donor acceptor
  cases donor
  cases acceptor
  have hdistinct : firstDistinct = secondDistinct := Subsingleton.elim _ _
  cases hdistinct
  rfl

theorem directedEnrichment_extEq {molecule : SemanticMolecule}
    {index : Fin molecule.interactions.length}
    {first second : InteractionRoles.DirectedEnrichment molecule index}
    (coordination : first.coordination = second.coordination) : first = second := by
  obtain ⟨firstCoordination, firstSupport, firstLength, firstKind⟩ := first
  obtain ⟨secondCoordination, secondSupport, secondLength, secondKind⟩ := second
  dsimp only at coordination
  cases coordination
  have hsupport : firstSupport = secondSupport := Subsingleton.elim _ _
  have hlength : firstLength = secondLength := Subsingleton.elim _ _
  have hkind : firstKind = secondKind := Subsingleton.elim _ _
  cases hsupport
  cases hlength
  cases hkind
  rfl

theorem donorIncidence_extEq {molecule : SemanticMolecule}
    {first second : DonorIncidence molecule LigandId LigandKind FragmentId FragmentKind}
    (index : first.index = second.index)
    (ligand : first.ligand = second.ligand)
    (ligandKind : first.ligandKind = second.ligandKind)
    (fragment : first.fragment = second.fragment)
    (fragmentKind : first.fragmentKind = second.fragmentKind)
    (basePriority : first.basePriority = second.basePriority)
    (coordination : first.evidence.coordination = second.evidence.coordination) :
    first = second := by
  obtain ⟨firstIndex, firstLigand, firstLigandKind, firstFragment, firstFragmentKind,
    firstPriority, firstEvidence⟩ := first
  obtain ⟨secondIndex, secondLigand, secondLigandKind, secondFragment, secondFragmentKind,
    secondPriority, secondEvidence⟩ := second
  dsimp only at index ligand ligandKind fragment fragmentKind basePriority coordination
  cases index
  cases ligand
  cases ligandKind
  cases fragment
  cases fragmentKind
  cases basePriority
  have hevidence : firstEvidence = secondEvidence :=
    directedEnrichment_extEq coordination
  cases hevidence
  rfl

theorem fragmentGroup_extEq {atomCount : Nat}
    {first second : FragmentGroup LigandId LigandKind FragmentId FragmentKind atomCount}
    (ligand : first.ligand = second.ligand)
    (ligandKind : first.ligandKind = second.ligandKind)
    (fragment : first.fragment = second.fragment)
    (fragmentKind : first.fragmentKind = second.fragmentKind)
    (centre : first.centre = second.centre) : first = second := by
  obtain ⟨firstLigand, firstLigandKind, firstFragment, firstFragmentKind, firstCentre⟩ := first
  obtain ⟨secondLigand, secondLigandKind, secondFragment, secondFragmentKind, secondCentre⟩ := second
  dsimp only at ligand ligandKind fragment fragmentKind centre
  cases ligand
  cases ligandKind
  cases fragment
  cases fragmentKind
  cases centre
  rfl

theorem ligandGroup_extEq {atomCount : Nat}
    {first second : LigandGroup LigandId LigandKind atomCount}
    (ligand : first.ligand = second.ligand)
    (ligandKind : first.ligandKind = second.ligandKind)
    (centre : first.centre = second.centre) : first = second := by
  obtain ⟨firstLigand, firstLigandKind, firstCentre⟩ := first
  obtain ⟨secondLigand, secondLigandKind, secondCentre⟩ := second
  dsimp only at ligand ligandKind centre
  cases ligand
  cases ligandKind
  cases centre
  rfl

/-! ## Exact recovery of the supplied enriched ledger -/

theorem decodeOccurrence_occurrenceOfIncidence (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)
    (facts : NativeOccurrenceFacts graph eV
      (rfl : graph.interactions.length = graph.interactions.length)
      (occurrenceOfIncidence graph eV inc)) :
    decodeOccurrence graph eV
      (rfl : graph.interactions.length = graph.interactions.length)
      (occurrenceOfIncidence graph eV inc) facts = inc := by
  apply donorIncidence_extEq
  · exact Fin.ext rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · apply directedCoordination_extEq
    · exact encodedAtomEquiv_sourceAtomOfEncoded graph eV inc.donor
    · exact encodedAtomEquiv_sourceAtomOfEncoded graph eV inc.centre

/-- Decoding a list of native occurrences, with a proof-only validity function. -/
def decodeOccurrences (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length) :
    (occs : List (VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind
      interactionCount)) →
    (∀ occ, occ ∈ occs → NativeOccurrenceFacts graph eV count_eq occ) →
    List (DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)
  | [], _ => []
  | occ :: rest, facts =>
      decodeOccurrence graph eV count_eq occ (facts occ List.mem_cons_self) ::
        decodeOccurrences graph eV count_eq rest
          (fun other member => facts other (List.mem_cons_of_mem occ member))

@[simp] theorem decodeOccurrences_nil (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (facts : ∀ occ, occ ∈ ([] : List (VNativeDonorOccurrence V LigandId LigandKind FragmentId
      FragmentKind interactionCount)) → NativeOccurrenceFacts graph eV count_eq occ) :
    decodeOccurrences graph eV count_eq [] facts = [] := rfl

@[simp] theorem decodeOccurrences_cons (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind interactionCount)
    (rest : List (VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind
      interactionCount))
    (facts : ∀ other, other ∈ occ :: rest → NativeOccurrenceFacts graph eV count_eq other) :
    decodeOccurrences graph eV count_eq (occ :: rest) facts =
      decodeOccurrence graph eV count_eq occ (facts occ List.mem_cons_self) ::
        decodeOccurrences graph eV count_eq rest
          (fun other member => facts other (List.mem_cons_of_mem occ member)) := rfl

theorem decodeOccurrences_channelOfLedger (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (incidences : List (DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)) :
    ∀ (facts : ∀ occ, occ ∈ incidences.map (occurrenceOfIncidence graph eV) →
        NativeOccurrenceFacts graph eV
          (rfl : graph.interactions.length = graph.interactions.length) occ),
      decodeOccurrences graph eV
        (rfl : graph.interactions.length = graph.interactions.length)
        (incidences.map (occurrenceOfIncidence graph eV)) facts = incidences := by
  induction incidences with
  | nil =>
      intro facts
      rfl
  | cons inc rest ih =>
      intro facts
      change decodeOccurrence graph eV
          (rfl : graph.interactions.length = graph.interactions.length)
          (occurrenceOfIncidence graph eV inc)
          (facts (occurrenceOfIncidence graph eV inc) List.mem_cons_self) ::
        decodeOccurrences graph eV
          (rfl : graph.interactions.length = graph.interactions.length)
          (rest.map (occurrenceOfIncidence graph eV))
          (fun other member =>
            facts other (List.mem_cons_of_mem (occurrenceOfIncidence graph eV inc) member))
        = inc :: rest
      congr 1
      · exact decodeOccurrence_occurrenceOfIncidence graph eV inc _
      · exact ih (fun occ member =>
          facts occ (List.mem_cons_of_mem (occurrenceOfIncidence graph eV inc) member))

/-- Decode a whole channel with its proof-only validity certificate. -/
def decodeIncidences (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
      interactionCount)
    (validity : NativeChannelValidity graph eV count_eq channel) :
    List (DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :=
  decodeOccurrences graph eV count_eq channel.occurrences validity.facts

/-- Decode a whole channel back to an enriched ledger. -/
def decodeLedger (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {interactionCount : Nat}
    (count_eq : interactionCount = graph.interactions.length)
    (channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
      interactionCount)
    (validity : NativeChannelValidity graph eV count_eq channel) :
    DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind :=
  { incidences := decodeIncidences graph eV count_eq channel validity }

/-- The ingress followed by decoding recovers the original enriched incidence list exactly. -/
theorem decodeIncidences_channelOfLedger (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    decodeIncidences graph eV
      (rfl : graph.interactions.length = graph.interactions.length)
      (channelOfLedger graph eV ledger) (nativeValidityOfLedger graph eV ledger) =
      ledger.incidences := by
  unfold decodeIncidences channelOfLedger
  exact decodeOccurrences_channelOfLedger graph eV ledger.incidences
    (nativeValidityOfLedger graph eV ledger).facts

/-- The full enriched `DonorLedger` round-trips through the native channel and the proof-only
validity certificate. -/
theorem decodeLedger_channelOfLedger (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    decodeLedger graph eV
      (rfl : graph.interactions.length = graph.interactions.length)
      (channelOfLedger graph eV ledger) (nativeValidityOfLedger graph eV ledger) = ledger := by
  obtain ⟨incidences⟩ := ledger
  simp [decodeLedger, decodeIncidences_channelOfLedger]

/-- The ingress map on individual incidences is injective.  It retains the exact occurrence index,
the donor and centre transported through the atom bijection, all four typed metadata fields and the
supplied base priority; the remaining fields of the enriched incidence are proof-only. -/
theorem occurrenceOfIncidence_injective (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) :
    Function.Injective
      (occurrenceOfIncidence (LigandId := LigandId) (LigandKind := LigandKind)
        (FragmentId := FragmentId) (FragmentKind := FragmentKind) graph eV) := by
  intro first second equal
  have hindex : first.index = second.index :=
    Fin.ext (by simpa using congrArg (fun occ => occ.index.val) equal)
  have hdonor : first.donor = second.donor :=
    (encodedAtomEquiv graph eV).symm.injective
      (by
        simpa only [occurrenceOfIncidence, sourceAtomOfEncoded] using
          congrArg (fun occ => occ.donor) equal)
  have hcentre : first.centre = second.centre :=
    (encodedAtomEquiv graph eV).symm.injective
      (by
        simpa only [occurrenceOfIncidence, sourceAtomOfEncoded] using
          congrArg (fun occ => occ.centre) equal)
  have hligand : first.ligand = second.ligand := by
    simpa only [occurrenceOfIncidence] using congrArg (fun occ => occ.ligand) equal
  have hligandKind : first.ligandKind = second.ligandKind := by
    simpa only [occurrenceOfIncidence] using congrArg (fun occ => occ.ligandKind) equal
  have hfragment : first.fragment = second.fragment := by
    simpa only [occurrenceOfIncidence] using congrArg (fun occ => occ.fragment) equal
  have hfragmentKind : first.fragmentKind = second.fragmentKind := by
    simpa only [occurrenceOfIncidence] using congrArg (fun occ => occ.fragmentKind) equal
  have hpriority : first.basePriority = second.basePriority := by
    simpa only [occurrenceOfIncidence] using congrArg (fun occ => occ.basePriority) equal
  exact donorIncidence_extEq hindex hligand hligandKind hfragment hfragmentKind hpriority
    (directedCoordination_extEq hdonor hcentre)

/-- The native channel loses no enriched information: the ingress is injective, unlike the raw
`DonorLedger.occurrences` projection. -/
theorem channelOfLedger_injective (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) :
    Function.Injective
      (channelOfLedger (LigandId := LigandId) (LigandKind := LigandKind)
        (FragmentId := FragmentId) (FragmentKind := FragmentKind) graph eV) := by
  intro first second equal
  have hocc :
      first.incidences.map
          (occurrenceOfIncidence (LigandId := LigandId) (LigandKind := LigandKind)
            (FragmentId := FragmentId) (FragmentKind := FragmentKind) graph eV) =
        second.incidences.map
          (occurrenceOfIncidence (LigandId := LigandId) (LigandKind := LigandKind)
            (FragmentId := FragmentId) (FragmentKind := FragmentKind) graph eV) := by
    simpa [channelOfLedger] using congrArg VNativeDonorChannel.occurrences equal
  have hlist : first.incidences = second.incidences :=
    (List.map_inj_right
      (f := occurrenceOfIncidence (LigandId := LigandId) (LigandKind := LigandKind)
        (FragmentId := FragmentId) (FragmentKind := FragmentKind) graph eV)
      (fun x y hxy => occurrenceOfIncidence_injective graph eV hxy)).mp hocc
  obtain ⟨firstIncidences⟩ := first
  obtain ⟨secondIncidences⟩ := second
  dsimp only at hlist
  cases hlist
  rfl

/-! ## Grouping, κ and denticity preservation -/

/-- The encoded fragment group of a native fragment group, under the explicit atom equivalence. -/
def nativeFragmentGroupToEncoded (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (group : NativeFragmentGroup V LigandId LigandKind FragmentId FragmentKind) :
    FragmentGroup LigandId LigandKind FragmentId FragmentKind
      (graph.certifiedEncoding eV).input.molecule.atomCount :=
  { ligand := group.ligand
    ligandKind := group.ligandKind
    fragment := group.fragment
    fragmentKind := group.fragmentKind
    centre := encodedAtomEquiv graph eV group.centre }

/-- The encoded ligand group of a native ligand group, under the explicit atom equivalence. -/
def nativeLigandGroupToEncoded (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (group : NativeLigandGroup V LigandId LigandKind) :
    LigandGroup LigandId LigandKind
      (graph.certifiedEncoding eV).input.molecule.atomCount :=
  { ligand := group.ligand
    ligandKind := group.ligandKind
    centre := encodedAtomEquiv graph eV group.centre }

theorem nativeFragmentGroupToEncoded_occurrenceOfIncidence
    (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    nativeFragmentGroupToEncoded graph eV (nativeFragmentGroup (occurrenceOfIncidence graph eV inc)) =
      inc.fragmentGroup := by
  apply fragmentGroup_extEq
  · rfl
  · rfl
  · rfl
  · rfl
  · show encodedAtomEquiv graph eV (sourceAtomOfEncoded graph eV inc.centre) = inc.centre
    exact encodedAtomEquiv_sourceAtomOfEncoded graph eV inc.centre

theorem nativeLigandGroupToEncoded_occurrenceOfIncidence
    (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    nativeLigandGroupToEncoded graph eV (nativeLigandGroup (occurrenceOfIncidence graph eV inc)) =
      inc.ligandGroup := by
  apply ligandGroup_extEq
  · rfl
  · rfl
  · show encodedAtomEquiv graph eV (sourceAtomOfEncoded graph eV inc.centre) = inc.centre
    exact encodedAtomEquiv_sourceAtomOfEncoded graph eV inc.centre

theorem nativeFragmentGroupBool_occurrenceOfIncidence
    (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)
    (group : NativeFragmentGroup V LigandId LigandKind FragmentId FragmentKind) :
    nativeFragmentGroupBool (occurrenceOfIncidence graph eV inc) group =
      DonorOccurrenceEncoding.fragmentGroupBool inc
        (nativeFragmentGroupToEncoded graph eV group) := by
  rw [Bool.eq_iff_iff, nativeFragmentGroupBool_eq_true_iff,
    DonorOccurrenceEncoding.fragmentGroupBool_eq_true_iff]
  simp only [SameNativeFragmentGroup, DonorOccurrenceEncoding.SameFragmentGroup,
    occurrenceOfIncidence, sourceAtomOfEncoded, nativeFragmentGroupToEncoded]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, (Equiv.symm_apply_eq (encodedAtomEquiv graph eV)).mp h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, (Equiv.symm_apply_eq (encodedAtomEquiv graph eV)).mpr h5⟩

theorem nativeLigandGroupBool_occurrenceOfIncidence
    (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)
    (group : NativeLigandGroup V LigandId LigandKind) :
    nativeLigandGroupBool (occurrenceOfIncidence graph eV inc) group =
      DonorOccurrenceEncoding.ligandGroupBool inc
        (nativeLigandGroupToEncoded graph eV group) := by
  rw [Bool.eq_iff_iff, nativeLigandGroupBool_eq_true_iff,
    DonorOccurrenceEncoding.ligandGroupBool_eq_true_iff]
  simp only [SameNativeLigandGroup, DonorOccurrenceEncoding.SameLigandGroup,
    occurrenceOfIncidence, sourceAtomOfEncoded, nativeLigandGroupToEncoded]
  constructor
  · rintro ⟨h1, h2, h5⟩
    exact ⟨h1, h2, (Equiv.symm_apply_eq (encodedAtomEquiv graph eV)).mp h5⟩
  · rintro ⟨h1, h2, h5⟩
    exact ⟨h1, h2, (Equiv.symm_apply_eq (encodedAtomEquiv graph eV)).mpr h5⟩

/-- Native ligand donor sets are the exact atom-equivalence image of the encoded ledger's recorded
ligand donor sets. -/
theorem nativeLigandDonors_channelOfLedger (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)
    (group : NativeLigandGroup V LigandId LigandKind) :
    nativeLigandDonors (channelOfLedger graph eV ledger).occurrences group =
      (DonorOccurrenceEncoding.ligandDonors ledger.incidences
        (nativeLigandGroupToEncoded graph eV group)).image (encodedAtomEquiv graph eV).symm := by
  have hfilter :
      (channelOfLedger graph eV ledger).occurrences.filter
          (fun occ => nativeLigandGroupBool occ group) =
        (ledger.incidences.filter (fun inc =>
          DonorOccurrenceEncoding.ligandGroupBool inc
            (nativeLigandGroupToEncoded graph eV group))).map
          (occurrenceOfIncidence graph eV) := by
    rw [channelOfLedger, List.filter_map]
    congr 1
    apply List.filter_congr
    intro inc _
    exact nativeLigandGroupBool_occurrenceOfIncidence graph eV inc group
  simp only [nativeLigandDonors, nativeLigandIncidences,
    DonorOccurrenceEncoding.ligandDonors, DonorOccurrenceEncoding.ligandIncidences]
  rw [hfilter]
  simp only [List.map_map]
  have hmap :
      (ledger.incidences.filter (fun inc =>
          DonorOccurrenceEncoding.ligandGroupBool inc
            (nativeLigandGroupToEncoded graph eV group))).map
          ((fun occ => occ.donor) ∘ occurrenceOfIncidence graph eV) =
        (ledger.incidences.filter (fun inc =>
          DonorOccurrenceEncoding.ligandGroupBool inc
            (nativeLigandGroupToEncoded graph eV group))).map
          ((encodedAtomEquiv graph eV).symm ∘ DonorIncidence.donor) := by
    apply List.map_congr_left
    intro inc _
    rfl
  rw [hmap, ← List.map_map]
  rw [toFinset_map_eq_image (f := (encodedAtomEquiv graph eV).symm)]

/-- Native fragment donor sets are the exact atom-equivalence image of the encoded ledger's
recorded fragment donor sets. -/
theorem nativeFragmentDonors_channelOfLedger (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)
    (group : NativeFragmentGroup V LigandId LigandKind FragmentId FragmentKind) :
    nativeFragmentDonors (channelOfLedger graph eV ledger).occurrences group =
      (DonorOccurrenceEncoding.fragmentDonors ledger.incidences
        (nativeFragmentGroupToEncoded graph eV group)).image (encodedAtomEquiv graph eV).symm := by
  have hfilter :
      (channelOfLedger graph eV ledger).occurrences.filter
          (fun occ => nativeFragmentGroupBool occ group) =
        (ledger.incidences.filter (fun inc =>
          DonorOccurrenceEncoding.fragmentGroupBool inc
            (nativeFragmentGroupToEncoded graph eV group))).map
          (occurrenceOfIncidence graph eV) := by
    rw [channelOfLedger, List.filter_map]
    congr 1
    apply List.filter_congr
    intro inc _
    exact nativeFragmentGroupBool_occurrenceOfIncidence graph eV inc group
  simp only [nativeFragmentDonors, nativeFragmentIncidences,
    DonorOccurrenceEncoding.fragmentDonors, DonorOccurrenceEncoding.fragmentIncidences]
  rw [hfilter]
  simp only [List.map_map]
  have hmap :
      (ledger.incidences.filter (fun inc =>
          DonorOccurrenceEncoding.fragmentGroupBool inc
            (nativeFragmentGroupToEncoded graph eV group))).map
          ((fun occ => occ.donor) ∘ occurrenceOfIncidence graph eV) =
        (ledger.incidences.filter (fun inc =>
          DonorOccurrenceEncoding.fragmentGroupBool inc
            (nativeFragmentGroupToEncoded graph eV group))).map
          ((encodedAtomEquiv graph eV).symm ∘ DonorIncidence.donor) := by
    apply List.map_congr_left
    intro inc _
    rfl
  rw [hmap, ← List.map_map]
  rw [toFinset_map_eq_image (f := (encodedAtomEquiv graph eV).symm)]

/-- Fragment κ is preserved: the native cardinality equals the encoded ledger's recorded κ. -/
theorem nativeRecordedFragmentKappa_channelOfLedger
    (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)
    (group : NativeFragmentGroup V LigandId LigandKind FragmentId FragmentKind) :
    nativeRecordedFragmentKappa (channelOfLedger graph eV ledger).occurrences group =
      DonorOccurrenceEncoding.recordedFragmentKappa ledger.incidences
        (nativeFragmentGroupToEncoded graph eV group) := by
  unfold nativeRecordedFragmentKappa DonorOccurrenceEncoding.recordedFragmentKappa
  rw [nativeFragmentDonors_channelOfLedger]
  exact Finset.card_image_of_injective _
    (encodedAtomEquiv graph eV).symm.injective

/-- Ligand denticity is preserved: the native cardinality equals the encoded ledger's recorded
denticity. -/
theorem nativeRecordedLigandDenticity_channelOfLedger
    (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)
    (group : NativeLigandGroup V LigandId LigandKind) :
    nativeRecordedLigandDenticity (channelOfLedger graph eV ledger).occurrences group =
      DonorOccurrenceEncoding.recordedLigandDenticity ledger.incidences
        (nativeLigandGroupToEncoded graph eV group) := by
  unfold nativeRecordedLigandDenticity DonorOccurrenceEncoding.recordedLigandDenticity
  rw [nativeLigandDonors_channelOfLedger]
  exact Finset.card_image_of_injective _
    (encodedAtomEquiv graph eV).symm.injective

/-- Derived native polydenticity agrees with the encoded ledger's derived polydenticity. -/
theorem nativeIsPolydentate_iff (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)
    (group : NativeLigandGroup V LigandId LigandKind) :
    NativeIsPolydentate (channelOfLedger graph eV ledger).occurrences group ↔
      DonorOccurrenceEncoding.IsPolydentate ledger.incidences
        (nativeLigandGroupToEncoded graph eV group) := by
  unfold NativeIsPolydentate DonorOccurrenceEncoding.IsPolydentate
  rw [nativeRecordedLigandDenticity_channelOfLedger]

/-! ## Generic atom relabelling and its two-sided inverse -/

/-- Relabel the atom labels of a native occurrence along an equivalence.  Every other field,
including the interaction index, is untouched. -/
def relabelOccurrence {W : Type*} (e : V ≃ W) {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :
    VNativeDonorOccurrence W LigandId LigandKind FragmentId FragmentKind n :=
  { index := occ.index
    donor := e occ.donor
    centre := e occ.centre
    ligand := occ.ligand
    ligandKind := occ.ligandKind
    fragment := occ.fragment
    fragmentKind := occ.fragmentKind
    basePriority := occ.basePriority }

@[simp] theorem relabelOccurrence_index {W : Type*} (e : V ≃ W) {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :
    (relabelOccurrence e occ).index = occ.index := rfl

@[simp] theorem relabelOccurrence_donor {W : Type*} (e : V ≃ W) {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :
    (relabelOccurrence e occ).donor = e occ.donor := rfl

@[simp] theorem relabelOccurrence_centre {W : Type*} (e : V ≃ W) {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :
    (relabelOccurrence e occ).centre = e occ.centre := rfl

@[simp] theorem relabelOccurrence_ligand {W : Type*} (e : V ≃ W) {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :
    (relabelOccurrence e occ).ligand = occ.ligand := rfl

@[simp] theorem relabelOccurrence_ligandKind {W : Type*} (e : V ≃ W) {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :
    (relabelOccurrence e occ).ligandKind = occ.ligandKind := rfl

@[simp] theorem relabelOccurrence_fragment {W : Type*} (e : V ≃ W) {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :
    (relabelOccurrence e occ).fragment = occ.fragment := rfl

@[simp] theorem relabelOccurrence_fragmentKind {W : Type*} (e : V ≃ W) {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :
    (relabelOccurrence e occ).fragmentKind = occ.fragmentKind := rfl

@[simp] theorem relabelOccurrence_basePriority {W : Type*} (e : V ≃ W) {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :
    (relabelOccurrence e occ).basePriority = occ.basePriority := rfl

/-- Relabel a whole native channel. -/
def relabelChannel {W : Type*} (e : V ≃ W) {n : Nat}
    (channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind n) :
    VNativeDonorChannel W LigandId LigandKind FragmentId FragmentKind n :=
  { occurrences := channel.occurrences.map (relabelOccurrence e) }

@[simp] theorem relabelChannel_occurrences {W : Type*} (e : V ≃ W) {n : Nat}
    (channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind n) :
    (relabelChannel e channel).occurrences =
      channel.occurrences.map (relabelOccurrence e) := rfl

theorem relabelOccurrence_symm {W : Type*} (e : V ≃ W) {n : Nat}
    (occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n) :
    relabelOccurrence e.symm (relabelOccurrence e occ) = occ := by
  cases occ
  simp [relabelOccurrence]

theorem relabelChannel_symm {W : Type*} (e : V ≃ W) {n : Nat}
    (channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind n) :
    relabelChannel e.symm (relabelChannel e channel) = channel := by
  cases channel with
  | mk occurrences =>
      have hpoint :
          ∀ occ : VNativeDonorOccurrence V LigandId LigandKind FragmentId FragmentKind n,
            relabelOccurrence e.symm (relabelOccurrence e occ) = occ :=
        fun occ => relabelOccurrence_symm e occ
      simp only [relabelChannel, List.map_map]
      rw [show (occurrences.map ((relabelOccurrence e.symm) ∘ relabelOccurrence e))
            = occurrences.map id from
          List.map_congr_left (fun occ _ => hpoint occ), List.map_id]

/-- The `Fin`-encoding relabel is a two-sided inverse. -/
theorem finRelabel_inverse (eV : V ≃ Fin (Fintype.card V)) {n : Nat}
    (channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind n) :
    relabelChannel eV.symm (relabelChannel eV channel) = channel :=
  relabelChannel_symm eV channel

/-- The reverse two-sided inverse of the `Fin`-encoding relabel. -/
theorem finRelabel_inverse' (eV : V ≃ Fin (Fintype.card V)) {n : Nat}
    (channel : VNativeDonorChannel (Fin (Fintype.card V))
      LigandId LigandKind FragmentId FragmentKind n) :
    relabelChannel eV (relabelChannel eV.symm channel) = channel :=
  relabelChannel_symm eV.symm channel

/-- Under the `Fin` relabel, an ingress occurrence keeps the exact encoded numeral of its source
interaction index, its donor, its centre, all typed identity metadata and its supplied priority. -/
theorem relabelOccurrence_occurrenceOfIncidence_data
    (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (inc : DonorIncidence (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    let occ := relabelOccurrence eV (occurrenceOfIncidence graph eV inc)
    occ.index.val = inc.index.val ∧
      occ.donor.val = inc.donor.val ∧
      occ.centre.val = inc.centre.val ∧
      occ.ligand = inc.ligand ∧
      occ.ligandKind = inc.ligandKind ∧
      occ.fragment = inc.fragment ∧
      occ.fragmentKind = inc.fragmentKind ∧
      occ.basePriority = inc.basePriority := by
  dsimp only
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · show (eV (sourceAtomOfEncoded graph eV inc.donor)).val = inc.donor.val
    rw [← encodedAtomEquiv_apply_val graph eV (sourceAtomOfEncoded graph eV inc.donor),
      encodedAtomEquiv_sourceAtomOfEncoded]
  · show (eV (sourceAtomOfEncoded graph eV inc.centre)).val = inc.centre.val
    rw [← encodedAtomEquiv_apply_val graph eV (sourceAtomOfEncoded graph eV inc.centre),
      encodedAtomEquiv_sourceAtomOfEncoded]

/-! ## Attachment to the existing whole state via an external satellite -/

/-- External satellite binding a native donor channel to the *same* existing `WholeState` graph.
The state is carried unchanged as a field; no `Domain` or whole-state field is modified. -/
structure DonorGroupingSatellite (V E B : Type*) [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (LigandId LigandKind FragmentId FragmentKind : Type*)
    [DecidableEq LigandId] [DecidableEq LigandKind]
    [DecidableEq FragmentId] [DecidableEq FragmentKind]
    (eV : V ≃ Fin (Fintype.card V)) where
  state : WholeState V E B
  channel : VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
    state.graph.interactions.length
  validity : NativeChannelValidity state.graph eV
    (rfl : state.graph.interactions.length = state.graph.interactions.length) channel

namespace DonorGroupingSatellite

variable {eV : V ≃ Fin (Fintype.card V)}

/-- Decode the satellite's channel back to an enriched ledger over the state's graph. -/
def decodedLedger (sat : DonorGroupingSatellite V E B LigandId LigandKind FragmentId FragmentKind eV) :
    DonorLedger (sat.state.graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind :=
  decodeLedger sat.state.graph eV
    (rfl : sat.state.graph.interactions.length = sat.state.graph.interactions.length)
    sat.channel sat.validity

end DonorGroupingSatellite

/-- Attach a native channel built from an arbitrary existing enriched ledger to an existing whole
state.  The state itself is unchanged; the channel and its proof-only validity are external. -/
def satelliteOfLedger (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : DonorLedger (state.graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    DonorGroupingSatellite V E B LigandId LigandKind FragmentId FragmentKind eV :=
  { state := state
    channel := channelOfLedger state.graph eV ledger
    validity := nativeValidityOfLedger state.graph eV ledger }

@[simp] theorem satelliteOfLedger_state (eV : V ≃ Fin (Fintype.card V))
    (state : WholeState V E B)
    (ledger : DonorLedger (state.graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (satelliteOfLedger eV state ledger).state = state := rfl

@[simp] theorem satelliteOfLedger_channel (eV : V ≃ Fin (Fintype.card V))
    (state : WholeState V E B)
    (ledger : DonorLedger (state.graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (satelliteOfLedger eV state ledger).channel = channelOfLedger state.graph eV ledger := rfl

/-- The satellite decodes back to the exact supplied enriched ledger. -/
theorem satelliteOfLedger_decodedLedger (eV : V ≃ Fin (Fintype.card V))
    (state : WholeState V E B)
    (ledger : DonorLedger (state.graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    (satelliteOfLedger eV state ledger).decodedLedger = ledger := by
  simp [DonorGroupingSatellite.decodedLedger, satelliteOfLedger, decodeLedger_channelOfLedger]

/-! ## Optional presence: `none` versus `some` with an empty channel -/

/-- The empty enriched ledger at the common encoded molecule. -/
def emptyDonorLedger (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) :
    DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind :=
  { incidences := [] }

@[simp] theorem channelOfLedger_emptyDonorLedger_occurrences
    (graph : FiniteAtomInteractionHypergraph V) (eV : V ≃ Fin (Fintype.card V)) :
    (channelOfLedger graph eV
      (emptyDonorLedger (LigandId := LigandId) (LigandKind := LigandKind)
        (FragmentId := FragmentId) (FragmentKind := FragmentKind) graph eV)).occurrences =
      [] := rfl

/-- A supplied empty ledger yields `some` of an empty channel, not `none`. -/
theorem some_empty_channel_ne_none (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) :
    (some (channelOfLedger graph eV (emptyDonorLedger graph eV)) :
      Option (VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
        graph.interactions.length)) ≠
      (none : Option (VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
        graph.interactions.length)) := by
  simp

/-- Optional ingress: absence stays absence, presence (even of an empty ledger) stays presence. -/
def optionalChannelOfLedger (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger? : Option (DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)) :
    Option (VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
      graph.interactions.length) :=
  ledger?.map (channelOfLedger graph eV)

@[simp] theorem optionalChannelOfLedger_none (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) :
    optionalChannelOfLedger graph eV
      (none : Option (DonorLedger (graph.certifiedEncoding eV).input.molecule
        LigandId LigandKind FragmentId FragmentKind)) =
      (none : Option (VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
        graph.interactions.length)) := rfl

@[simp] theorem optionalChannelOfLedger_some (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind) :
    optionalChannelOfLedger graph eV (some ledger) =
      (some (channelOfLedger graph eV ledger) :
        Option (VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
          graph.interactions.length)) := rfl

/-! ## Arbitrary possible-family set recovery -/

/-- The possible native channels of an arbitrary joint family of enriched ledgers. -/
def possibleNativeChannels (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (family : Set (DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)) :
    Set (VNativeDonorChannel V LigandId LigandKind FragmentId FragmentKind
      graph.interactions.length) :=
  channelOfLedger graph eV '' family

/-- Decoding recovers every member of an arbitrary joint possible family exactly. -/
theorem possibleNativeChannels_recovery (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (family : Set (DonorLedger (graph.certifiedEncoding eV).input.molecule
      LigandId LigandKind FragmentId FragmentKind)) :
    (fun ledger =>
      decodeLedger graph eV
        (rfl : graph.interactions.length = graph.interactions.length)
        (channelOfLedger graph eV ledger) (nativeValidityOfLedger graph eV ledger)) ''
        family = family := by
  ext ledger
  constructor
  · rintro ⟨original, member, equal⟩
    rw [← equal]
    simpa only [decodeLedger_channelOfLedger] using member
  · intro member
    exact ⟨ledger, member, decodeLedger_channelOfLedger graph eV ledger⟩

end DonorGroupingIngress

end TetraStereo.OneCenter
