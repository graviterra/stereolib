import TetraStereo.OneCenter.OrganicStereoChemicalOccurrenceFidelity
import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondSpatialAssignment
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

/-!
# Source covalent order-two edge to configured ordinary-double-bond geometry and emitted `E`/`Z`

`OrganicStereoChemicalOccurrenceFidelity` proves that an actual source hyperedge with exact
binary covalent support transports through the exact certified encoding, and it proves that a
typed order-two occurrence alone does **not** determine `E`/`Z`.  This module adds the missing
geometry bridge, using a genuinely configured input:

* an actual source hyperedge whose participant list is *some* ordering of two distinct labels
  (`List.Perm [first, second]`, orientation-free) and whose kind is exactly `covalent 2` yields a
  genuine `AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBond` on the encoded source
  atoms.  The two extra structural obligations are stated explicitly: no interaction of the
  encoded source declares the same unordered pair as aromatic, and the extracted localized
  covalent records are key-unique.  Neither mentions geometry or configuration;
* the strict source-atom order of the canonical carrier is derived from those data, giving an
  actual `AromaticCanonicalOrdinaryDoubleBondCarrier` whose two endpoints are exactly the two
  encoded source labels, in one of the two possible orientations;
* `SourceDoubleBondGeometryData.input` is the **configured** input
  `{ molecule := encoded molecule, spatial? := some suppliedSpatial, diagram? := suppliedDiagram }`.
  The exact encoded molecule is retained (`input_molecule`), so every source carrier and
  interaction proof is about the same molecule; the configuration channels are preserved exactly
  (`input_spatial?`, `input_diagram?`, `spatialPointAt?_eq`);
* the existing executable producer
  `AuthoritativeChemicalInput.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?` is applied to
  that constructed carrier with the caller's existing dependency views and Rule-5 flags.  Whenever
  it actually returns `some assignment`, the produced record is the declarative assignment for the
  same carrier, and the emitted `E`/`Z` annotation is read off `assignment.outcome`;
* `producedAssignment_eq_some_of_seqcis` / `..._of_seqtrans` are **non-circular constructive**
  success theorems: from actual individual-route membership, the two endpoint frame and senior
  reference equations (the narrower ranking premise), four coordinate lookups in the supplied
  spatial configuration, exact coplanarity and the sign of the Rule-3 side product, they build an
  assignment and prove that the producer actually returns it, with emitted `Z` (respectively `E`)
  and the same source carrier.  Producer success, the assigned geometry and the desired annotation
  are derived, not assumed.

The bond order is used **only** to construct the constitutional ordinary double bond.  It is not
used to select the emitted annotation: the annotation is a function of the geometry channel and
the Rule-5 endpoint flags.  `emittedDoubleBond_not_determined_by_bondOrder` records the resulting
dichotomy explicitly.

No claim is made about glycosidic `alpha`/`beta` anomers, sphingoid chemical class, input
certification (`SpatialIndicesWellFormed`/`DiagramIndicesWellFormed` are not assumed or proved),
chemical admissibility or CIP priority; the Rule-5 endpoint flags and the endpoint ranking-frame
success are caller premises, not established Rule-5 facts.
-/

/-! ## Emitted double-bond annotation -/

namespace StereoOutcome

/-- The `E`/`Z` annotation a stereo outcome emits, if it emits one.  An enantiomorphic
`seqCis`/`seqTrans` double bond emits no plain `E`/`Z` annotation; this is the same distinction
used by `sequenceDoubleBondOutcomeOfGeometry`. -/
def doubleBondStereo? : StereoOutcome → Option DoubleBondStereo
  | .alkene value => some value
  | _ => none

@[simp] theorem doubleBondStereo?_alkene (value : DoubleBondStereo) :
    (StereoOutcome.alkene value).doubleBondStereo? = some value := rfl

@[simp] theorem doubleBondStereo?_enantiomorphicDoubleBond
    (value : SequenceDoubleBondDescriptor) :
    (StereoOutcome.enantiomorphicDoubleBond value).doubleBondStereo? = none := rfl

/-- The emitted annotation is exactly the `alkene` payload. -/
theorem doubleBondStereo?_eq_some_iff (outcome : StereoOutcome) (value : DoubleBondStereo) :
    outcome.doubleBondStereo? = some value ↔ outcome = StereoOutcome.alkene value := by
  cases outcome <;> simp [doubleBondStereo?]

end StereoOutcome

namespace AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment

/-- The `E`/`Z` annotation emitted by a produced ordinary-double-bond spatial assignment.
This reads only the actual produced `outcome`; it never inspects the bond order. -/
def emittedDoubleBondStereo?
    {source : AuthoritativeChemicalInput}
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    Option DoubleBondStereo :=
  assignment.outcome.doubleBondStereo?

@[simp] theorem emittedDoubleBondStereo?_eq
    {source : AuthoritativeChemicalInput}
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment.emittedDoubleBondStereo? = assignment.outcome.doubleBondStereo? := rfl

/-- The emitted annotation is exactly the `alkene` payload of the produced outcome. -/
theorem emittedDoubleBondStereo?_eq_some_iff
    {source : AuthoritativeChemicalInput}
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
    (value : DoubleBondStereo) :
    assignment.emittedDoubleBondStereo? = some value ↔
      assignment.outcome = StereoOutcome.alkene value := by
  simp [emittedDoubleBondStereo?, StereoOutcome.doubleBondStereo?_eq_some_iff]

end AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment

namespace OrganicStereoSourceDoubleBondGeometryFidelity

open AuthoritativeChemicalInput

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Generic list orientation and pair-ordering helpers -/

/-- A list that is a permutation of an ordered pair is that pair in one of the two orders. -/
theorem pair_permutation_cases {Alpha : Type*} (values : List Alpha) (left right : Alpha)
    (permutation : values.Perm [left, right]) :
    values = [left, right] ∨ values = [right, left] := by
  have length : values.length = 2 := permutation.length_eq
  obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp length
  have firstMember : first = left ∨ first = right := by
    have member := permutation.mem_iff.mp (List.mem_cons_self : first ∈ [first, second])
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  rcases firstMember with same | same
  · subst first
    have tail := permutation.cons_inv
    have same : second = right := by simpa using tail
    exact Or.inl (by rw [same])
  · subst first
    have swapped : ([left, right] : List Alpha).Perm [right, left] := List.Perm.swap _ _ _
    have tail := (permutation.trans swapped).cons_inv
    have same : second = left := by simpa using tail
    exact Or.inr (by rw [same])

/-- The canonical bond order is independent of the orientation of its two endpoints. -/
theorem aromaticCanonicalBondOrder_comm (molecule : SemanticMolecule) (left right : Nat) :
    molecule.aromaticCanonicalBondOrder left right =
      molecule.aromaticCanonicalBondOrder right left := by
  unfold SemanticMolecule.aromaticCanonicalBondOrder
  rw [semanticEdgeKey_comm right left,
    SemanticMolecule.localizedBondOrder_comm molecule right left]

/-- The ordinary-double-bond predicate is independent of the orientation of its two endpoints.
`AromaticCanonicalAdjacent` and `aromaticCanonicalBondOrder` both use the unordered
`semanticEdgeKey`. -/
theorem aromaticCanonicalOrdinaryDoubleBond_comm (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) :
    source.AromaticCanonicalOrdinaryDoubleBond left right ↔
      source.AromaticCanonicalOrdinaryDoubleBond right left := by
  unfold AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBond
    AuthoritativeChemicalInput.AromaticCanonicalAdjacent
  constructor
  · rintro ⟨⟨different, member⟩, order⟩
    exact ⟨⟨fun same => different same.symm, by simpa [semanticEdgeKey_comm] using member⟩,
      by simpa [aromaticCanonicalBondOrder_comm] using order⟩
  · rintro ⟨⟨different, member⟩, order⟩
    exact ⟨⟨fun same => different same.symm, by simpa [semanticEdgeKey_comm] using member⟩,
      by simpa [aromaticCanonicalBondOrder_comm] using order⟩

/-- Order the two encoded endpoint atoms by the strict canonical source-atom order.  This is the
orientation used by `aromaticCanonicalOrdinaryDoubleBondPairs`. -/
def encodedOrderedPair {count : Nat} (first second : Fin count) : Fin count × Fin count :=
  if first < second then (first, second) else (second, first)

/-- The ordered pair is the original pair in one of the two orientations. -/
theorem encodedOrderedPair_eq_or {count : Nat} (first second : Fin count) :
    encodedOrderedPair first second = (first, second) ∨
      encodedOrderedPair first second = (second, first) := by
  unfold encodedOrderedPair
  by_cases ordering : first < second <;> simp [ordering]

/-- Two distinct encoded atoms have a strict canonical orientation. -/
theorem encodedOrderedPair_fst_lt_snd {count : Nat} {first second : Fin count}
    (different : first ≠ second) :
    (encodedOrderedPair first second).1 < (encodedOrderedPair first second).2 := by
  unfold encodedOrderedPair
  by_cases ordering : first < second
  · simp [ordering]
  · have reverse : second < first :=
      lt_of_le_of_ne (le_of_not_gt ordering) (Ne.symm different)
    simp [ordering, reverse]

/-! ## Encoding lemmas for orientation-free binary covalent source edges -/

/-- The exact source encoding of an orientation-free binary edge yields a participant list that is
a permutation of the two encoded endpoint labels. -/
theorem encodeInteraction_participants_perm
    (enumeration : V ≃ Fin (Fintype.card V))
    (edge : List V × SemanticInteractionKind) (first second : V)
    (support : edge.1.Perm [first, second]) :
    (FiniteAtomInteractionHypergraph.encodeInteraction enumeration edge).participants.Perm
      [(enumeration first).val, (enumeration second).val] := by
  rw [FiniteAtomInteractionHypergraph.encodeInteraction_participants]
  exact support.map _

/-- An encoded `covalent 2` interaction whose participants are exactly two distinct labels has
localized covalent record equal to the unordered source key of those labels, at order two. -/
theorem encodeInteraction_localizedCovalentRecord?
    (enumeration : V ≃ Fin (Fintype.card V))
    (edge : List V × SemanticInteractionKind) (first second : V)
    (support : edge.1.Perm [first, second])
    (kind_two : edge.2 = SemanticInteractionKind.covalent 2) :
    (FiniteAtomInteractionHypergraph.encodeInteraction enumeration edge).localizedCovalentRecord? =
      some (semanticEdgeKey (enumeration first).val (enumeration second).val, 2) := by
  rcases pair_permutation_cases edge.1 first second support with ordering | ordering
  · simp [SemanticInteraction.localizedCovalentRecord?, ordering, kind_two]
  · have keyEq :
        semanticEdgeKey (enumeration second).val (enumeration first).val =
          semanticEdgeKey (enumeration first).val (enumeration second).val :=
      semanticEdgeKey_comm _ _
    simp [SemanticInteraction.localizedCovalentRecord?, ordering, kind_two, keyEq]

/-- A binary interaction with exactly two participants and a `covalent` kind is not an aromatic
pair declaration. -/
theorem aromaticPairEdge?_eq_none_of_covalent
    (interaction : SemanticInteraction) (order : Nat)
    (length_two : interaction.participants.length = 2)
    (kind : interaction.kind = SemanticInteractionKind.covalent order) :
    SemanticMolecule.aromaticPairEdge? interaction = none := by
  obtain ⟨left, right, participants⟩ := List.length_eq_two.mp length_two
  unfold SemanticMolecule.aromaticPairEdge?
  simp [participants, kind]

/-- A non-aromatic interaction whose localized record is `(key, order)` contributes `key` to the
canonical normalized pair keys. -/
theorem aromaticNormalizedPairKey?_eq_some_of_record
    (interaction : SemanticInteraction) (key : Nat × Nat) (order : Nat)
    (notAromatic : SemanticMolecule.aromaticPairEdge? interaction = none)
    (record : interaction.localizedCovalentRecord? = some (key, order)) :
    SemanticMolecule.aromaticNormalizedPairKey? interaction = some key := by
  unfold SemanticMolecule.aromaticNormalizedPairKey?
  split
  · rename_i observed
    rw [notAromatic] at observed
    cases observed
  · simpa using congrArg (Option.map Prod.fst) record

/-! ## Actual source order-two edge data on a configured input -/

/-- Real source data for one ordinary double bond, on a genuinely configured input.

The source hyperedge indexed by `edgeIndex` is an actual covalent order-two interaction whose
participant list is a permutation of the two distinct endpoint labels.  The remaining fields are
explicit structural obligations about the exact certified encoding of that same source:

* `spatial` is the supplied exact coordinate configuration and `diagram` the supplied drawing
  channel.  The configured input keeps the exact encoded molecule and installs these channels;
* `no_aromatic_pair`: no encoded interaction declares the same unordered pair as aromatic, so the
  canonical bond order of the pair is the localized covalent order rather than the aromatic
  placeholder `1`;
* `localized_records_unique`: extracted localized covalent records have pairwise distinct keys,
  so exact key lookup recovers this edge's order.

Neither structural field mentions `E`/`Z`, anomeric configuration, CIP priority or a chemical
class. -/
structure SourceDoubleBondGeometryData (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) where
  /-- Index of the actual source hyperedge. -/
  edgeIndex : Fin source.interactions.length
  /-- First source endpoint label. -/
  first : V
  /-- Second source endpoint label. -/
  second : V
  /-- The two source endpoint labels are distinct. -/
  distinct : first ≠ second
  /-- Orientation-free exact binary support of the source hyperedge. -/
  support_perm : (source.interactions.get edgeIndex).1.Perm [first, second]
  /-- The actual source hyperedge is a covalent order-two interaction. -/
  kind_two : (source.interactions.get edgeIndex).2 = SemanticInteractionKind.covalent 2
  /-- Supplied exact spatial coordinates for the configured input. -/
  spatial : SpatialConfiguration
  /-- Supplied drawing channel for the configured input. -/
  diagram : Option DiagramConfiguration := none
  /-- Structural consistency: no encoded interaction declares the same unordered pair aromatic. -/
  no_aromatic_pair :
    semanticEdgeKey
        (OrganicStereoChemicalOccurrenceFidelity.encodedSourceAtomEquiv source enumeration first).val
        (OrganicStereoChemicalOccurrenceFidelity.encodedSourceAtomEquiv source enumeration second).val ∉
      (source.certifiedEncoding enumeration).input.molecule.aromaticPairEdges
  /-- Structural consistency: extracted localized covalent record keys are unique. -/
  localized_records_unique :
    (source.certifiedEncoding enumeration).input.molecule.LocalizedCovalentRecordsUnique

namespace SourceDoubleBondGeometryData

variable {source : FiniteAtomInteractionHypergraph V}
variable {enumeration : V ≃ Fin (Fintype.card V)}
variable (data : SourceDoubleBondGeometryData source enumeration)

/-- The configured input: precisely the exact encoded molecule, with the supplied spatial and
diagram channels. -/
abbrev input (_data : SourceDoubleBondGeometryData source enumeration) :
    AuthoritativeChemicalInput :=
  { molecule := (source.certifiedEncoding enumeration).input.molecule,
    spatial? := some _data.spatial,
    diagram? := _data.diagram }

/-- The configured input keeps the exact encoded molecule; every carrier and interaction proof
below is about this same molecule. -/
theorem input_molecule :
    data.input.molecule = (source.certifiedEncoding enumeration).input.molecule := rfl

/-- The configured input exposes the supplied coordinates. -/
theorem input_spatial? : data.input.spatial? = some data.spatial := rfl

/-- The configured input exposes the supplied diagram channel. -/
theorem input_diagram? : data.input.diagram? = data.diagram := rfl

/-- Channel preservation: the configured input's spatial point lookup is exactly the bind of its
own `spatial?` channel.  This is the general form, before specializing the required channel. -/
theorem spatialPointAt?_bind
    (atom : AuthoritativeChemicalInput.AromaticCanonicalAtom data.input) :
    data.input.aromaticCanonicalSpatialPointAt? atom =
      data.input.spatial?.bind (fun spatial => spatial.positions[atom.val]?) := rfl

/-- Exact spatial point lookup in the configured input is lookup in the supplied configuration
(the specialization of `spatialPointAt?_bind` to the required channel `some data.spatial`). -/
theorem spatialPointAt?_eq
    (atom : AuthoritativeChemicalInput.AromaticCanonicalAtom data.input) :
    data.input.aromaticCanonicalSpatialPointAt? atom = data.spatial.positions[atom.val]? := rfl

/-- The encoded semantic molecule used by all carrier proofs. -/
abbrev molecule : SemanticMolecule :=
  data.input.molecule

/-- The first encoded endpoint atom (the source enumeration index). -/
abbrev encodedFirst : AuthoritativeChemicalInput.AromaticCanonicalAtom data.input :=
  OrganicStereoChemicalOccurrenceFidelity.encodedSourceAtomEquiv source enumeration data.first

/-- The second encoded endpoint atom. -/
abbrev encodedSecond : AuthoritativeChemicalInput.AromaticCanonicalAtom data.input :=
  OrganicStereoChemicalOccurrenceFidelity.encodedSourceAtomEquiv source enumeration data.second

/-- The two encoded endpoint atoms ordered by the strict canonical atom order. -/
abbrev orderedPair :
    AuthoritativeChemicalInput.AromaticCanonicalAtom data.input ×
      AuthoritativeChemicalInput.AromaticCanonicalAtom data.input :=
  encodedOrderedPair data.encodedFirst data.encodedSecond

/-- The two encoded endpoint atoms are distinct. -/
theorem encodedFirst_ne_encodedSecond : data.encodedFirst ≠ data.encodedSecond :=
  OrganicStereoChemicalOccurrenceFidelity.encodedSourceAtomEquiv_ne source enumeration data.distinct

/-- The actual interaction at the transported encoded index is still the encoding of the same
original source hyperedge: this is the existing same-source occurrence transport, reused. -/
theorem sameSourceInteraction :
    data.molecule.interactions.get
        (OrganicStereoChemicalOccurrenceFidelity.encodedInteractionIndex
          source enumeration data.edgeIndex) =
      FiniteAtomInteractionHypergraph.encodeInteraction enumeration
        (source.interactions.get data.edgeIndex) :=
  OrganicStereoChemicalOccurrenceFidelity.certifiedEncoding_get_encoded
    source enumeration data.edgeIndex

/-- The exact encoded source interaction occurs in the encoded molecule. -/
theorem sameSourceInteraction_mem :
    FiniteAtomInteractionHypergraph.encodeInteraction enumeration
        (source.interactions.get data.edgeIndex) ∈ data.molecule.interactions := by
  rw [← data.sameSourceInteraction]
  exact List.get_mem _ _

/-- The transported interaction still has the two encoded source endpoints as its participants,
in the orientation of the original source encoding. -/
theorem sameSourceInteraction_participants :
    (data.molecule.interactions.get
        (OrganicStereoChemicalOccurrenceFidelity.encodedInteractionIndex
          source enumeration data.edgeIndex)).participants.Perm
      [data.encodedFirst.val, data.encodedSecond.val] := by
  rw [data.sameSourceInteraction,
    FiniteAtomInteractionHypergraph.encodeInteraction_participants]
  exact data.support_perm.map (fun atom => (enumeration atom).val)

/-- The transported interaction is still a covalent order-two interaction. -/
theorem sameSourceInteraction_kind :
    (data.molecule.interactions.get
        (OrganicStereoChemicalOccurrenceFidelity.encodedInteractionIndex
          source enumeration data.edgeIndex)).kind =
      SemanticInteractionKind.covalent 2 := by
  rw [data.sameSourceInteraction,
    FiniteAtomInteractionHypergraph.encodeInteraction_kind]
  exact data.kind_two

/-- The encoded same-source interaction contributes the expected localized covalent record. -/
theorem encodedInteraction_record :
    (FiniteAtomInteractionHypergraph.encodeInteraction enumeration
        (source.interactions.get data.edgeIndex)).localizedCovalentRecord? =
      some (semanticEdgeKey data.encodedFirst.val data.encodedSecond.val, 2) := by
  simpa using encodeInteraction_localizedCovalentRecord? enumeration
    (source.interactions.get data.edgeIndex) data.first data.second
    data.support_perm data.kind_two

/-- The encoded same-source interaction is not an aromatic pair declaration. -/
theorem encodedInteraction_not_aromaticPair :
    SemanticMolecule.aromaticPairEdge?
        (FiniteAtomInteractionHypergraph.encodeInteraction enumeration
          (source.interactions.get data.edgeIndex)) = none := by
  apply aromaticPairEdge?_eq_none_of_covalent _ 2 _ (by
    rw [FiniteAtomInteractionHypergraph.encodeInteraction_kind]
    exact data.kind_two)
  simpa using (encodeInteraction_participants_perm enumeration
    (source.interactions.get data.edgeIndex) data.first data.second data.support_perm).length_eq

/-- The localized covalent record of the encoded endpoints is present in the encoded molecule. -/
theorem key_mem_localizedCovalentRecords :
    (semanticEdgeKey data.encodedFirst.val data.encodedSecond.val, 2) ∈
      data.molecule.localizedCovalentRecords := by
  unfold SemanticMolecule.localizedCovalentRecords
  rw [List.mem_filterMap]
  exact ⟨_, data.sameSourceInteraction_mem, data.encodedInteraction_record⟩

/-- The encoded endpoint pair occurs in the source-canonical adjacency key list. -/
theorem key_mem_aromaticNormalizedPairKeys :
    semanticEdgeKey data.encodedFirst.val data.encodedSecond.val ∈
      data.molecule.aromaticNormalizedPairKeys := by
  unfold SemanticMolecule.aromaticNormalizedPairKeys
  rw [List.mem_filterMap]
  exact ⟨_, data.sameSourceInteraction_mem,
    aromaticNormalizedPairKey?_eq_some_of_record _ _ _
      data.encodedInteraction_not_aromaticPair data.encodedInteraction_record⟩

/-- The encoded endpoints are a source-canonical adjacent pair. -/
theorem aromaticCanonicalAdjacent :
    data.input.AromaticCanonicalAdjacent data.encodedFirst data.encodedSecond :=
  ⟨data.encodedFirst_ne_encodedSecond, data.key_mem_aromaticNormalizedPairKeys⟩

/-- The canonical bond order of the encoded endpoints is exactly two: the pair is not aromatic and
the unique localized covalent record carries order two. -/
theorem aromaticCanonicalBondOrder_two :
    data.molecule.aromaticCanonicalBondOrder
        data.encodedFirst.val data.encodedSecond.val = 2 := by
  have notAromatic : ¬ data.molecule.aromaticPairEdges.contains
      (semanticEdgeKey data.encodedFirst.val data.encodedSecond.val) :=
    fun present => data.no_aromatic_pair (List.contains_iff_mem.mp present)
  unfold SemanticMolecule.aromaticCanonicalBondOrder
  rw [if_neg notAromatic]
  have notSame : data.encodedFirst.val ≠ data.encodedSecond.val :=
    fun same => data.encodedFirst_ne_encodedSecond (Fin.ext same)
  unfold SemanticMolecule.localizedBondOrder
  rw [if_neg notSame]
  exact SemanticMolecule.localizedBondOrderAtKey_eq_of_mem_unique
    data.molecule.localizedCovalentRecords
    (semanticEdgeKey data.encodedFirst.val data.encodedSecond.val) 2
    (by simpa [SemanticMolecule.LocalizedCovalentRecordsUnique,
        SemanticMolecule.localizedCovalentKeys] using data.localized_records_unique)
    data.key_mem_localizedCovalentRecords

/-- The encoded source endpoints form an actual canonical ordinary double bond. -/
theorem aromaticCanonicalOrdinaryDoubleBond :
    data.input.AromaticCanonicalOrdinaryDoubleBond data.encodedFirst data.encodedSecond :=
  ⟨data.aromaticCanonicalAdjacent, data.aromaticCanonicalBondOrder_two⟩

/-- The same ordinary double bond in the opposite endpoint orientation. -/
theorem aromaticCanonicalOrdinaryDoubleBond_swapped :
    data.input.AromaticCanonicalOrdinaryDoubleBond data.encodedSecond data.encodedFirst :=
  (aromaticCanonicalOrdinaryDoubleBond_comm data.input data.encodedFirst
    data.encodedSecond).mp data.aromaticCanonicalOrdinaryDoubleBond

/-- The strict canonical orientation is an ordinary double bond. -/
theorem orderedPair_ordinary :
    data.input.AromaticCanonicalOrdinaryDoubleBond data.orderedPair.1 data.orderedPair.2 := by
  have pairDef :
      data.orderedPair = encodedOrderedPair data.encodedFirst data.encodedSecond := rfl
  rcases encodedOrderedPair_eq_or data.encodedFirst data.encodedSecond with ordering | ordering
  · rw [pairDef, ordering]
    simpa using data.aromaticCanonicalOrdinaryDoubleBond
  · rw [pairDef, ordering]
    simpa using data.aromaticCanonicalOrdinaryDoubleBond_swapped

/-- The canonical pair is strictly ordered. -/
theorem orderedPair_ordered : data.orderedPair.1 < data.orderedPair.2 :=
  encodedOrderedPair_fst_lt_snd data.encodedFirst_ne_encodedSecond

/-- The actual canonical ordinary-double-bond carrier constructed from the original source edge.
Its pair is the two encoded source endpoints in strict canonical order. -/
noncomputable def bond :
    AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBondCarrier data.input :=
  ⟨data.orderedPair, by
    change (data.orderedPair.1, data.orderedPair.2) ∈
      data.input.aromaticCanonicalOrdinaryDoubleBondPairs
    exact (AuthoritativeChemicalInput.mem_aromaticCanonicalOrdinaryDoubleBondPairs_iff
      data.input data.orderedPair.1 data.orderedPair.2).mpr
      ⟨data.orderedPair_ordered, data.orderedPair_ordinary⟩⟩

/-- The carrier's underlying pair is the ordered encoded endpoint pair. -/
theorem bond_pair : data.bond.1 = data.orderedPair := rfl

/-- The carrier endpoints are exactly the encoded source endpoints, in one of the two possible
orientations.  The orientation is derived from the canonical strict atom order, not assumed. -/
theorem bond_left_right :
    (data.bond.left = data.encodedFirst ∧ data.bond.right = data.encodedSecond) ∨
      (data.bond.left = data.encodedSecond ∧ data.bond.right = data.encodedFirst) := by
  have pairEq : data.bond.1 = data.orderedPair := rfl
  rcases encodedOrderedPair_eq_or data.encodedFirst data.encodedSecond with ordering | ordering
  · left
    constructor
    · simp [AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBondCarrier.left,
        pairEq, ordering]
    · simp [AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBondCarrier.right,
        pairEq, ordering]
  · right
    constructor
    · simp [AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBondCarrier.left,
        pairEq, ordering]
    · simp [AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBondCarrier.right,
        pairEq, ordering]

end SourceDoubleBondGeometryData

/-! ## Existing geometry hypotheses for the actual producer -/

/-- The caller's existing geometry hypotheses for the actual executable producer.  The two
dependency views and the carrier fuel are passed through verbatim; the two Booleans are the
Rule-5 enantiomorphic-status flags used by the producer.  Nothing here selects a desired `E`/`Z`
or chemical class. -/
structure SourceDoubleBondGeometryHypotheses
    {source : FiniteAtomInteractionHypergraph V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (data : SourceDoubleBondGeometryData source enumeration) where
  /-- Fuel for source occurrence analysis. -/
  carrierFuel : Nat
  /-- Dependency view at the first endpoint. -/
  leftView : data.input.AromaticCanonicalDependencyView
    (data.input.aromaticCanonicalRootOccurrence carrierFuel data.bond.left)
  /-- Dependency view at the second endpoint. -/
  rightView : data.input.AromaticCanonicalDependencyView
    (data.input.aromaticCanonicalRootOccurrence carrierFuel data.bond.right)
  /-- Rule-5 enantiomorphic status of the first endpoint. -/
  leftEnantiomorphic : Bool
  /-- Rule-5 enantiomorphic status of the second endpoint. -/
  rightEnantiomorphic : Bool

namespace SourceDoubleBondGeometryHypotheses

variable {source : FiniteAtomInteractionHypergraph V}
variable {enumeration : V ≃ Fin (Fintype.card V)}
variable {data : SourceDoubleBondGeometryData source enumeration}
variable (hypotheses : SourceDoubleBondGeometryHypotheses data)

/-- The actual producer applied to the carrier constructed from the original source edge. -/
noncomputable def producedAssignment? :
    Option data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
  data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
    hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
    hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic

end SourceDoubleBondGeometryHypotheses

/-! ## Producer soundness and emitted annotation from the actual produced result -/

namespace SourceDoubleBondGeometryData

variable {source : FiniteAtomInteractionHypergraph V}
variable {enumeration : V ≃ Fin (Fintype.card V)}
variable (data : SourceDoubleBondGeometryData source enumeration)
variable (hypotheses : SourceDoubleBondGeometryHypotheses data)

/-- If the actual producer returns an assignment, then it is the declarative assignment for the
carrier constructed from the original source edge.  In particular the produced bond is exactly
that carrier and belongs to the individual ordinary-double-bond route. -/
theorem spatialAssignment_sound
    {assignment : data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment}
    (computed : data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
      hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic = some assignment) :
    assignment.bond = data.bond ∧
      data.bond ∈ data.input.aromaticCanonicalIndividualDoubleBondCarriers ∧
        data.input.DeclarativeAromaticCanonicalOrdinaryDoubleBondSpatialAssignment
          hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
          hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic assignment := by
  have sound := data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?_sound
    hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
    hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic assignment computed
  unfold AuthoritativeChemicalInput.DeclarativeAromaticCanonicalOrdinaryDoubleBondSpatialAssignment
    at sound
  exact ⟨sound.1, sound.2.1, sound⟩

/-- The produced assignment's endpoints are exactly the encoded source endpoints, in one of the two
possible orientations.  This is derived from the actual produced record and the source data. -/
theorem assignment_left_right
    {assignment : data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment}
    (computed : data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
      hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic = some assignment) :
    (assignment.bond.left = data.encodedFirst ∧ assignment.bond.right = data.encodedSecond) ∨
      (assignment.bond.left = data.encodedSecond ∧ assignment.bond.right = data.encodedFirst) := by
  have bondEq := (data.spatialAssignment_sound hypotheses computed).1
  rw [bondEq]
  exact data.bond_left_right

/-- From a successful actual run, extract the produced geometry, the produced outcome and the exact
executable outcome equation.  This is the only place where the produced annotation is read off. -/
theorem assignment_geometry_outcome
    {assignment : data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment}
    (computed : data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
      hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic = some assignment) :
    ∃ geometry outcome,
      assignment.geometry = geometry ∧
        assignment.outcome = outcome ∧
          aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
            hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic geometry = some outcome := by
  have executable :=
    (data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?_eq_some_iff
      hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic assignment).mp computed
  obtain ⟨_, _, _, leftReference, rightReference, _, _, _, _, geometry, outcome,
    _, _, _, _, _, _, _, _, _, outcomeComputed, finalEq⟩ := executable
  have assignmentEq :
      ({ bond := data.bond, leftReference := leftReference, rightReference := rightReference,
         geometry := geometry, outcome := outcome } :
        data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) = assignment := finalEq
  refine ⟨geometry, outcome, ?_, ?_, outcomeComputed⟩
  · rw [← assignmentEq]
  · rw [← assignmentEq]

end SourceDoubleBondGeometryData

/-! ### Outcome computation from exact geometry and Rule-5 flags -/

/-- Closed `seqcis` outcome with agreeing flags. -/
theorem planarOutcome?_seqcis_of_eq (value : Bool) :
    aromaticCanonicalOrdinaryDoubleBondPlanarOutcome? value value
        OfficialRule3Geometry.seqcis =
      some (StereoOutcome.alkene DoubleBondStereo.Z) := by
  cases value <;> rfl

/-- Closed `seqtrans` outcome with agreeing flags. -/
theorem planarOutcome?_seqtrans_of_eq (value : Bool) :
    aromaticCanonicalOrdinaryDoubleBondPlanarOutcome? value value
        OfficialRule3Geometry.seqtrans =
      some (StereoOutcome.alkene DoubleBondStereo.E) := by
  cases value <;> rfl

/-- `seqcis` together with equal Rule-5 flags emits exactly `Z`. -/
theorem planarOutcome_alkene_Z_of_seqcis
    {leftEnantiomorphic rightEnantiomorphic : Bool} {outcome : StereoOutcome}
    (equal : leftEnantiomorphic = rightEnantiomorphic)
    (computed : aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
      leftEnantiomorphic rightEnantiomorphic OfficialRule3Geometry.seqcis = some outcome) :
    outcome = StereoOutcome.alkene DoubleBondStereo.Z := by
  rw [← equal] at computed
  rw [planarOutcome?_seqcis_of_eq leftEnantiomorphic] at computed
  exact (Option.some.inj computed).symm

/-- `seqtrans` together with equal Rule-5 flags emits exactly `E`. -/
theorem planarOutcome_alkene_E_of_seqtrans
    {leftEnantiomorphic rightEnantiomorphic : Bool} {outcome : StereoOutcome}
    (equal : leftEnantiomorphic = rightEnantiomorphic)
    (computed : aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
      leftEnantiomorphic rightEnantiomorphic OfficialRule3Geometry.seqtrans = some outcome) :
    outcome = StereoOutcome.alkene DoubleBondStereo.E := by
  rw [← equal] at computed
  rw [planarOutcome?_seqtrans_of_eq leftEnantiomorphic] at computed
  exact (Option.some.inj computed).symm

/-- `seqcis` together with distinct Rule-5 flags emits the enantiomorphic `seqCis` outcome, not a
plain `E`/`Z` annotation. -/
theorem planarOutcome_seqCis_of_seqcis
    {leftEnantiomorphic rightEnantiomorphic : Bool} {outcome : StereoOutcome}
    (different : leftEnantiomorphic ≠ rightEnantiomorphic)
    (computed : aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
      leftEnantiomorphic rightEnantiomorphic OfficialRule3Geometry.seqcis = some outcome) :
    outcome = StereoOutcome.enantiomorphicDoubleBond SequenceDoubleBondDescriptor.seqCis := by
  cases leftEnantiomorphic <;> cases rightEnantiomorphic <;>
    simp_all [aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?]

/-- `seqtrans` together with distinct Rule-5 flags emits the enantiomorphic `seqTrans` outcome, not
a plain `E`/`Z` annotation. -/
theorem planarOutcome_seqTrans_of_seqtrans
    {leftEnantiomorphic rightEnantiomorphic : Bool} {outcome : StereoOutcome}
    (different : leftEnantiomorphic ≠ rightEnantiomorphic)
    (computed : aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
      leftEnantiomorphic rightEnantiomorphic OfficialRule3Geometry.seqtrans = some outcome) :
    outcome = StereoOutcome.enantiomorphicDoubleBond SequenceDoubleBondDescriptor.seqTrans := by
  cases leftEnantiomorphic <;> cases rightEnantiomorphic <;>
    simp_all [aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?]

/-! ### Emitted annotation from the actual produced result -/

namespace SourceDoubleBondGeometryData

variable {source : FiniteAtomInteractionHypergraph V}
variable {enumeration : V ≃ Fin (Fintype.card V)}
variable (data : SourceDoubleBondGeometryData source enumeration)
variable (hypotheses : SourceDoubleBondGeometryHypotheses data)

/-- A successful actual run emits `Z` exactly when the produced geometry is `seqcis` and the two
Rule-5 endpoint flags agree. -/
theorem emittedDoubleBond_eq_some_Z_of_seqcis
    {assignment : data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment}
    (computed : data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
      hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic = some assignment)
    (geometry : assignment.geometry = OfficialRule3Geometry.seqcis)
    (equal : hypotheses.leftEnantiomorphic = hypotheses.rightEnantiomorphic) :
    assignment.emittedDoubleBondStereo? = some DoubleBondStereo.Z := by
  obtain ⟨producedGeometry, producedOutcome, geometryEq, outcomeEq, outcomeComputed⟩ :=
    data.assignment_geometry_outcome hypotheses computed
  have computedOutcome : aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic assignment.geometry =
        some assignment.outcome := by
    rw [geometryEq, outcomeEq]
    exact outcomeComputed
  rw [geometry] at computedOutcome
  have outcomeEq' := planarOutcome_alkene_Z_of_seqcis equal computedOutcome
  simp [AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment.emittedDoubleBondStereo?,
    outcomeEq']

/-- A successful actual run emits `E` exactly when the produced geometry is `seqtrans` and the two
Rule-5 endpoint flags agree. -/
theorem emittedDoubleBond_eq_some_E_of_seqtrans
    {assignment : data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment}
    (computed : data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
      hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic = some assignment)
    (geometry : assignment.geometry = OfficialRule3Geometry.seqtrans)
    (equal : hypotheses.leftEnantiomorphic = hypotheses.rightEnantiomorphic) :
    assignment.emittedDoubleBondStereo? = some DoubleBondStereo.E := by
  obtain ⟨producedGeometry, producedOutcome, geometryEq, outcomeEq, outcomeComputed⟩ :=
    data.assignment_geometry_outcome hypotheses computed
  have computedOutcome : aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic assignment.geometry =
        some assignment.outcome := by
    rw [geometryEq, outcomeEq]
    exact outcomeComputed
  rw [geometry] at computedOutcome
  have outcomeEq' := planarOutcome_alkene_E_of_seqtrans equal computedOutcome
  simp [AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment.emittedDoubleBondStereo?,
    outcomeEq']

/-- A successful actual run with `seqcis` geometry and distinct Rule-5 flags emits no plain `E`/`Z`
annotation: the produced outcome is `enantiomorphicDoubleBond seqCis`. -/
theorem emittedDoubleBond_eq_none_of_seqcis
    {assignment : data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment}
    (computed : data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
      hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic = some assignment)
    (geometry : assignment.geometry = OfficialRule3Geometry.seqcis)
    (different : hypotheses.leftEnantiomorphic ≠ hypotheses.rightEnantiomorphic) :
    assignment.emittedDoubleBondStereo? = none := by
  obtain ⟨producedGeometry, producedOutcome, geometryEq, outcomeEq, outcomeComputed⟩ :=
    data.assignment_geometry_outcome hypotheses computed
  have computedOutcome : aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic assignment.geometry =
        some assignment.outcome := by
    rw [geometryEq, outcomeEq]
    exact outcomeComputed
  rw [geometry] at computedOutcome
  have outcomeEq' := planarOutcome_seqCis_of_seqcis different computedOutcome
  simp [AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment.emittedDoubleBondStereo?,
    outcomeEq']

/-- A successful actual run with `seqtrans` geometry and distinct Rule-5 flags emits no plain
`E`/`Z` annotation: the produced outcome is `enantiomorphicDoubleBond seqTrans`. -/
theorem emittedDoubleBond_eq_none_of_seqtrans
    {assignment : data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment}
    (computed : data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
      hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic = some assignment)
    (geometry : assignment.geometry = OfficialRule3Geometry.seqtrans)
    (different : hypotheses.leftEnantiomorphic ≠ hypotheses.rightEnantiomorphic) :
    assignment.emittedDoubleBondStereo? = none := by
  obtain ⟨producedGeometry, producedOutcome, geometryEq, outcomeEq, outcomeComputed⟩ :=
    data.assignment_geometry_outcome hypotheses computed
  have computedOutcome : aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic assignment.geometry =
        some assignment.outcome := by
    rw [geometryEq, outcomeEq]
    exact outcomeComputed
  rw [geometry] at computedOutcome
  have outcomeEq' := planarOutcome_seqTrans_of_seqtrans different computedOutcome
  simp [AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment.emittedDoubleBondStereo?,
    outcomeEq']

/-! ### Non-circular construction of an actual successful producer run -/

/-- Constructive `seqcis` success.  From actual individual-route membership, the two endpoint
ranking-frame equations (a narrower explicit ranking premise), four exact coordinate lookups in
the supplied spatial configuration, exact coplanarity and a positive Rule-3 side product, the
actual producer returns an assignment on the constructed source carrier and the result emits `Z`.

No premise states producer success, assignment existence, the assigned geometry or a desired
annotation: the geometry is classified from the coordinates and the annotation from the geometry
and the (supplied) Rule-5 flags. -/
theorem producedAssignment_eq_some_of_seqcis
    (route : data.bond ∈ data.input.aromaticCanonicalIndividualDoubleBondCarriers)
    (leftFrame : data.input.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      hypotheses.carrierFuel)
    (rightFrame : data.input.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      hypotheses.carrierFuel)
    (leftReference rightReference : AuthoritativeChemicalInput.AromaticCanonicalAtom data.input)
    (leftPoint rightPoint leftReferencePoint rightReferencePoint : CartesianPoint3)
    (leftFrameComputed :
      data.input.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
        hypotheses.carrierFuel data.bond.left data.bond.right hypotheses.leftView
        (2 * (hypotheses.carrierFuel + 1)) = some leftFrame)
    (rightFrameComputed :
      data.input.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
        hypotheses.carrierFuel data.bond.right data.bond.left hypotheses.rightView
        (2 * (hypotheses.carrierFuel + 1)) = some rightFrame)
    (leftReferenceComputed :
      data.input.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? leftFrame =
        some leftReference)
    (rightReferenceComputed :
      data.input.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? rightFrame =
        some rightReference)
    (leftPointComputed : data.spatial.positions[data.bond.left.val]? = some leftPoint)
    (rightPointComputed : data.spatial.positions[data.bond.right.val]? = some rightPoint)
    (leftReferencePointComputed :
      data.spatial.positions[leftReference.val]? = some leftReferencePoint)
    (rightReferencePointComputed :
      data.spatial.positions[rightReference.val]? = some rightReferencePoint)
    (coplanar : CartesianPoint3.rule3Coplanarity leftPoint rightPoint
      leftReferencePoint rightReferencePoint = 0)
    (positive : 0 < CartesianPoint3.rule3SideProduct leftPoint rightPoint
      leftReferencePoint rightReferencePoint)
    (equal : hypotheses.leftEnantiomorphic = hypotheses.rightEnantiomorphic) :
    ∃ assignment : data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment,
      data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
        hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
        hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic = some assignment ∧
      assignment.bond = data.bond ∧
      assignment.geometry = OfficialRule3Geometry.seqcis ∧
      assignment.emittedDoubleBondStereo? = some DoubleBondStereo.Z := by
  let assignment : data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
    { bond := data.bond
      leftReference := leftReference
      rightReference := rightReference
      geometry := OfficialRule3Geometry.seqcis
      outcome := StereoOutcome.alkene DoubleBondStereo.Z }
  have leftPointInput :
      data.input.aromaticCanonicalSpatialPointAt? data.bond.left = some leftPoint := by
    rw [data.spatialPointAt?_eq]
    exact leftPointComputed
  have rightPointInput :
      data.input.aromaticCanonicalSpatialPointAt? data.bond.right = some rightPoint := by
    rw [data.spatialPointAt?_eq]
    exact rightPointComputed
  have leftReferencePointInput :
      data.input.aromaticCanonicalSpatialPointAt? leftReference = some leftReferencePoint := by
    rw [data.spatialPointAt?_eq]
    exact leftReferencePointComputed
  have rightReferencePointInput :
      data.input.aromaticCanonicalSpatialPointAt? rightReference = some rightReferencePoint := by
    rw [data.spatialPointAt?_eq]
    exact rightReferencePointComputed
  have geometryComputed : rule3GeometryOfSpatialReferences?
      leftPoint rightPoint leftReferencePoint rightReferencePoint =
        some OfficialRule3Geometry.seqcis :=
    (rule3GeometryOfSpatialReferences?_eq_some_iff _ _ _ _ _).mpr ⟨coplanar, positive⟩
  have outcomeComputed : aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic
        OfficialRule3Geometry.seqcis =
      some (StereoOutcome.alkene DoubleBondStereo.Z) := by
    rw [equal]
    exact planarOutcome?_seqcis_of_eq _
  have judgment :
      data.input.AromaticCanonicalOrdinaryDoubleBondSpatialExecutableJudgment
        hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
        hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic assignment := by
    refine ⟨route, leftFrame, rightFrame, leftReference, rightReference,
      leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
      OfficialRule3Geometry.seqcis, StereoOutcome.alkene DoubleBondStereo.Z,
      leftFrameComputed, rightFrameComputed, leftReferenceComputed, rightReferenceComputed,
      leftPointInput, rightPointInput, leftReferencePointInput, rightReferencePointInput,
      geometryComputed, outcomeComputed, ?_⟩
    rfl
  refine ⟨assignment, ?_, rfl, rfl, rfl⟩
  exact (data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?_eq_some_iff
    hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
    hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic assignment).mpr judgment

/-- Constructive `seqtrans` success.  Same data as `producedAssignment_eq_some_of_seqcis` but with
a negative Rule-3 side product; the actual producer returns an assignment on the constructed
source carrier and the result emits `E`. -/
theorem producedAssignment_eq_some_of_seqtrans
    (route : data.bond ∈ data.input.aromaticCanonicalIndividualDoubleBondCarriers)
    (leftFrame : data.input.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      hypotheses.carrierFuel)
    (rightFrame : data.input.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      hypotheses.carrierFuel)
    (leftReference rightReference : AuthoritativeChemicalInput.AromaticCanonicalAtom data.input)
    (leftPoint rightPoint leftReferencePoint rightReferencePoint : CartesianPoint3)
    (leftFrameComputed :
      data.input.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
        hypotheses.carrierFuel data.bond.left data.bond.right hypotheses.leftView
        (2 * (hypotheses.carrierFuel + 1)) = some leftFrame)
    (rightFrameComputed :
      data.input.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
        hypotheses.carrierFuel data.bond.right data.bond.left hypotheses.rightView
        (2 * (hypotheses.carrierFuel + 1)) = some rightFrame)
    (leftReferenceComputed :
      data.input.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? leftFrame =
        some leftReference)
    (rightReferenceComputed :
      data.input.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? rightFrame =
        some rightReference)
    (leftPointComputed : data.spatial.positions[data.bond.left.val]? = some leftPoint)
    (rightPointComputed : data.spatial.positions[data.bond.right.val]? = some rightPoint)
    (leftReferencePointComputed :
      data.spatial.positions[leftReference.val]? = some leftReferencePoint)
    (rightReferencePointComputed :
      data.spatial.positions[rightReference.val]? = some rightReferencePoint)
    (coplanar : CartesianPoint3.rule3Coplanarity leftPoint rightPoint
      leftReferencePoint rightReferencePoint = 0)
    (negative : CartesianPoint3.rule3SideProduct leftPoint rightPoint
      leftReferencePoint rightReferencePoint < 0)
    (equal : hypotheses.leftEnantiomorphic = hypotheses.rightEnantiomorphic) :
    ∃ assignment : data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment,
      data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
        hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
        hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic = some assignment ∧
      assignment.bond = data.bond ∧
      assignment.geometry = OfficialRule3Geometry.seqtrans ∧
      assignment.emittedDoubleBondStereo? = some DoubleBondStereo.E := by
  let assignment : data.input.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
    { bond := data.bond
      leftReference := leftReference
      rightReference := rightReference
      geometry := OfficialRule3Geometry.seqtrans
      outcome := StereoOutcome.alkene DoubleBondStereo.E }
  have leftPointInput :
      data.input.aromaticCanonicalSpatialPointAt? data.bond.left = some leftPoint := by
    rw [data.spatialPointAt?_eq]
    exact leftPointComputed
  have rightPointInput :
      data.input.aromaticCanonicalSpatialPointAt? data.bond.right = some rightPoint := by
    rw [data.spatialPointAt?_eq]
    exact rightPointComputed
  have leftReferencePointInput :
      data.input.aromaticCanonicalSpatialPointAt? leftReference = some leftReferencePoint := by
    rw [data.spatialPointAt?_eq]
    exact leftReferencePointComputed
  have rightReferencePointInput :
      data.input.aromaticCanonicalSpatialPointAt? rightReference = some rightReferencePoint := by
    rw [data.spatialPointAt?_eq]
    exact rightReferencePointComputed
  have geometryComputed : rule3GeometryOfSpatialReferences?
      leftPoint rightPoint leftReferencePoint rightReferencePoint =
        some OfficialRule3Geometry.seqtrans :=
    (rule3GeometryOfSpatialReferences?_eq_some_iff _ _ _ _ _).mpr ⟨coplanar, negative⟩
  have outcomeComputed : aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
      hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic
        OfficialRule3Geometry.seqtrans =
      some (StereoOutcome.alkene DoubleBondStereo.E) := by
    rw [equal]
    exact planarOutcome?_seqtrans_of_eq _
  have judgment :
      data.input.AromaticCanonicalOrdinaryDoubleBondSpatialExecutableJudgment
        hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
        hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic assignment := by
    refine ⟨route, leftFrame, rightFrame, leftReference, rightReference,
      leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
      OfficialRule3Geometry.seqtrans, StereoOutcome.alkene DoubleBondStereo.E,
      leftFrameComputed, rightFrameComputed, leftReferenceComputed, rightReferenceComputed,
      leftPointInput, rightPointInput, leftReferencePointInput, rightReferencePointInput,
      geometryComputed, outcomeComputed, ?_⟩
    rfl
  refine ⟨assignment, ?_, rfl, rfl, rfl⟩
  exact (data.input.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?_eq_some_iff
    hypotheses.carrierFuel data.bond hypotheses.leftView hypotheses.rightView
    hypotheses.leftEnantiomorphic hypotheses.rightEnantiomorphic assignment).mpr judgment

end SourceDoubleBondGeometryData

/-! ## Scope: bond order does not determine the emitted annotation -/

/-- The planar outcome function emits `Z` for together (`seqcis`) geometry and `E` for opposite
(`seqtrans`) geometry when the Rule-5 endpoint flags agree; these are different `StereoOutcome`
values.  The covalent bond order does not appear in this function, so order two alone cannot
select between them.  This is the geometry-side counterpart of
`LipidAnnotationIngress.SphingoidDoubleBondBinding.typedChemical_does_not_determine_EZ`. -/
theorem emittedDoubleBond_not_determined_by_bondOrder :
    aromaticCanonicalOrdinaryDoubleBondPlanarOutcome? false false
        OfficialRule3Geometry.seqcis =
      some (StereoOutcome.alkene DoubleBondStereo.Z) ∧
    aromaticCanonicalOrdinaryDoubleBondPlanarOutcome? false false
        OfficialRule3Geometry.seqtrans =
      some (StereoOutcome.alkene DoubleBondStereo.E) ∧
    (StereoOutcome.alkene DoubleBondStereo.Z) ≠ StereoOutcome.alkene DoubleBondStereo.E := by
  refine ⟨rfl, rfl, ?_⟩
  simp

/-- The two geometry-determined outcomes do emit different plain `E`/`Z` annotations. -/
theorem emittedDoubleBond_geometry_dichotomy :
    StereoOutcome.doubleBondStereo? (StereoOutcome.alkene DoubleBondStereo.Z) =
        some DoubleBondStereo.Z ∧
      StereoOutcome.doubleBondStereo? (StereoOutcome.alkene DoubleBondStereo.E) =
        some DoubleBondStereo.E :=
  ⟨rfl, rfl⟩

end OrganicStereoSourceDoubleBondGeometryFidelity

end TetraStereo.OneCenter

/-! ## Kernel-authority guards for the decisive results -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.encodeInteraction_localizedCovalentRecord?
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.aromaticCanonicalBondOrder_comm
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.sameSourceInteraction
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.input_molecule
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.spatialPointAt?_eq
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.key_mem_localizedCovalentRecords
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.key_mem_aromaticNormalizedPairKeys
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.aromaticCanonicalBondOrder_two
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.aromaticCanonicalOrdinaryDoubleBond
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.bond
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.bond_left_right
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.spatialAssignment_sound
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.assignment_left_right
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.assignment_geometry_outcome
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.emittedDoubleBond_eq_some_Z_of_seqcis
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.emittedDoubleBond_eq_some_E_of_seqtrans
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.emittedDoubleBond_eq_none_of_seqcis
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.emittedDoubleBond_eq_none_of_seqtrans
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.producedAssignment_eq_some_of_seqcis
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.SourceDoubleBondGeometryData.producedAssignment_eq_some_of_seqtrans
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSourceDoubleBondGeometryFidelity.emittedDoubleBond_not_determined_by_bondOrder
