import TetraStereo.OneCenter.OrganicStereoElectronicSites
import TetraStereo.OneCenter.OrganicStereoFiniteEncoding

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace OrganicStereoIndependentElectronicEncoding

open OrganicStereoElectronicSites
open OrganicStereoElectronicSites.ReferenceGeometryEvidence

/-!
# Independent electronic site encoding over arbitrary finite atom labels

`OrganicStereoElectronicSites` starts from a `source : AuthoritativeChemicalInput` and a count
function already indexed by `source.AromaticCanonicalAtom`.  This module supplies the missing
bridge: an *independent* electronic site inventory over an arbitrary finite atom-label type `V`,
one explicit enumeration `e : V ≃ Fin (card V)`, and a proof that the existing source-indexed APIs
receive exactly that inventory through `graph.encodeAuthoritative e`, using the same enumeration as
`OrganicStereoFiniteEncoding`.

The independent data are:

* `IndependentSiteCounts V`: an arbitrary per-label `SuppliedSiteCounts`, reusing the existing count
  vocabulary (implicit protia, lone pairs, vacancies, unpaired-electron positions, and the two CIP
  reference kinds);
* `IndependentSiteIdentity counts`: `owner : V`, `kind : SiteKind`, and a slot
  `Fin ((counts owner).count kind)`, so multiple sites of one kind at one atom are distinct
  identities;
* `IndependentElectronicSiteSource graph`: the counts together with the single source-semantic tie
  `(counts owner).unpairedElectronPositions = (graph.atomData owner).unpairedElectrons`.  No other
  count is constrained and no count is inferred from nuclear positions.

The encoding uses the *same* enumeration `e` as `FiniteAtomInteractionHypergraph.encode`.  The
resulting source atom index is `Fin (card V)` in encoding order, so the bridge enumerates the
independent counts through the inverse atom equivalence and proves the `unpaired_tied` field of the
existing `ElectronicSiteSource` from the actual encoded finite-graph atom lookup.  The identity
equivalence then transports complete and optional per-site geometry, preserving owner, kind, slot,
counts, optional-evidence knownness, and every real coordinate exactly.

Boundaries honoured here:

* the independent label type `V` is arbitrary and finite; it is never replaced by an
  already-encoded source-indexed inventory;
* the only bridge from an unbounded external index space is the explicit bijection `e`; no bounded
  assignment of arbitrary natural numbers to owners is asserted or constructed;
* geometry evidence is optional per site, and absence of a point or direction is kept distinct from
  an explicitly supplied zero;
* whole-state geometry is freely configurable and is never inferred from `graph.atomData` or any
  nuclear position;
* all conclusions about finite data are stated as exact indexed equalities; no claim is made about
  the order of any list representation.
-/

/-! ## A reusable equality-induced equivalence on `Fin` -/

/-- The equivalence of `Fin` types induced by an equality of their bounds.  This is the concrete
form used for every slot and atom reindexing below; it lets round trips be proved by the generic
`Equiv` laws rather than by reasoning about dependent `Fin` proofs. -/
def finCastEquiv {n m : ℕ} (h : n = m) : Fin n ≃ Fin m where
  toFun index := Fin.cast h index
  invFun index := Fin.cast h.symm index
  left_inv index := Fin.ext (by simp)
  right_inv index := Fin.ext (by simp)

@[simp] theorem finCastEquiv_apply {n m : ℕ} (h : n = m) (index : Fin n) :
    finCastEquiv h index = Fin.cast h index := rfl

@[simp] theorem finCastEquiv_symm_apply {n m : ℕ} (h : n = m) (index : Fin m) :
    (finCastEquiv h).symm index = Fin.cast h.symm index := rfl

@[simp] theorem finCastEquiv_apply_val {n m : ℕ} (h : n = m) (index : Fin n) :
    ((finCastEquiv h index).val) = index.val := rfl

/-! ## Optional reference geometry

The repository's existing `ReferenceGeometryEvidence` is reused directly.  It already separates
`unspecified`, `pointOnly`, `directionOnly`, and `pointAndDirection`, so absence of a point or
direction is distinct from an explicitly supplied zero coordinate, and `toComplete?` yields a
`ReferenceGeometry` only when both components were supplied.  This module adds only the knownness
predicates used to state preservation, over that existing type; it never pattern-matches on the
evidence constructors, so the direction-only case closes by the same generic transport. -/

namespace EvidenceFacts

/-- Point evidence is present. -/
def pointKnown (evidence : ReferenceGeometryEvidence) : Prop :=
  evidence.point?.isSome = true

/-- Direction evidence is present. -/
def directionKnown (evidence : ReferenceGeometryEvidence) : Prop :=
  evidence.direction?.isSome = true

/-- Both point and direction evidence are present, so complete reference geometry exists. -/
def IsComplete (evidence : ReferenceGeometryEvidence) : Prop :=
  evidence.toComplete?.isSome = true

/-- An explicit zero point, used to distinguish absence from an explicit zero coordinate. -/
def originPoint : RealPoint3 := ⟨0, 0, 0⟩

/-- An explicit zero direction, used to distinguish absence from an explicit zero direction. -/
def zeroDirection : RealDirection3 := ⟨0, 0, 0⟩

/-- Complete evidence is recognized as complete. -/
@[simp] theorem toEvidence_isComplete (geometry : ReferenceGeometry) :
    EvidenceFacts.IsComplete geometry.toEvidence := by
  cases geometry with
  | mk point direction => rfl

/-- The empty optional evidence is not complete. -/
theorem unspecified_not_isComplete :
    ¬ EvidenceFacts.IsComplete (unspecified : ReferenceGeometryEvidence) := by
  simp [IsComplete]

/-- Point-only evidence is not complete. -/
theorem pointOnly_not_isComplete (point : RealPoint3) :
    ¬ EvidenceFacts.IsComplete (pointOnly point) := by
  simp [IsComplete]

/-- Direction-only evidence carries no point. -/
@[simp] theorem directionOnly_not_pointKnown (direction : RealDirection3) :
    ¬ EvidenceFacts.pointKnown (directionOnly direction) := by
  simp [pointKnown]

/-- Direction-only evidence carries exactly the supplied direction. -/
@[simp] theorem directionOnly_directionKnown (direction : RealDirection3) :
    EvidenceFacts.directionKnown (directionOnly direction) :=
  rfl

/-- Direction-only evidence is not complete: no complete reference geometry is fabricated from a
supplied direction alone. -/
theorem directionOnly_not_isComplete (direction : RealDirection3) :
    ¬ EvidenceFacts.IsComplete (directionOnly direction) := by
  simp [IsComplete]

/-- Absence of point evidence in the direction-only state is distinct from an explicitly supplied
zero point carrying the same direction. -/
theorem directionOnly_ne_pointAndDirection_origin (direction : RealDirection3) :
    directionOnly direction ≠ pointAndDirection originPoint direction := by
  intro equal
  have pointEq := congrArg point? equal
  simp [point?, originPoint] at pointEq

/-- Absence of direction evidence is distinct from an explicitly supplied zero direction. -/
theorem unspecified_ne_directionOnly_zeroDirection :
    unspecified ≠ directionOnly zeroDirection := by
  intro equal
  have directionEq := congrArg direction? equal
  simp [direction?, zeroDirection] at directionEq

/-- Absence of point evidence is distinct from an explicitly supplied zero point. -/
theorem unspecified_ne_pointOnly_origin : unspecified ≠ pointOnly originPoint := by
  intro equal
  have pointEq := congrArg point? equal
  simp [point?, originPoint] at pointEq

/-- Absence of direction evidence is distinct from an explicitly supplied zero direction. -/
theorem pointOnly_ne_pointAndDirection_zeroDirection (point : RealPoint3) :
    pointOnly point ≠ pointAndDirection point zeroDirection := by
  intro equal
  have directionEq := congrArg direction? equal
  simp [direction?, zeroDirection] at directionEq

/-- At the `point?` projection, absence and an explicit zero point are different values. -/
theorem unspecified_point?_ne_pointOnly_origin_point? :
    (unspecified : ReferenceGeometryEvidence).point? ≠ (pointOnly originPoint).point? := by
  simp [point?, originPoint]

/-- At the `direction?` projection, absence and an explicit zero direction are different values. -/
theorem pointOnly_direction?_ne_pointAndDirection_zeroDirection_direction?
    (point : RealPoint3) :
    (pointOnly point).direction? ≠ (pointAndDirection point zeroDirection).direction? := by
  simp [direction?, zeroDirection]

end EvidenceFacts

namespace GeometryFacts

/-- Complete geometry is recovered exactly from its evidence presentation. -/
@[simp] theorem toEvidence_toComplete? (geometry : ReferenceGeometry) :
    geometry.toEvidence.toComplete? = some geometry := by
  cases geometry with
  | mk point direction => rfl

end GeometryFacts

/-! ## Independently supplied site counts at arbitrary labels -/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Independently supplied site counts over an arbitrary finite label type.  Every field of
`SuppliedSiteCounts` is retained exactly as supplied; no count is derived from geometry. -/
structure IndependentSiteCounts (V : Type*) where
  /-- The supplied count record at each atom label. -/
  counts : V → SuppliedSiteCounts

namespace IndependentSiteCounts

/-- The supplied multiplicity of one site kind at one label. -/
def countAt (siteCounts : IndependentSiteCounts V) (owner : V) (kind : SiteKind) : ℕ :=
  (siteCounts.counts owner).count kind

/-- The total supplied multiplicity over all labels. -/
def total (siteCounts : IndependentSiteCounts V) : ℕ :=
  (Finset.univ : Finset V).sum fun owner => (siteCounts.counts owner).total

end IndependentSiteCounts

/-! ## Independent site identities -/

/-- An individual electronic or CIP-reference site identity over the independent label type.  The
owner is a label `V` rather than an already-encoded source index, and the slot is a `Fin` index
into the supplied multiplicity, so several sites of one kind at one owner are distinct. -/
structure IndependentSiteIdentity {V : Type*} [DecidableEq V] [Fintype V]
    (siteCounts : IndependentSiteCounts V) where
  owner : V
  kind : SiteKind
  slot : Fin ((siteCounts.counts owner).count kind)

/-- Site identities are exactly the nested sigma of owner, kind and slot. -/
def independentSiteIdentityEquivSigma (siteCounts : IndependentSiteCounts V) :
    IndependentSiteIdentity siteCounts ≃
      (Σ owner : V, Σ kind : SiteKind, Fin ((siteCounts.counts owner).count kind)) where
  toFun identity := ⟨identity.owner, identity.kind, identity.slot⟩
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv identity := by
    cases identity
    rfl
  right_inv data := by
    rcases data with ⟨owner, kind, slot⟩
    rfl

noncomputable instance independentSiteIdentityDecidableEq
    (siteCounts : IndependentSiteCounts V) :
    DecidableEq (IndependentSiteIdentity siteCounts) :=
  Equiv.decidableEq (independentSiteIdentityEquivSigma siteCounts)

noncomputable instance independentSiteIdentityFintype
    (siteCounts : IndependentSiteCounts V) :
    Fintype (IndependentSiteIdentity siteCounts) :=
  Fintype.ofEquiv
    (Σ owner : V, Σ kind : SiteKind, Fin ((siteCounts.counts owner).count kind))
    (independentSiteIdentityEquivSigma siteCounts).symm

/-- The number of identities at one owner and kind is exactly the supplied count.  The label type
is bound explicitly so no unused instance argument is included. -/
@[simp] theorem slot_count_card {V : Type*} (siteCounts : IndependentSiteCounts V)
    (owner : V) (kind : SiteKind) :
    Fintype.card (Fin ((siteCounts.counts owner).count kind)) =
      (siteCounts.counts owner).count kind :=
  Fintype.card_fin _

/-- The total number of identities is the sum of the supplied multiplicities. -/
theorem independentSiteIdentity_card_eq_sum (siteCounts : IndependentSiteCounts V) :
    Fintype.card (IndependentSiteIdentity siteCounts) =
      (Finset.univ : Finset V).sum fun owner => (siteCounts.counts owner).total := by
  rw [Fintype.card_congr (independentSiteIdentityEquivSigma siteCounts), Fintype.card_sigma]
  refine Finset.sum_congr rfl ?_
  intro owner _
  rw [Fintype.card_sigma]
  simp [SuppliedSiteCounts.total]

/-- Two slots of one kind at one owner are equal exactly when their values are equal. -/
theorem independentSiteIdentity_ext {siteCounts : IndependentSiteCounts V}
    {owner : V} {kind : SiteKind}
    {slot₁ slot₂ : Fin ((siteCounts.counts owner).count kind)}
    (valueEq : slot₁.val = slot₂.val) :
    (⟨owner, kind, slot₁⟩ : IndependentSiteIdentity siteCounts) =
      ⟨owner, kind, slot₂⟩ := by
  rw [Fin.ext valueEq]

/-- Distinct slots are distinct site identities: multiplicity is never collapsed. -/
theorem independentSiteIdentity_slots_distinct
    (siteCounts : IndependentSiteCounts V) (owner : V) (kind : SiteKind)
    {slot₁ slot₂ : Fin ((siteCounts.counts owner).count kind)} (different : slot₁ ≠ slot₂) :
    (⟨owner, kind, slot₁⟩ : IndependentSiteIdentity siteCounts) ≠
      ⟨owner, kind, slot₂⟩ := by
  intro equal
  have valueEq : slot₁.val = slot₂.val :=
    congrArg (fun identity : IndependentSiteIdentity siteCounts => identity.slot.val) equal
  exact different (Fin.ext valueEq)

/-! ## Independent source with the single source-semantic tie -/

/-- An independent electronic site source over a finite atom-labelled interaction graph.  Only the
declared unpaired-electron count is tied to the graph's semantic atom data; every other supplied
count is arbitrary and no geometry is read. -/
structure IndependentElectronicSiteSource
    (graph : FiniteAtomInteractionHypergraph V) where
  /-- The independently supplied per-label counts. -/
  siteCounts : IndependentSiteCounts V
  /-- The only declared tie: the supplied unpaired-electron positions equal the graph atom data's
  unpaired-electron count, exactly. -/
  unpaired_tied : ∀ owner : V,
    (siteCounts.counts owner).unpairedElectronPositions =
      (graph.atomData owner).unpairedElectrons

namespace IndependentElectronicSiteSource

/-- Build a source from arbitrary per-label endpoint electronic inventories, reusing the existing
inventory type and its projection.  No two-position equation is imposed, and all fields other than
the unpaired count remain exactly as supplied. -/
def ofEndpointInventories (graph : FiniteAtomInteractionHypergraph V)
    (inventories : V →
      AuthoritativeChemicalInput.AromaticCanonicalRule3EndpointElectronicInventory)
    (unpaired_tied : ∀ owner,
      (inventories owner).unpairedElectronPositions =
        (graph.atomData owner).unpairedElectrons) :
    IndependentElectronicSiteSource graph where
  siteCounts :=
    ⟨fun owner => SuppliedSiteCounts.ofEndpointInventory (inventories owner)⟩
  unpaired_tied owner := unpaired_tied owner

/-- The declared unpaired count of the independent source is exactly the graph atom data. -/
theorem unpaired_eq_atomData {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph) (owner : V) :
    (siteSource.siteCounts.counts owner).unpairedElectronPositions =
      (graph.atomData owner).unpairedElectrons :=
  siteSource.unpaired_tied owner

end IndependentElectronicSiteSource

/-! ## The encoding enumeration and the induced atom equivalence -/

/-- The atom equivalence induced by the encoding enumeration.  It is exactly the chosen `e`
followed by the size identification between `Fin (card V)` and the encoded atom index; no second
enumeration is chosen anywhere in this module. -/
def encodedAtomEquiv (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) :
    V ≃ (graph.encodeAuthoritative e).AromaticCanonicalAtom :=
  e.trans (finCastEquiv
    (FiniteAtomInteractionHypergraph.encode_atomCount graph e).symm)

@[simp] theorem encodedAtomEquiv_apply (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (atom : V) :
    encodedAtomEquiv graph e atom =
      Fin.cast (FiniteAtomInteractionHypergraph.encode_atomCount graph e).symm (e atom) :=
  rfl

/-- The encoded atom index has the same numeral as the independent enumeration index. -/
@[simp] theorem encodedAtomEquiv_apply_val (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (atom : V) :
    ((encodedAtomEquiv graph e atom).val) = (e atom).val :=
  rfl

/-! ## The actual finite-graph source atom lookup -/

/-- The encoded molecule's atoms are the source atom data in enumeration order, so the source
semantic atom at the image of a label is exactly that label's `atomData`.  This is the concrete
lookup fact used below to discharge the unpaired tie; it is proved from
`FiniteAtomInteractionHypergraph.encode_atomAt`, not assumed. -/
theorem sourceSemanticAtom_encoded (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (atom : V) :
    sourceSemanticAtom (graph.encodeAuthoritative e) (encodedAtomEquiv graph e atom) =
      graph.atomData atom := by
  unfold sourceSemanticAtom
  have lookup : listGet? (graph.encode e).atoms
      (encodedAtomEquiv graph e atom).val = some (graph.atomData atom) := by
    have base := FiniteAtomInteractionHypergraph.encode_atomAt graph e (e atom)
    rw [← encodedAtomEquiv_apply_val] at base
    rw [Equiv.symm_apply_apply] at base
    exact base
  have getEq : listGet? (graph.encode e).atoms
      (encodedAtomEquiv graph e atom).val =
      some ((graph.encode e).atoms.get
        ⟨(encodedAtomEquiv graph e atom).val,
          (encodedAtomEquiv graph e atom).isLt⟩) := by
    simpa using listGet?_eq_some_get
      (graph.encode e).atoms
      ⟨(encodedAtomEquiv graph e atom).val, (encodedAtomEquiv graph e atom).isLt⟩
  rw [lookup] at getEq
  exact (Option.some_inj.mp getEq).symm

/-- At every encoded source owner, the source semantic atom is the graph atom data at exactly the
label whose enumeration image is that owner. -/
theorem sourceSemanticAtom_encoded_owner (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V))
    (owner : (graph.encodeAuthoritative e).AromaticCanonicalAtom) :
    sourceSemanticAtom (graph.encodeAuthoritative e) owner =
      graph.atomData ((encodedAtomEquiv graph e).symm owner) := by
  conv_lhs => rw [← Equiv.apply_symm_apply (encodedAtomEquiv graph e) owner]
  exact sourceSemanticAtom_encoded graph e ((encodedAtomEquiv graph e).symm owner)

/-! ## Source-indexed counts obtained by the inverse identity equivalence -/

/-- The source-indexed counts obtained from independent counts through the inverse of the encoding
atom equivalence.  This is a definitional reindexing only: no count is changed. -/
def encodedSiteCounts (siteCounts : IndependentSiteCounts V)
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V)) :
    IndependentSiteCounts (graph.encodeAuthoritative e).AromaticCanonicalAtom where
  counts := fun owner => siteCounts.counts ((encodedAtomEquiv graph e).symm owner)

/-- At the image of every independent label, the source-indexed count record is exactly the
independent record at that label.  All six counts are preserved at once. -/
@[simp] theorem encodedSiteCounts_apply (siteCounts : IndependentSiteCounts V)
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (atom : V) :
    (encodedSiteCounts siteCounts graph e).counts (encodedAtomEquiv graph e atom) =
      siteCounts.counts atom := by
  show siteCounts.counts
      ((encodedAtomEquiv graph e).symm (encodedAtomEquiv graph e atom)) =
    siteCounts.counts atom
  rw [Equiv.symm_apply_apply]

/-- Source-indexed counts at one kind and owner. -/
@[simp] theorem encodedSiteCounts_countAt (siteCounts : IndependentSiteCounts V)
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (atom : V) (kind : SiteKind) :
    ((encodedSiteCounts siteCounts graph e).counts
        (encodedAtomEquiv graph e atom)).count kind =
      (siteCounts.counts atom).count kind := by
  rw [encodedSiteCounts_apply]

/-- The unpaired tie of the existing `ElectronicSiteSource` is discharged by the actual encoded
finite-graph atom lookup.  The left-hand side is the independently supplied unpaired count; the
right-hand side is the semantic atom stored by `graph.encodeAuthoritative e` at that owner. -/
theorem encodedSiteCounts_unpaired_tied {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (owner : (graph.encodeAuthoritative e).AromaticCanonicalAtom) :
    ((encodedSiteCounts siteSource.siteCounts graph e).counts owner).unpairedElectronPositions =
      (sourceSemanticAtom (graph.encodeAuthoritative e) owner).unpairedElectrons := by
  show (siteSource.siteCounts.counts
      ((encodedAtomEquiv graph e).symm owner)).unpairedElectronPositions =
    (sourceSemanticAtom (graph.encodeAuthoritative e) owner).unpairedElectrons
  rw [siteSource.unpaired_tied ((encodedAtomEquiv graph e).symm owner)]
  rw [sourceSemanticAtom_encoded_owner]

/-- The source-indexed electronic site source assembled from independent data.  Its `counts` field
is the inverse-equivalence reindexing and its `unpaired_tied` field is the theorem above, not a
hypothesis. -/
def encodedElectronicSiteSource (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V)) :
    ElectronicSiteSource (graph.encodeAuthoritative e) where
  counts := (encodedSiteCounts siteSource.siteCounts graph e).counts
  unpaired_tied := encodedSiteCounts_unpaired_tied siteSource e

/-- The encoded source's counts are exactly the reindexed independent counts. -/
@[simp] theorem encodedElectronicSiteSource_counts (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V)) :
    (encodedElectronicSiteSource graph siteSource e).counts =
      (encodedSiteCounts siteSource.siteCounts graph e).counts :=
  rfl

/-- Field-level form of `encodedSiteCounts_apply` for the assembled source. -/
@[simp] theorem encodedElectronicSiteSource_counts_apply
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V)) (atom : V) :
    (encodedElectronicSiteSource graph siteSource e).counts
        (encodedAtomEquiv graph e atom) =
      siteSource.siteCounts.counts atom := by
  rw [encodedElectronicSiteSource_counts]
  rw [encodedSiteCounts_apply]

/-- The existing source's `unpaired_tied` field, restated as an explicit theorem. -/
theorem encodedElectronicSiteSource_unpaired_tied
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (owner : (graph.encodeAuthoritative e).AromaticCanonicalAtom) :
    ((encodedElectronicSiteSource graph siteSource e).counts owner).unpairedElectronPositions =
      (sourceSemanticAtom (graph.encodeAuthoritative e) owner).unpairedElectrons :=
  (encodedElectronicSiteSource graph siteSource e).unpaired_tied owner

/-- The same count expressed directly at the graph's atom data, without going through the
source-semantic projection. -/
theorem encodedElectronicSiteSource_unpaired_eq_atomData
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (owner : (graph.encodeAuthoritative e).AromaticCanonicalAtom) :
    ((encodedElectronicSiteSource graph siteSource e).counts owner).unpairedElectronPositions =
      (graph.atomData ((encodedAtomEquiv graph e).symm owner)).unpairedElectrons := by
  rw [encodedElectronicSiteSource_counts]
  exact siteSource.unpaired_tied ((encodedAtomEquiv graph e).symm owner)

/-! ## The identity equivalence to the source-indexed site API -/

/-- The sigma-level transport: owner by the encoding atom equivalence, kind and slot values
unchanged.  The slot bound is transported by the reindexed count record. -/
def sigmaIdentityEquiv (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V)) :
    (Σ owner : V, Σ kind : SiteKind,
        Fin ((siteSource.siteCounts.counts owner).count kind)) ≃
      (Σ owner : (graph.encodeAuthoritative e).AromaticCanonicalAtom,
        Σ kind : SiteKind,
          Fin (((encodedElectronicSiteSource graph siteSource e).counts owner).count kind)) :=
  Equiv.sigmaCongr (encodedAtomEquiv graph e) fun owner =>
    Equiv.sigmaCongrRight fun kind =>
      finCastEquiv (by
        rw [encodedElectronicSiteSource_counts_apply graph siteSource e owner])

/-- The identity equivalence between independent site identities over `V` and the existing
source-indexed site identities over `graph.encodeAuthoritative e`. -/
def sourceIdentityEquiv (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V)) :
    IndependentSiteIdentity siteSource.siteCounts ≃
      SiteIdentity (graph.encodeAuthoritative e)
        (encodedElectronicSiteSource graph siteSource e) :=
  (independentSiteIdentityEquivSigma siteSource.siteCounts).trans <|
    (sigmaIdentityEquiv graph siteSource e).trans <|
      (siteIdentityEquivSigma (graph.encodeAuthoritative e)
        (encodedElectronicSiteSource graph siteSource e)).symm

/-- The owner is transported by the single encoding atom equivalence. -/
@[simp] theorem sourceIdentityEquiv_owner (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    (sourceIdentityEquiv graph siteSource e identity).owner =
      encodedAtomEquiv graph e identity.owner :=
  rfl

/-- The owner's numerical value is exactly the enumeration value of the independent label. -/
@[simp] theorem sourceIdentityEquiv_owner_val (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    (sourceIdentityEquiv graph siteSource e identity).owner.val =
      (e identity.owner).val := by
  rw [sourceIdentityEquiv_owner]
  rw [encodedAtomEquiv_apply_val]

/-- The site kind is unchanged. -/
@[simp] theorem sourceIdentityEquiv_kind (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    (sourceIdentityEquiv graph siteSource e identity).kind = identity.kind :=
  rfl

/-- The slot value is unchanged; only its bound is transported. -/
@[simp] theorem sourceIdentityEquiv_slot_val (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    ((sourceIdentityEquiv graph siteSource e identity).slot).val = identity.slot.val :=
  rfl

/-- The entire supplied count record at the mapped owner is exactly the independent record. -/
@[simp] theorem sourceIdentityEquiv_counts (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    (encodedElectronicSiteSource graph siteSource e).counts
        (sourceIdentityEquiv graph siteSource e identity).owner =
      siteSource.siteCounts.counts identity.owner := by
  rw [sourceIdentityEquiv_owner]
  rw [encodedElectronicSiteSource_counts_apply]

/-- The multiplicity of every kind at the mapped owner is unchanged. -/
@[simp] theorem sourceIdentityEquiv_count (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : IndependentSiteIdentity siteSource.siteCounts) (kind : SiteKind) :
    ((encodedElectronicSiteSource graph siteSource e).counts
        (sourceIdentityEquiv graph siteSource e identity).owner).count kind =
      (siteSource.siteCounts.counts identity.owner).count kind := by
  rw [sourceIdentityEquiv_counts]

/-- Decoding a source identity back to an independent identity. -/
def decodeSiteIdentity (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : SiteIdentity (graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e)) :
    IndependentSiteIdentity siteSource.siteCounts :=
  (sourceIdentityEquiv graph siteSource e).symm identity

/-- Decoding an encoded independent identity recovers it exactly. -/
@[simp] theorem decodeSiteIdentity_encode (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    decodeSiteIdentity graph siteSource e
        (sourceIdentityEquiv graph siteSource e identity) = identity :=
  Equiv.symm_apply_apply (sourceIdentityEquiv graph siteSource e) identity

/-- Encoding a decoded source identity recovers the source identity exactly. -/
@[simp] theorem encode_decodeSiteIdentity (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : SiteIdentity (graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e)) :
    sourceIdentityEquiv graph siteSource e
        (decodeSiteIdentity graph siteSource e identity) = identity :=
  Equiv.apply_symm_apply (sourceIdentityEquiv graph siteSource e) identity

/-- Decoding transports the owner back through the inverse atom equivalence. -/
@[simp] theorem decodeSiteIdentity_owner (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : SiteIdentity (graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e)) :
    (decodeSiteIdentity graph siteSource e identity).owner =
      (encodedAtomEquiv graph e).symm identity.owner :=
  rfl

/-- Decoding leaves the kind unchanged.  The inverse of the sigma transport carries a dependent
slot-type cast, so this is derived from the encoding round trip together with the forward
projection lemma rather than by definitional reduction. -/
@[simp] theorem decodeSiteIdentity_kind (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : SiteIdentity (graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e)) :
    (decodeSiteIdentity graph siteSource e identity).kind = identity.kind := by
  have key : (sourceIdentityEquiv graph siteSource e
      (decodeSiteIdentity graph siteSource e identity)).kind = identity.kind :=
    congrArg (fun decoded => decoded.kind)
      (encode_decodeSiteIdentity graph siteSource e identity)
  rw [sourceIdentityEquiv_kind] at key
  exact key

/-- Decoding leaves the slot value unchanged; only the transported `Fin` bound changes. -/
@[simp] theorem decodeSiteIdentity_slot_val (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : SiteIdentity (graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e)) :
    ((decodeSiteIdentity graph siteSource e identity).slot).val = identity.slot.val := by
  have key : ((sourceIdentityEquiv graph siteSource e
      (decodeSiteIdentity graph siteSource e identity)).slot).val = identity.slot.val :=
    congrArg (fun decoded => decoded.slot.val)
      (encode_decodeSiteIdentity graph siteSource e identity)
  rw [sourceIdentityEquiv_slot_val] at key
  exact key

/-- The identity equivalence is injective. -/
theorem sourceIdentityEquiv_injective (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V)) :
    Function.Injective (sourceIdentityEquiv graph siteSource e) :=
  (sourceIdentityEquiv graph siteSource e).injective

/-- The identity equivalence is surjective. -/
theorem sourceIdentityEquiv_surjective (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V)) :
    Function.Surjective (sourceIdentityEquiv graph siteSource e) :=
  (sourceIdentityEquiv graph siteSource e).surjective

/-- The number of source-indexed identities is exactly the number of independent identities. -/
theorem sourceIdentity_card_eq_independent (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V)) :
    Fintype.card (SiteIdentity (graph.encodeAuthoritative e)
        (encodedElectronicSiteSource graph siteSource e)) =
      Fintype.card (IndependentSiteIdentity siteSource.siteCounts) :=
  (Fintype.card_congr (sourceIdentityEquiv graph siteSource e)).symm

/-! ## Whole-state geometry assignments -/

/-- A whole-state geometry over independent identities: one value of `G` per site.  The type is
parameterized only by the independent counts, never by `graph.atomData` or any nuclear position. -/
structure IndependentSiteAssignment (siteCounts : IndependentSiteCounts V) (G : Type*) where
  valueAt : IndependentSiteIdentity siteCounts → G

/-- A whole-state geometry over source-indexed identities. -/
structure EncodedSiteAssignment {source : AuthoritativeChemicalInput}
    (siteSource : ElectronicSiteSource source) (G : Type*) where
  valueAt : SiteIdentity source siteSource → G

/-- Complete real geometry over independent identities, reusing `ReferenceGeometry`. -/
abbrev IndependentCompleteGeometry (siteCounts : IndependentSiteCounts V) :=
  IndependentSiteAssignment siteCounts ReferenceGeometry

/-- Optional real geometry over independent identities, reusing the repository's existing
`ReferenceGeometryEvidence`. -/
abbrev IndependentOptionalGeometry (siteCounts : IndependentSiteCounts V) :=
  IndependentSiteAssignment siteCounts ReferenceGeometryEvidence

/-- Optional real geometry over source-indexed identities, reusing the repository's existing
`ReferenceGeometryEvidence`. -/
abbrev EncodedOptionalGeometry {source : AuthoritativeChemicalInput}
    (siteSource : ElectronicSiteSource source) :=
  EncodedSiteAssignment siteSource ReferenceGeometryEvidence

@[ext] theorem IndependentSiteAssignment.ext {siteCounts : IndependentSiteCounts V}
    {G : Type*} {first second : IndependentSiteAssignment siteCounts G}
    (pointwise : ∀ identity, first.valueAt identity = second.valueAt identity) :
    first = second := by
  cases first with
  | mk firstValue =>
      cases second with
      | mk secondValue =>
          congr
          funext identity
          exact pointwise identity

@[ext] theorem EncodedSiteAssignment.ext {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source} {G : Type*}
    {first second : EncodedSiteAssignment siteSource G}
    (pointwise : ∀ identity, first.valueAt identity = second.valueAt identity) :
    first = second := by
  cases first with
  | mk firstValue =>
      cases second with
      | mk secondValue =>
          congr
          funext identity
          exact pointwise identity

namespace IndependentSiteAssignment

/-- The constant whole-state geometry with the supplied value at every site. -/
def constant {siteCounts : IndependentSiteCounts V} {G : Type*} (value : G) :
    IndependentSiteAssignment siteCounts G where
  valueAt _ := value

@[simp] theorem constant_valueAt {siteCounts : IndependentSiteCounts V} {G : Type*}
    (value : G) (identity : IndependentSiteIdentity siteCounts) :
    (constant value).valueAt identity = value :=
  rfl

end IndependentSiteAssignment

namespace EncodedSiteAssignment

/-- The constant whole-state geometry with the supplied value at every source-indexed site. -/
def constant {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source} {G : Type*} (value : G) :
    EncodedSiteAssignment siteSource G where
  valueAt _ := value

@[simp] theorem constant_valueAt {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source} {G : Type*}
    (value : G) (identity : SiteIdentity source siteSource) :
    (constant value).valueAt identity = value :=
  rfl

end EncodedSiteAssignment

/-! ## Transporting complete and optional geometry -/

/-- Encode complete per-site geometry through the inverse identity equivalence, into the existing
`IndexedSiteGeometry` type. -/
def encodeCompleteGeometry (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndependentCompleteGeometry siteSource.siteCounts) :
    IndexedSiteGeometry (graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e) where
  geometryAt identity :=
    geometry.valueAt ((sourceIdentityEquiv graph siteSource e).symm identity)

/-- Decode complete per-site geometry back to independent identities. -/
def decodeCompleteGeometry (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndexedSiteGeometry (graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e)) :
    IndependentCompleteGeometry siteSource.siteCounts where
  valueAt identity := geometry.geometryAt (sourceIdentityEquiv graph siteSource e identity)

/-- At the encoded image of every independent identity, the encoded complete geometry is exactly
the independent geometry: owner, kind, slot and every real coordinate are preserved. -/
@[simp] theorem encodeCompleteGeometry_apply (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndependentCompleteGeometry siteSource.siteCounts)
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    (encodeCompleteGeometry graph siteSource e geometry).geometryAt
        (sourceIdentityEquiv graph siteSource e identity) =
      geometry.valueAt identity := by
  change geometry.valueAt ((sourceIdentityEquiv graph siteSource e).symm
    (sourceIdentityEquiv graph siteSource e identity)) = geometry.valueAt identity
  rw [Equiv.symm_apply_apply]

/-- Decoding the encoded complete geometry recovers the original independent geometry exactly. -/
theorem decodeCompleteGeometry_encodeCompleteGeometry
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndependentCompleteGeometry siteSource.siteCounts) :
    decodeCompleteGeometry graph siteSource e
        (encodeCompleteGeometry graph siteSource e geometry) = geometry := by
  cases geometry with
  | mk valueAt =>
      apply IndependentSiteAssignment.ext
      intro identity
      simp [decodeCompleteGeometry, encodeCompleteGeometry, Equiv.symm_apply_apply]

/-- Encoding a decoded complete geometry recovers the source-indexed geometry exactly. -/
theorem encodeCompleteGeometry_decodeCompleteGeometry
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndexedSiteGeometry (graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e)) :
    encodeCompleteGeometry graph siteSource e
        (decodeCompleteGeometry graph siteSource e geometry) = geometry := by
  apply IndexedSiteGeometry.ext
  intro identity
  simp [decodeCompleteGeometry, encodeCompleteGeometry, Equiv.apply_symm_apply]

/-- Complete geometry encoding is injective: no coordinate is merged or dropped. -/
theorem encodeCompleteGeometry_injective (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V)) :
    Function.Injective (encodeCompleteGeometry graph siteSource e) := by
  intro first second equal
  calc
    first = decodeCompleteGeometry graph siteSource e
        (encodeCompleteGeometry graph siteSource e first) :=
      (decodeCompleteGeometry_encodeCompleteGeometry graph siteSource e first).symm
    _ = decodeCompleteGeometry graph siteSource e
        (encodeCompleteGeometry graph siteSource e second) := congrArg _ equal
    _ = second :=
      decodeCompleteGeometry_encodeCompleteGeometry graph siteSource e second

/-- Encode optional per-site geometry through the inverse identity equivalence. -/
def encodeOptionalGeometry (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndependentOptionalGeometry siteSource.siteCounts) :
    EncodedSiteAssignment (source := graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e) ReferenceGeometryEvidence where
  valueAt identity :=
    geometry.valueAt ((sourceIdentityEquiv graph siteSource e).symm identity)

/-- Decode optional per-site geometry back to independent identities. -/
def decodeOptionalGeometry (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : EncodedSiteAssignment (source := graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e) ReferenceGeometryEvidence) :
    IndependentOptionalGeometry siteSource.siteCounts where
  valueAt identity :=
    geometry.valueAt (sourceIdentityEquiv graph siteSource e identity)

/-- At the encoded image of every independent identity, the optional geometry is exactly the
independent optional geometry. -/
@[simp] theorem encodeOptionalGeometry_apply (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndependentOptionalGeometry siteSource.siteCounts)
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    (encodeOptionalGeometry graph siteSource e geometry).valueAt
        (sourceIdentityEquiv graph siteSource e identity) =
      geometry.valueAt identity := by
  change geometry.valueAt ((sourceIdentityEquiv graph siteSource e).symm
    (sourceIdentityEquiv graph siteSource e identity)) = geometry.valueAt identity
  rw [Equiv.symm_apply_apply]

/-- The point evidence, including its presence or absence, is preserved exactly. -/
@[simp] theorem encodeOptionalGeometry_point? (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndependentOptionalGeometry siteSource.siteCounts)
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    ((encodeOptionalGeometry graph siteSource e geometry).valueAt
        (sourceIdentityEquiv graph siteSource e identity)).point? =
      (geometry.valueAt identity).point? := by
  rw [encodeOptionalGeometry_apply]

/-- The direction evidence, including its presence or absence, is preserved exactly. -/
@[simp] theorem encodeOptionalGeometry_direction? (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndependentOptionalGeometry siteSource.siteCounts)
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    ((encodeOptionalGeometry graph siteSource e geometry).valueAt
        (sourceIdentityEquiv graph siteSource e identity)).direction? =
      (geometry.valueAt identity).direction? := by
  rw [encodeOptionalGeometry_apply]

/-- Optional knownness of the point is preserved. -/
@[simp] theorem encodeOptionalGeometry_pointKnown
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndependentOptionalGeometry siteSource.siteCounts)
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    EvidenceFacts.pointKnown ((encodeOptionalGeometry graph siteSource e geometry).valueAt
        (sourceIdentityEquiv graph siteSource e identity)) ↔
      EvidenceFacts.pointKnown (geometry.valueAt identity) := by
  simp [EvidenceFacts.pointKnown]

/-- Optional knownness of the direction is preserved. -/
@[simp] theorem encodeOptionalGeometry_directionKnown
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndependentOptionalGeometry siteSource.siteCounts)
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    EvidenceFacts.directionKnown ((encodeOptionalGeometry graph siteSource e geometry).valueAt
        (sourceIdentityEquiv graph siteSource e identity)) ↔
      EvidenceFacts.directionKnown (geometry.valueAt identity) := by
  simp [EvidenceFacts.directionKnown]

/-- The complete-geometry view of the optional evidence is preserved exactly. -/
@[simp] theorem encodeOptionalGeometry_toComplete?
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndependentOptionalGeometry siteSource.siteCounts)
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    ((encodeOptionalGeometry graph siteSource e geometry).valueAt
        (sourceIdentityEquiv graph siteSource e identity)).toComplete? =
      (geometry.valueAt identity).toComplete? := by
  rw [encodeOptionalGeometry_apply]

/-- Completeness of the optional evidence is preserved. -/
@[simp] theorem encodeOptionalGeometry_isComplete
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndependentOptionalGeometry siteSource.siteCounts)
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    EvidenceFacts.IsComplete ((encodeOptionalGeometry graph siteSource e geometry).valueAt
        (sourceIdentityEquiv graph siteSource e identity)) ↔
      EvidenceFacts.IsComplete (geometry.valueAt identity) := by
  simp [EvidenceFacts.IsComplete]

/-- Direction-only optional geometry survives the source bridge exactly: the encoded site still has
no point, and the very same supplied direction is retained. -/
theorem encodeOptionalGeometry_directionOnly_point?
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (direction : RealDirection3)
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    ((encodeOptionalGeometry graph siteSource e
        (IndependentSiteAssignment.constant (directionOnly direction))).valueAt
      (sourceIdentityEquiv graph siteSource e identity)).point? = none := by
  rw [encodeOptionalGeometry_point?]
  simp

/-- Direction-only evidence keeps the supplied direction exactly through the bridge. -/
theorem encodeOptionalGeometry_directionOnly_direction?
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (direction : RealDirection3)
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    ((encodeOptionalGeometry graph siteSource e
        (IndependentSiteAssignment.constant (directionOnly direction))).valueAt
      (sourceIdentityEquiv graph siteSource e identity)).direction? = some direction := by
  rw [encodeOptionalGeometry_direction?]
  simp

/-- Direction-only evidence remains incomplete after encoding; no point is fabricated. -/
theorem encodeOptionalGeometry_directionOnly_not_isComplete
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (direction : RealDirection3)
    (identity : IndependentSiteIdentity siteSource.siteCounts) :
    ¬ EvidenceFacts.IsComplete
      ((encodeOptionalGeometry graph siteSource e
          (IndependentSiteAssignment.constant (directionOnly direction))).valueAt
        (sourceIdentityEquiv graph siteSource e identity)) := by
  rw [encodeOptionalGeometry_isComplete]
  simpa using EvidenceFacts.directionOnly_not_isComplete direction

/-- Decoding the encoded optional geometry recovers the original independent geometry exactly,
including every absence and every real coordinate. -/
theorem decodeOptionalGeometry_encodeOptionalGeometry
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : IndependentOptionalGeometry siteSource.siteCounts) :
    decodeOptionalGeometry graph siteSource e
        (encodeOptionalGeometry graph siteSource e geometry) = geometry := by
  cases geometry with
  | mk valueAt =>
      apply IndependentSiteAssignment.ext
      intro identity
      simp [decodeOptionalGeometry, encodeOptionalGeometry, Equiv.symm_apply_apply]

/-- Encoding a decoded optional geometry recovers the source-indexed geometry exactly. -/
theorem encodeOptionalGeometry_decodeOptionalGeometry
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (geometry : EncodedSiteAssignment (source := graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e) ReferenceGeometryEvidence) :
    encodeOptionalGeometry graph siteSource e
        (decodeOptionalGeometry graph siteSource e geometry) = geometry := by
  apply EncodedSiteAssignment.ext
  intro identity
  simp [decodeOptionalGeometry, encodeOptionalGeometry, Equiv.apply_symm_apply]

/-- Optional geometry encoding is injective. -/
theorem encodeOptionalGeometry_injective (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V)) :
    Function.Injective (encodeOptionalGeometry graph siteSource e) := by
  intro first second equal
  calc
    first = decodeOptionalGeometry graph siteSource e
        (encodeOptionalGeometry graph siteSource e first) :=
      (decodeOptionalGeometry_encodeOptionalGeometry graph siteSource e first).symm
    _ = decodeOptionalGeometry graph siteSource e
        (encodeOptionalGeometry graph siteSource e second) := congrArg _ equal
    _ = second :=
      decodeOptionalGeometry_encodeOptionalGeometry graph siteSource e second

/-- Total geometry embeds into the existing evidence type by marking both components present. -/
def completeToEvidence {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source}
    (geometry : IndexedSiteGeometry source siteSource) :
    EncodedSiteAssignment siteSource ReferenceGeometryEvidence where
  valueAt identity := (geometry.geometryAt identity).toEvidence

/-- The evidence image of a complete geometry recovers the complete geometry exactly. -/
@[simp] theorem completeToEvidence_toComplete?
    {source : AuthoritativeChemicalInput} {siteSource : ElectronicSiteSource source}
    (geometry : IndexedSiteGeometry source siteSource)
    (identity : SiteIdentity source siteSource) :
    ((completeToEvidence geometry).valueAt identity).toComplete? =
      some (geometry.geometryAt identity) := by
  simp [completeToEvidence]

/-! ## Whole-state geometry may vary -/

/-- Complete per-site geometry over independent identities is freely configurable: two
whole-state geometries over the same inventory differ at a site.  The assignment type has no
access to `graph.atomData` or to any nuclear position. -/
theorem exists_distinct_complete_geometries (siteCounts : IndependentSiteCounts V)
    (identity : IndependentSiteIdentity siteCounts) :
    ∃ first second : IndependentCompleteGeometry siteCounts,
      first ≠ second ∧ first.valueAt identity ≠ second.valueAt identity := by
  refine ⟨IndependentSiteAssignment.constant ReferenceGeometry.origin,
    IndependentSiteAssignment.constant ReferenceGeometry.unitX, ?_, ?_⟩
  · intro equal
    have atSite := congrArg (fun geometry => geometry.valueAt identity) equal
    exact ReferenceGeometry.origin_ne_unitX atSite
  · simpa using ReferenceGeometry.origin_ne_unitX

/-- Optional per-site geometry is freely configurable as well, and the distinction between no
point evidence and an explicitly supplied zero point is retained at a real site. -/
theorem exists_distinct_optional_geometries (siteCounts : IndependentSiteCounts V)
    (identity : IndependentSiteIdentity siteCounts) :
    ∃ first second : IndependentOptionalGeometry siteCounts,
      first ≠ second ∧ first.valueAt identity ≠ second.valueAt identity := by
  refine ⟨IndependentSiteAssignment.constant unspecified,
    IndependentSiteAssignment.constant
      (pointOnly EvidenceFacts.originPoint), ?_, ?_⟩
  · intro equal
    have atSite := congrArg (fun geometry => geometry.valueAt identity) equal
    exact EvidenceFacts.unspecified_ne_pointOnly_origin atSite
  · simp

/-- Direction-only evidence and the same direction with an explicit zero point are distinct
whole-state optional geometries: absence of a point is never identified with a supplied zero, and
the assignment remains freely configurable. -/
theorem exists_directionOnly_vs_explicit_zero_point (siteCounts : IndependentSiteCounts V)
    (identity : IndependentSiteIdentity siteCounts) (direction : RealDirection3) :
    ∃ first second : IndependentOptionalGeometry siteCounts,
      first ≠ second ∧
        first.valueAt identity = directionOnly direction ∧
        second.valueAt identity = pointAndDirection EvidenceFacts.originPoint direction := by
  refine ⟨IndependentSiteAssignment.constant (directionOnly direction),
    IndependentSiteAssignment.constant
      (pointAndDirection EvidenceFacts.originPoint direction), ?_, rfl, rfl⟩
  intro equal
  have atSite := congrArg (fun geometry => geometry.valueAt identity) equal
  exact EvidenceFacts.directionOnly_ne_pointAndDirection_origin direction atSite

/-- Two source-indexed optional geometries over one encoded source may differ at a fixed source
identity; the bridge does not fix any geometry from the atom data. -/
theorem exists_distinct_encoded_optional_geometries
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : SiteIdentity (graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e)) :
    ∃ first second : EncodedSiteAssignment (source := graph.encodeAuthoritative e)
        (encodedElectronicSiteSource graph siteSource e) ReferenceGeometryEvidence,
      first ≠ second ∧ first.valueAt identity ≠ second.valueAt identity := by
  refine ⟨EncodedSiteAssignment.constant unspecified,
    EncodedSiteAssignment.constant
      (pointOnly EvidenceFacts.originPoint), ?_, ?_⟩
  · intro equal
    have atSite := congrArg (fun geometry => geometry.valueAt identity) equal
    exact EvidenceFacts.unspecified_ne_pointOnly_origin atSite
  · simp

/-- The existing total-geometry API already varies at every source identity; the encoded source
inherits that non-vacuity. -/
theorem exists_distinct_encoded_complete_geometries
    (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph)
    (e : V ≃ Fin (Fintype.card V))
    (identity : SiteIdentity (graph.encodeAuthoritative e)
      (encodedElectronicSiteSource graph siteSource e)) :
    ∃ first second : IndexedSiteGeometry (graph.encodeAuthoritative e)
        (encodedElectronicSiteSource graph siteSource e),
      first ≠ second ∧ first.geometryAt identity ≠ second.geometryAt identity :=
  exists_distinct_geometries_same_inventory
    (graph.encodeAuthoritative e) (encodedElectronicSiteSource graph siteSource e) identity

/-! ## A concrete two-label witness -/

/-- A concrete periodic element (carbon) used only to exhibit the bridge. -/
def exampleCarbon : PeriodicElement where
  atomicNumber := 6
  positive := by decide
  atMost118 := by decide

/-- Two independent labels: `0` carries one unpaired electron, `1` is a closed shell. -/
def exampleGraph : FiniteAtomInteractionHypergraph (Fin 2) where
  atomData owner :=
    if owner = 0 then
      { element := exampleCarbon, unpairedElectrons := 1 }
    else
      { element := exampleCarbon }
  interactions := []
  arity_ge_two := by simp
  participants_nodup := by simp

/-- Independently supplied counts: a lone pair and one unpaired position at label `0`, two
implicit protia at label `1`.  Only the unpaired count is tied to the graph. -/
def exampleCounts : IndependentSiteCounts (Fin 2) where
  counts owner :=
    if owner = 0 then
      { implicitProtia := 0
        lonePairs := 1
        vacancies := 0
        unpairedElectronPositions := 1
        cipNotionalPhantoms := 0
        cipVirtualDuplicates := 0 }
    else
      { implicitProtia := 2
        lonePairs := 0
        vacancies := 0
        unpairedElectronPositions := 0
        cipNotionalPhantoms := 0
        cipVirtualDuplicates := 0 }

/-- The concrete unpaired tie is discharged from the graph data by computation. -/
theorem exampleCounts_unpaired_tied :
    ∀ owner, (exampleCounts.counts owner).unpairedElectronPositions =
      (exampleGraph.atomData owner).unpairedElectrons := by
  intro owner
  by_cases zero : owner = 0
  · simp [exampleCounts, exampleGraph, zero]
  · simp [exampleCounts, exampleGraph, zero]

/-- The concrete independent site source; its `unpaired_tied` field is the theorem above. -/
def exampleSource : IndependentElectronicSiteSource exampleGraph where
  siteCounts := exampleCounts
  unpaired_tied := exampleCounts_unpaired_tied

/-- The same enumeration shape as the graph encoding: the two labels are already `Fin 2`. -/
def exampleEnumeration : Fin 2 ≃ Fin (Fintype.card (Fin 2)) :=
  finCastEquiv (by rw [Fintype.card_fin])

/-- One concrete independent site: the unpaired-electron site at label `0`. -/
def exampleIdentity : IndependentSiteIdentity exampleSource.siteCounts where
  owner := 0
  kind := .electronic .unpairedElectron
  slot := ⟨0, by decide⟩

/-- The bridge maps that concrete identity to a source-indexed site, so the construction is
non-vacuous on an actual finite graph. -/
def exampleEncodedIdentity :
    SiteIdentity (exampleGraph.encodeAuthoritative exampleEnumeration)
      (encodedElectronicSiteSource exampleGraph exampleSource exampleEnumeration) :=
  sourceIdentityEquiv exampleGraph exampleSource exampleEnumeration exampleIdentity

/-- The concrete owner value is the enumeration value of the independent label. -/
@[simp] theorem exampleEncodedIdentity_owner_val :
    exampleEncodedIdentity.owner.val = (exampleEnumeration 0).val :=
  sourceIdentityEquiv_owner_val exampleGraph exampleSource exampleEnumeration exampleIdentity

/-- The concrete kind is unchanged by the bridge. -/
@[simp] theorem exampleEncodedIdentity_kind :
    exampleEncodedIdentity.kind = SiteKind.electronic ElectronicSiteKind.unpairedElectron :=
  sourceIdentityEquiv_kind exampleGraph exampleSource exampleEnumeration exampleIdentity

/-- The concrete slot value is unchanged by the bridge. -/
@[simp] theorem exampleEncodedIdentity_slot_val :
    exampleEncodedIdentity.slot.val = 0 :=
  sourceIdentityEquiv_slot_val exampleGraph exampleSource exampleEnumeration exampleIdentity

/-- Concrete decoding of the encoded identity recovers it exactly. -/
theorem example_decode_encode :
    decodeSiteIdentity exampleGraph exampleSource exampleEnumeration exampleEncodedIdentity =
      exampleIdentity :=
  decodeSiteIdentity_encode exampleGraph exampleSource exampleEnumeration exampleIdentity

/-- At the exhibited concrete owner, the encoded source's unpaired count is discharged against
the actual encoded semantic atom, not assumed. -/
theorem exampleEncodedIdentity_unpaired_tied :
    ((encodedElectronicSiteSource exampleGraph exampleSource exampleEnumeration).counts
        exampleEncodedIdentity.owner).unpairedElectronPositions =
      (sourceSemanticAtom (exampleGraph.encodeAuthoritative exampleEnumeration)
        exampleEncodedIdentity.owner).unpairedElectrons :=
  encodedElectronicSiteSource_unpaired_tied exampleGraph exampleSource exampleEnumeration
    exampleEncodedIdentity.owner
