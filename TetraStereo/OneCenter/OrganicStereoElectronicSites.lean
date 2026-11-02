import TetraStereo.OneCenter.AuthoritativeChemicalInputEndpointElectronicInventory
import TetraStereo.OneCenter.P94MoleculeCoordinateTorsion
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.SuccPred

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace OrganicStereoElectronicSites

open BlueBookP94.CoordinateTorsion








































/-! ## Real reference geometry -/

/-- An exact real reference point. -/
structure RealPoint3 where
  x : ℝ
  y : ℝ
  z : ℝ

noncomputable instance realPoint3DecidableEq : DecidableEq RealPoint3 :=
  Classical.decEq _

/-- An exact real reference direction.  No normalization or nonzero condition is imposed. -/
structure RealDirection3 where
  x : ℝ
  y : ℝ
  z : ℝ

noncomputable instance realDirection3DecidableEq : DecidableEq RealDirection3 :=
  Classical.decEq _

/-- Supplied geometry associated with one site.  The point and direction are reference data, not a
claim that an electron is localized at the point. -/
structure ReferenceGeometry where
  point : RealPoint3
  direction : RealDirection3

noncomputable instance referenceGeometryDecidableEq : DecidableEq ReferenceGeometry :=
  Classical.decEq _

namespace ReferenceGeometry

/-- The neutral reference geometry used only as an unreachable default and as a concrete point. -/
def origin : ReferenceGeometry where
  point := ⟨0, 0, 0⟩
  direction := ⟨0, 0, 0⟩

/-- A distinct concrete reference geometry. -/
def unitX : ReferenceGeometry where
  point := ⟨1, 0, 0⟩
  direction := ⟨0, 0, 0⟩

theorem origin_ne_unitX : origin ≠ unitX := by
  intro equal
  have pointEq : origin.point = unitX.point := congrArg ReferenceGeometry.point equal
  have xEq : (0 : ℝ) = 1 := by
    simpa [origin, unitX] using congrArg RealPoint3.x pointEq
  exact zero_ne_one xEq

end ReferenceGeometry

/-- Cast a rational point from the legacy spatial configuration to a real reference point. -/
def realPointOfRat (point : CartesianPoint3) : RealPoint3 where
  x := (point.x : ℝ)
  y := (point.y : ℝ)
  z := (point.z : ℝ)

/-- Evidence-level geometry.  Unlike `ReferenceGeometry`, this records which components were
independently supplied.  The four states `unspecified`, `pointOnly`, `directionOnly`, and
`pointAndDirection` are distinct; in particular no absent component is fabricated as a zero
vector or an origin point. -/
inductive ReferenceGeometryEvidence where
  | unspecified
  | pointOnly (point : RealPoint3)
  | directionOnly (direction : RealDirection3)
  | pointAndDirection (point : RealPoint3) (direction : RealDirection3)

noncomputable instance referenceGeometryEvidenceDecidableEq :
    DecidableEq ReferenceGeometryEvidence :=
  Classical.decEq _

namespace ReferenceGeometryEvidence

/-- The supplied point, if any. -/
def point? : ReferenceGeometryEvidence → Option RealPoint3
  | .unspecified => none
  | .pointOnly point => some point
  | .directionOnly _ => none
  | .pointAndDirection point _ => some point

/-- The supplied direction, if any. -/
def direction? : ReferenceGeometryEvidence → Option RealDirection3
  | .unspecified => none
  | .pointOnly _ => none
  | .directionOnly direction => some direction
  | .pointAndDirection _ direction => some direction

/-- A complete reference geometry only when both components were supplied. -/
def toComplete? : ReferenceGeometryEvidence → Option ReferenceGeometry
  | .pointAndDirection point direction => some ⟨point, direction⟩
  | _ => none

/-- A legacy rational point supplies a point but no direction.  It is represented as `pointOnly`,
never as `pointAndDirection` with a fabricated zero vector. -/
def ofRationalPoint (point : CartesianPoint3) : ReferenceGeometryEvidence :=
  .pointOnly (realPointOfRat point)

@[simp] theorem ofRationalPoint_point? (point : CartesianPoint3) :
    (ofRationalPoint point).point? = some (realPointOfRat point) :=
  rfl

@[simp] theorem ofRationalPoint_direction? (point : CartesianPoint3) :
    (ofRationalPoint point).direction? = none :=
  rfl

/-- Absence of a direction is distinct from an explicitly supplied zero direction. -/
theorem pointOnly_ne_pointAndDirection_zero (point : RealPoint3) :
    pointOnly point ≠ pointAndDirection point ⟨0, 0, 0⟩ := by
  intro equal
  cases equal

/-- Absence of a point is distinct from an explicitly supplied zero point. -/
theorem directionOnly_ne_pointAndDirection_zero (direction : RealDirection3) :
    directionOnly direction ≠ pointAndDirection ⟨0, 0, 0⟩ direction := by
  intro equal
  cases equal

@[simp] theorem directionOnly_point? (direction : RealDirection3) :
    (directionOnly direction).point? = none :=
  rfl

@[simp] theorem directionOnly_direction? (direction : RealDirection3) :
    (directionOnly direction).direction? = some direction :=
  rfl

@[simp] theorem toComplete?_directionOnly (direction : RealDirection3) :
    (directionOnly direction).toComplete? = none :=
  rfl

/-- The complete geometry state retains both components when both are supplied. -/
@[simp] theorem toComplete?_pointAndDirection (point : RealPoint3)
    (direction : RealDirection3) :
    (pointAndDirection point direction).toComplete? =
      some ⟨point, direction⟩ :=
  rfl

/-- Incomplete evidence has no complete-reference interpretation. -/
@[simp] theorem toComplete?_unspecified :
    (unspecified : ReferenceGeometryEvidence).toComplete? = none :=
  rfl

@[simp] theorem toComplete?_pointOnly (point : RealPoint3) :
    (pointOnly point).toComplete? = none :=
  rfl

/-- Exhaustive closure of the four evidence states: none, point only, direction only, or both. -/
theorem evidence_cases (evidence : ReferenceGeometryEvidence) :
    evidence = unspecified ∨
      (∃ point, evidence = pointOnly point) ∨
      (∃ direction, evidence = directionOnly direction) ∨
      (∃ point direction, evidence = pointAndDirection point direction) := by
  cases evidence with
  | unspecified => exact Or.inl rfl
  | pointOnly point => exact Or.inr (Or.inl ⟨point, rfl⟩)
  | directionOnly direction => exact Or.inr (Or.inr (Or.inl ⟨direction, rfl⟩))
  | pointAndDirection point direction =>
      exact Or.inr (Or.inr (Or.inr ⟨point, direction, rfl⟩))

end ReferenceGeometryEvidence

namespace ReferenceGeometry

/-- Forget only the provenance distinction between supplied and absent components. -/
def toEvidence (geometry : ReferenceGeometry) : ReferenceGeometryEvidence :=
  .pointAndDirection geometry.point geometry.direction

end ReferenceGeometry

/-! ## Site kinds and supplied counts -/

/-- The four electronic site kinds retained by the endpoint inventory. -/
inductive ElectronicSiteKind where
  | implicitProtium
  | lonePair
  | vacancy
  | unpairedElectron
  deriving DecidableEq, Repr, Fintype

/-- CIP notional reference kinds.  These are bookkeeping references, not electrons or nuclei. -/
inductive CIPReferenceKind where
  | notionalPhantom
  | virtualDuplicate
  deriving DecidableEq, Repr, Fintype

/-- Every retained site kind.  Electronic and CIP-reference constructors are disjoint by
construction. -/
inductive SiteKind where
  | electronic (kind : ElectronicSiteKind)
  | cipReference (kind : CIPReferenceKind)
  deriving DecidableEq, Repr, Fintype

/-- A site kind is electronic exactly in the first constructor family. -/
def SiteKind.IsElectronic : SiteKind → Prop
  | .electronic _ => True
  | .cipReference _ => False

/-- A site kind is the CIP notional phantom exactly in its dedicated constructor. -/
def SiteKind.IsCIPNotionalPhantom : SiteKind → Prop
  | .cipReference .notionalPhantom => True
  | _ => False

/-- Electronic kinds are electronically meaningful. -/
theorem electronic_isElectronic (kind : ElectronicSiteKind) :
    (SiteKind.electronic kind).IsElectronic :=
  trivial

/-- The CIP notional phantom is not an electronic kind. -/
theorem cipNotionalPhantom_not_isElectronic :
    ¬ (SiteKind.cipReference .notionalPhantom).IsElectronic := by
  simp [SiteKind.IsElectronic]

/-- The CIP notional phantom is never equal to an electronic kind. -/
theorem cipNotionalPhantom_ne_electronic (kind : ElectronicSiteKind) :
    SiteKind.cipReference .notionalPhantom ≠ SiteKind.electronic kind := by
  intro equal
  cases equal

/-- The CIP notional phantom is a phantom reference, not an electron pair or nucleus. -/
theorem cipNotionalPhantom_isCIPNotionalPhantom :
    (SiteKind.cipReference .notionalPhantom).IsCIPNotionalPhantom :=
  trivial

/-- The CIP virtual-duplicate reference is never equal to a lone-pair electronic kind. -/
theorem virtualDuplicate_ne_lonePair :
    SiteKind.cipReference .virtualDuplicate ≠ SiteKind.electronic .lonePair := by
  intro equal
  cases equal

/-- Explicit per-atom supplied site counts.  The first four fields reuse the vocabulary of the
existing endpoint electronic inventory; the last two retain CIP reference bookkeeping separately. -/
structure SuppliedSiteCounts where
  implicitProtia : ℕ
  lonePairs : ℕ
  vacancies : ℕ
  unpairedElectronPositions : ℕ
  cipNotionalPhantoms : ℕ
  cipVirtualDuplicates : ℕ
  deriving DecidableEq, Repr

namespace SuppliedSiteCounts

/-- The supplied multiplicity of one site kind at one owner. -/
def count (counts : SuppliedSiteCounts) : SiteKind → ℕ
  | .electronic .implicitProtium => counts.implicitProtia
  | .electronic .lonePair => counts.lonePairs
  | .electronic .vacancy => counts.vacancies
  | .electronic .unpairedElectron => counts.unpairedElectronPositions
  | .cipReference .notionalPhantom => counts.cipNotionalPhantoms
  | .cipReference .virtualDuplicate => counts.cipVirtualDuplicates

/-- Total retained multiplicity at one owner. -/
def total (counts : SuppliedSiteCounts) : ℕ :=
  (Finset.univ : Finset SiteKind).sum counts.count

/-- Embed the existing endpoint electronic inventory, adding no CIP-reference sites. -/
def ofEndpointInventory
    (inventory :
      AuthoritativeChemicalInput.AromaticCanonicalRule3EndpointElectronicInventory) :
    SuppliedSiteCounts where
  implicitProtia := inventory.implicitProtia
  lonePairs := inventory.lonePairs
  vacancies := inventory.vacancies
  unpairedElectronPositions := inventory.unpairedElectronPositions
  cipNotionalPhantoms := 0
  cipVirtualDuplicates := 0

/-- The electronic projection of a supplied count record, reusing the existing inventory type. -/
def electronicInventory (counts : SuppliedSiteCounts) :
    AuthoritativeChemicalInput.AromaticCanonicalRule3EndpointElectronicInventory where
  implicitProtia := counts.implicitProtia
  lonePairs := counts.lonePairs
  vacancies := counts.vacancies
  unpairedElectronPositions := counts.unpairedElectronPositions

@[simp] theorem electronicInventory_ofEndpointInventory
    (inventory :
      AuthoritativeChemicalInput.AromaticCanonicalRule3EndpointElectronicInventory) :
    (ofEndpointInventory inventory).electronicInventory = inventory := by
  cases inventory
  rfl

@[simp] theorem count_electronic_lonePair (counts : SuppliedSiteCounts) :
    counts.count (.electronic .lonePair) = counts.lonePairs :=
  rfl

@[simp] theorem count_electronic_unpairedElectron (counts : SuppliedSiteCounts) :
    counts.count (.electronic .unpairedElectron) = counts.unpairedElectronPositions :=
  rfl

@[simp] theorem count_cipNotionalPhantom (counts : SuppliedSiteCounts) :
    counts.count (.cipReference .notionalPhantom) = counts.cipNotionalPhantoms :=
  rfl

@[simp] theorem count_cipVirtualDuplicate (counts : SuppliedSiteCounts) :
    counts.count (.cipReference .virtualDuplicate) = counts.cipVirtualDuplicates :=
  rfl

end SuppliedSiteCounts

/-- The source semantic atom at a bounded owner index. -/
def sourceSemanticAtom (source : AuthoritativeChemicalInput)
    (owner : source.AromaticCanonicalAtom) : SemanticAtom :=
  source.molecule.atoms.get ⟨owner.val, owner.isLt⟩

/-- The explicit per-atom count source.  The unpaired-electron count is tied to the source semantic
atom field; all other counts are supplied and are never inferred from geometry. -/
structure ElectronicSiteSource (source : AuthoritativeChemicalInput) where
  counts : source.AromaticCanonicalAtom → SuppliedSiteCounts
  unpaired_tied : ∀ owner,
    (counts owner).unpairedElectronPositions =
      (sourceSemanticAtom source owner).unpairedElectrons

namespace ElectronicSiteSource

/-- Build a count source from arbitrary per-atom endpoint electronic inventories.  No two-position
equation is required, and vacancy/radical counts remain exactly what was supplied. -/
def ofEndpointInventories (source : AuthoritativeChemicalInput)
    (inventories : source.AromaticCanonicalAtom →
      AuthoritativeChemicalInput.AromaticCanonicalRule3EndpointElectronicInventory)
    (unpaired_tied : ∀ owner,
      (inventories owner).unpairedElectronPositions =
        (sourceSemanticAtom source owner).unpairedElectrons) :
    ElectronicSiteSource source where
  counts owner := SuppliedSiteCounts.ofEndpointInventory (inventories owner)
  unpaired_tied owner := unpaired_tied owner

/-- Relabel the owners of a count source along an atom equivalence that preserves the source
unpaired-electron tie.  Every supplied multiplicity moves with its atom and none is altered. -/
def relabel {source source' : AuthoritativeChemicalInput}
    (siteSource : ElectronicSiteSource source)
    (atoms : source.AromaticCanonicalAtom ≃ source'.AromaticCanonicalAtom)
    (unpaired_preserved : ∀ owner,
      (sourceSemanticAtom source owner).unpairedElectrons =
        (sourceSemanticAtom source' (atoms owner)).unpairedElectrons) :
    ElectronicSiteSource source' where
  counts owner' := siteSource.counts (atoms.symm owner')
  unpaired_tied owner' := by
    rw [siteSource.unpaired_tied (atoms.symm owner')]
    simpa using unpaired_preserved (atoms.symm owner')

/-- A relabelled count source has exactly the original multiplicity at the image owner. -/
@[simp] theorem relabel_counts {source source' : AuthoritativeChemicalInput}
    (siteSource : ElectronicSiteSource source)
    (atoms : source.AromaticCanonicalAtom ≃ source'.AromaticCanonicalAtom)
    (unpaired_preserved : ∀ owner,
      (sourceSemanticAtom source owner).unpairedElectrons =
        (sourceSemanticAtom source' (atoms owner)).unpairedElectrons)
    (owner : source.AromaticCanonicalAtom) :
    (relabel siteSource atoms unpaired_preserved).counts (atoms owner) =
      siteSource.counts owner := by
  simp [ElectronicSiteSource.relabel]

end ElectronicSiteSource

/-- The unpaired-site count is exactly the source semantic atom's explicit unpaired-electron
count. -/
theorem unpairedElectronPositions_eq_sourceSemanticAtom
    (source : AuthoritativeChemicalInput) (siteSource : ElectronicSiteSource source)
    (owner : source.AromaticCanonicalAtom) :
    (siteSource.counts owner).unpairedElectronPositions =
      (sourceSemanticAtom source owner).unpairedElectrons :=
  siteSource.unpaired_tied owner

/-! ## Individual site identities -/

/-- A source-bound individual site identity.  The slot is a `Fin` index into the explicitly
supplied multiplicity, so multiple sites of the same kind at one owner are distinct. -/
structure SiteIdentity (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) where
  owner : source.AromaticCanonicalAtom
  kind : SiteKind
  slot : Fin ((siteSource.counts owner).count kind)

/-- Site identities are equivalent to a nested sigma of owner, kind, and slot. -/
def siteIdentityEquivSigma (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) :
    SiteIdentity source siteSource ≃
      (Σ owner : source.AromaticCanonicalAtom,
        Σ kind : SiteKind, Fin ((siteSource.counts owner).count kind)) where
  toFun identity := ⟨identity.owner, identity.kind, identity.slot⟩
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv identity := by
    cases identity
    rfl
  right_inv data := by
    rcases data with ⟨owner, kind, slot⟩
    rfl

noncomputable instance siteIdentityDecidableEq (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) : DecidableEq (SiteIdentity source siteSource) :=
  Equiv.decidableEq (siteIdentityEquivSigma source siteSource)

noncomputable instance siteIdentityFintype (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) : Fintype (SiteIdentity source siteSource) :=
  Fintype.ofEquiv
    (Σ owner : source.AromaticCanonicalAtom,
      Σ kind : SiteKind, Fin ((siteSource.counts owner).count kind))
    (siteIdentityEquivSigma source siteSource).symm

/-- Explicit atom-relabelling compatibility for source-bound site identities.  The `counts_eq`
field is the exact multiplicity transport: no site is created, merged, or dropped. -/
structure AtomRelabel (source source' : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (siteSource' : ElectronicSiteSource source') where
  atoms : source.AromaticCanonicalAtom ≃ source'.AromaticCanonicalAtom
  counts_eq : ∀ owner kind,
    (siteSource'.counts (atoms owner)).count kind =
      (siteSource.counts owner).count kind

namespace AtomRelabel

variable {source source' : AuthoritativeChemicalInput}
variable {siteSource : ElectronicSiteSource source}
variable {siteSource' : ElectronicSiteSource source'}

/-- Build the compatibility datum for a count source relabelled along `atoms`. -/
def ofSourceRelabel (siteSource : ElectronicSiteSource source)
    (atoms : source.AromaticCanonicalAtom ≃ source'.AromaticCanonicalAtom)
    (unpaired_preserved : ∀ owner,
      (sourceSemanticAtom source owner).unpairedElectrons =
        (sourceSemanticAtom source' (atoms owner)).unpairedElectrons) :
    AtomRelabel source source' siteSource
      (ElectronicSiteSource.relabel siteSource atoms unpaired_preserved) where
  atoms := atoms
  counts_eq owner kind :=
    congrArg (fun counts : SuppliedSiteCounts => counts.count kind)
      (ElectronicSiteSource.relabel_counts siteSource atoms unpaired_preserved owner)

/-- The inverse compatibility datum. -/
def symm (relabel : AtomRelabel source source' siteSource siteSource') :
    AtomRelabel source' source siteSource' siteSource where
  atoms := relabel.atoms.symm
  counts_eq owner kind := by
    simpa using (relabel.counts_eq (relabel.atoms.symm owner) kind).symm

/-- Exact transport of individual site identities along an atom relabelling.  Because this is an
`Equiv` built from the slot-preserving count equality, no site is lost or collapsed. -/
def siteIdentityEquiv (relabel : AtomRelabel source source' siteSource siteSource') :
    SiteIdentity source siteSource ≃ SiteIdentity source' siteSource' :=
  (siteIdentityEquivSigma source siteSource).trans <|
    (Equiv.sigmaCongr relabel.atoms fun owner =>
      Equiv.sigmaCongrRight fun kind =>
        finCongr (relabel.counts_eq owner kind).symm).trans
      (siteIdentityEquivSigma source' siteSource').symm

@[simp] theorem siteIdentityEquiv_owner
    (relabel : AtomRelabel source source' siteSource siteSource')
    (identity : SiteIdentity source siteSource) :
    (relabel.siteIdentityEquiv identity).owner = relabel.atoms identity.owner :=
  rfl

@[simp] theorem siteIdentityEquiv_kind
    (relabel : AtomRelabel source source' siteSource siteSource')
    (identity : SiteIdentity source siteSource) :
    (relabel.siteIdentityEquiv identity).kind = identity.kind :=
  rfl

/-- The slot value is preserved exactly; only its `Fin` bound is transported. -/
@[simp] theorem siteIdentityEquiv_slot_val
    (relabel : AtomRelabel source source' siteSource siteSource')
    (identity : SiteIdentity source siteSource) :
    (relabel.siteIdentityEquiv identity).slot.val = identity.slot.val :=
  rfl

@[simp] theorem siteIdentityEquiv_left_inv
    (relabel : AtomRelabel source source' siteSource siteSource')
    (identity : SiteIdentity source siteSource) :
    relabel.siteIdentityEquiv.symm (relabel.siteIdentityEquiv identity) = identity :=
  relabel.siteIdentityEquiv.left_inv identity

@[simp] theorem siteIdentityEquiv_right_inv
    (relabel : AtomRelabel source source' siteSource siteSource')
    (identity : SiteIdentity source' siteSource') :
    relabel.siteIdentityEquiv (relabel.siteIdentityEquiv.symm identity) = identity :=
  relabel.siteIdentityEquiv.right_inv identity

end AtomRelabel

/-- Every owner is a genuinely bounded source atom index. -/
theorem SiteIdentity.owner_lt {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source}
    (identity : SiteIdentity source siteSource) :
    identity.owner.val < source.molecule.atomCount :=
  identity.owner.isLt

/-- Two lone-pair sites at one atom with different slots are different identities. -/
theorem lonePair_slots_distinct (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (owner : source.AromaticCanonicalAtom)
    {slot₁ slot₂ : Fin ((siteSource.counts owner).count (.electronic .lonePair))}
    (different : slot₁ ≠ slot₂) :
    (⟨owner, .electronic .lonePair, slot₁⟩ : SiteIdentity source siteSource) ≠
      ⟨owner, .electronic .lonePair, slot₂⟩ := by
  intro equal
  have valueEq : slot₁.val = slot₂.val :=
    congrArg (fun identity : SiteIdentity source siteSource => identity.slot.val) equal
  exact different (Fin.ext valueEq)

/-- The canonical enumeration of every lone-pair slot at one atom has exactly the supplied
multiplicity, for every natural number. -/
theorem lonePair_slots_card (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (owner : source.AromaticCanonicalAtom) :
    (List.finRange ((siteSource.counts owner).count (.electronic .lonePair))).length =
      (siteSource.counts owner).lonePairs := by
  simp

/-- The CIP notional phantom is never the same identity as an electronic site. -/
theorem cipNotionalPhantom_identity_ne_electronic
    (source : AuthoritativeChemicalInput) (siteSource : ElectronicSiteSource source)
    (owner : source.AromaticCanonicalAtom)
    (electronicKind : ElectronicSiteKind)
    (phantomSlot :
      Fin ((siteSource.counts owner).count (.cipReference .notionalPhantom)))
    (electronicSlot :
      Fin ((siteSource.counts owner).count (.electronic electronicKind))) :
    (⟨owner, .cipReference .notionalPhantom, phantomSlot⟩ :
        SiteIdentity source siteSource) ≠
      ⟨owner, .electronic electronicKind, electronicSlot⟩ := by
  intro equal
  have kindEq := congrArg SiteIdentity.kind equal
  cases kindEq

/-- The number of all individual site identities is the sum of the supplied multiplicities. -/
theorem siteIdentity_card_eq_sum (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) :
    Fintype.card (SiteIdentity source siteSource) =
      (Finset.univ : Finset source.AromaticCanonicalAtom).sum
        fun owner => (siteSource.counts owner).total := by
  rw [Fintype.card_congr (siteIdentityEquivSigma source siteSource), Fintype.card_sigma]
  refine Finset.sum_congr rfl ?_
  intro owner _
  rw [Fintype.card_sigma]
  simp [SuppliedSiteCounts.total]

/-! ## Indexed and finite site representations -/

/-- A total indexed representation: exactly one supplied real reference geometry for every
individual identity. -/
structure IndexedSiteGeometry (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) where
  geometryAt : SiteIdentity source siteSource → ReferenceGeometry

@[ext] theorem IndexedSiteGeometry.ext {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source}
    {left right : IndexedSiteGeometry source siteSource}
    (pointwise : ∀ identity, left.geometryAt identity = right.geometryAt identity) :
    left = right := by
  cases left
  cases right
  congr
  funext identity
  exact pointwise identity

namespace IndexedSiteGeometry

/-- Relabel every indexed site identity along an atom relabelling.  The geometry attached to each
site is unchanged; the inverse is supplied exactly by `AtomRelabel.siteIdentityEquiv`. -/
def relabel {source source' : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source}
    {siteSource' : ElectronicSiteSource source'}
    (indexed : IndexedSiteGeometry source siteSource)
    (relabel : AtomRelabel source source' siteSource siteSource') :
    IndexedSiteGeometry source' siteSource' where
  geometryAt identity' := indexed.geometryAt (relabel.siteIdentityEquiv.symm identity')

/-- Relabelling preserves the reference geometry of every original site exactly. -/
@[simp] theorem relabel_geometryAt {source source' : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source}
    {siteSource' : ElectronicSiteSource source'}
    (indexed : IndexedSiteGeometry source siteSource)
    (relabel : AtomRelabel source source' siteSource siteSource')
    (identity : SiteIdentity source siteSource) :
    (indexed.relabel relabel).geometryAt (relabel.siteIdentityEquiv identity) =
      indexed.geometryAt identity := by
  simp [IndexedSiteGeometry.relabel]

end IndexedSiteGeometry

/-- One explicit finite site record. -/
structure SiteRecord (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) where
  identity : SiteIdentity source siteSource
  geometry : ReferenceGeometry

noncomputable instance siteRecordDecidableEq (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) : DecidableEq (SiteRecord source siteSource) :=
  Classical.decEq _

/-- A site record carrying only the independently supplied geometry evidence.  This retains the
distinction between unknown, point-only, and point-and-direction states. -/
structure SiteEvidenceRecord (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) where
  identity : SiteIdentity source siteSource
  evidence : ReferenceGeometryEvidence

noncomputable instance siteEvidenceRecordDecidableEq (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) :
    DecidableEq (SiteEvidenceRecord source siteSource) :=
  Classical.decEq _

/-- Independent finite site data. -/
abbrev FiniteSiteData (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) : Type :=
  List (SiteRecord source siteSource)

/-- Finite site data at evidence level. -/
abbrev FiniteSiteEvidenceData (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) : Type :=
  List (SiteEvidenceRecord source siteSource)

/-- The canonical enumeration of all identities. -/
noncomputable def allIdentities (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) : List (SiteIdentity source siteSource) :=
  (Finset.univ : Finset (SiteIdentity source siteSource)).toList

theorem allIdentities_nodup (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) :
    (allIdentities source siteSource).Nodup :=
  Finset.nodup_toList _

theorem mem_allIdentities (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (identity : SiteIdentity source siteSource) :
    identity ∈ allIdentities source siteSource := by
  unfold allIdentities
  rw [Finset.mem_toList]
  exact Finset.mem_univ identity

/-- The canonical enumeration length is exactly the sum of supplied multiplicities. -/
theorem length_allIdentities (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) :
    (allIdentities source siteSource).length =
      (Finset.univ : Finset source.AromaticCanonicalAtom).sum
        fun owner => (siteSource.counts owner).total := by
  unfold allIdentities
  rw [Finset.length_toList]
  exact siteIdentity_card_eq_sum source siteSource

namespace FiniteSiteData

/-- Finite data is valid when it contains every individual identity exactly once.  Order is
irrelevant; multiplicity is exact because identities include the supplied `Fin` slot. -/
def Valid {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source}
    (data : FiniteSiteData source siteSource) : Prop :=
  (data.map SiteRecord.identity).Nodup ∧
    ∀ identity : SiteIdentity source siteSource,
      identity ∈ data.map SiteRecord.identity

/-- Exact identity lookup in finite data. -/
noncomputable def lookup? {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source}
    (data : FiniteSiteData source siteSource)
    (identity : SiteIdentity source siteSource) : Option (SiteRecord source siteSource) :=
  match data with
  | [] => none
  | record :: rest =>
      if record.identity = identity then some record else lookup? rest identity

/-- On duplicate-free keys, lookup succeeds exactly for the unique matching record. -/
theorem lookup?_eq_some_iff_of_nodup {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source}
    (data : FiniteSiteData source siteSource)
    (nodup : (data.map SiteRecord.identity).Nodup)
    (identity : SiteIdentity source siteSource)
    (record : SiteRecord source siteSource) :
    data.lookup? identity = some record ↔
      record ∈ data ∧ record.identity = identity := by
  induction data with
  | nil => simp [lookup?]
  | cons head tail inductionHypothesis =>
      have keysNodup : (head.identity :: tail.map SiteRecord.identity).Nodup := by
        simpa using nodup
      have headFresh : head.identity ∉ tail.map SiteRecord.identity :=
        (List.nodup_cons.mp keysNodup).1
      have tailNodup : (tail.map SiteRecord.identity).Nodup :=
        (List.nodup_cons.mp keysNodup).2
      by_cases same : head.identity = identity
      · subst identity
        constructor
        · intro computed
          have recordEq : head = record := by
            simpa [lookup?] using computed
          subst record
          exact ⟨List.mem_cons_self, rfl⟩
        · rintro ⟨present, identityEq⟩
          rcases List.mem_cons.mp present with headEq | tailPresent
          · subst record
            simp [lookup?]
          · exfalso
            apply headFresh
            exact List.mem_map.mpr ⟨record, tailPresent, identityEq⟩
      · constructor
        · intro computed
          have tailComputed : lookup? tail identity = some record := by
            simpa [lookup?, same] using computed
          rcases inductionHypothesis tailNodup |>.mp tailComputed with
            ⟨present, identityEq⟩
          exact ⟨List.mem_cons_of_mem _ present, identityEq⟩
        · rintro ⟨present, identityEq⟩
          rcases List.mem_cons.mp present with headEq | tailPresent
          · subst record
            exact False.elim (same identityEq)
          · have tailComputed : lookup? tail identity = some record :=
              (inductionHypothesis tailNodup).mpr ⟨tailPresent, identityEq⟩
            simpa [lookup?, same] using tailComputed

/-- Valid finite data always has a lookup result for every identity. -/
theorem lookup?_exists_of_valid {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source}
    (data : FiniteSiteData source siteSource)
    (valid : data.Valid) (identity : SiteIdentity source siteSource) :
    ∃ record, FiniteSiteData.lookup? data identity = some record := by
  rcases List.mem_map.mp (valid.2 identity) with ⟨record, present, identityEq⟩
  refine ⟨record, ?_⟩
  exact (lookup?_eq_some_iff_of_nodup data valid.1 identity record).mpr
    ⟨present, identityEq⟩

end FiniteSiteData

/-- Compile an indexed representation to its canonical finite data. -/
noncomputable def toFiniteData (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (indexed : IndexedSiteGeometry source siteSource) :
    FiniteSiteData source siteSource :=
  (allIdentities source siteSource).map fun identity =>
    { identity := identity, geometry := indexed.geometryAt identity }

/-- The canonical finite data contains every identity exactly once. -/
theorem valid_toFiniteData (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (indexed : IndexedSiteGeometry source siteSource) :
    (toFiniteData source siteSource indexed).Valid := by
  have keys : (toFiniteData source siteSource indexed).map SiteRecord.identity =
      allIdentities source siteSource := by
    simp [toFiniteData, List.map_map, Function.comp_def]
  constructor
  · rw [keys]
    exact allIdentities_nodup source siteSource
  · intro identity
    rw [keys]
    exact mem_allIdentities source siteSource identity

namespace FiniteSiteData

/-- Relabel finite site data exactly: every identity is transported by the atom relabelling and
every recorded geometry is retained unchanged. -/
def relabel {source source' : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source}
    {siteSource' : ElectronicSiteSource source'}
    (data : FiniteSiteData source siteSource)
    (relabel : AtomRelabel source source' siteSource siteSource') :
    FiniteSiteData source' siteSource' :=
  data.map fun record =>
    { identity := relabel.siteIdentityEquiv record.identity, geometry := record.geometry }

@[simp] theorem relabel_length {source source' : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source}
    {siteSource' : ElectronicSiteSource source'}
    (data : FiniteSiteData source siteSource)
    (relabel : AtomRelabel source source' siteSource siteSource') :
    (data.relabel relabel).length = data.length := by
  simp [FiniteSiteData.relabel]

/-- Relabelling preserves validity: the image data still contains every transported identity
exactly once. -/
theorem relabel_valid {source source' : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source}
    {siteSource' : ElectronicSiteSource source'}
    (data : FiniteSiteData source siteSource)
    (relabel : AtomRelabel source source' siteSource siteSource')
    (valid : data.Valid) :
    (data.relabel relabel).Valid := by
  have keys : (data.relabel relabel).map SiteRecord.identity =
      data.map fun record => relabel.siteIdentityEquiv record.identity := by
    simp [FiniteSiteData.relabel, List.map_map, Function.comp_def]
  constructor
  · rw [keys]
    simpa [Function.comp_def] using
      List.Nodup.map relabel.siteIdentityEquiv.injective valid.1
  · intro identity'
    rw [keys]
    rcases relabel.siteIdentityEquiv.surjective identity' with ⟨identity, identityEq⟩
    rcases List.mem_map.mp (valid.2 identity) with ⟨record, present, recordIdentity⟩
    refine List.mem_map.mpr ⟨record, present, ?_⟩
    change relabel.siteIdentityEquiv record.identity = identity'
    rw [recordIdentity]
    exact identityEq

end FiniteSiteData

/-- Compile an indexed representation to evidence-level finite data, retaining supplied/unknown
geometry provenance alongside every individual identity. -/
noncomputable def toFiniteEvidence (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (indexed : IndexedSiteGeometry source siteSource) :
    FiniteSiteEvidenceData source siteSource :=
  (allIdentities source siteSource).map fun identity =>
    { identity := identity, evidence := (indexed.geometryAt identity).toEvidence }

/-- Every individual identity appears in evidence compilation with exactly its indexed geometry
evidence. -/
theorem mem_toFiniteEvidence (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (indexed : IndexedSiteGeometry source siteSource)
    (identity : SiteIdentity source siteSource) :
    ∃ record ∈ toFiniteEvidence source siteSource indexed,
      record.identity = identity ∧
        record.evidence = (indexed.geometryAt identity).toEvidence := by
  refine ⟨{ identity := identity, evidence := (indexed.geometryAt identity).toEvidence },
    List.mem_map.mpr ⟨identity, mem_allIdentities source siteSource identity, rfl⟩,
    rfl, rfl⟩

/-- Compile finite data to its indexed representation.  The origin default is unreachable on valid
data; `toIndexed_geometryAt_of_lookup` states the exact result. -/
noncomputable def toIndexed (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (data : FiniteSiteData source siteSource) (_valid : data.Valid) :
    IndexedSiteGeometry source siteSource where
  geometryAt identity :=
    Option.getD
      (Option.map SiteRecord.geometry (FiniteSiteData.lookup? data identity))
      ReferenceGeometry.origin

/-- On a successful lookup, the indexed geometry is exactly the stored record geometry. -/
theorem toIndexed_geometryAt_of_lookup (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (data : FiniteSiteData source siteSource) (valid : data.Valid)
    {identity : SiteIdentity source siteSource} {record : SiteRecord source siteSource}
    (found : FiniteSiteData.lookup? data identity = some record) :
    (toIndexed source siteSource data valid).geometryAt identity = record.geometry := by
  simp [toIndexed, found]

/-- Every stored record's owner, kind, slot, and real point are preserved by compilation to the
indexed representation. -/
theorem toIndexed_geometryAt_of_mem (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (data : FiniteSiteData source siteSource) (valid : data.Valid)
    {record : SiteRecord source siteSource} (present : record ∈ data) :
    (toIndexed source siteSource data valid).geometryAt record.identity = record.geometry := by
  apply toIndexed_geometryAt_of_lookup source siteSource data valid
  exact (FiniteSiteData.lookup?_eq_some_iff_of_nodup data valid.1
    record.identity record).mpr ⟨present, rfl⟩

/-- On valid finite data the internal origin default is never surfaced: every indexed geometry is
the geometry of an explicitly stored record. -/
theorem toIndexed_geometryAt_sourced_of_valid (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (data : FiniteSiteData source siteSource) (valid : data.Valid)
    (identity : SiteIdentity source siteSource) :
    ∃ record ∈ data,
      (toIndexed source siteSource data valid).geometryAt identity = record.geometry := by
  rcases FiniteSiteData.lookup?_exists_of_valid data valid identity with ⟨record, found⟩
  have present : record ∈ data :=
    ((FiniteSiteData.lookup?_eq_some_iff_of_nodup data valid.1 identity record).mp found).1
  exact ⟨record, present,
    toIndexed_geometryAt_of_lookup source siteSource data valid found⟩

/-- Round trip: compiling the canonical data back to an indexed representation recovers the
original indexed representation exactly. -/
theorem toIndexed_toFiniteData (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (indexed : IndexedSiteGeometry source siteSource) :
    toIndexed source siteSource (toFiniteData source siteSource indexed)
        (valid_toFiniteData source siteSource indexed) = indexed := by
  apply IndexedSiteGeometry.ext
  intro identity
  exact toIndexed_geometryAt_of_mem source siteSource (toFiniteData source siteSource indexed)
    (valid_toFiniteData source siteSource indexed)
    (record := { identity := identity, geometry := indexed.geometryAt identity })
    (List.mem_map.mpr ⟨identity, mem_allIdentities source siteSource identity, rfl⟩)

/-- Every canonical record is present, with the exact stored geometry. -/
theorem mem_toFiniteData_iff (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (indexed : IndexedSiteGeometry source siteSource)
    (record : SiteRecord source siteSource) :
    record ∈ toFiniteData source siteSource indexed ↔
      record.identity ∈ allIdentities source siteSource ∧
        record.geometry = indexed.geometryAt record.identity := by
  unfold toFiniteData
  rw [List.mem_map]
  constructor
  · rintro ⟨identity, present, equal⟩
    cases equal
    exact ⟨present, rfl⟩
  · rintro ⟨present, geometryEq⟩
    refine ⟨record.identity, present, ?_⟩
    cases record
    simpa using geometryEq.symm

/-- Two configurations over the same supplied inventory may differ in every site geometry. -/
def constantGeometry (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (geometry : ReferenceGeometry) :
    IndexedSiteGeometry source siteSource where
  geometryAt _ := geometry

theorem exists_distinct_geometries_same_inventory
    (source : AuthoritativeChemicalInput) (siteSource : ElectronicSiteSource source)
    (identity : SiteIdentity source siteSource) :
    ∃ left right : IndexedSiteGeometry source siteSource,
      left ≠ right ∧ left.geometryAt identity ≠ right.geometryAt identity := by
  refine ⟨constantGeometry source siteSource ReferenceGeometry.origin,
    constantGeometry source siteSource ReferenceGeometry.unitX, ?_, ?_⟩
  · intro equal
    have pointEq := congrArg (fun indexed => indexed.geometryAt identity) equal
    exact ReferenceGeometry.origin_ne_unitX pointEq
  · exact ReferenceGeometry.origin_ne_unitX

/-! ## Embedding the legacy rational P-94 ledger -/

/-- The raw index carried by a legacy participant. -/
def legacyParticipantIndex : VirtualTorsionParticipant → ℕ
  | .lonePair center => center
  | .duplicateAtom original => original

/-- The expanded site kind corresponding to a legacy participant.  A duplicate atom retains its
CIP virtual-duplicate role; it is not reinterpreted as an electron pair. -/
def legacySiteKind : VirtualTorsionParticipant → SiteKind
  | .lonePair _ => .electronic .lonePair
  | .duplicateAtom _ => .cipReference .virtualDuplicate

/-- A bounded source owner together with a chosen lone-pair slot for one legacy centre. -/
structure LonePairLegacyAssignment (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (center : ℕ) where
  owner : source.AromaticCanonicalAtom
  owner_eq : owner.val = center
  slot : Fin ((siteSource.counts owner).count (.electronic .lonePair))

/-- A bounded source owner together with a chosen virtual-duplicate slot for one legacy duplicate
atom. -/
structure DuplicateLegacyAssignment (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (original : ℕ) where
  owner : source.AromaticCanonicalAtom
  owner_eq : owner.val = original
  slot : Fin ((siteSource.counts owner).count (.cipReference .virtualDuplicate))

/-- An explicit expanded assignment for one legacy participant occurrence. -/
inductive LegacySiteAssignment (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) : VirtualTorsionParticipant → Type
  | lonePair {center : ℕ}
      (assignment : LonePairLegacyAssignment source siteSource center) :
      LegacySiteAssignment source siteSource (.lonePair center)
  | duplicate {original : ℕ}
      (assignment : DuplicateLegacyAssignment source siteSource original) :
      LegacySiteAssignment source siteSource (.duplicateAtom original)

/-- The expanded identity assigned to one legacy participant occurrence. -/
def legacySiteIdentity (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (participant : VirtualTorsionParticipant)
    (assignment : LegacySiteAssignment source siteSource participant) :
    SiteIdentity source siteSource :=
  match participant, assignment with
  | .lonePair _, .lonePair assignment =>
      ⟨assignment.owner, .electronic .lonePair, assignment.slot⟩
  | .duplicateAtom _, .duplicate assignment =>
      ⟨assignment.owner, .cipReference .virtualDuplicate, assignment.slot⟩

/-- The assigned owner is the actual bounded source owner of the legacy participant. -/
@[simp] theorem legacySiteIdentity_owner_val (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (participant : VirtualTorsionParticipant)
    (assignment : LegacySiteAssignment source siteSource participant) :
    (legacySiteIdentity source siteSource participant assignment).owner.val =
      legacyParticipantIndex participant := by
  cases participant with
  | lonePair center =>
      cases assignment with
      | lonePair assignment => exact assignment.owner_eq
  | duplicateAtom original =>
      cases assignment with
      | duplicate assignment => exact assignment.owner_eq

/-- The assigned kind preserves the legacy role: a lone pair stays a lone pair, and a duplicate
atom stays a CIP virtual duplicate. -/
@[simp] theorem legacySiteIdentity_kind (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (participant : VirtualTorsionParticipant)
    (assignment : LegacySiteAssignment source siteSource participant) :
    (legacySiteIdentity source siteSource participant assignment).kind =
      legacySiteKind participant := by
  cases participant with
  | lonePair center =>
      cases assignment with
      | lonePair assignment => rfl
  | duplicateAtom original =>
      cases assignment with
      | duplicate assignment => rfl

/-- Distinct legacy participants give distinct expanded identities, whatever slots are chosen. -/
theorem legacySiteIdentity_injective (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    {participant₁ participant₂ : VirtualTorsionParticipant}
    {assignment₁ : LegacySiteAssignment source siteSource participant₁}
    {assignment₂ : LegacySiteAssignment source siteSource participant₂}
    (identityEq :
      legacySiteIdentity source siteSource participant₁ assignment₁ =
        legacySiteIdentity source siteSource participant₂ assignment₂) :
    participant₁ = participant₂ := by
  cases participant₁ with
  | lonePair center₁ =>
      cases assignment₁ with
      | lonePair assignment₁ =>
          cases participant₂ with
          | lonePair center₂ =>
              cases assignment₂ with
              | lonePair assignment₂ =>
                  have ownerValueEq :=
                    congrArg (fun identity => identity.owner.val) identityEq
                  have centers : center₁ = center₂ := by
                    simpa [legacySiteIdentity_owner_val, legacyParticipantIndex] using
                      ownerValueEq
                  exact congrArg VirtualTorsionParticipant.lonePair centers
          | duplicateAtom original₂ =>
              cases assignment₂ with
              | duplicate assignment₂ =>
                  have kindEq := congrArg SiteIdentity.kind identityEq
                  simp [legacySiteIdentity_kind, legacySiteKind] at kindEq
  | duplicateAtom original₁ =>
      cases assignment₁ with
      | duplicate assignment₁ =>
          cases participant₂ with
          | lonePair center₂ =>
              cases assignment₂ with
              | lonePair assignment₂ =>
                  have kindEq := congrArg SiteIdentity.kind identityEq
                  simp [legacySiteIdentity_kind, legacySiteKind] at kindEq
          | duplicateAtom original₂ =>
              cases assignment₂ with
              | duplicate assignment₂ =>
                  have ownerValueEq :=
                    congrArg (fun identity => identity.owner.val) identityEq
                  have originals : original₁ = original₂ := by
                    simpa [legacySiteIdentity_owner_val, legacyParticipantIndex] using
                      ownerValueEq
                  exact congrArg VirtualTorsionParticipant.duplicateAtom originals

/-- Embed one participant with an explicitly supplied real direction.  No direction is fabricated:
the caller supplies it for this occurrence. -/
def embedParticipant (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    (participant : VirtualTorsionParticipant) (point : CartesianPoint3)
    (direction : RealDirection3)
    (assignment : LegacySiteAssignment source siteSource participant) :
    SiteRecord source siteSource :=
  { identity := legacySiteIdentity source siteSource participant assignment
    geometry := { point := realPointOfRat point, direction := direction } }

/-- Embed one legacy ledger entry with the direction supplied for that occurrence. -/
def embedLedgerEntry (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (entry : VirtualTorsionPoint)
    (assignment : LegacySiteAssignment source siteSource entry.participant)
    (direction : RealDirection3) :
    SiteRecord source siteSource :=
  embedParticipant source siteSource entry.participant entry.point direction assignment

/-- The embedded owner is the actual bounded source owner of the legacy participant. -/
@[simp] theorem embedLedgerEntry_owner_val (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (entry : VirtualTorsionPoint)
    (assignment : LegacySiteAssignment source siteSource entry.participant)
    (direction : RealDirection3) :
    (embedLedgerEntry source siteSource entry assignment direction).identity.owner.val =
      legacyParticipantIndex entry.participant :=
  legacySiteIdentity_owner_val source siteSource entry.participant assignment

/-- The embedded kind preserves the legacy role. -/
@[simp] theorem embedLedgerEntry_kind (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (entry : VirtualTorsionPoint)
    (assignment : LegacySiteAssignment source siteSource entry.participant)
    (direction : RealDirection3) :
    (embedLedgerEntry source siteSource entry assignment direction).identity.kind =
      legacySiteKind entry.participant :=
  legacySiteIdentity_kind source siteSource entry.participant assignment

/-- The embedded real point is exactly the cast of the legacy rational point. -/
@[simp] theorem embedLedgerEntry_point (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (entry : VirtualTorsionPoint)
    (assignment : LegacySiteAssignment source siteSource entry.participant)
    (direction : RealDirection3) :
    (embedLedgerEntry source siteSource entry assignment direction).geometry.point =
      realPointOfRat entry.point :=
  rfl

/-- The embedded direction is exactly the independently supplied direction, never a fabrication. -/
@[simp] theorem embedLedgerEntry_direction (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (entry : VirtualTorsionPoint)
    (assignment : LegacySiteAssignment source siteSource entry.participant)
    (direction : RealDirection3) :
    (embedLedgerEntry source siteSource entry assignment direction).geometry.direction =
      direction :=
  rfl

/-- Distinct legacy participants give distinct expanded identities. -/
theorem embedLedgerEntry_identity_injective (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source)
    {entry₁ entry₂ : VirtualTorsionPoint}
    {assignment₁ : LegacySiteAssignment source siteSource entry₁.participant}
    {assignment₂ : LegacySiteAssignment source siteSource entry₂.participant}
    {direction₁ direction₂ : RealDirection3}
    (identityEq :
      (embedLedgerEntry source siteSource entry₁ assignment₁ direction₁).identity =
        (embedLedgerEntry source siteSource entry₂ assignment₂ direction₂).identity) :
    entry₁.participant = entry₂.participant := by
  cases entry₁ with
  | mk participant₁ point₁ =>
      cases entry₂ with
      | mk participant₂ point₂ =>
          exact legacySiteIdentity_injective source siteSource identityEq

/-- Embed the legacy ledger using assignments indexed by actual occurrences.  The assignment is a
function on `Fin ledger.length`; no assignment is required for a participant outside the ledger. -/
def embedLedger (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (ledger : VirtualTorsionPointLedger)
    (assignment : (index : Fin ledger.length) →
      LegacySiteAssignment source siteSource (ledger.get index).participant)
    (direction : (index : Fin ledger.length) → RealDirection3) :
    FiniteSiteData source siteSource :=
  List.ofFn fun index =>
    embedLedgerEntry source siteSource (ledger.get index) (assignment index) (direction index)

@[simp] theorem embedLedger_length (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (ledger : VirtualTorsionPointLedger)
    (assignment : (index : Fin ledger.length) →
      LegacySiteAssignment source siteSource (ledger.get index).participant)
    (direction : (index : Fin ledger.length) → RealDirection3) :
    (embedLedger source siteSource ledger assignment direction).length = ledger.length := by
  simp [embedLedger]

/-- The empty legacy ledger embeds with no assignment or direction premise. -/
def emptyLedgerEmbedding (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) : FiniteSiteData source siteSource :=
  embedLedger source siteSource [] (fun index => Fin.elim0 index)
    (fun index => Fin.elim0 index)

@[simp] theorem emptyLedgerEmbedding_eq_nil (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) :
    emptyLedgerEmbedding source siteSource = [] :=
  rfl

/-- Every occurrence is preserved with its exact owner, legacy role, real point, and independently
supplied direction. -/
theorem embedLedger_entry_preserved (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (ledger : VirtualTorsionPointLedger)
    (assignment : (index : Fin ledger.length) →
      LegacySiteAssignment source siteSource (ledger.get index).participant)
    (direction : (index : Fin ledger.length) → RealDirection3)
    (index : Fin ledger.length) :
    ∃ record ∈ embedLedger source siteSource ledger assignment direction,
      record.identity.owner.val = legacyParticipantIndex (ledger.get index).participant ∧
        record.identity.kind = legacySiteKind (ledger.get index).participant ∧
        record.geometry.point = realPointOfRat (ledger.get index).point ∧
        record.geometry.direction = direction index := by
  refine ⟨embedLedgerEntry source siteSource (ledger.get index) (assignment index)
      (direction index), List.mem_ofFn.mpr ⟨index, rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact embedLedgerEntry_owner_val source siteSource (ledger.get index) (assignment index)
      (direction index)
  · exact embedLedgerEntry_kind source siteSource (ledger.get index) (assignment index)
      (direction index)
  · exact embedLedgerEntry_point source siteSource (ledger.get index) (assignment index)
      (direction index)
  · exact embedLedgerEntry_direction source siteSource (ledger.get index) (assignment index)
      (direction index)

/-- Every old ledger entry occurs in the expanded data with its exact owner, legacy role, and real
point. -/
theorem embedLedger_all_entries_preserved (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (ledger : VirtualTorsionPointLedger)
    (assignment : (index : Fin ledger.length) →
      LegacySiteAssignment source siteSource (ledger.get index).participant)
    (direction : (index : Fin ledger.length) → RealDirection3) :
    ∀ entry ∈ ledger,
      ∃ index : Fin ledger.length,
        ledger.get index = entry ∧
          ∃ record ∈ embedLedger source siteSource ledger assignment direction,
            record.identity.owner.val = legacyParticipantIndex entry.participant ∧
              record.identity.kind = legacySiteKind entry.participant ∧
              record.geometry.point = realPointOfRat entry.point := by
  intro entry present
  rcases List.mem_iff_get.mp present with ⟨index, getEq⟩
  subst entry
  refine ⟨index, rfl, ?_⟩
  rcases embedLedger_entry_preserved source siteSource ledger assignment direction index with
    ⟨record, member, ownerEq, kindEq, pointEq, _⟩
  exact ⟨record, member, ownerEq, kindEq, pointEq⟩

/-- A valid legacy ledger embeds as duplicate-free expanded data with occurrence-indexed
assignments. -/
theorem embedLedger_nodup (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (ledger : VirtualTorsionPointLedger)
    (valid : VirtualTorsionPointLedger.Valid ledger)
    (assignment : (index : Fin ledger.length) →
      LegacySiteAssignment source siteSource (ledger.get index).participant)
    (direction : (index : Fin ledger.length) → RealDirection3) :
    (embedLedger source siteSource ledger assignment direction).Nodup := by
  have participantNodup :
      (ledger.map VirtualTorsionPoint.participant).Nodup := by
    simpa [VirtualTorsionPointLedger.Valid, VirtualTorsionPointLedger.keys] using valid
  have ledgerNodup : ledger.Nodup :=
    List.Nodup.of_map VirtualTorsionPoint.participant participantNodup
  have participantInjective :=
    List.inj_on_of_nodup_map (f := VirtualTorsionPoint.participant) participantNodup
  unfold embedLedger
  apply List.nodup_ofFn.mpr
  intro index₁ index₂ recordEq
  have identityEq := congrArg SiteRecord.identity recordEq
  have participantEq :=
    embedLedgerEntry_identity_injective source siteSource identityEq
  have entryEq : ledger.get index₁ = ledger.get index₂ :=
    participantInjective (List.get_mem ledger index₁) (List.get_mem ledger index₂)
      participantEq
  exact ledgerNodup.get_inj_iff.mp entryEq

/-- Embed the legacy ledger into evidence-level records.  Each occurrence keeps its supplied point
and explicitly records that no direction was supplied. -/
def embedLedgerEvidence (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (ledger : VirtualTorsionPointLedger)
    (assignment : (index : Fin ledger.length) →
      LegacySiteAssignment source siteSource (ledger.get index).participant) :
    FiniteSiteEvidenceData source siteSource :=
  List.ofFn fun index =>
    { identity :=
        legacySiteIdentity source siteSource (ledger.get index).participant (assignment index)
      evidence := ReferenceGeometryEvidence.ofRationalPoint (ledger.get index).point }

@[simp] theorem embedLedgerEvidence_length (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (ledger : VirtualTorsionPointLedger)
    (assignment : (index : Fin ledger.length) →
      LegacySiteAssignment source siteSource (ledger.get index).participant) :
    (embedLedgerEvidence source siteSource ledger assignment).length = ledger.length := by
  simp [embedLedgerEvidence]

/-- The empty legacy ledger embeds into evidence-level data without any absurd premise. -/
def emptyLedgerEvidenceEmbedding (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) : FiniteSiteEvidenceData source siteSource :=
  embedLedgerEvidence source siteSource [] (fun index => Fin.elim0 index)

@[simp] theorem emptyLedgerEvidenceEmbedding_eq_nil (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) :
    emptyLedgerEvidenceEmbedding source siteSource = [] :=
  rfl

/-- Every legacy occurrence is preserved at evidence level with its point and with direction
absence recorded distinctly from an explicitly zero direction. -/
theorem embedLedgerEvidence_entry_preserved (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (ledger : VirtualTorsionPointLedger)
    (assignment : (index : Fin ledger.length) →
      LegacySiteAssignment source siteSource (ledger.get index).participant)
    (index : Fin ledger.length) :
    ∃ record ∈ embedLedgerEvidence source siteSource ledger assignment,
      record.identity.owner.val = legacyParticipantIndex (ledger.get index).participant ∧
        record.identity.kind = legacySiteKind (ledger.get index).participant ∧
        record.evidence.point? = some (realPointOfRat (ledger.get index).point) ∧
        record.evidence.direction? = none := by
  refine ⟨{ identity :=
              legacySiteIdentity source siteSource (ledger.get index).participant
                (assignment index)
            evidence :=
              ReferenceGeometryEvidence.ofRationalPoint (ledger.get index).point },
    List.mem_ofFn.mpr ⟨index, rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact legacySiteIdentity_owner_val source siteSource (ledger.get index).participant
      (assignment index)
  · exact legacySiteIdentity_kind source siteSource (ledger.get index).participant
      (assignment index)
  · rfl
  · rfl

/-- Every old ledger entry occurs at evidence level with its exact owner, legacy role, and real
point, and with direction absence. -/
theorem embedLedgerEvidence_all_entries_preserved (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (ledger : VirtualTorsionPointLedger)
    (assignment : (index : Fin ledger.length) →
      LegacySiteAssignment source siteSource (ledger.get index).participant) :
    ∀ entry ∈ ledger,
      ∃ index : Fin ledger.length,
        ledger.get index = entry ∧
          ∃ record ∈ embedLedgerEvidence source siteSource ledger assignment,
            record.identity.owner.val = legacyParticipantIndex entry.participant ∧
              record.identity.kind = legacySiteKind entry.participant ∧
              record.evidence.point? = some (realPointOfRat entry.point) ∧
              record.evidence.direction? = none := by
  intro entry present
  rcases List.mem_iff_get.mp present with ⟨index, getEq⟩
  subst entry
  refine ⟨index, rfl, ?_⟩
  rcases embedLedgerEvidence_entry_preserved source siteSource ledger assignment index with
    ⟨record, member, ownerEq, kindEq, pointEq, directionEq⟩
  exact ⟨record, member, ownerEq, kindEq, pointEq, directionEq⟩

/-- A valid legacy ledger embeds as duplicate-free evidence-level data. -/
theorem embedLedgerEvidence_nodup (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) (ledger : VirtualTorsionPointLedger)
    (valid : VirtualTorsionPointLedger.Valid ledger)
    (assignment : (index : Fin ledger.length) →
      LegacySiteAssignment source siteSource (ledger.get index).participant) :
    (embedLedgerEvidence source siteSource ledger assignment).Nodup := by
  have participantNodup :
      (ledger.map VirtualTorsionPoint.participant).Nodup := by
    simpa [VirtualTorsionPointLedger.Valid, VirtualTorsionPointLedger.keys] using valid
  have ledgerNodup : ledger.Nodup :=
    List.Nodup.of_map VirtualTorsionPoint.participant participantNodup
  have participantInjective :=
    List.inj_on_of_nodup_map (f := VirtualTorsionPoint.participant) participantNodup
  unfold embedLedgerEvidence
  apply List.nodup_ofFn.mpr
  intro index₁ index₂ recordEq
  have identityEq := congrArg SiteEvidenceRecord.identity recordEq
  have participantEq :=
    legacySiteIdentity_injective source siteSource identityEq
  have entryEq : ledger.get index₁ = ledger.get index₂ :=
    participantInjective (List.get_mem ledger index₁) (List.get_mem ledger index₂)
      participantEq
  exact ledgerNodup.get_inj_iff.mp entryEq

/-! ## Selected reverse projection to the legacy centre-only key -/

/-- An explicit selection of an expanded site that has a legacy counterpart.  Projection is
defined only on this selection, never on an arbitrary identity. -/
inductive SelectedLegacySite (source : AuthoritativeChemicalInput)
    (siteSource : ElectronicSiteSource source) : Type
  | lonePair (owner : source.AromaticCanonicalAtom)
      (slot : Fin ((siteSource.counts owner).count (.electronic .lonePair))) :
      SelectedLegacySite source siteSource
  | duplicate (owner : source.AromaticCanonicalAtom)
      (slot : Fin ((siteSource.counts owner).count (.cipReference .virtualDuplicate))) :
      SelectedLegacySite source siteSource

namespace SelectedLegacySite

/-- The selected site's individual identity. -/
def identity {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source} :
    SelectedLegacySite source siteSource → SiteIdentity source siteSource
  | .lonePair owner slot => ⟨owner, .electronic .lonePair, slot⟩
  | .duplicate owner slot => ⟨owner, .cipReference .virtualDuplicate, slot⟩

/-- The legacy centre-only key produced by an explicit selection. -/
def toLegacyParticipant {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source} :
    SelectedLegacySite source siteSource → VirtualTorsionParticipant
  | .lonePair owner _ => .lonePair owner.val
  | .duplicate owner _ => .duplicateAtom owner.val

@[simp] theorem identity_lonePair {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source} (owner : source.AromaticCanonicalAtom)
    (slot : Fin ((siteSource.counts owner).count (.electronic .lonePair))) :
    (lonePair owner slot).identity =
      (⟨owner, .electronic .lonePair, slot⟩ : SiteIdentity source siteSource) :=
  rfl

@[simp] theorem identity_duplicate {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source} (owner : source.AromaticCanonicalAtom)
    (slot : Fin ((siteSource.counts owner).count (.cipReference .virtualDuplicate))) :
    (duplicate owner slot).identity =
      (⟨owner, .cipReference .virtualDuplicate, slot⟩ : SiteIdentity source siteSource) :=
  rfl

@[simp] theorem toLegacyParticipant_lonePair {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source} (owner : source.AromaticCanonicalAtom)
    (slot : Fin ((siteSource.counts owner).count (.electronic .lonePair))) :
    (lonePair owner slot).toLegacyParticipant = .lonePair owner.val :=
  rfl

@[simp] theorem toLegacyParticipant_duplicate {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source} (owner : source.AromaticCanonicalAtom)
    (slot : Fin ((siteSource.counts owner).count (.cipReference .virtualDuplicate))) :
    (duplicate owner slot).toLegacyParticipant = .duplicateAtom owner.val :=
  rfl

/-- Explicit selection preserves the individual identity: distinct selected lone-pair slots remain
distinct expanded identities. -/
theorem lonePair_identity_injective {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source} (owner : source.AromaticCanonicalAtom) :
    Function.Injective fun slot :
        Fin ((siteSource.counts owner).count (.electronic .lonePair)) =>
      (lonePair owner slot).identity := by
  intro slot₁ slot₂ equal
  have valueEq : slot₁.val = slot₂.val :=
    congrArg (fun identity : SiteIdentity source siteSource => identity.slot.val) equal
  exact Fin.ext valueEq

/-- Projection to the centre-only legacy key forgets the slot. -/
theorem lonePair_projection_collapses {source : AuthoritativeChemicalInput}
    {siteSource : ElectronicSiteSource source} (owner : source.AromaticCanonicalAtom)
    (slot₁ slot₂ : Fin ((siteSource.counts owner).count (.electronic .lonePair))) :
    (lonePair owner slot₁).toLegacyParticipant =
      (lonePair owner slot₂).toLegacyParticipant :=
  rfl

/-- With at least two supplied lone pairs at one atom, the legacy projection is not lossless:
two distinct individual sites share one centre-only key. -/
theorem multiple_lonePairs_projection_not_lossless
    (source : AuthoritativeChemicalInput) (siteSource : ElectronicSiteSource source)
    (owner : source.AromaticCanonicalAtom)
    (two : 2 ≤ (siteSource.counts owner).count (.electronic .lonePair)) :
    ∃ slot₁ slot₂ : Fin ((siteSource.counts owner).count (.electronic .lonePair)),
      slot₁ ≠ slot₂ ∧
        (SelectedLegacySite.lonePair owner slot₁).identity ≠
          (SelectedLegacySite.lonePair owner slot₂).identity ∧
        (SelectedLegacySite.lonePair owner slot₁).toLegacyParticipant =
          (SelectedLegacySite.lonePair owner slot₂).toLegacyParticipant := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, ?_, rfl⟩
  · intro equal
    have valueEq : (0 : ℕ) = 1 := congrArg Fin.val equal
    omega
  · intro equal
    have valueEq : (0 : ℕ) = 1 :=
      congrArg (fun identity : SiteIdentity source siteSource => identity.slot.val) equal
    omega

end SelectedLegacySite

/-- The legacy centre-only key is unambiguous exactly when at most one lone pair is supplied at
the owner. -/
theorem legacyLonePairSlot_subsingleton_iff
    (source : AuthoritativeChemicalInput) (siteSource : ElectronicSiteSource source)
    (owner : source.AromaticCanonicalAtom) :
    Subsingleton (Fin ((siteSource.counts owner).count (.electronic .lonePair))) ↔
      (siteSource.counts owner).count (.electronic .lonePair) ≤ 1 :=
  Fin.subsingleton_iff_le_one

end OrganicStereoElectronicSites
end TetraStereo.OneCenter
