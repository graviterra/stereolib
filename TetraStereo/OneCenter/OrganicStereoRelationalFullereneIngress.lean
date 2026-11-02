import TetraStereo.OneCenter.IUPACP93RelationalFullereneAuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress

set_option autoImplicit false

/-!
# Native ingress for the relational P-93 fullerene authority carrier

`IUPACP93RelationalFullereneAuthorityCarrier` is the relational ownership boundary for the five
fullerene derivative rows.  Its whole-addend substituent corpus, its exact ordered addend family
and its cage assignment are atom-indexed; the surrounding source family
(`RelationalSourceOrientedMolecularFullereneConfigurationInput`) is a `RawMolecule`-indexed,
proof-carrying dependent record.

This module supplies a concrete, lossless codec for that carrier.  The codec is deliberately
split by what the carrier's own validity actually bounds.

## Natively relabelled data

The following fields contain raw `Nat` atom references and are relabelled to an arbitrary finite
atom type `V` through an explicit enumeration `e : V ≃ Fin n`:

* `MolecularFullereneAddend`: the complete external atom set, the complete ordered-port set
  (a port is an ordered pair, so its orientation is preserved), and the identity class.  The
  addend is never truncated to its attachment sites: `attachmentPorts` and `identityClass` are
  carried whole.
* `P93FullereneSubstituentStereogenicUnit`: all seven constructors.  The legacy physical-unit
  codec `OrganicStereoSuppliedCitationIngress.relabelUnit` is *not* sufficient here, because
  `doubleBond` and `bondAxis` both project to `.bond`; the constructor distinction is preserved
  by a dedicated seven-constructor mirror and the projection is proved to commute with the
  legacy codec.
* `P93RelationalFullereneSubstituentCIPAssignment`: the whole-addend owner, the typed unit, the
  citation token and the CIP descriptor.  Citation components and prime counts are nomenclature
  data, not atom indices, and are copied literally; descriptors are copied literally.
* `FullereneConfigurationAssignment.unit` (the sorted cage identity) is relabelled; the
  chirality type and descriptor payload list are copied literally.
* `observation.addends`, `observation.chiralAddends` and
  `observation.substituentAssignments`.

## Explicitly retained raw source syntax

The dependent input family `observation.inputs`, the separate `observation.selectedInput`, the
raw `observation.molecule` and the optional `observation.spatial?` are retained literally.  This
is not an escape from the codec: the fields are part of the native record and the decoder reads
them back unchanged.

The reason is concrete.  `RelationalSymmetryDerivedMolecularFullereneConfigurationInput.evidence`
is a `MolecularFullereneAddendRelationalEvidence molecule carrier`: a record whose fields are
proofs about the raw `Nat` molecule (`addend.ValidFor molecule carrier`, exact port partitions,
constitutional isomorphism against raw bond orders).  Those fields are not invariant under an
arbitrary relabelling `V ≃ Fin n`, and proving such an invariance would be a new chemical
theorem, not a codec.  Moreover, only the *selected* input is judged by
`RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment`; the other family members
are constrained only by the arbitrary policy relation `InputFamilyObserved`, so their atom
indices are not bounded by the carrier's own `ValidFor` at all.  Reindexing them would therefore
require either an unproved invariance theorem or a new boundedness restriction.  They are
preserved as explicit independent raw source syntax, exactly as the input boundary carries them,
and they are bound by the actual `structureAgreement`, `selectedInputJudged` and `InputObserved`
obligations of `ValidFor` — never replaced by the weaker `policy.RawMoleculeObserved` relation.

## Bounds

The codec takes explicit boundedness hypotheses.  Where the carrier's own `ValidFor` supplies
them they are *derived*, never assumed:

* addend external atoms are bounded by `MolecularFullereneAddend.ValidFor`'s
  `ExternalPartitionJudgment`;
* port sites are bounded because `PortJudgment` places every site in the checked cage carrier,
  and cage atoms are in-bounds carbon atoms (`MolecularFullereneCarrierJudgment.carbonAtoms`);
* every stereogenic-unit atom lies in the owner's external atom set by the assignment's
  `unitOwned` field;
* the assignment unit is the sorted cage carrier by
  `FullereneConfigurationAssignmentJudgment`.

No atom index is invented, no addend is projected to one site, and no count-only agreement is
used: the shared context is the existing `PhysicalFrameSourceBinding`, whose graph, spatial and
diagram channels are tied to the authoritative input by actual equalities.

## What is not claimed

`ValidFor` is transported only through the exact record equality
`unrelabelObservation (relabelObservation observation) = observation`, at the same `source` and
`policy`.  This module does not claim invariance of any policy predicate under an arbitrary
permutation of atom indices, and it does not construct chemical validity, descriptors, citations
or source authorization.
-/

namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic
open OrganicStereoSuppliedCitationIngress

namespace OrganicStereoRelationalFullereneIngress

variable {V : Type*} {n : ℕ} {policy : P93RelationalFullereneAuthorityPolicy}

/-! ## Generic finite-set image inverses

These two lemmas factor out the `Finset.attach`/`Finset.image` pattern used below.  A relabelling
function is allowed to depend on the membership proof of its argument; only its left/right
inverse on the value is used. -/

theorem finset_image_unrelabel_relabel
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α)
    (relabel : (a : α) → a ∈ s → β) (unrelabel : β → α)
    (leftInv : ∀ a ha, unrelabel (relabel a ha) = a) :
    (s.attach.image fun a => relabel a.1 a.2).image unrelabel = s := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, hEq⟩ := Finset.mem_image.mp ha
    obtain ⟨attached, _hattached, rfl⟩ := Finset.mem_image.mp hb
    rw [leftInv] at hEq
    rw [← hEq]
    exact attached.2
  · intro ha
    exact Finset.mem_image.mpr ⟨relabel a ha,
      Finset.mem_image_of_mem (fun x : {x // x ∈ s} => relabel x.1 x.2)
        (Finset.mem_attach s ⟨a, ha⟩),
      leftInv a ha⟩

theorem finset_image_relabel_unrelabel
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset β) (unrelabel : β → α)
    (relabel : (a : α) → a ∈ s.image unrelabel → β)
    (rightInv : ∀ b hb, relabel (unrelabel b) hb = b) :
    (s.image unrelabel).attach.image (fun a => relabel a.1 a.2) = s := by
  ext b
  constructor
  · intro hb
    obtain ⟨attached, _hattached, hEq⟩ := Finset.mem_image.mp hb
    obtain ⟨source, sourceMem, hSource⟩ := Finset.mem_image.mp attached.2
    have attachedEq : attached =
        ⟨unrelabel source, Finset.mem_image_of_mem unrelabel sourceMem⟩ :=
      Subtype.ext hSource.symm
    subst attached
    have bEq : b = source := by
      rw [← hEq]
      exact rightInv source _
    rw [bEq]
    exact sourceMem
  · intro hb
    exact Finset.mem_image.mpr
      ⟨⟨unrelabel b, Finset.mem_image_of_mem unrelabel hb⟩, Finset.mem_attach _ _,
        rightInv b _⟩

/-! ## Ordered pairs of atom indices -/

/-- Relabel a finite set of ordered raw atom pairs into `V`.  The pair order is preserved:
`(site, externalAtom)` and `(externalAtom, site)` remain distinct. -/
def relabelNatPairs [DecidableEq V] (e : V ≃ Fin n) (pairs : Finset (Nat × Nat))
    (bounded : ∀ pair ∈ pairs, pair.1 < n ∧ pair.2 < n) : Finset (V × V) :=
  pairs.attach.image fun pair =>
    (decodeAtom e pair.1.1 (bounded pair.1 pair.2).1,
      decodeAtom e pair.1.2 (bounded pair.1 pair.2).2)

/-- Raw ordered atom pairs of a finite set of pairs over `V`. -/
def unrelabelNatPairs (e : V ≃ Fin n) (pairs : Finset (V × V)) : Finset (Nat × Nat) :=
  pairs.image fun pair => (encodeAtom e pair.1, encodeAtom e pair.2)

theorem unrelabelNatPairs_bounded (e : V ≃ Fin n) (pairs : Finset (V × V)) :
    ∀ pair ∈ unrelabelNatPairs e pairs, pair.1 < n ∧ pair.2 < n := by
  intro pair member
  rw [unrelabelNatPairs, Finset.mem_image] at member
  obtain ⟨presented, _presentedMember, rfl⟩ := member
  exact ⟨encodeAtom_lt e presented.1, encodeAtom_lt e presented.2⟩

theorem unrelabelNatPairs_relabelNatPairs [DecidableEq V] (e : V ≃ Fin n)
    (pairs : Finset (Nat × Nat))
    (bounded : ∀ pair ∈ pairs, pair.1 < n ∧ pair.2 < n) :
    unrelabelNatPairs e (relabelNatPairs e pairs bounded) = pairs := by
  simpa [relabelNatPairs, unrelabelNatPairs] using
    finset_image_unrelabel_relabel (s := pairs)
      (relabel := fun a ha =>
        (decodeAtom e a.1 (bounded a ha).1, decodeAtom e a.2 (bounded a ha).2))
      (unrelabel := fun b : V × V => (encodeAtom e b.1, encodeAtom e b.2))
      (by
        intro a ha
        exact Prod.ext (encodeAtom_decodeAtom e a.1 (bounded a ha).1)
          (encodeAtom_decodeAtom e a.2 (bounded a ha).2))

theorem relabelNatPairs_unrelabelNatPairs [DecidableEq V] (e : V ≃ Fin n)
    (pairs : Finset (V × V)) :
    relabelNatPairs e (unrelabelNatPairs e pairs)
        (unrelabelNatPairs_bounded e pairs) = pairs := by
  simpa [relabelNatPairs, unrelabelNatPairs] using
    finset_image_relabel_unrelabel (s := pairs)
      (unrelabel := fun b : V × V => (encodeAtom e b.1, encodeAtom e b.2))
      (relabel := fun a ha =>
        (decodeAtom e a.1 ((unrelabelNatPairs_bounded e pairs) a ha).1,
          decodeAtom e a.2 ((unrelabelNatPairs_bounded e pairs) a ha).2))
      (by
        intro b hb
        exact Prod.ext (decodeAtom_encodeAtom e b.1 _) (decodeAtom_encodeAtom e b.2 _))

/-! ## Whole constitutional addends -/

/-- Boundedness of one complete addend at arity `n`.  Both the external atom set and both
coordinates of every attachment port must be bounded.  The identity class is nomenclature data
and is not bounded. -/
def molecularFullereneAddendBoundedIn (n : Nat) (addend : MolecularFullereneAddend) : Prop :=
  (∀ atom ∈ addend.externalAtoms, atom < n) ∧
    ∀ port ∈ addend.attachmentPorts, port.1 < n ∧ port.2 < n

/-- A complete graph-backed addend over the finite atom type `V`.

Every role-bearing field is present: the full external atom set, the full ordered port set and
the identity class.  Nothing is projected to `attachmentSites`. -/
structure SuppliedAddend (V : Type*) where
  externalAtoms : Finset V
  attachmentPorts : Finset (V × V)
  identityClass : Nat
  deriving DecidableEq

/-- Relabel one complete bounded addend. -/
def relabelAddend [DecidableEq V] (e : V ≃ Fin n) (addend : MolecularFullereneAddend)
    (bounded : molecularFullereneAddendBoundedIn n addend) : SuppliedAddend V where
  externalAtoms := relabelFinset e addend.externalAtoms bounded.1
  attachmentPorts := relabelNatPairs e addend.attachmentPorts bounded.2
  identityClass := addend.identityClass

/-- Decode one complete addend. -/
def unrelabelAddend (e : V ≃ Fin n) (addend : SuppliedAddend V) : MolecularFullereneAddend where
  externalAtoms := unrelabelFinset e addend.externalAtoms
  attachmentPorts := unrelabelNatPairs e addend.attachmentPorts
  identityClass := addend.identityClass

/-- Every decoded addend is bounded. -/
def unrelabelAddendBounded (e : V ≃ Fin n) (addend : SuppliedAddend V) :
    molecularFullereneAddendBoundedIn n (unrelabelAddend e addend) :=
  ⟨unrelabelFinset_bounded e addend.externalAtoms,
    unrelabelNatPairs_bounded e addend.attachmentPorts⟩

theorem unrelabelAddend_relabelAddend [DecidableEq V] (e : V ≃ Fin n)
    (addend : MolecularFullereneAddend)
    (bounded : molecularFullereneAddendBoundedIn n addend) :
    unrelabelAddend e (relabelAddend e addend bounded) = addend := by
  rcases addend with ⟨externalAtoms, attachmentPorts, identityClass⟩
  simp [relabelAddend, unrelabelAddend, unrelabelFinset_relabelFinset,
    unrelabelNatPairs_relabelNatPairs]

theorem relabelAddend_unrelabelAddend [DecidableEq V] (e : V ≃ Fin n)
    (addend : SuppliedAddend V) :
    relabelAddend e (unrelabelAddend e addend) (unrelabelAddendBounded e addend) = addend := by
  rcases addend with ⟨externalAtoms, attachmentPorts, identityClass⟩
  simp [relabelAddend, unrelabelAddend, relabelFinset_unrelabelFinset,
    relabelNatPairs_unrelabelNatPairs]

/-- Port orientation is preserved, so a cage-to-addend port and its reverse remain distinct. -/
theorem unrelabelAddend_attachmentPorts (e : V ≃ Fin n) (addend : SuppliedAddend V) :
    (unrelabelAddend e addend).attachmentPorts =
      addend.attachmentPorts.image (fun port => (encodeAtom e port.1, encodeAtom e port.2)) := rfl

/-- The identity class is retained literally. -/
@[simp] theorem unrelabelAddend_identityClass (e : V ≃ Fin n) (addend : SuppliedAddend V) :
    (unrelabelAddend e addend).identityClass = addend.identityClass := rfl

/-- The reported attachment sites of the decoded addend are exactly the images of the native
ports' first coordinates.  The native record keeps every port, so the site projection is a
consequence of the encoding rather than a replacement for the addend. -/
theorem unrelabelAddend_attachmentSites (e : V ≃ Fin n) (addend : SuppliedAddend V) :
    (unrelabelAddend e addend).attachmentSites =
      addend.attachmentPorts.image (fun port => encodeAtom e port.1) := by
  rw [MolecularFullereneAddend.attachmentSites, unrelabelAddend_attachmentPorts,
    Finset.image_image]
  rfl

/-! ### Ordered lists of addends -/

/-- Relabel an ordered list of complete bounded addends. -/
def relabelAddends [DecidableEq V] (e : V ≃ Fin n) (addends : List MolecularFullereneAddend)
    (bounded : ∀ addend ∈ addends, molecularFullereneAddendBoundedIn n addend) :
    List (SuppliedAddend V) :=
  addends.attach.map fun addend => relabelAddend e addend.1 (bounded addend.1 addend.2)

/-- Decode an ordered list of complete addends. -/
def unrelabelAddends (e : V ≃ Fin n) (addends : List (SuppliedAddend V)) :
    List MolecularFullereneAddend :=
  addends.map (unrelabelAddend e)

@[simp] theorem relabelAddends_length [DecidableEq V] (e : V ≃ Fin n)
    (addends : List MolecularFullereneAddend)
    (bounded : ∀ addend ∈ addends, molecularFullereneAddendBoundedIn n addend) :
    (relabelAddends e addends bounded).length = addends.length := by
  simp [relabelAddends]

@[simp] theorem unrelabelAddends_length (e : V ≃ Fin n) (addends : List (SuppliedAddend V)) :
    (unrelabelAddends e addends).length = addends.length := by
  simp [unrelabelAddends]

def unrelabelAddendsBounded (e : V ≃ Fin n) (addends : List (SuppliedAddend V)) :
    ∀ addend ∈ unrelabelAddends e addends, molecularFullereneAddendBoundedIn n addend := by
  intro addend member
  rw [unrelabelAddends, List.mem_map] at member
  obtain ⟨presented, _presentedMember, rfl⟩ := member
  exact unrelabelAddendBounded e presented

/-- Exact ordered-list recovery: order and multiplicity are preserved. -/
theorem unrelabelAddends_relabelAddends [DecidableEq V] (e : V ≃ Fin n)
    (addends : List MolecularFullereneAddend)
    (bounded : ∀ addend ∈ addends, molecularFullereneAddendBoundedIn n addend) :
    unrelabelAddends e (relabelAddends e addends bounded) = addends := by
  unfold unrelabelAddends relabelAddends
  rw [List.map_map]
  trans addends.attach.map Subtype.val
  · apply List.map_congr_left
    intro addend _
    exact unrelabelAddend_relabelAddend e addend.1 (bounded addend.1 addend.2)
  · exact List.attach_map_subtype_val addends

theorem relabelAddends_unrelabelAddends [DecidableEq V] (e : V ≃ Fin n)
    (addends : List (SuppliedAddend V)) :
    relabelAddends e (unrelabelAddends e addends) (unrelabelAddendsBounded e addends) =
      addends := by
  unfold relabelAddends unrelabelAddends
  rw [List.attach_map, List.map_map]
  trans addends.attach.map Subtype.val
  · apply List.map_congr_left
    intro addend _
    exact relabelAddend_unrelabelAddend e addend.1
  · exact List.attach_map_subtype_val addends

/-! ### Finite sets of addends (`chiralAddends`) -/

/-- Relabel a finite set of complete bounded addends. -/
def relabelAddendFinset [DecidableEq V] (e : V ≃ Fin n)
    (addends : Finset MolecularFullereneAddend)
    (bounded : ∀ addend ∈ addends, molecularFullereneAddendBoundedIn n addend) :
    Finset (SuppliedAddend V) :=
  addends.attach.image fun addend => relabelAddend e addend.1 (bounded addend.1 addend.2)

/-- Decode a finite set of complete addends. -/
def unrelabelAddendFinset [DecidableEq V] (e : V ≃ Fin n)
    (addends : Finset (SuppliedAddend V)) : Finset MolecularFullereneAddend :=
  addends.image (unrelabelAddend e)

def unrelabelAddendFinsetBounded [DecidableEq V] (e : V ≃ Fin n)
    (addends : Finset (SuppliedAddend V)) :
    ∀ addend ∈ unrelabelAddendFinset e addends, molecularFullereneAddendBoundedIn n addend := by
  intro addend member
  rw [unrelabelAddendFinset, Finset.mem_image] at member
  obtain ⟨presented, _presentedMember, rfl⟩ := member
  exact unrelabelAddendBounded e presented

/-- Exact finite-set recovery of the chiral addend family. -/
theorem unrelabelAddendFinset_relabelAddendFinset [DecidableEq V] (e : V ≃ Fin n)
    (addends : Finset MolecularFullereneAddend)
    (bounded : ∀ addend ∈ addends, molecularFullereneAddendBoundedIn n addend) :
    unrelabelAddendFinset e (relabelAddendFinset e addends bounded) = addends := by
  simpa [relabelAddendFinset, unrelabelAddendFinset] using
    finset_image_unrelabel_relabel (s := addends)
      (relabel := fun a ha => relabelAddend e a (bounded a ha))
      (unrelabel := fun b => unrelabelAddend e b)
      (by intro a ha; exact unrelabelAddend_relabelAddend e a (bounded a ha))

theorem relabelAddendFinset_unrelabelAddendFinset [DecidableEq V] (e : V ≃ Fin n)
    (addends : Finset (SuppliedAddend V)) :
    relabelAddendFinset e (unrelabelAddendFinset e addends)
        (unrelabelAddendFinsetBounded e addends) = addends := by
  simpa [relabelAddendFinset, unrelabelAddendFinset] using
    finset_image_relabel_unrelabel (s := addends)
      (unrelabel := fun b => unrelabelAddend e b)
      (relabel := fun a ha => relabelAddend e a ((unrelabelAddendFinsetBounded e addends) a ha))
      (by intro b hb; exact relabelAddend_unrelabelAddend e b)

/-! ## Typed substituent stereogenic units

`P93FullereneSubstituentStereogenicUnit` has seven constructors, and the two bond-axis
constructors `doubleBond` and `bondAxis` both project to `P93AuthorityPhysicalUnit.bond`.
Reusing the legacy physical-unit codec for the unit itself would therefore silently identify the
two source distinctions, so this module owns a seven-constructor mirror and proves that the
projection commutes with the legacy codec. -/

/-- Boundedness of one typed stereogenic unit at arity `n`. -/
def stereogenicUnitBoundedIn (n : Nat) : P93FullereneSubstituentStereogenicUnit → Prop
  | .center atom => atom < n
  | .doubleBond first second => first < n ∧ second < n
  | .cumuleneAxis path => ∀ atom ∈ path, atom < n
  | .bondAxis first second => first < n ∧ second < n
  | .plane members => ∀ atom ∈ members, atom < n
  | .helix path => ∀ atom ∈ path, atom < n
  | .polyhedron mid positions => mid < n ∧ ∀ atom ∈ positions, atom < n

/-- A typed substituent stereogenic unit over the finite atom type `V`, retaining all seven
constructor distinctions. -/
inductive SuppliedStereogenicUnit (V : Type*) where
  | center (atom : V)
  | doubleBond (first second : V)
  | cumuleneAxis (path : List V)
  | bondAxis (first second : V)
  | plane (members : Finset V)
  | helix (path : List V)
  | polyhedron (center : V) (positions : Finset V)
  deriving DecidableEq

/-- The native physical-unit projection of a native typed unit.  It is the six-constructor
`SuppliedPhysicalUnit` of the existing citation ingress, so the legacy codec is reused on the
projection. -/
def SuppliedStereogenicUnit.toSuppliedPhysicalUnit :
    SuppliedStereogenicUnit V → SuppliedPhysicalUnit V
  | .center atom => .atomCenter atom
  | .doubleBond first second => .bond first second
  | .cumuleneAxis path => .axis path
  | .bondAxis first second => .bond first second
  | .plane members => .plane members
  | .helix path => .helix path
  | .polyhedron mid positions => .polyhedron mid positions

/-- The native unit's bound is exactly the legacy physical-unit bound of its projection. -/
def stereogenicUnitToPhysicalUnitBounded (unit : P93FullereneSubstituentStereogenicUnit)
    (bounded : stereogenicUnitBoundedIn n unit) :
    OrganicStereoSuppliedCitationIngress.P93AuthorityPhysicalUnit.BoundedIn n
      unit.toPhysicalUnit := by
  cases unit with
  | center atom => exact bounded
  | doubleBond first second => exact bounded
  | cumuleneAxis path => exact bounded
  | bondAxis first second => exact bounded
  | plane members => exact bounded
  | helix path => exact bounded
  | polyhedron mid positions => exact bounded

/-- Relabel one bounded typed stereogenic unit, preserving its constructor. -/
def relabelStereogenicUnit [DecidableEq V] (e : V ≃ Fin n) :
    (unit : P93FullereneSubstituentStereogenicUnit) →
      stereogenicUnitBoundedIn n unit → SuppliedStereogenicUnit V
  | .center atom, bounded => .center (decodeAtom e atom bounded)
  | .doubleBond first second, bounded =>
      .doubleBond (decodeAtom e first bounded.1) (decodeAtom e second bounded.2)
  | .cumuleneAxis path, bounded => .cumuleneAxis (relabelList e path bounded)
  | .bondAxis first second, bounded =>
      .bondAxis (decodeAtom e first bounded.1) (decodeAtom e second bounded.2)
  | .plane members, bounded => .plane (relabelFinset e members bounded)
  | .helix path, bounded => .helix (relabelList e path bounded)
  | .polyhedron mid positions, bounded =>
      .polyhedron (decodeAtom e mid bounded.1) (relabelFinset e positions bounded.2)

/-- Raw atom indices of a native typed stereogenic unit. -/
def unrelabelStereogenicUnit (e : V ≃ Fin n) :
    SuppliedStereogenicUnit V → P93FullereneSubstituentStereogenicUnit
  | .center atom => .center (encodeAtom e atom)
  | .doubleBond first second => .doubleBond (encodeAtom e first) (encodeAtom e second)
  | .cumuleneAxis path => .cumuleneAxis (unrelabelList e path)
  | .bondAxis first second => .bondAxis (encodeAtom e first) (encodeAtom e second)
  | .plane members => .plane (unrelabelFinset e members)
  | .helix path => .helix (unrelabelList e path)
  | .polyhedron mid positions =>
      .polyhedron (encodeAtom e mid) (unrelabelFinset e positions)

/-- Every decoded typed unit is bounded. -/
def unrelabelStereogenicUnitBounded (e : V ≃ Fin n) (unit : SuppliedStereogenicUnit V) :
    stereogenicUnitBoundedIn n (unrelabelStereogenicUnit e unit) := by
  cases unit with
  | center atom => exact encodeAtom_lt e atom
  | doubleBond first second =>
      exact ⟨encodeAtom_lt e first, encodeAtom_lt e second⟩
  | cumuleneAxis path => exact unrelabelList_bounded e path
  | bondAxis first second =>
      exact ⟨encodeAtom_lt e first, encodeAtom_lt e second⟩
  | plane members => exact unrelabelFinset_bounded e members
  | helix path => exact unrelabelList_bounded e path
  | polyhedron mid positions =>
      exact ⟨encodeAtom_lt e mid, unrelabelFinset_bounded e positions⟩

theorem unrelabelStereogenicUnit_relabelStereogenicUnit [DecidableEq V] (e : V ≃ Fin n)
    (unit : P93FullereneSubstituentStereogenicUnit)
    (bounded : stereogenicUnitBoundedIn n unit) :
    unrelabelStereogenicUnit e (relabelStereogenicUnit e unit bounded) = unit := by
  cases unit with
  | center atom => simp [relabelStereogenicUnit, unrelabelStereogenicUnit, encodeAtom_decodeAtom]
  | doubleBond first second =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, encodeAtom_decodeAtom]
  | cumuleneAxis path =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, unrelabelList_relabelList]
  | bondAxis first second =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, encodeAtom_decodeAtom]
  | plane members =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, unrelabelFinset_relabelFinset]
  | helix path =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, unrelabelList_relabelList]
  | polyhedron mid positions =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, unrelabelFinset_relabelFinset,
        encodeAtom_decodeAtom]

theorem relabelStereogenicUnit_unrelabelStereogenicUnit [DecidableEq V] (e : V ≃ Fin n)
    (unit : SuppliedStereogenicUnit V) :
    relabelStereogenicUnit e (unrelabelStereogenicUnit e unit)
        (unrelabelStereogenicUnitBounded e unit) = unit := by
  cases unit with
  | center atom =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, decodeAtom_encodeAtom]
  | doubleBond first second =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, decodeAtom_encodeAtom]
  | cumuleneAxis path =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, relabelList_unrelabelList]
  | bondAxis first second =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, decodeAtom_encodeAtom]
  | plane members =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, relabelFinset_unrelabelFinset]
  | helix path =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, relabelList_unrelabelList]
  | polyhedron mid positions =>
      simp [relabelStereogenicUnit, unrelabelStereogenicUnit, relabelFinset_unrelabelFinset,
        decodeAtom_encodeAtom]

/-- The seven-constructor codec commutes with the existing physical-unit codec.  This is a reuse
statement: atom references are decoded by the same primitive in both paths. -/
theorem relabelStereogenicUnit_toSuppliedPhysicalUnit [DecidableEq V] (e : V ≃ Fin n)
    (unit : P93FullereneSubstituentStereogenicUnit)
    (bounded : stereogenicUnitBoundedIn n unit) :
    (relabelStereogenicUnit e unit bounded).toSuppliedPhysicalUnit =
      relabelUnit e unit.toPhysicalUnit (stereogenicUnitToPhysicalUnitBounded unit bounded) := by
  cases unit with
  | center atom => rfl
  | doubleBond first second => rfl
  | cumuleneAxis path => rfl
  | bondAxis first second => rfl
  | plane members => rfl
  | helix path => rfl
  | polyhedron mid positions => rfl

/-- The reverse direction of the physical-unit commutation: decoding the native projection is
the source projection of the decoded unit. -/
theorem toPhysicalUnit_unrelabelStereogenicUnit (e : V ≃ Fin n)
    (unit : SuppliedStereogenicUnit V) :
    (unrelabelStereogenicUnit e unit).toPhysicalUnit =
      unrelabelUnit e unit.toSuppliedPhysicalUnit := by
  cases unit with
  | center atom => rfl
  | doubleBond first second => rfl
  | cumuleneAxis path => rfl
  | bondAxis first second => rfl
  | plane members => rfl
  | helix path => rfl
  | polyhedron mid positions => rfl

/-- The old physical-unit projection identifies the two bond-axis constructors. -/
theorem toSuppliedPhysicalUnit_doubleBond_eq_bondAxis (first second : V) :
    (SuppliedStereogenicUnit.doubleBond first second).toSuppliedPhysicalUnit =
      (SuppliedStereogenicUnit.bondAxis first second).toSuppliedPhysicalUnit := rfl

/-- The native typed codec keeps the two bond-axis constructors distinct. -/
theorem suppliedStereogenicUnit_doubleBond_ne_bondAxis (first second : V) :
    (SuppliedStereogenicUnit.doubleBond first second : SuppliedStereogenicUnit V) ≠
      .bondAxis first second := by
  intro equal
  cases equal

/-- The native descriptor-match predicate.  It is the constructor-shape predicate of the source
record, restated for the native unit. -/
def suppliedDescriptorMatchesUnit :
    P93FullereneSubstituentCIPDescriptor → SuppliedStereogenicUnit V → Prop
  | P93FullereneSubstituentCIPDescriptor.center _,
      SuppliedStereogenicUnit.center _
  | .axis _, .cumuleneAxis _
  | .axis _, .bondAxis _ _
  | .plane _, .plane _
  | .helix _, .helix _
  | .doubleBond _, .doubleBond _ _
  | .polyhedron _, .polyhedron _ _ => True
  | _, _ => False

/-- Descriptor/unit agreement is exactly preserved by the codec. -/
theorem descriptorMatches_unrelabelStereogenicUnit [DecidableEq V] (e : V ≃ Fin n)
    (descriptor : P93FullereneSubstituentCIPDescriptor) (unit : SuppliedStereogenicUnit V) :
    P93FullereneSubstituentDescriptorMatchesUnit descriptor
        (unrelabelStereogenicUnit e unit) ↔
      suppliedDescriptorMatchesUnit descriptor unit := by
  cases descriptor <;> cases unit <;> simp [suppliedDescriptorMatchesUnit,
    P93FullereneSubstituentDescriptorMatchesUnit, unrelabelStereogenicUnit]

/-- Descriptor/unit agreement is preserved in the relabelling direction. -/
theorem descriptorMatches_relabelStereogenicUnit_iff [DecidableEq V] (e : V ≃ Fin n)
    (descriptor : P93FullereneSubstituentCIPDescriptor)
    (unit : P93FullereneSubstituentStereogenicUnit)
    (bounded : stereogenicUnitBoundedIn n unit) :
    suppliedDescriptorMatchesUnit descriptor (relabelStereogenicUnit e unit bounded) ↔
      P93FullereneSubstituentDescriptorMatchesUnit descriptor unit := by
  rw [← descriptorMatches_unrelabelStereogenicUnit]
  rw [unrelabelStereogenicUnit_relabelStereogenicUnit]

/-! ## Whole-addend-owned substituent CIP assignments -/

/-- Boundedness of one source substituent assignment. -/
def substituentAssignmentBoundedIn (n : Nat)
    (assignment : P93RelationalFullereneSubstituentCIPAssignment) : Prop :=
  molecularFullereneAddendBoundedIn n assignment.owner ∧
    stereogenicUnitBoundedIn n assignment.unit

/-- One whole-addend-owned CIP result over the finite atom type `V`.

The owner is the complete addend (not one attachment site), the typed unit keeps its seven-way
constructor, and the citation and descriptor are source nomenclature copied literally. -/
structure SuppliedSubstituentCIPAssignment (V : Type*) where
  owner : SuppliedAddend V
  unit : SuppliedStereogenicUnit V
  citation : P93AuthorityCitationToken
  descriptor : P93FullereneSubstituentCIPDescriptor
  deriving DecidableEq

/-- Relabel one whole-addend-owned assignment. -/
def relabelSubstituentCIPAssignment [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : substituentAssignmentBoundedIn n assignment) :
    SuppliedSubstituentCIPAssignment V where
  owner := relabelAddend e assignment.owner bounded.1
  unit := relabelStereogenicUnit e assignment.unit bounded.2
  citation := assignment.citation
  descriptor := assignment.descriptor

/-- Decode one whole-addend-owned assignment. -/
def unrelabelSubstituentCIPAssignment [DecidableEq V] (e : V ≃ Fin n)
    (assignment : SuppliedSubstituentCIPAssignment V) :
    P93RelationalFullereneSubstituentCIPAssignment where
  owner := unrelabelAddend e assignment.owner
  unit := unrelabelStereogenicUnit e assignment.unit
  citation := assignment.citation
  descriptor := assignment.descriptor

def unrelabelSubstituentCIPAssignmentBounded [DecidableEq V] (e : V ≃ Fin n)
    (assignment : SuppliedSubstituentCIPAssignment V) :
    substituentAssignmentBoundedIn n (unrelabelSubstituentCIPAssignment e assignment) :=
  ⟨unrelabelAddendBounded e assignment.owner,
    unrelabelStereogenicUnitBounded e assignment.unit⟩

theorem unrelabelSubstituentCIPAssignment_relabelSubstituentCIPAssignment [DecidableEq V]
    (e : V ≃ Fin n) (assignment : P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : substituentAssignmentBoundedIn n assignment) :
    unrelabelSubstituentCIPAssignment e
        (relabelSubstituentCIPAssignment e assignment bounded) = assignment := by
  rcases assignment with ⟨owner, unit, citation, descriptor⟩
  simp [relabelSubstituentCIPAssignment, unrelabelSubstituentCIPAssignment,
    unrelabelAddend_relabelAddend, unrelabelStereogenicUnit_relabelStereogenicUnit]

theorem relabelSubstituentCIPAssignment_unrelabelSubstituentCIPAssignment [DecidableEq V]
    (e : V ≃ Fin n) (assignment : SuppliedSubstituentCIPAssignment V) :
    relabelSubstituentCIPAssignment e (unrelabelSubstituentCIPAssignment e assignment)
        (unrelabelSubstituentCIPAssignmentBounded e assignment) = assignment := by
  rcases assignment with ⟨owner, unit, citation, descriptor⟩
  simp [relabelSubstituentCIPAssignment, unrelabelSubstituentCIPAssignment,
    relabelAddend_unrelabelAddend, relabelStereogenicUnit_unrelabelStereogenicUnit]

/-! ### Ordered lists of assignments -/

/-- Relabel an ordered list of bounded whole-addend-owned assignments. -/
def relabelSubstituentAssignments [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : ∀ assignment ∈ assignments, substituentAssignmentBoundedIn n assignment) :
    List (SuppliedSubstituentCIPAssignment V) :=
  assignments.attach.map fun assignment =>
    relabelSubstituentCIPAssignment e assignment.1 (bounded assignment.1 assignment.2)

/-- Decode an ordered list of whole-addend-owned assignments. -/
def unrelabelSubstituentAssignments [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (SuppliedSubstituentCIPAssignment V)) :
    List P93RelationalFullereneSubstituentCIPAssignment :=
  assignments.map (unrelabelSubstituentCIPAssignment e)

@[simp] theorem relabelSubstituentAssignments_length [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : ∀ assignment ∈ assignments, substituentAssignmentBoundedIn n assignment) :
    (relabelSubstituentAssignments e assignments bounded).length = assignments.length := by
  simp [relabelSubstituentAssignments]

@[simp] theorem unrelabelSubstituentAssignments_length [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (SuppliedSubstituentCIPAssignment V)) :
    (unrelabelSubstituentAssignments e assignments).length = assignments.length := by
  simp [unrelabelSubstituentAssignments]

def unrelabelSubstituentAssignmentsBounded [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (SuppliedSubstituentCIPAssignment V)) :
    ∀ assignment ∈ unrelabelSubstituentAssignments e assignments,
      substituentAssignmentBoundedIn n assignment := by
  intro assignment member
  rw [unrelabelSubstituentAssignments, List.mem_map] at member
  obtain ⟨presented, _presentedMember, rfl⟩ := member
  exact unrelabelSubstituentCIPAssignmentBounded e presented

/-- Exact ordered recovery of the complete substituent corpus, including order and
multiplicity. -/
theorem unrelabelSubstituentAssignments_relabelSubstituentAssignments [DecidableEq V]
    (e : V ≃ Fin n) (assignments : List P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : ∀ assignment ∈ assignments, substituentAssignmentBoundedIn n assignment) :
    unrelabelSubstituentAssignments e
        (relabelSubstituentAssignments e assignments bounded) = assignments := by
  unfold unrelabelSubstituentAssignments relabelSubstituentAssignments
  rw [List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact unrelabelSubstituentCIPAssignment_relabelSubstituentCIPAssignment e assignment.1
      (bounded assignment.1 assignment.2)
  · exact List.attach_map_subtype_val assignments

theorem relabelSubstituentAssignments_unrelabelSubstituentAssignments [DecidableEq V]
    (e : V ≃ Fin n) (assignments : List (SuppliedSubstituentCIPAssignment V)) :
    relabelSubstituentAssignments e (unrelabelSubstituentAssignments e assignments)
        (unrelabelSubstituentAssignmentsBounded e assignments) = assignments := by
  unfold relabelSubstituentAssignments unrelabelSubstituentAssignments
  rw [List.attach_map, List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact relabelSubstituentCIPAssignment_unrelabelSubstituentCIPAssignment e assignment.1
  · exact List.attach_map_subtype_val assignments

/-- A map of the relabelled corpus is the map of the source corpus whenever the two maps agree
after decoding.  This is the order- and multiplicity-preserving projection principle. -/
theorem relabelSubstituentAssignments_map [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : ∀ assignment ∈ assignments, substituentAssignmentBoundedIn n assignment)
    {β : Type*} (suppliedMap : SuppliedSubstituentCIPAssignment V → β)
    (sourceMap : P93RelationalFullereneSubstituentCIPAssignment → β)
    (agree : ∀ assignment bound,
      suppliedMap (relabelSubstituentCIPAssignment e assignment bound) =
        sourceMap assignment) :
    (relabelSubstituentAssignments e assignments bounded).map suppliedMap =
      assignments.map sourceMap := by
  unfold relabelSubstituentAssignments
  rw [List.map_map]
  trans assignments.attach.map (fun assignment => sourceMap assignment.1)
  · apply List.map_congr_left
    intro assignment _
    exact agree assignment.1 (bounded assignment.1 assignment.2)
  · exact List.attach_map_val

/-- Citation tokens are retained literally, in order and multiplicity. -/
theorem relabelSubstituentAssignments_citations [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : ∀ assignment ∈ assignments, substituentAssignmentBoundedIn n assignment) :
    (relabelSubstituentAssignments e assignments bounded).map
        (fun assignment => assignment.citation) =
      assignments.map (fun assignment => assignment.citation) :=
  relabelSubstituentAssignments_map e assignments bounded
    (fun assignment => assignment.citation) (fun assignment => assignment.citation)
    (by intro assignment _; rfl)

/-- Citation component values and prime counts are retained literally. -/
theorem relabelSubstituentAssignments_citationKeys [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : ∀ assignment ∈ assignments, substituentAssignmentBoundedIn n assignment) :
    (relabelSubstituentAssignments e assignments bounded).map
        (fun assignment => assignment.citation.key) =
      assignments.map (fun assignment => assignment.citation.key) :=
  relabelSubstituentAssignments_map e assignments bounded
    (fun assignment => assignment.citation.key) (fun assignment => assignment.citation.key)
    (by intro assignment _; rfl)

/-- CIP descriptors are retained literally, in order and multiplicity. -/
theorem relabelSubstituentAssignments_descriptors [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : ∀ assignment ∈ assignments, substituentAssignmentBoundedIn n assignment) :
    (relabelSubstituentAssignments e assignments bounded).map
        (fun assignment => assignment.descriptor) =
      assignments.map (fun assignment => assignment.descriptor) :=
  relabelSubstituentAssignments_map e assignments bounded
    (fun assignment => assignment.descriptor) (fun assignment => assignment.descriptor)
    (by intro assignment _; rfl)

/-- Whole-addend owners are recovered exactly, so no owner is lost or projected. -/
theorem relabelSubstituentAssignments_owners [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : ∀ assignment ∈ assignments, substituentAssignmentBoundedIn n assignment) :
    (relabelSubstituentAssignments e assignments bounded).map
        (fun assignment => unrelabelAddend e assignment.owner) =
      assignments.map (fun assignment => assignment.owner) :=
  relabelSubstituentAssignments_map e assignments bounded
    (fun assignment => unrelabelAddend e assignment.owner)
    (fun assignment => assignment.owner)
    (by
      intro assignment bound
      exact unrelabelAddend_relabelAddend e assignment.owner bound.1)

/-- Typed units are recovered exactly, including the `doubleBond`/`bondAxis` distinction. -/
theorem relabelSubstituentAssignments_units [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : ∀ assignment ∈ assignments, substituentAssignmentBoundedIn n assignment) :
    (relabelSubstituentAssignments e assignments bounded).map
        (fun assignment => unrelabelStereogenicUnit e assignment.unit) =
      assignments.map (fun assignment => assignment.unit) :=
  relabelSubstituentAssignments_map e assignments bounded
    (fun assignment => unrelabelStereogenicUnit e assignment.unit)
    (fun assignment => assignment.unit)
    (by
      intro assignment bound
      exact unrelabelStereogenicUnit_relabelStereogenicUnit e assignment.unit bound.2)

/-! ### Existing validity consumed at the same source and policy -/

/-- `ValidFor` of a decoded whole-addend-owned assignment is exactly `ValidFor` of the original
assignment at the same source, molecule, relational input and policy.  This is record equality,
not an invariance claim about renumbering. -/
theorem validFor_unrelabelSubstituentCIPAssignment_iff [DecidableEq V] (e : V ≃ Fin n)
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)
    (assignment : P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : substituentAssignmentBoundedIn n assignment) :
    (unrelabelSubstituentCIPAssignment e
        (relabelSubstituentCIPAssignment e assignment bounded)).ValidFor
        policy source molecule input ↔
      assignment.ValidFor policy source molecule input := by
  rw [unrelabelSubstituentCIPAssignment_relabelSubstituentCIPAssignment]

/-- The decoded corpus satisfies the existing completeness predicate exactly when the source
corpus does.  All four completeness obligations are therefore recovered, not re-assumed. -/
theorem substituentCorpusComplete_unrelabel_relabel_iff [DecidableEq V] (e : V ≃ Fin n)
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)
    (assignments : List P93RelationalFullereneSubstituentCIPAssignment)
    (bounded : ∀ assignment ∈ assignments, substituentAssignmentBoundedIn n assignment) :
    P93RelationalFullereneSubstituentCIPAssignmentsComplete policy source molecule input
        (unrelabelSubstituentAssignments e
          (relabelSubstituentAssignments e assignments bounded)) ↔
      P93RelationalFullereneSubstituentCIPAssignmentsComplete policy source molecule input
        assignments := by
  rw [unrelabelSubstituentAssignments_relabelSubstituentAssignments]

/-! ## Bounds derived from the carrier's own validity

Nothing below introduces a new restriction on atom indices.  Every bound is a consequence of the
pre-existing `ValidFor` predicates and of the exact atom-count agreement produced by the physical
frame binding. -/

/-- An addend is bounded whenever its own source `ValidFor` holds and both the cage carrier and the
molecule's atom count are already bounded by `n`. -/
theorem molecularFullereneAddendBoundedIn_of_validFor
    {molecule : RawMolecule} {carrier : Finset Nat} {addend : MolecularFullereneAddend} {n : Nat}
    (carrierBound : ∀ atom ∈ carrier, atom < n)
    (atomCountEq : molecule.atomCount = n)
    (valid : addend.ValidFor molecule carrier) :
    molecularFullereneAddendBoundedIn n addend := by
  refine ⟨?_, ?_⟩
  · intro atom member
    exact atomCountEq ▸ (valid.2.2.2.2.1 atom member).1
  · rintro ⟨site, external⟩ member
    obtain ⟨siteInCarrier, externalInAddend, _positive⟩ :=
      (valid.2.2.1.1 site external).1 member
    exact ⟨carrierBound site siteInCarrier,
      atomCountEq ▸ (valid.2.2.2.2.1 external externalInAddend).1⟩

/-- The typed-unit bound follows from a bound on its whole atom carrier, constructor by
constructor.  No constructor is collapsed. -/
theorem stereogenicUnitBoundedIn_of_atomCarrier
    {n : Nat} {unit : P93FullereneSubstituentStereogenicUnit}
    (bounded : ∀ atom ∈ P93RelationalFullereneSubstituentAtomCarrier unit, atom < n) :
    stereogenicUnitBoundedIn n unit := by
  cases unit with
  | center atom =>
      exact bounded atom (by simp [P93RelationalFullereneSubstituentAtomCarrier])
  | doubleBond first second =>
      exact ⟨bounded first (by simp [P93RelationalFullereneSubstituentAtomCarrier]),
        bounded second (by simp [P93RelationalFullereneSubstituentAtomCarrier])⟩
  | cumuleneAxis path =>
      intro atom member
      exact bounded atom (by simpa [P93RelationalFullereneSubstituentAtomCarrier] using member)
  | bondAxis first second =>
      exact ⟨bounded first (by simp [P93RelationalFullereneSubstituentAtomCarrier]),
        bounded second (by simp [P93RelationalFullereneSubstituentAtomCarrier])⟩
  | plane members =>
      intro atom member
      exact bounded atom (by simpa [P93RelationalFullereneSubstituentAtomCarrier] using member)
  | helix path =>
      intro atom member
      exact bounded atom (by simpa [P93RelationalFullereneSubstituentAtomCarrier] using member)
  | polyhedron center positions =>
      exact ⟨bounded center (by simp [P93RelationalFullereneSubstituentAtomCarrier]),
        fun atom member =>
          bounded atom (by simp [P93RelationalFullereneSubstituentAtomCarrier, member])⟩

/-- One assignment's bounds follow from its own `ValidFor`: the owner is one of the exact
graph-backed addends, and the unit is constitutionally owned by that addend. -/
theorem substituentAssignmentBoundedIn_of_validFor
    {policy : P93RelationalFullereneAuthorityPolicy}
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    {input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule}
    {assignment : P93RelationalFullereneSubstituentCIPAssignment} {n : Nat}
    (carrierBound : ∀ atom ∈ input.topologyInput.carrier, atom < n)
    (atomCountEq : molecule.atomCount = n)
    (valid : assignment.ValidFor policy source molecule input) :
    substituentAssignmentBoundedIn n assignment := by
  have ownerInAddends : assignment.owner ∈ input.evidence.addends :=
    input.evidence.chiralAddendsOwned assignment.owner valid.ownerChiral
  have ownerValid : assignment.owner.ValidFor molecule input.topologyInput.carrier :=
    input.evidence.addendsValid assignment.owner ownerInAddends
  have ownerBounded : molecularFullereneAddendBoundedIn n assignment.owner :=
    molecularFullereneAddendBoundedIn_of_validFor carrierBound atomCountEq ownerValid
  refine ⟨ownerBounded, ?_⟩
  exact stereogenicUnitBoundedIn_of_atomCarrier fun atom member =>
    ownerBounded.1 atom (valid.unitOwned member)

/-- The complete source observation's relabelling bounds.  Each conjunct corresponds to one
role-bearing field of the observation, not to an atom count. -/
def relationalObservationBoundedIn (n : Nat)
    (observation : P93RelationalFullereneAuthorityObservation policy) : Prop :=
  (∀ addend ∈ observation.addends, molecularFullereneAddendBoundedIn n addend) ∧
    (∀ addend ∈ observation.chiralAddends, molecularFullereneAddendBoundedIn n addend) ∧
      (∀ atom ∈ observation.assignment.unit, atom < n) ∧
        ∀ assignment ∈ observation.substituentAssignments,
          substituentAssignmentBoundedIn n assignment

/-- Every relabelled field of a valid observation is bounded, using only the observation's own
`ValidFor` and the exact atom-count agreement. -/
theorem relationalObservationBoundedIn_of_validFor
    {policy : P93RelationalFullereneAuthorityPolicy}
    {source : AuthoritativeChemicalInput}
    {observation : P93RelationalFullereneAuthorityObservation policy} {n : Nat}
    (atomCountEq : observation.molecule.atomCount = n)
    (valid : observation.ValidFor policy source) :
    relationalObservationBoundedIn n observation := by
  have carrierJudged : MolecularFullereneCarrierJudgment observation.molecule
      observation.selectedInput.symmetryInput.cage := by
    have oriented :=
      RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment.relational
        observation.molecule observation.spatial? observation.selectedInput
        valid.selectedInputJudged
    unfold RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment at oriented
    exact oriented.1
  have cageBound : ∀ atom ∈ observation.selectedInput.symmetryInput.cage.carrier, atom < n := by
    intro atom member
    obtain ⟨spec, atomAt, _carbon⟩ := carrierJudged.carbonAtoms atom member
    have lookup := listGet?_eq_some_implies_lt observation.molecule.atoms atom spec atomAt
    have counted : atom < observation.molecule.atomCount := by
      simpa [RawMolecule.atomCount] using lookup
    exact atomCountEq ▸ counted
  have carrierBound :
      ∀ atom ∈ observation.selectedInput.symmetryInput.topologyInput.carrier, atom < n := by
    intro atom member
    exact cageBound atom (by simpa using member)
  have addendsBound : ∀ addend ∈ observation.addends,
      molecularFullereneAddendBoundedIn n addend := by
    intro addend member
    have evidenceMember : addend ∈ observation.selectedInput.symmetryInput.evidence.addends := by
      rw [← valid.addendsExact]
      exact member
    exact molecularFullereneAddendBoundedIn_of_validFor carrierBound atomCountEq
      (observation.selectedInput.symmetryInput.evidence.addendsValid addend evidenceMember)
  have chiralBound : ∀ addend ∈ observation.chiralAddends,
      molecularFullereneAddendBoundedIn n addend := by
    intro addend member
    have evidenceChiral : addend ∈
        observation.selectedInput.symmetryInput.evidence.chiralAddends := by
      rw [← valid.chiralAddendsExact]
      exact member
    have evidenceMember : addend ∈ observation.selectedInput.symmetryInput.evidence.addends :=
      observation.selectedInput.symmetryInput.evidence.chiralAddendsOwned addend evidenceChiral
    exact molecularFullereneAddendBoundedIn_of_validFor carrierBound atomCountEq
      (observation.selectedInput.symmetryInput.evidence.addendsValid addend evidenceMember)
  have unitBound : ∀ atom ∈ observation.assignment.unit, atom < n := by
    intro atom member
    obtain ⟨chiralityType, payloads, _typeMatches, _payloadJudgment, assignmentEq⟩ :=
      valid.localAssignmentJudged
    have unitEq : observation.assignment.unit =
        observation.selectedInput.symmetryInput.cage.toFullereneConfigurationInput.unit := by
      rw [assignmentEq]
    rw [unitEq] at member
    have carrierMember : atom ∈ observation.selectedInput.symmetryInput.cage.carrier := by
      simpa [MolecularFullereneConfigurationInput.toFullereneConfigurationInput] using member
    exact cageBound atom carrierMember
  have corpusBound : ∀ assignment ∈ observation.substituentAssignments,
      substituentAssignmentBoundedIn n assignment := by
    intro assignment member
    exact substituentAssignmentBoundedIn_of_validFor carrierBound atomCountEq
      (valid.substituentCorpusComplete.assignmentsValid assignment member)
  exact ⟨addendsBound, chiralBound, unitBound, corpusBound⟩

/-! ## The native observation mirror -/

/-- One complete relational observation over the finite atom type `V`.

The ordered addend families, their identity-class data, the cage-atom assignment unit and the
whole-addend-owned substituent corpus are relabelled.  The per-observation `RawMolecule`, the
dependent input family and the selected input are retained as explicit source syntax: the policy
relation `RawMoleculeObserved` is arbitrary, so nothing in `ValidFor` forces the observation's
molecule to be the semantic conversion of the bound source, and the addend evidence records are
proof-carrying rather than reconstructible from index data.  The optional spatial channel is shared
at the satellite level, where its exact encode equality is available. -/
structure SuppliedRelationalFullereneObservation (V : Type*) [DecidableEq V]
    (policy : P93RelationalFullereneAuthorityPolicy) where
  molecule : RawMolecule
  inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)
  selectedInput : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule
  addends : List (SuppliedAddend V)
  chiralAddends : Finset (SuppliedAddend V)
  assignmentUnit : List V
  chiralityType : FullereneChiralityType
  payloads : List FullereneDescriptorPayload
  substituentAssignments : List (SuppliedSubstituentCIPAssignment V)

/-- Relabel one complete observation, preserving order, multiplicity, every identity-class entry
and every typed constructor. -/
def relabelRelationalObservation [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93RelationalFullereneAuthorityObservation policy)
    (bounded : relationalObservationBoundedIn n observation) :
    SuppliedRelationalFullereneObservation V policy where
  molecule := observation.molecule
  inputs := observation.inputs
  selectedInput := observation.selectedInput
  addends := relabelAddends e observation.addends bounded.1
  chiralAddends := relabelAddendFinset e observation.chiralAddends bounded.2.1
  assignmentUnit := relabelList e observation.assignment.unit bounded.2.2.1
  chiralityType := observation.assignment.chiralityType
  payloads := observation.assignment.payloads
  substituentAssignments :=
    relabelSubstituentAssignments e observation.substituentAssignments bounded.2.2.2

/-- Decode one complete observation.  The optional spatial channel is supplied by the shared
satellite source, because `structureAgreement` forces it to be the source's channel. -/
def unrelabelRelationalObservation [DecidableEq V] (e : V ≃ Fin n)
    (spatial? : Option SpatialConfiguration)
    (observation : SuppliedRelationalFullereneObservation V policy) :
    P93RelationalFullereneAuthorityObservation policy where
  molecule := observation.molecule
  spatial? := spatial?
  inputs := observation.inputs
  selectedInput := observation.selectedInput
  addends := unrelabelAddends e observation.addends
  chiralAddends := unrelabelAddendFinset e observation.chiralAddends
  assignment :=
    { unit := unrelabelList e observation.assignmentUnit
      chiralityType := observation.chiralityType
      payloads := observation.payloads }
  substituentAssignments := unrelabelSubstituentAssignments e observation.substituentAssignments

/-- Exact record recovery for one complete observation.  The only side condition is the exact
spatial-channel agreement that `ValidFor` already supplies for every valid observation. -/
theorem unrelabelRelationalObservation_relabelRelationalObservation [DecidableEq V]
    (e : V ≃ Fin n) (observation : P93RelationalFullereneAuthorityObservation policy)
    (bounded : relationalObservationBoundedIn n observation)
    (spatial? : Option SpatialConfiguration)
    (spatialExact : observation.spatial? = spatial?) :
    unrelabelRelationalObservation e spatial?
        (relabelRelationalObservation e observation bounded) = observation := by
  obtain ⟨molecule, spatial, inputs, selectedInput, addends, chiralAddends, assignment,
    substituentAssignments⟩ := observation
  subst spatialExact
  simp [relabelRelationalObservation, unrelabelRelationalObservation,
    unrelabelAddends_relabelAddends, unrelabelAddendFinset_relabelAddendFinset,
    unrelabelList_relabelList, unrelabelSubstituentAssignments_relabelSubstituentAssignments]

/-- A decoded native observation is bounded, field by field, because every native atom is
in range by construction. -/
def unrelabelRelationalObservationBounded [DecidableEq V] (e : V ≃ Fin n)
    (spatial? : Option SpatialConfiguration)
    (observation : SuppliedRelationalFullereneObservation V policy) :
    relationalObservationBoundedIn n
      (unrelabelRelationalObservation e spatial? observation) :=
  ⟨unrelabelAddendsBounded e observation.addends,
    unrelabelAddendFinsetBounded e observation.chiralAddends,
    unrelabelList_bounded e observation.assignmentUnit,
    unrelabelSubstituentAssignmentsBounded e observation.substituentAssignments⟩

/-- Decoding then re-encoding a native observation returns it exactly, including the ordered
addend list and every corpus entry. -/
theorem relabelRelationalObservation_unrelabelRelationalObservation [DecidableEq V]
    (e : V ≃ Fin n) (spatial? : Option SpatialConfiguration)
    (observation : SuppliedRelationalFullereneObservation V policy) :
    relabelRelationalObservation e (unrelabelRelationalObservation e spatial? observation)
        (unrelabelRelationalObservationBounded e spatial? observation) = observation := by
  obtain ⟨molecule, inputs, selectedInput, addends, chiralAddends, assignmentUnit,
    chiralityType, payloads, substituentAssignments⟩ := observation
  simp [relabelRelationalObservation, unrelabelRelationalObservation,
    relabelAddends_unrelabelAddends,
    relabelAddendFinset_unrelabelAddendFinset, relabelList_unrelabelList,
    relabelSubstituentAssignments_unrelabelSubstituentAssignments]

/-! ## The relational satellite and exact full recovery -/

/-- A raw relational source: one explicit physical-frame binding of the authoritative input and an
ordered list of complete relational observations, each certified against the bound source.  No
boundedness data is stored; every bound used by the codec is derived from `ValidFor` during
adaptation. -/
structure RawRelationalFullereneObservationSource (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93RelationalFullereneAuthorityPolicy) where
  binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V
  observations : List (P93RelationalFullereneAuthorityObservation policy)
  valid : ∀ observation ∈ observations,
    observation.ValidFor policy binding.source

/-- The composable relational channel.  The graph and both optional evidence channels are one
independent finite source; `observations` is the ordered native payload list.  No original
observation and no original `AuthoritativeChemicalInput` is stored here. -/
structure RelationalFullereneObservationSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93RelationalFullereneAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (SuppliedRelationalFullereneObservation V policy)

namespace RelationalFullereneObservationSatellite

variable {V : Type*} [DecidableEq V] [Fintype V]
  {policy : P93RelationalFullereneAuthorityPolicy}

/-- The satellite's shared finite source, with the observations intentionally excluded. -/
def toFiniteSource (satellite : RelationalFullereneObservationSatellite V policy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

/-- The shared spatial channel encoded from the satellite.  It is exactly the source's stored
channel whenever the binding's `spatial_eq` holds, and it is the channel handed to each observation
decoder. -/
def sharedSpatial? (satellite : RelationalFullereneObservationSatellite V policy)
    (e : V ≃ Fin (Fintype.card V)) : Option SpatialConfiguration :=
  OrganicFiniteSource.encodeSpatial? e satellite.spatial?

end RelationalFullereneObservationSatellite

/-- Atom-count agreement for one valid observation: the observation's own raw molecule and the
bound authoritative source have the same atom count.  This is a consequence of the exact topology
conversion and the binding's graph equality, not an input assumption. -/
theorem relationalObservationAtomCount_eq {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : P93RelationalFullereneAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    observation.molecule.atomCount = Fintype.card V := by
  rw [← RawMolecule.toMolecularFullereneTopologySemanticMolecule?_atomCount
    observation.molecule observation.selectedInput.symmetryInput.cage.carrier
    binding.source.molecule valid.structureAgreement.1]
  exact binding.atomCount_eq

/-- Adapt a raw relational source into the satellite: the shared finite source is retained
verbatim, and each valid observation is relabelled field by field.  Bounds are derived from the
observation's own `ValidFor` and the exact atom-count agreement. -/
def adapt {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    RelationalFullereneObservationSatellite V policy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := raw.observations.attach.map fun observation =>
    relabelRelationalObservation raw.binding.enumeration observation.1
      (relationalObservationBoundedIn_of_validFor
        (relationalObservationAtomCount_eq raw.binding observation.1
          (raw.valid observation.1 observation.2))
        (raw.valid observation.1 observation.2))

@[simp] theorem adapt_graph {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    (adapt raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adapt_spatial? {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    (adapt raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adapt_diagram? {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    (adapt raw).diagram? = raw.binding.shared.diagram? := rfl

@[simp] theorem adapt_observations {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    (adapt raw).observations = raw.observations.attach.map (fun observation =>
      relabelRelationalObservation raw.binding.enumeration observation.1
        (relationalObservationBoundedIn_of_validFor
          (relationalObservationAtomCount_eq raw.binding observation.1
            (raw.valid observation.1 observation.2))
          (raw.valid observation.1 observation.2))) := rfl

/-! ## The decoder and exact source recovery -/

/-- The recovered relational source record: the exact authoritative input together with the ordered
list of complete relational observations. -/
@[ext] structure RecoveredRelationalFullereneObservationSource
    (policy : P93RelationalFullereneAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : List (P93RelationalFullereneAuthorityObservation policy)

/-- Decode a relational satellite into the recovered source record.  The authoritative input is
the exact encode of the shared finite source; every observation is decoded with the explicit
enumeration and the satellite's shared spatial channel. -/
def suppliedSource {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (e : V ≃ Fin (Fintype.card V))
    (satellite : RelationalFullereneObservationSatellite V policy) :
    RecoveredRelationalFullereneObservationSource policy where
  source := satellite.toFiniteSource.encode e
  observations := satellite.observations.map fun observation =>
    unrelabelRelationalObservation e (satellite.sharedSpatial? e) observation

/-- The ordered observation list is recovered exactly, including order, multiplicity, every
identity-class entry, every typed constructor and every substituent corpus entry. -/
theorem decodedObservations_adapt {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    (adapt raw).observations.map
        (unrelabelRelationalObservation raw.binding.enumeration
          ((adapt raw).sharedSpatial? raw.binding.enumeration)) =
      raw.observations := by
  obtain ⟨binding, observations, valid⟩ := raw
  rw [adapt_observations, List.map_map]
  refine Eq.trans ?_ (List.attach_map_subtype_val observations)
  apply List.map_congr_left
  intro observation _
  obtain ⟨observation, member⟩ := observation
  have validObservation : observation.ValidFor policy binding.source := valid observation member
  have spatialExact : observation.spatial? =
      (adapt ⟨binding, observations, valid⟩).sharedSpatial? binding.enumeration := by
    simp only [RelationalFullereneObservationSatellite.sharedSpatial?, adapt_spatial?]
    rw [binding.spatial_eq]
    exact validObservation.structureAgreement.2.1.symm
  exact unrelabelRelationalObservation_relabelRelationalObservation binding.enumeration
    observation
    (relationalObservationBoundedIn_of_validFor
      (relationalObservationAtomCount_eq binding observation validObservation)
      validObservation)
    _ spatialExact

/-- **Exact full source recovery.**  Adapting a raw relational source into the satellite and
decoding it returns the exact authoritative input and the exact ordered observation list.  The
source equality is the genuine encode equality of the binding; the observation equality is the
exact per-observation inverse, including the ordered addend families, the arbitrary chiral-addend
sets and the whole substituent corpus. -/
theorem suppliedSource_adapt {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    suppliedSource raw.binding.enumeration (adapt raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredRelationalFullereneObservationSource.ext
  · exact raw.binding.encode_shared
  · simp only [suppliedSource]
    exact decodedObservations_adapt raw

/-- Validity is transported to the recovered observations at the same policy and the *recovered*
source.  Nothing is re-judged at a different source and no policy predicate is assumed invariant
under an arbitrary atom permutation. -/
theorem suppliedSource_adapt_validFor {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalFullereneObservationSource V policy) :
    ∀ observation ∈ (suppliedSource raw.binding.enumeration (adapt raw)).observations,
      observation.ValidFor policy
        (suppliedSource raw.binding.enumeration (adapt raw)).source := by
  intro observation member
  have recovered := suppliedSource_adapt raw
  have observationsEq :
      (suppliedSource raw.binding.enumeration (adapt raw)).observations = raw.observations := by
    simpa using congrArg
      (fun recovered : RecoveredRelationalFullereneObservationSource policy =>
        recovered.observations) recovered
  have sourceEq :
      (suppliedSource raw.binding.enumeration (adapt raw)).source = raw.binding.source := by
    simpa using congrArg
      (fun recovered : RecoveredRelationalFullereneObservationSource policy =>
        recovered.source) recovered
  rw [observationsEq] at member
  rw [sourceEq]
  exact raw.valid observation member

/-! ## Concrete certified-source adapter -/

/-- Adapt a certified authoritative input together with its ordered list of valid relational
observations.  The exact ingress of the certified input supplies the shared binding, with no extra
reconstruction. -/
def adaptCertified {policy : P93RelationalFullereneAuthorityPolicy}
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (P93RelationalFullereneAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor policy certified.input) :
    RelationalFullereneObservationSatellite
      (Fin certified.input.molecule.atomCount) policy :=
  adapt { binding := OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding.ofCertified
            certified
          observations := observations
          valid := valid }

/-- **Concrete exact recovery from a certified source.**  Decoding the adapted satellite returns
the exact certified authoritative input and the exact ordered relational observation list. -/
theorem suppliedSource_adaptCertified {policy : P93RelationalFullereneAuthorityPolicy}
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (P93RelationalFullereneAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor policy certified.input) :
    suppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertified certified observations valid) =
      { source := certified.input, observations := observations } :=
  suppliedSource_adapt
    { binding := OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding.ofCertified
        certified
      observations := observations
      valid := valid }

end OrganicStereoRelationalFullereneIngress
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.finset_image_unrelabel_relabel
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.finset_image_relabel_unrelabel
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.unrelabelAddend_relabelAddend
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.relabelAddend_unrelabelAddend
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.unrelabelAddends_relabelAddends
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.relabelAddends_unrelabelAddends
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.unrelabelAddendFinset_relabelAddendFinset
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.relabelAddendFinset_unrelabelAddendFinset
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.unrelabelStereogenicUnit_relabelStereogenicUnit
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.relabelStereogenicUnit_unrelabelStereogenicUnit
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.relabelStereogenicUnit_toSuppliedPhysicalUnit
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.toPhysicalUnit_unrelabelStereogenicUnit
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.unrelabelSubstituentCIPAssignment_relabelSubstituentCIPAssignment
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.relabelSubstituentCIPAssignment_unrelabelSubstituentCIPAssignment
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.validFor_unrelabelSubstituentCIPAssignment_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.substituentCorpusComplete_unrelabel_relabel_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.descriptorMatches_relabelStereogenicUnit_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.unrelabelSubstituentAssignments_relabelSubstituentAssignments
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.relabelSubstituentAssignments_unrelabelSubstituentAssignments
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.unrelabelRelationalObservation_relabelRelationalObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.relabelRelationalObservation_unrelabelRelationalObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.molecularFullereneAddendBoundedIn_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.stereogenicUnitBoundedIn_of_atomCarrier
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.substituentAssignmentBoundedIn_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.relationalObservationBoundedIn_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.relationalObservationAtomCount_eq
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.decodedObservations_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.suppliedSource_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.suppliedSource_adapt_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress.suppliedSource_adaptCertified
