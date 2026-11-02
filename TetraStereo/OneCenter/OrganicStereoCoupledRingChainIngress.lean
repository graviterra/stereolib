import TetraStereo.OneCenter.IUPACP93CoupledRingChainAuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Lossless native ingress for the coupled ring/chain P-93.6 carrier

This module provides a concrete, lossless encoding of the *existing* source carrier
`P93CoupledRingChainAuthorityObservation` (and its reviewed descriptor evidence) into an
arbitrary finite atom type `V`.  It does not introduce a new chemical classification, and it
does not claim that any policy hook is inhabited.

## What is relabelled

Every genuine atom reference inside a carrier record is relabelled through an explicit
enumeration `e : V ≃ Fin n`:

* physical units (`P93AuthorityPhysicalUnit`) via the accepted
  `OrganicStereoSuppliedCitationIngress` codec;
* the planar frame of a cyclophane plane observation via the accepted
  `OrganicStereoP93PhysicalFrameIngress.relabelPlane`/`decodePlane` codec;
* every family-specific observation embedded in `P93RingChainReviewedDescriptorEvidence`, using
  concrete mirror records; the evidence is never collapsed to a unit, a descriptor, or `Unit`;
* the reviewed base-name certificate's interaction participants, using the source certificate's
  own `StructurallyWellFormed` witness to derive the bounds;
* repeated-component atom sets;
* component-correspondence atom and attachment pairs (see the resolution policy below).

## What stays exact metadata

The following are not atom references and are copied literally: base-name token lists, citation
tokens, locants (including `P93FusedLocant`), unit/descriptor/kind/context values, component and
list indices, `P93RingChainAssignmentOwnership` records, phane-node index cycles
(`ringPhaneCycles`), assembly ring indices and junction ring indices, multiplicative selection
data, and every original ordered list.

## Unresolved source references in component correspondences

In the multiplicative-*selected* branch, `P93RingChainComponentCorrespondence.ValidFor` bounds
every correspondence pair by the two component supports, so all pair indices are genuine atoms.
In the multiplicative-*rejected* branch the decision predicate does not constrain the
correspondence lists at all.  Such an index is therefore not bounded by the original validity.
The native representation keeps it as an explicit unresolved source reference
(`SuppliedRingChainSourceAtom.unresolved index`) instead of inventing a new well-formedness
restriction.  In-bound indices become native atoms.  Consequently:

* source-side exactness (`decode (encode x) = x`) is unconditional, including order and
  repetitions;
* native-side exactness (`encode (decode x) = x`) holds exactly for native records whose
  unresolved references are already out of range (`n ≤ index`); this is recorded by
  `SuppliedRingChainCorrespondence.Canonical` and its observation-level analogue.  A native
  `.unresolved i` with `i < n` is *canonically* re-encoded as the corresponding native atom,
  which is the intended resolution, not an information loss about the source side.

## Source binding

The satellite reuses `OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding`, whose
`graph_eq`, `spatial_eq` and `diagram_eq` are actual equalities to the authoritative input.  The
exact source is therefore recovered (not merely its atom count).  The decoder reads every encoded
field; no original `AuthoritativeChemicalInput` or original observation is stored in the native
records.
-/

namespace TetraStereo.OneCenter

namespace OrganicStereoCoupledRingChainIngress

open TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
open TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress

variable {V : Type*} {n : ℕ}

/-! ## Generic ordered list codecs -/

/-- Relabel an ordered list of raw atom pairs.  Order, multiplicity and the two roles inside
each pair are preserved. -/
def relabelPairList [DecidableEq V] (e : V ≃ Fin n) (pairs : List (Nat × Nat))
    (bounded : ∀ pair ∈ pairs, pair.1 < n ∧ pair.2 < n) : List (V × V) :=
  pairs.attach.map fun pair =>
    (decodeAtom e pair.1.1 (bounded pair.1 pair.2).1,
      decodeAtom e pair.1.2 (bounded pair.1 pair.2).2)

/-- Raw indices of an ordered list of native atom pairs. -/
def unrelabelPairList (e : V ≃ Fin n) (pairs : List (V × V)) : List (Nat × Nat) :=
  pairs.map fun pair => (encodeAtom e pair.1, encodeAtom e pair.2)

/-- Every decoded pair is in range. -/
def unrelabelPairListBounded (e : V ≃ Fin n) (pairs : List (V × V)) :
    ∀ pair ∈ unrelabelPairList e pairs, pair.1 < n ∧ pair.2 < n := by
  intro pair member
  rw [unrelabelPairList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact ⟨encodeAtom_lt e presented.1, encodeAtom_lt e presented.2⟩

theorem unrelabelPairList_relabelPairList [DecidableEq V] (e : V ≃ Fin n)
    (pairs : List (Nat × Nat))
    (bounded : ∀ pair ∈ pairs, pair.1 < n ∧ pair.2 < n) :
    unrelabelPairList e (relabelPairList e pairs bounded) = pairs := by
  unfold unrelabelPairList relabelPairList
  rw [List.map_map]
  trans pairs.attach.map Subtype.val
  · apply List.map_congr_left
    intro pair _
    obtain ⟨pairValue, pairMember⟩ := pair
    rcases pairValue with ⟨first, second⟩
    simp [encodeAtom_decodeAtom]
  · exact List.attach_map_subtype_val pairs

theorem relabelPairList_unrelabelPairList [DecidableEq V] (e : V ≃ Fin n)
    (pairs : List (V × V)) :
    relabelPairList e (unrelabelPairList e pairs)
        (unrelabelPairListBounded e pairs) = pairs := by
  unfold relabelPairList unrelabelPairList
  rw [List.attach_map, List.map_map]
  trans pairs.attach.map Subtype.val
  · apply List.map_congr_left
    intro pair _
    obtain ⟨presented, _presentedMember⟩ := pair
    rcases presented with ⟨first, second⟩
    simp [decodeAtom_encodeAtom]
  · exact List.attach_map_subtype_val pairs

/-- Relabel an ordered list of raw atom finsets. -/
def relabelFinsetList [DecidableEq V] (e : V ≃ Fin n) (sets : List (Finset Nat))
    (bounded : ∀ set ∈ sets, ∀ atom ∈ set, atom < n) : List (Finset V) :=
  sets.attach.map fun set => relabelFinset e set.1 (bounded set.1 set.2)

/-- Raw indices of an ordered list of native atom finsets. -/
def unrelabelFinsetList (e : V ≃ Fin n) (sets : List (Finset V)) : List (Finset Nat) :=
  sets.map (unrelabelFinset e)

def unrelabelFinsetListBounded (e : V ≃ Fin n) (sets : List (Finset V)) :
    ∀ set ∈ unrelabelFinsetList e sets, ∀ atom ∈ set, atom < n := by
  intro set member atom atomMember
  rw [unrelabelFinsetList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact unrelabelFinset_bounded e presented atom atomMember

theorem unrelabelFinsetList_relabelFinsetList [DecidableEq V] (e : V ≃ Fin n)
    (sets : List (Finset Nat))
    (bounded : ∀ set ∈ sets, ∀ atom ∈ set, atom < n) :
    unrelabelFinsetList e (relabelFinsetList e sets bounded) = sets := by
  unfold unrelabelFinsetList relabelFinsetList
  rw [List.map_map]
  trans sets.attach.map Subtype.val
  · apply List.map_congr_left
    intro set _
    obtain ⟨setValue, setMember⟩ := set
    exact unrelabelFinset_relabelFinset e setValue (bounded setValue setMember)
  · exact List.attach_map_subtype_val sets

theorem relabelFinsetList_unrelabelFinsetList [DecidableEq V] (e : V ≃ Fin n)
    (sets : List (Finset V)) :
    relabelFinsetList e (unrelabelFinsetList e sets)
        (unrelabelFinsetListBounded e sets) = sets := by
  unfold relabelFinsetList unrelabelFinsetList
  rw [List.attach_map, List.map_map]
  trans sets.attach.map Subtype.val
  · apply List.map_congr_left
    intro set _
    obtain ⟨presented, _presentedMember⟩ := set
    exact relabelFinset_unrelabelFinset e presented
  · exact List.attach_map_subtype_val sets

/-- Relabel an ordered list of ordered atom lists. -/
def relabelListList [DecidableEq V] (e : V ≃ Fin n) (rows : List (List Nat))
    (bounded : ∀ row ∈ rows, ∀ atom ∈ row, atom < n) : List (List V) :=
  rows.attach.map fun row => relabelList e row.1 (bounded row.1 row.2)

/-- Raw indices of an ordered list of ordered atom lists. -/
def unrelabelListList (e : V ≃ Fin n) (rows : List (List V)) : List (List Nat) :=
  rows.map (unrelabelList e)

def unrelabelListListBounded (e : V ≃ Fin n) (rows : List (List V)) :
    ∀ row ∈ unrelabelListList e rows, ∀ atom ∈ row, atom < n := by
  intro row member atom atomMember
  rw [unrelabelListList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact unrelabelList_bounded e presented atom atomMember

theorem unrelabelListList_relabelListList [DecidableEq V] (e : V ≃ Fin n)
    (rows : List (List Nat))
    (bounded : ∀ row ∈ rows, ∀ atom ∈ row, atom < n) :
    unrelabelListList e (relabelListList e rows bounded) = rows := by
  unfold unrelabelListList relabelListList
  rw [List.map_map]
  trans rows.attach.map Subtype.val
  · apply List.map_congr_left
    intro row _
    obtain ⟨rowValue, rowMember⟩ := row
    exact unrelabelList_relabelList e rowValue (bounded rowValue rowMember)
  · exact List.attach_map_subtype_val rows

theorem relabelListList_unrelabelListList [DecidableEq V] (e : V ≃ Fin n)
    (rows : List (List V)) :
    relabelListList e (unrelabelListList e rows)
        (unrelabelListListBounded e rows) = rows := by
  unfold relabelListList unrelabelListList
  rw [List.attach_map, List.map_map]
  trans rows.attach.map Subtype.val
  · apply List.map_congr_left
    intro row _
    obtain ⟨presented, _presentedMember⟩ := row
    exact relabelList_unrelabelList e presented
  · exact List.attach_map_subtype_val rows

/-- Relabel an ordered list of `(atom, fused locant)` pairs.  The locant is naming metadata and
is copied literally. -/
def relabelAtomLocantList [DecidableEq V] (e : V ≃ Fin n)
    (values : List (Nat × P93FusedLocant))
    (bounded : ∀ value ∈ values, value.1 < n) : List (V × P93FusedLocant) :=
  values.attach.map fun value =>
    (decodeAtom e value.1.1 (bounded value.1 value.2), value.1.2)

/-- Raw indices of an ordered list of `(atom, fused locant)` pairs. -/
def unrelabelAtomLocantList (e : V ≃ Fin n)
    (values : List (V × P93FusedLocant)) : List (Nat × P93FusedLocant) :=
  values.map fun value => (encodeAtom e value.1, value.2)

def unrelabelAtomLocantListBounded (e : V ≃ Fin n)
    (values : List (V × P93FusedLocant)) :
    ∀ value ∈ unrelabelAtomLocantList e values, value.1 < n := by
  intro value member
  rw [unrelabelAtomLocantList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact encodeAtom_lt e presented.1

theorem unrelabelAtomLocantList_relabelAtomLocantList [DecidableEq V] (e : V ≃ Fin n)
    (values : List (Nat × P93FusedLocant))
    (bounded : ∀ value ∈ values, value.1 < n) :
    unrelabelAtomLocantList e (relabelAtomLocantList e values bounded) = values := by
  unfold unrelabelAtomLocantList relabelAtomLocantList
  rw [List.map_map]
  trans values.attach.map Subtype.val
  · apply List.map_congr_left
    intro value _
    obtain ⟨valueData, valueMember⟩ := value
    rcases valueData with ⟨atom, locant⟩
    simp [encodeAtom_decodeAtom]
  · exact List.attach_map_subtype_val values

theorem relabelAtomLocantList_unrelabelAtomLocantList [DecidableEq V] (e : V ≃ Fin n)
    (values : List (V × P93FusedLocant)) :
    relabelAtomLocantList e (unrelabelAtomLocantList e values)
        (unrelabelAtomLocantListBounded e values) = values := by
  unfold relabelAtomLocantList unrelabelAtomLocantList
  rw [List.attach_map, List.map_map]
  trans values.attach.map Subtype.val
  · apply List.map_congr_left
    intro value _
    obtain ⟨presented, _presentedMember⟩ := value
    rcases presented with ⟨atom, locant⟩
    simp [decodeAtom_encodeAtom]
  · exact List.attach_map_subtype_val values

/-! ## Native stereogenic-unit and physical-identity mirror inductives -/

/-- Native mirror of `P93RingChainStereogenicUnit`, one constructor for one constructor.  Ordered
paths stay ordered lists, planar and polyhedral supports stay finite sets, and the polyhedral
center remains a distinguished atom. -/
inductive SuppliedRingChainStereogenicUnit (V : Type*) where
  | center (atom : V)
  | doubleBond (first second : V)
  | cumuleneAxis (path : List V)
  | bondAxis (first second : V)
  | fusedAxis (path : List V)
  | plane (members : Finset V)
  | helix (path : List V)
  | polyhedron (center : V) (positions : Finset V)
  deriving DecidableEq

/-- Bounds on every atom reference of a stereogenic unit. -/
def RingChainUnitBoundedIn (n : Nat) : P93RingChainStereogenicUnit → Prop
  | .center atom => atom < n
  | .doubleBond first second => first < n ∧ second < n
  | .cumuleneAxis path => ∀ atom ∈ path, atom < n
  | .bondAxis first second => first < n ∧ second < n
  | .fusedAxis path => ∀ atom ∈ path, atom < n
  | .plane members => ∀ atom ∈ members, atom < n
  | .helix path => ∀ atom ∈ path, atom < n
  | .polyhedron center positions => center < n ∧ ∀ atom ∈ positions, atom < n

def relabelRingChainUnit [DecidableEq V] (e : V ≃ Fin n) :
    (unit : P93RingChainStereogenicUnit) →
      RingChainUnitBoundedIn n unit → SuppliedRingChainStereogenicUnit V
  | .center atom, bounded => .center (decodeAtom e atom bounded)
  | .doubleBond first second, bounded =>
      .doubleBond (decodeAtom e first bounded.1) (decodeAtom e second bounded.2)
  | .cumuleneAxis path, bounded => .cumuleneAxis (relabelList e path bounded)
  | .bondAxis first second, bounded =>
      .bondAxis (decodeAtom e first bounded.1) (decodeAtom e second bounded.2)
  | .fusedAxis path, bounded => .fusedAxis (relabelList e path bounded)
  | .plane members, bounded => .plane (relabelFinset e members bounded)
  | .helix path, bounded => .helix (relabelList e path bounded)
  | .polyhedron center positions, bounded =>
      .polyhedron (decodeAtom e center bounded.1)
        (relabelFinset e positions bounded.2)

def unrelabelRingChainUnit (e : V ≃ Fin n) :
    SuppliedRingChainStereogenicUnit V → P93RingChainStereogenicUnit
  | .center atom => .center (encodeAtom e atom)
  | .doubleBond first second =>
      .doubleBond (encodeAtom e first) (encodeAtom e second)
  | .cumuleneAxis path => .cumuleneAxis (unrelabelList e path)
  | .bondAxis first second =>
      .bondAxis (encodeAtom e first) (encodeAtom e second)
  | .fusedAxis path => .fusedAxis (unrelabelList e path)
  | .plane members => .plane (unrelabelFinset e members)
  | .helix path => .helix (unrelabelList e path)
  | .polyhedron center positions =>
      .polyhedron (encodeAtom e center) (unrelabelFinset e positions)

def unrelabelRingChainUnitBounded (e : V ≃ Fin n) :
    (unit : SuppliedRingChainStereogenicUnit V) →
      RingChainUnitBoundedIn n (unrelabelRingChainUnit e unit)
  | .center atom => encodeAtom_lt e atom
  | .doubleBond first second =>
      ⟨encodeAtom_lt e first, encodeAtom_lt e second⟩
  | .cumuleneAxis path => unrelabelList_bounded e path
  | .bondAxis first second =>
      ⟨encodeAtom_lt e first, encodeAtom_lt e second⟩
  | .fusedAxis path => unrelabelList_bounded e path
  | .plane members => unrelabelFinset_bounded e members
  | .helix path => unrelabelList_bounded e path
  | .polyhedron center positions =>
      ⟨encodeAtom_lt e center, unrelabelFinset_bounded e positions⟩

theorem unrelabelRingChainUnit_relabelRingChainUnit [DecidableEq V] (e : V ≃ Fin n)
    (unit : P93RingChainStereogenicUnit)
    (bounded : RingChainUnitBoundedIn n unit) :
    unrelabelRingChainUnit e (relabelRingChainUnit e unit bounded) = unit := by
  cases unit with
  | center atom => simp [relabelRingChainUnit, unrelabelRingChainUnit, encodeAtom_decodeAtom]
  | doubleBond first second =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, encodeAtom_decodeAtom]
  | cumuleneAxis path =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, unrelabelList_relabelList]
  | bondAxis first second =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, encodeAtom_decodeAtom]
  | fusedAxis path =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, unrelabelList_relabelList]
  | plane members =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, unrelabelFinset_relabelFinset]
  | helix path =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, unrelabelList_relabelList]
  | polyhedron center positions =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, unrelabelFinset_relabelFinset,
        encodeAtom_decodeAtom]

theorem relabelRingChainUnit_unrelabelRingChainUnit [DecidableEq V] (e : V ≃ Fin n)
    (unit : SuppliedRingChainStereogenicUnit V) :
    relabelRingChainUnit e (unrelabelRingChainUnit e unit)
        (unrelabelRingChainUnitBounded e unit) = unit := by
  cases unit with
  | center atom => simp [relabelRingChainUnit, unrelabelRingChainUnit, decodeAtom_encodeAtom]
  | doubleBond first second =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, decodeAtom_encodeAtom]
  | cumuleneAxis path =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, relabelList_unrelabelList]
  | bondAxis first second =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, decodeAtom_encodeAtom]
  | fusedAxis path =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, relabelList_unrelabelList]
  | plane members =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, relabelFinset_unrelabelFinset]
  | helix path =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, relabelList_unrelabelList]
  | polyhedron center positions =>
      simp [relabelRingChainUnit, unrelabelRingChainUnit, relabelFinset_unrelabelFinset,
        decodeAtom_encodeAtom]

/-- Native mirror of `P93RingChainPhysicalIdentity`.  The `bond`, `axis`, `plane` and `helix`
support remain finite sets, exactly as in the source carrier. -/
inductive SuppliedRingChainPhysicalIdentity (V : Type*) where
  | center (atom : V)
  | bond (atoms : Finset V)
  | axis (atoms : Finset V)
  | plane (members : Finset V)
  | helix (atoms : Finset V)
  | polyhedron (center : V) (positions : Finset V)
  deriving DecidableEq

def RingChainPhysicalIdentityBoundedIn (n : Nat) : P93RingChainPhysicalIdentity → Prop
  | .center atom => atom < n
  | .bond atoms => ∀ atom ∈ atoms, atom < n
  | .axis atoms => ∀ atom ∈ atoms, atom < n
  | .plane members => ∀ atom ∈ members, atom < n
  | .helix atoms => ∀ atom ∈ atoms, atom < n
  | .polyhedron center positions => center < n ∧ ∀ atom ∈ positions, atom < n

def relabelRingChainPhysicalIdentity [DecidableEq V] (e : V ≃ Fin n) :
    (identity : P93RingChainPhysicalIdentity) →
      RingChainPhysicalIdentityBoundedIn n identity → SuppliedRingChainPhysicalIdentity V
  | .center atom, bounded => .center (decodeAtom e atom bounded)
  | .bond atoms, bounded => .bond (relabelFinset e atoms bounded)
  | .axis atoms, bounded => .axis (relabelFinset e atoms bounded)
  | .plane members, bounded => .plane (relabelFinset e members bounded)
  | .helix atoms, bounded => .helix (relabelFinset e atoms bounded)
  | .polyhedron center positions, bounded =>
      .polyhedron (decodeAtom e center bounded.1)
        (relabelFinset e positions bounded.2)

def unrelabelRingChainPhysicalIdentity (e : V ≃ Fin n) :
    SuppliedRingChainPhysicalIdentity V → P93RingChainPhysicalIdentity
  | .center atom => .center (encodeAtom e atom)
  | .bond atoms => .bond (unrelabelFinset e atoms)
  | .axis atoms => .axis (unrelabelFinset e atoms)
  | .plane members => .plane (unrelabelFinset e members)
  | .helix atoms => .helix (unrelabelFinset e atoms)
  | .polyhedron center positions =>
      .polyhedron (encodeAtom e center) (unrelabelFinset e positions)

def unrelabelRingChainPhysicalIdentityBounded (e : V ≃ Fin n) :
    (identity : SuppliedRingChainPhysicalIdentity V) →
      RingChainPhysicalIdentityBoundedIn n (unrelabelRingChainPhysicalIdentity e identity)
  | .center atom => encodeAtom_lt e atom
  | .bond atoms => unrelabelFinset_bounded e atoms
  | .axis atoms => unrelabelFinset_bounded e atoms
  | .plane members => unrelabelFinset_bounded e members
  | .helix atoms => unrelabelFinset_bounded e atoms
  | .polyhedron center positions =>
      ⟨encodeAtom_lt e center, unrelabelFinset_bounded e positions⟩

theorem unrelabelRingChainPhysicalIdentity_relabelRingChainPhysicalIdentity
    [DecidableEq V] (e : V ≃ Fin n) (identity : P93RingChainPhysicalIdentity)
    (bounded : RingChainPhysicalIdentityBoundedIn n identity) :
    unrelabelRingChainPhysicalIdentity e
        (relabelRingChainPhysicalIdentity e identity bounded) = identity := by
  cases identity with
  | center atom =>
      simp [relabelRingChainPhysicalIdentity, unrelabelRingChainPhysicalIdentity,
        encodeAtom_decodeAtom]
  | bond atoms =>
      simp [relabelRingChainPhysicalIdentity, unrelabelRingChainPhysicalIdentity,
        unrelabelFinset_relabelFinset]
  | axis atoms =>
      simp [relabelRingChainPhysicalIdentity, unrelabelRingChainPhysicalIdentity,
        unrelabelFinset_relabelFinset]
  | plane members =>
      simp [relabelRingChainPhysicalIdentity, unrelabelRingChainPhysicalIdentity,
        unrelabelFinset_relabelFinset]
  | helix atoms =>
      simp [relabelRingChainPhysicalIdentity, unrelabelRingChainPhysicalIdentity,
        unrelabelFinset_relabelFinset]
  | polyhedron center positions =>
      simp [relabelRingChainPhysicalIdentity, unrelabelRingChainPhysicalIdentity,
        unrelabelFinset_relabelFinset, encodeAtom_decodeAtom]

theorem relabelRingChainPhysicalIdentity_unrelabelRingChainPhysicalIdentity
    [DecidableEq V] (e : V ≃ Fin n) (identity : SuppliedRingChainPhysicalIdentity V) :
    relabelRingChainPhysicalIdentity e (unrelabelRingChainPhysicalIdentity e identity)
        (unrelabelRingChainPhysicalIdentityBounded e identity) = identity := by
  cases identity with
  | center atom =>
      simp [relabelRingChainPhysicalIdentity, unrelabelRingChainPhysicalIdentity,
        decodeAtom_encodeAtom]
  | bond atoms =>
      simp [relabelRingChainPhysicalIdentity, unrelabelRingChainPhysicalIdentity,
        relabelFinset_unrelabelFinset]
  | axis atoms =>
      simp [relabelRingChainPhysicalIdentity, unrelabelRingChainPhysicalIdentity,
        relabelFinset_unrelabelFinset]
  | plane members =>
      simp [relabelRingChainPhysicalIdentity, unrelabelRingChainPhysicalIdentity,
        relabelFinset_unrelabelFinset]
  | helix atoms =>
      simp [relabelRingChainPhysicalIdentity, unrelabelRingChainPhysicalIdentity,
        relabelFinset_unrelabelFinset]
  | polyhedron center positions =>
      simp [relabelRingChainPhysicalIdentity, unrelabelRingChainPhysicalIdentity,
        relabelFinset_unrelabelFinset, decodeAtom_encodeAtom]

/-! ## Reviewed base-name certificate -/

/-- Native mirror of `SemanticInteraction`: participants are atoms of `V`, the kind is copied. -/
structure SuppliedRingChainSemanticInteraction (V : Type*) where
  participants : List V
  kind : SemanticInteractionKind
  deriving DecidableEq

def relabelSemanticInteraction (e : V ≃ Fin n) (interaction : SemanticInteraction)
    (bounded : ∀ atom ∈ interaction.participants, atom < n) :
    SuppliedRingChainSemanticInteraction V where
  participants := relabelList e interaction.participants bounded
  kind := interaction.kind

def unrelabelSemanticInteraction (e : V ≃ Fin n)
    (interaction : SuppliedRingChainSemanticInteraction V) : SemanticInteraction where
  participants := unrelabelList e interaction.participants
  kind := interaction.kind

def unrelabelSemanticInteractionBounded (e : V ≃ Fin n)
    (interaction : SuppliedRingChainSemanticInteraction V) :
    ∀ atom ∈ (unrelabelSemanticInteraction e interaction).participants, atom < n := by
  obtain ⟨participants, kind⟩ := interaction
  exact unrelabelList_bounded e participants

theorem unrelabelSemanticInteraction_relabelSemanticInteraction (e : V ≃ Fin n)
    (interaction : SemanticInteraction)
    (bounded : ∀ atom ∈ interaction.participants, atom < n) :
    unrelabelSemanticInteraction e (relabelSemanticInteraction e interaction bounded) =
      interaction := by
  obtain ⟨participants, kind⟩ := interaction
  simp [relabelSemanticInteraction, unrelabelSemanticInteraction, unrelabelList_relabelList]

theorem relabelSemanticInteraction_unrelabelSemanticInteraction (e : V ≃ Fin n)
    (interaction : SuppliedRingChainSemanticInteraction V) :
    relabelSemanticInteraction e (unrelabelSemanticInteraction e interaction)
        (unrelabelSemanticInteractionBounded e interaction) = interaction := by
  obtain ⟨participants, kind⟩ := interaction
  simp [relabelSemanticInteraction, unrelabelSemanticInteraction,
    unrelabelSemanticInteractionBounded, relabelList_unrelabelList]

def relabelSemanticInteractionList (e : V ≃ Fin n)
    (interactions : List SemanticInteraction)
    (bounded : ∀ interaction ∈ interactions,
      ∀ atom ∈ interaction.participants, atom < n) :
    List (SuppliedRingChainSemanticInteraction V) :=
  interactions.attach.map fun interaction =>
    relabelSemanticInteraction e interaction.1 (bounded interaction.1 interaction.2)

def unrelabelSemanticInteractionList (e : V ≃ Fin n)
    (interactions : List (SuppliedRingChainSemanticInteraction V)) :
    List SemanticInteraction :=
  interactions.map (unrelabelSemanticInteraction e)

def unrelabelSemanticInteractionListBounded (e : V ≃ Fin n)
    (interactions : List (SuppliedRingChainSemanticInteraction V)) :
    ∀ interaction ∈ unrelabelSemanticInteractionList e interactions,
      ∀ atom ∈ interaction.participants, atom < n := by
  intro interaction member
  rw [unrelabelSemanticInteractionList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact unrelabelSemanticInteractionBounded e presented

theorem unrelabelSemanticInteractionList_relabelSemanticInteractionList
    (e : V ≃ Fin n) (interactions : List SemanticInteraction)
    (bounded : ∀ interaction ∈ interactions,
      ∀ atom ∈ interaction.participants, atom < n) :
    unrelabelSemanticInteractionList e
        (relabelSemanticInteractionList e interactions bounded) = interactions := by
  unfold unrelabelSemanticInteractionList relabelSemanticInteractionList
  rw [List.map_map]
  trans interactions.attach.map Subtype.val
  · apply List.map_congr_left
    intro interaction _
    exact unrelabelSemanticInteraction_relabelSemanticInteraction e interaction.1
      (bounded interaction.1 interaction.2)
  · exact List.attach_map_subtype_val interactions

theorem relabelSemanticInteractionList_unrelabelSemanticInteractionList
    (e : V ≃ Fin n)
    (interactions : List (SuppliedRingChainSemanticInteraction V)) :
    relabelSemanticInteractionList e
        (unrelabelSemanticInteractionList e interactions)
        (unrelabelSemanticInteractionListBounded e interactions) = interactions := by
  unfold relabelSemanticInteractionList unrelabelSemanticInteractionList
  rw [List.attach_map, List.map_map]
  trans interactions.attach.map Subtype.val
  · apply List.map_congr_left
    intro interaction _
    exact relabelSemanticInteraction_unrelabelSemanticInteraction e interaction.1
  · exact List.attach_map_subtype_val interactions

/-- Native mirror of `P93RingChainReviewedBaseNameCertificate`.  The frozen name and the frozen
literal atom records are copied; the frozen interaction records are relabelled natively. -/
structure SuppliedRingChainBaseNameCertificate (V : Type*) where
  frozenName : P93RingChainBaseName
  frozenAtoms : List SemanticAtom
  frozenInteractions : List (SuppliedRingChainSemanticInteraction V)

/-- Bounds on the certificate's interaction participants.  This is the only atom-indexed part of
the certificate. -/
def RingChainCertificateBoundedIn (n : Nat)
    (certificate : P93RingChainReviewedBaseNameCertificate) : Prop :=
  ∀ interaction ∈ certificate.frozenInteractions,
    ∀ atom ∈ interaction.participants, atom < n

def relabelRingChainCertificate [DecidableEq V] (e : V ≃ Fin n)
    (certificate : P93RingChainReviewedBaseNameCertificate)
    (bounded : RingChainCertificateBoundedIn n certificate) :
    SuppliedRingChainBaseNameCertificate V where
  frozenName := certificate.frozenName
  frozenAtoms := certificate.frozenAtoms
  frozenInteractions :=
    relabelSemanticInteractionList e certificate.frozenInteractions bounded

def unrelabelRingChainCertificate (e : V ≃ Fin n)
    (certificate : SuppliedRingChainBaseNameCertificate V) :
    P93RingChainReviewedBaseNameCertificate where
  frozenName := certificate.frozenName
  frozenAtoms := certificate.frozenAtoms
  frozenInteractions :=
    unrelabelSemanticInteractionList e certificate.frozenInteractions

def unrelabelRingChainCertificateBounded (e : V ≃ Fin n)
    (certificate : SuppliedRingChainBaseNameCertificate V) :
    RingChainCertificateBoundedIn n (unrelabelRingChainCertificate e certificate) := by
  intro interaction member
  exact unrelabelSemanticInteractionListBounded e certificate.frozenInteractions
    interaction member

theorem unrelabelRingChainCertificate_relabelRingChainCertificate [DecidableEq V]
    (e : V ≃ Fin n) (certificate : P93RingChainReviewedBaseNameCertificate)
    (bounded : RingChainCertificateBoundedIn n certificate) :
    unrelabelRingChainCertificate e
        (relabelRingChainCertificate e certificate bounded) = certificate := by
  obtain ⟨frozenName, frozenAtoms, frozenInteractions⟩ := certificate
  simp [relabelRingChainCertificate, unrelabelRingChainCertificate,
    unrelabelSemanticInteractionList_relabelSemanticInteractionList]

theorem relabelRingChainCertificate_unrelabelRingChainCertificate [DecidableEq V]
    (e : V ≃ Fin n) (certificate : SuppliedRingChainBaseNameCertificate V) :
    relabelRingChainCertificate e (unrelabelRingChainCertificate e certificate)
        (unrelabelRingChainCertificateBounded e certificate) = certificate := by
  obtain ⟨frozenName, frozenAtoms, frozenInteractions⟩ := certificate
  simp [relabelRingChainCertificate, unrelabelRingChainCertificate,
    relabelSemanticInteractionList_unrelabelSemanticInteractionList]

/-! ## Component correspondences with explicit unresolved source references -/

/-- A native atom reference that either resolves to an actual atom of `V` or records an
out-of-range source index explicitly.  The unresolved case is used exactly when the source
carrier's own validity does not bound the index. -/
inductive SuppliedRingChainSourceAtom (V : Type*) where
  | label (atom : V)
  | unresolved (index : Nat)
  deriving DecidableEq

/-- Resolve a raw source index: in-range indices become native atoms, out-of-range indices stay
explicit. -/
def encodeSourceAtom (e : V ≃ Fin n) (value : Nat) : SuppliedRingChainSourceAtom V :=
  if h : value < n then .label (decodeAtom e value h) else .unresolved value

/-- Raw source index of a native atom reference. -/
def decodeSourceAtom (e : V ≃ Fin n) : SuppliedRingChainSourceAtom V → Nat
  | .label atom => encodeAtom e atom
  | .unresolved index => index

/-- A native atom reference is canonical when an unresolved index is genuinely out of range. -/
def SourceAtomCanonical (e : V ≃ Fin n) : SuppliedRingChainSourceAtom V → Prop
  | .label _ => True
  | .unresolved index => n ≤ index

theorem decodeSourceAtom_encodeSourceAtom (e : V ≃ Fin n) (value : Nat) :
    decodeSourceAtom e (encodeSourceAtom e value) = value := by
  unfold encodeSourceAtom
  split
  · exact encodeAtom_decodeAtom e value ‹value < n›
  · rfl

theorem encodeSourceAtom_decodeSourceAtom (e : V ≃ Fin n)
    (atom : SuppliedRingChainSourceAtom V) (canonical : SourceAtomCanonical e atom) :
    encodeSourceAtom e (decodeSourceAtom e atom) = atom := by
  cases atom with
  | label value =>
      simp only [decodeSourceAtom, encodeSourceAtom, dif_pos (encodeAtom_lt e value),
        decodeAtom_encodeAtom]
  | unresolved index =>
      unfold SourceAtomCanonical at canonical
      have outOfRange : ¬ index < n := by omega
      unfold decodeSourceAtom encodeSourceAtom
      rw [dif_neg outOfRange]

def encodeSourceAtomPairList (e : V ≃ Fin n) (pairs : List (Nat × Nat)) :
    List (SuppliedRingChainSourceAtom V × SuppliedRingChainSourceAtom V) :=
  pairs.map fun pair => (encodeSourceAtom e pair.1, encodeSourceAtom e pair.2)

def decodeSourceAtomPairList (e : V ≃ Fin n)
    (pairs : List (SuppliedRingChainSourceAtom V × SuppliedRingChainSourceAtom V)) :
    List (Nat × Nat) :=
  pairs.map fun pair => (decodeSourceAtom e pair.1, decodeSourceAtom e pair.2)

def SourceAtomPairListCanonical (e : V ≃ Fin n)
    (pairs : List (SuppliedRingChainSourceAtom V × SuppliedRingChainSourceAtom V)) : Prop :=
  ∀ pair ∈ pairs, SourceAtomCanonical e pair.1 ∧ SourceAtomCanonical e pair.2

theorem decodeSourceAtomPairList_encodeSourceAtomPairList (e : V ≃ Fin n)
    (pairs : List (Nat × Nat)) :
    decodeSourceAtomPairList e (encodeSourceAtomPairList e pairs) = pairs := by
  unfold decodeSourceAtomPairList encodeSourceAtomPairList
  rw [List.map_map]
  trans pairs.map id
  · apply List.map_congr_left
    intro pair _
    obtain ⟨first, second⟩ := pair
    simp [Function.comp_apply, decodeSourceAtom_encodeSourceAtom]
  · exact List.map_id pairs

theorem encodeSourceAtomPairList_decodeSourceAtomPairList (e : V ≃ Fin n)
    (pairs : List (SuppliedRingChainSourceAtom V × SuppliedRingChainSourceAtom V))
    (canonical : SourceAtomPairListCanonical e pairs) :
    encodeSourceAtomPairList e (decodeSourceAtomPairList e pairs) = pairs := by
  unfold encodeSourceAtomPairList decodeSourceAtomPairList
  rw [List.map_map]
  trans pairs.map id
  · apply List.map_congr_left
    intro pair member
    obtain ⟨first, second⟩ := pair
    simp [Function.comp_apply,
      encodeSourceAtom_decodeSourceAtom e first (canonical (first, second) member).1,
      encodeSourceAtom_decodeSourceAtom e second (canonical (first, second) member).2]
  · exact List.map_id pairs

/-- Native mirror of one component correspondence.  Component indices are component metadata, not
atom labels, and are copied exactly. -/
structure SuppliedRingChainComponentCorrespondence (V : Type*) where
  leftIndex : Nat
  rightIndex : Nat
  atomPairs : List (SuppliedRingChainSourceAtom V × SuppliedRingChainSourceAtom V)
  attachmentPairs : List (SuppliedRingChainSourceAtom V × SuppliedRingChainSourceAtom V)

def relabelComponentCorrespondence (e : V ≃ Fin n)
    (correspondence : P93RingChainComponentCorrespondence) :
    SuppliedRingChainComponentCorrespondence V where
  leftIndex := correspondence.leftIndex
  rightIndex := correspondence.rightIndex
  atomPairs := encodeSourceAtomPairList e correspondence.atomPairs
  attachmentPairs := encodeSourceAtomPairList e correspondence.attachmentPairs

def unrelabelComponentCorrespondence (e : V ≃ Fin n)
    (correspondence : SuppliedRingChainComponentCorrespondence V) :
    P93RingChainComponentCorrespondence where
  leftIndex := correspondence.leftIndex
  rightIndex := correspondence.rightIndex
  atomPairs := decodeSourceAtomPairList e correspondence.atomPairs
  attachmentPairs := decodeSourceAtomPairList e correspondence.attachmentPairs

def ComponentCorrespondenceCanonical (e : V ≃ Fin n)
    (correspondence : SuppliedRingChainComponentCorrespondence V) : Prop :=
  SourceAtomPairListCanonical e correspondence.atomPairs ∧
    SourceAtomPairListCanonical e correspondence.attachmentPairs

theorem unrelabelComponentCorrespondence_relabelComponentCorrespondence
    (e : V ≃ Fin n) (correspondence : P93RingChainComponentCorrespondence) :
    unrelabelComponentCorrespondence e (relabelComponentCorrespondence e correspondence) =
      correspondence := by
  obtain ⟨leftIndex, rightIndex, atomPairs, attachmentPairs⟩ := correspondence
  simp [relabelComponentCorrespondence, unrelabelComponentCorrespondence,
    decodeSourceAtomPairList_encodeSourceAtomPairList]

theorem relabelComponentCorrespondence_unrelabelComponentCorrespondence
    (e : V ≃ Fin n) (correspondence : SuppliedRingChainComponentCorrespondence V)
    (canonical : ComponentCorrespondenceCanonical e correspondence) :
    relabelComponentCorrespondence e (unrelabelComponentCorrespondence e correspondence) =
      correspondence := by
  obtain ⟨leftIndex, rightIndex, atomPairs, attachmentPairs⟩ := correspondence
  obtain ⟨atomCanonical, attachmentCanonical⟩ := canonical
  have atomEq :=
    encodeSourceAtomPairList_decodeSourceAtomPairList e atomPairs atomCanonical
  have attachmentEq :=
    encodeSourceAtomPairList_decodeSourceAtomPairList e attachmentPairs attachmentCanonical
  simp [relabelComponentCorrespondence, unrelabelComponentCorrespondence, atomEq,
    attachmentEq]

def relabelComponentCorrespondenceList (e : V ≃ Fin n)
    (correspondences : List P93RingChainComponentCorrespondence) :
    List (SuppliedRingChainComponentCorrespondence V) :=
  correspondences.map (relabelComponentCorrespondence e)

def unrelabelComponentCorrespondenceList (e : V ≃ Fin n)
    (correspondences : List (SuppliedRingChainComponentCorrespondence V)) :
    List P93RingChainComponentCorrespondence :=
  correspondences.map (unrelabelComponentCorrespondence e)

def ComponentCorrespondenceListCanonical (e : V ≃ Fin n)
    (correspondences : List (SuppliedRingChainComponentCorrespondence V)) : Prop :=
  ∀ correspondence ∈ correspondences,
    ComponentCorrespondenceCanonical e correspondence

theorem unrelabelComponentCorrespondenceList_relabelComponentCorrespondenceList
    (e : V ≃ Fin n) (correspondences : List P93RingChainComponentCorrespondence) :
    unrelabelComponentCorrespondenceList e
        (relabelComponentCorrespondenceList e correspondences) = correspondences := by
  unfold unrelabelComponentCorrespondenceList relabelComponentCorrespondenceList
  rw [List.map_map]
  trans correspondences.map id
  · apply List.map_congr_left
    intro correspondence _
    exact unrelabelComponentCorrespondence_relabelComponentCorrespondence e correspondence
  · exact List.map_id correspondences

theorem relabelComponentCorrespondenceList_unrelabelComponentCorrespondenceList
    (e : V ≃ Fin n)
    (correspondences : List (SuppliedRingChainComponentCorrespondence V))
    (canonical : ComponentCorrespondenceListCanonical e correspondences) :
    relabelComponentCorrespondenceList e
        (unrelabelComponentCorrespondenceList e correspondences) = correspondences := by
  unfold relabelComponentCorrespondenceList unrelabelComponentCorrespondenceList
  rw [List.map_map]
  trans correspondences.map id
  · apply List.map_congr_left
    intro correspondence member
    exact relabelComponentCorrespondence_unrelabelComponentCorrespondence e correspondence
      (canonical correspondence member)
  · exact List.map_id correspondences

/-! ## Repeated components -/

/-- Native mirror of one repeated component's atom support. -/
structure SuppliedRingChainRepeatedComponent (V : Type*) where
  atoms : Finset V

def relabelRepeatedComponent [DecidableEq V] (e : V ≃ Fin n)
    (component : P93RingChainRepeatedComponent)
    (bounded : ∀ atom ∈ component.atoms, atom < n) :
    SuppliedRingChainRepeatedComponent V where
  atoms := relabelFinset e component.atoms bounded

def unrelabelRepeatedComponent (e : V ≃ Fin n)
    (component : SuppliedRingChainRepeatedComponent V) :
    P93RingChainRepeatedComponent where
  atoms := unrelabelFinset e component.atoms

def unrelabelRepeatedComponentBounded (e : V ≃ Fin n)
    (component : SuppliedRingChainRepeatedComponent V) :
    ∀ atom ∈ (unrelabelRepeatedComponent e component).atoms, atom < n :=
  unrelabelFinset_bounded e component.atoms

theorem unrelabelRepeatedComponent_relabelRepeatedComponent [DecidableEq V]
    (e : V ≃ Fin n) (component : P93RingChainRepeatedComponent)
    (bounded : ∀ atom ∈ component.atoms, atom < n) :
    unrelabelRepeatedComponent e (relabelRepeatedComponent e component bounded) =
      component := by
  obtain ⟨atoms⟩ := component
  simp [relabelRepeatedComponent, unrelabelRepeatedComponent,
    unrelabelFinset_relabelFinset]

theorem relabelRepeatedComponent_unrelabelRepeatedComponent [DecidableEq V]
    (e : V ≃ Fin n) (component : SuppliedRingChainRepeatedComponent V) :
    relabelRepeatedComponent e (unrelabelRepeatedComponent e component)
        (unrelabelRepeatedComponentBounded e component) = component := by
  obtain ⟨atoms⟩ := component
  simp [relabelRepeatedComponent, unrelabelRepeatedComponent,
    relabelFinset_unrelabelFinset]

def relabelRepeatedComponentList [DecidableEq V] (e : V ≃ Fin n)
    (components : List P93RingChainRepeatedComponent)
    (bounded : ∀ component ∈ components, ∀ atom ∈ component.atoms, atom < n) :
    List (SuppliedRingChainRepeatedComponent V) :=
  components.attach.map fun component =>
    relabelRepeatedComponent e component.1 (bounded component.1 component.2)

def unrelabelRepeatedComponentList (e : V ≃ Fin n)
    (components : List (SuppliedRingChainRepeatedComponent V)) :
    List P93RingChainRepeatedComponent :=
  components.map (unrelabelRepeatedComponent e)

def unrelabelRepeatedComponentListBounded (e : V ≃ Fin n)
    (components : List (SuppliedRingChainRepeatedComponent V)) :
    ∀ component ∈ unrelabelRepeatedComponentList e components,
      ∀ atom ∈ component.atoms, atom < n := by
  intro component member atom atomMember
  rw [unrelabelRepeatedComponentList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact unrelabelRepeatedComponentBounded e presented atom atomMember

theorem unrelabelRepeatedComponentList_relabelRepeatedComponentList
    [DecidableEq V] (e : V ≃ Fin n) (components : List P93RingChainRepeatedComponent)
    (bounded : ∀ component ∈ components, ∀ atom ∈ component.atoms, atom < n) :
    unrelabelRepeatedComponentList e
        (relabelRepeatedComponentList e components bounded) = components := by
  unfold unrelabelRepeatedComponentList relabelRepeatedComponentList
  rw [List.map_map]
  trans components.attach.map Subtype.val
  · apply List.map_congr_left
    intro component _
    exact unrelabelRepeatedComponent_relabelRepeatedComponent e component.1
      (bounded component.1 component.2)
  · exact List.attach_map_subtype_val components

theorem relabelRepeatedComponentList_unrelabelRepeatedComponentList
    [DecidableEq V] (e : V ≃ Fin n)
    (components : List (SuppliedRingChainRepeatedComponent V)) :
    relabelRepeatedComponentList e
        (unrelabelRepeatedComponentList e components)
        (unrelabelRepeatedComponentListBounded e components) = components := by
  unfold relabelRepeatedComponentList unrelabelRepeatedComponentList
  rw [List.attach_map, List.map_map]
  trans components.attach.map Subtype.val
  · apply List.map_congr_left
    intro component _
    exact relabelRepeatedComponent_unrelabelRepeatedComponent e component.1
  · exact List.attach_map_subtype_val components

section AcyclicSources

variable {policy : P93AcyclicAuthorityPolicy}

/-! ## Acyclic evidence mirrors -/

/-- Every decoded acyclic assignment unit is in range. -/
def unrelabelRingChainAcyclicAssignmentBounded [DecidableEq V] (e : V ≃ Fin n)
    (assignment : OrganicStereoP93AcyclicIngress.SuppliedAcyclicAssignment V policy.Component) :
    OrganicStereoP93AcyclicIngress.UnitBoundedIn n
      (OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment e assignment).unit :=
  unrelabelUnitBounded e assignment.unit

structure SuppliedRingChainAcyclicCenter (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : OrganicStereoP93AcyclicIngress.SuppliedAcyclicAssignment V policy.Component
  centerNeedsLocantInBaseName : Bool
  isotopicAffixPresent : Bool
  observedAffixOrder : List BlueBookP93.Acyclic.AffixKind

def relabelRingChainAcyclicCenter [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93AcyclicSingleCenterAuthorityObservation policy)
    (bounded : OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.assignment.unit) :
    SuppliedRingChainAcyclicCenter V policy where
  assignment :=
    OrganicStereoP93AcyclicIngress.relabelAcyclicAssignment e observation.assignment bounded
  centerNeedsLocantInBaseName := observation.centerNeedsLocantInBaseName
  isotopicAffixPresent := observation.isotopicAffixPresent
  observedAffixOrder := observation.observedAffixOrder

def unrelabelRingChainAcyclicCenter [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainAcyclicCenter V policy) :
    P93AcyclicSingleCenterAuthorityObservation policy where
  assignment :=
    OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment e observation.assignment
  centerNeedsLocantInBaseName := observation.centerNeedsLocantInBaseName
  isotopicAffixPresent := observation.isotopicAffixPresent
  observedAffixOrder := observation.observedAffixOrder

def unrelabelRingChainAcyclicCenterBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainAcyclicCenter V policy) :
    OrganicStereoP93AcyclicIngress.UnitBoundedIn n
      (unrelabelRingChainAcyclicCenter e observation).assignment.unit :=
  unrelabelRingChainAcyclicAssignmentBounded e observation.assignment

theorem unrelabelRingChainAcyclicCenter_relabelRingChainAcyclicCenter [DecidableEq V]
    (e : V ≃ Fin n) (observation : P93AcyclicSingleCenterAuthorityObservation policy)
    (bounded : OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.assignment.unit) :
    unrelabelRingChainAcyclicCenter e
        (relabelRingChainAcyclicCenter e observation bounded) = observation := by
  obtain ⟨assignment, locant, isotopic, order⟩ := observation
  simp [relabelRingChainAcyclicCenter, unrelabelRingChainAcyclicCenter,
    OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment_relabelAcyclicAssignment]

theorem relabelRingChainAcyclicCenter_unrelabelRingChainAcyclicCenter [DecidableEq V]
    (e : V ≃ Fin n) (observation : SuppliedRingChainAcyclicCenter V policy) :
    relabelRingChainAcyclicCenter e (unrelabelRingChainAcyclicCenter e observation)
        (unrelabelRingChainAcyclicCenterBounded e observation) = observation := by
  obtain ⟨assignment, locant, isotopic, order⟩ := observation
  simp [relabelRingChainAcyclicCenter, unrelabelRingChainAcyclicCenter,
    unrelabelRingChainAcyclicCenterBounded,
    OrganicStereoP93AcyclicIngress.relabelAcyclicAssignment_unrelabelAcyclicAssignment]

structure SuppliedRingChainAcyclicDoubleBond (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : OrganicStereoP93AcyclicIngress.SuppliedAcyclicAssignment V policy.Component
  context : BlueBookP93.Acyclic.NomenclatureContext
  carbonContext : BlueBookP93.Acyclic.CarbonDoubleBondContext

def relabelRingChainAcyclicDoubleBond [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93AcyclicDoubleBondAuthorityObservation policy)
    (bounded : OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.assignment.unit) :
    SuppliedRingChainAcyclicDoubleBond V policy where
  assignment :=
    OrganicStereoP93AcyclicIngress.relabelAcyclicAssignment e observation.assignment bounded
  context := observation.context
  carbonContext := observation.carbonContext

def unrelabelRingChainAcyclicDoubleBond [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainAcyclicDoubleBond V policy) :
    P93AcyclicDoubleBondAuthorityObservation policy where
  assignment :=
    OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment e observation.assignment
  context := observation.context
  carbonContext := observation.carbonContext

def unrelabelRingChainAcyclicDoubleBondBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainAcyclicDoubleBond V policy) :
    OrganicStereoP93AcyclicIngress.UnitBoundedIn n
      (unrelabelRingChainAcyclicDoubleBond e observation).assignment.unit :=
  unrelabelRingChainAcyclicAssignmentBounded e observation.assignment

theorem unrelabelRingChainAcyclicDoubleBond_relabelRingChainAcyclicDoubleBond
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93AcyclicDoubleBondAuthorityObservation policy)
    (bounded : OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.assignment.unit) :
    unrelabelRingChainAcyclicDoubleBond e
        (relabelRingChainAcyclicDoubleBond e observation bounded) = observation := by
  obtain ⟨assignment, context, carbonContext⟩ := observation
  simp [relabelRingChainAcyclicDoubleBond, unrelabelRingChainAcyclicDoubleBond,
    OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment_relabelAcyclicAssignment]

theorem relabelRingChainAcyclicDoubleBond_unrelabelRingChainAcyclicDoubleBond
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainAcyclicDoubleBond V policy) :
    relabelRingChainAcyclicDoubleBond e
        (unrelabelRingChainAcyclicDoubleBond e observation)
        (unrelabelRingChainAcyclicDoubleBondBounded e observation) = observation := by
  obtain ⟨assignment, context, carbonContext⟩ := observation
  simp [relabelRingChainAcyclicDoubleBond, unrelabelRingChainAcyclicDoubleBond,
    unrelabelRingChainAcyclicDoubleBondBounded,
    OrganicStereoP93AcyclicIngress.relabelAcyclicAssignment_unrelabelAcyclicAssignment]

structure SuppliedRingChainAcyclicEvenCumulene (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : OrganicStereoP93AcyclicIngress.SuppliedAcyclicAssignment V policy.Component
  context : BlueBookP93.Acyclic.NomenclatureContext
  generalDescriptor : BlueBookP93.Acyclic.Descriptor
  preferredDescriptor : BlueBookP93.Acyclic.Descriptor

def relabelRingChainAcyclicEvenCumulene [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93AcyclicEvenCumuleneAuthorityObservation policy)
    (bounded : OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.assignment.unit) :
    SuppliedRingChainAcyclicEvenCumulene V policy where
  assignment :=
    OrganicStereoP93AcyclicIngress.relabelAcyclicAssignment e observation.assignment bounded
  context := observation.context
  generalDescriptor := observation.generalDescriptor
  preferredDescriptor := observation.preferredDescriptor

def unrelabelRingChainAcyclicEvenCumulene [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainAcyclicEvenCumulene V policy) :
    P93AcyclicEvenCumuleneAuthorityObservation policy where
  assignment :=
    OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment e observation.assignment
  context := observation.context
  generalDescriptor := observation.generalDescriptor
  preferredDescriptor := observation.preferredDescriptor

def unrelabelRingChainAcyclicEvenCumuleneBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainAcyclicEvenCumulene V policy) :
    OrganicStereoP93AcyclicIngress.UnitBoundedIn n
      (unrelabelRingChainAcyclicEvenCumulene e observation).assignment.unit :=
  unrelabelRingChainAcyclicAssignmentBounded e observation.assignment

theorem unrelabelRingChainAcyclicEvenCumulene_relabelRingChainAcyclicEvenCumulene
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93AcyclicEvenCumuleneAuthorityObservation policy)
    (bounded : OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.assignment.unit) :
    unrelabelRingChainAcyclicEvenCumulene e
        (relabelRingChainAcyclicEvenCumulene e observation bounded) = observation := by
  obtain ⟨assignment, context, generalDescriptor, preferredDescriptor⟩ := observation
  simp [relabelRingChainAcyclicEvenCumulene, unrelabelRingChainAcyclicEvenCumulene,
    OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment_relabelAcyclicAssignment]

theorem relabelRingChainAcyclicEvenCumulene_unrelabelRingChainAcyclicEvenCumulene
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainAcyclicEvenCumulene V policy) :
    relabelRingChainAcyclicEvenCumulene e
        (unrelabelRingChainAcyclicEvenCumulene e observation)
        (unrelabelRingChainAcyclicEvenCumuleneBounded e observation) = observation := by
  obtain ⟨assignment, context, generalDescriptor, preferredDescriptor⟩ := observation
  simp [relabelRingChainAcyclicEvenCumulene, unrelabelRingChainAcyclicEvenCumulene,
    unrelabelRingChainAcyclicEvenCumuleneBounded,
    OrganicStereoP93AcyclicIngress.relabelAcyclicAssignment_unrelabelAcyclicAssignment]

structure SuppliedRingChainAcyclicOddCumulene (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : OrganicStereoP93AcyclicIngress.SuppliedAcyclicAssignment V policy.Component
  geometry : BlueBookP93.Acyclic.OddCumuleneTerminalGeometry

def relabelRingChainAcyclicOddCumulene [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93AcyclicOddCumuleneAuthorityObservation policy)
    (bounded : OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.assignment.unit) :
    SuppliedRingChainAcyclicOddCumulene V policy where
  assignment :=
    OrganicStereoP93AcyclicIngress.relabelAcyclicAssignment e observation.assignment bounded
  geometry := observation.geometry

def unrelabelRingChainAcyclicOddCumulene [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainAcyclicOddCumulene V policy) :
    P93AcyclicOddCumuleneAuthorityObservation policy where
  assignment :=
    OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment e observation.assignment
  geometry := observation.geometry

def unrelabelRingChainAcyclicOddCumuleneBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainAcyclicOddCumulene V policy) :
    OrganicStereoP93AcyclicIngress.UnitBoundedIn n
      (unrelabelRingChainAcyclicOddCumulene e observation).assignment.unit :=
  unrelabelRingChainAcyclicAssignmentBounded e observation.assignment

theorem unrelabelRingChainAcyclicOddCumulene_relabelRingChainAcyclicOddCumulene
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93AcyclicOddCumuleneAuthorityObservation policy)
    (bounded : OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.assignment.unit) :
    unrelabelRingChainAcyclicOddCumulene e
        (relabelRingChainAcyclicOddCumulene e observation bounded) = observation := by
  obtain ⟨assignment, geometry⟩ := observation
  simp [relabelRingChainAcyclicOddCumulene, unrelabelRingChainAcyclicOddCumulene,
    OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment_relabelAcyclicAssignment]

theorem relabelRingChainAcyclicOddCumulene_unrelabelRingChainAcyclicOddCumulene
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainAcyclicOddCumulene V policy) :
    relabelRingChainAcyclicOddCumulene e
        (unrelabelRingChainAcyclicOddCumulene e observation)
        (unrelabelRingChainAcyclicOddCumuleneBounded e observation) = observation := by
  obtain ⟨assignment, geometry⟩ := observation
  simp [relabelRingChainAcyclicOddCumulene, unrelabelRingChainAcyclicOddCumulene,
    unrelabelRingChainAcyclicOddCumuleneBounded,
    OrganicStereoP93AcyclicIngress.relabelAcyclicAssignment_unrelabelAcyclicAssignment]

end AcyclicSources

section MonocyclicSources

variable {policy : P93MonocyclicAuthorityPolicy}

/-! ## Monocyclic evidence mirrors -/

structure SuppliedRingChainMonocyclicPhysicalUnit (V : Type*) where
  ringAtoms : List V
  unit : SuppliedPhysicalUnit V

def MonocyclicPhysicalUnitBoundedIn (n : Nat)
    (unit : P93MonocyclicPhysicalUnit) : Prop :=
  (∀ atom ∈ unit.ringAtoms, atom < n) ∧
    OrganicStereoP93AcyclicIngress.UnitBoundedIn n unit.unit

def relabelMonocyclicPhysicalUnit [DecidableEq V] (e : V ≃ Fin n)
    (unit : P93MonocyclicPhysicalUnit)
    (bounded : MonocyclicPhysicalUnitBoundedIn n unit) :
    SuppliedRingChainMonocyclicPhysicalUnit V where
  ringAtoms := relabelList e unit.ringAtoms bounded.1
  unit := relabelUnit e unit.unit bounded.2

def unrelabelMonocyclicPhysicalUnit (e : V ≃ Fin n)
    (unit : SuppliedRingChainMonocyclicPhysicalUnit V) :
    P93MonocyclicPhysicalUnit where
  ringAtoms := unrelabelList e unit.ringAtoms
  unit := unrelabelUnit e unit.unit

def unrelabelMonocyclicPhysicalUnitBounded (e : V ≃ Fin n)
    (unit : SuppliedRingChainMonocyclicPhysicalUnit V) :
    MonocyclicPhysicalUnitBoundedIn n (unrelabelMonocyclicPhysicalUnit e unit) :=
  ⟨unrelabelList_bounded e unit.ringAtoms, unrelabelUnitBounded e unit.unit⟩

theorem unrelabelMonocyclicPhysicalUnit_relabelMonocyclicPhysicalUnit
    [DecidableEq V] (e : V ≃ Fin n) (unit : P93MonocyclicPhysicalUnit)
    (bounded : MonocyclicPhysicalUnitBoundedIn n unit) :
    unrelabelMonocyclicPhysicalUnit e
        (relabelMonocyclicPhysicalUnit e unit bounded) = unit := by
  obtain ⟨ringAtoms, physicalUnit⟩ := unit
  simp [relabelMonocyclicPhysicalUnit, unrelabelMonocyclicPhysicalUnit,
    unrelabelList_relabelList, unrelabelUnit_relabelUnit]

theorem relabelMonocyclicPhysicalUnit_unrelabelMonocyclicPhysicalUnit
    [DecidableEq V] (e : V ≃ Fin n)
    (unit : SuppliedRingChainMonocyclicPhysicalUnit V) :
    relabelMonocyclicPhysicalUnit e (unrelabelMonocyclicPhysicalUnit e unit)
        (unrelabelMonocyclicPhysicalUnitBounded e unit) = unit := by
  obtain ⟨ringAtoms, physicalUnit⟩ := unit
  simp [relabelMonocyclicPhysicalUnit, unrelabelMonocyclicPhysicalUnit,
    unrelabelMonocyclicPhysicalUnitBounded,
    relabelList_unrelabelList, relabelUnit_unrelabelUnit]

structure SuppliedRingChainMonocyclicCenter (V : Type*)
    (policy : P93MonocyclicAuthorityPolicy) where
  physical : SuppliedRingChainMonocyclicPhysicalUnit V
  citation : P93AuthorityCitationToken
  kind : BlueBookP93.Acyclic.UnitKind
  descriptor : BlueBookP93.Acyclic.Descriptor
  knowledge : BlueBookP93.Cyclic.ConfigurationKnowledge
  «notation» : BlueBookP93.Cyclic.MonocycleNotation

def relabelRingChainMonocyclicCenter [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93MonocyclicCenterAuthorityObservation policy)
    (bounded : MonocyclicPhysicalUnitBoundedIn n observation.physical) :
    SuppliedRingChainMonocyclicCenter V policy where
  physical := relabelMonocyclicPhysicalUnit e observation.physical bounded
  citation := observation.citation
  kind := observation.kind
  descriptor := observation.descriptor
  knowledge := observation.knowledge
  «notation» := observation.«notation»

def unrelabelRingChainMonocyclicCenter [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainMonocyclicCenter V policy) :
    P93MonocyclicCenterAuthorityObservation policy where
  physical := unrelabelMonocyclicPhysicalUnit e observation.physical
  citation := observation.citation
  kind := observation.kind
  descriptor := observation.descriptor
  knowledge := observation.knowledge
  «notation» := observation.«notation»

def unrelabelRingChainMonocyclicCenterBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainMonocyclicCenter V policy) :
    MonocyclicPhysicalUnitBoundedIn n
      (unrelabelRingChainMonocyclicCenter e observation).physical :=
  unrelabelMonocyclicPhysicalUnitBounded e observation.physical

theorem unrelabelRingChainMonocyclicCenter_relabelRingChainMonocyclicCenter
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93MonocyclicCenterAuthorityObservation policy)
    (bounded : MonocyclicPhysicalUnitBoundedIn n observation.physical) :
    unrelabelRingChainMonocyclicCenter e
        (relabelRingChainMonocyclicCenter e observation bounded) = observation := by
  obtain ⟨physical, citation, kind, descriptor, knowledge, notationData⟩ := observation
  simp [relabelRingChainMonocyclicCenter, unrelabelRingChainMonocyclicCenter,
    unrelabelMonocyclicPhysicalUnit_relabelMonocyclicPhysicalUnit]

theorem relabelRingChainMonocyclicCenter_unrelabelRingChainMonocyclicCenter
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainMonocyclicCenter V policy) :
    relabelRingChainMonocyclicCenter e
        (unrelabelRingChainMonocyclicCenter e observation)
        (unrelabelRingChainMonocyclicCenterBounded e observation) = observation := by
  obtain ⟨physical, citation, kind, descriptor, knowledge, notationData⟩ := observation
  simp [relabelRingChainMonocyclicCenter, unrelabelRingChainMonocyclicCenter,
    unrelabelRingChainMonocyclicCenterBounded,
    relabelMonocyclicPhysicalUnit_unrelabelMonocyclicPhysicalUnit]

structure SuppliedRingChainMonocyclicDoubleBond (V : Type*)
    (policy : P93MonocyclicAuthorityPolicy) where
  physical : SuppliedRingChainMonocyclicPhysicalUnit V
  doubleBondCount : Nat
  geometry : BlueBookP93.Cyclic.MonocyclicSeniorLigandGeometry
  descriptor? : Option BlueBookP93.Acyclic.Descriptor

def relabelRingChainMonocyclicDoubleBond [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93MonocyclicDoubleBondAuthorityObservation policy)
    (bounded : MonocyclicPhysicalUnitBoundedIn n observation.physical) :
    SuppliedRingChainMonocyclicDoubleBond V policy where
  physical := relabelMonocyclicPhysicalUnit e observation.physical bounded
  doubleBondCount := observation.doubleBondCount
  geometry := observation.geometry
  descriptor? := observation.descriptor?

def unrelabelRingChainMonocyclicDoubleBond [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainMonocyclicDoubleBond V policy) :
    P93MonocyclicDoubleBondAuthorityObservation policy where
  physical := unrelabelMonocyclicPhysicalUnit e observation.physical
  doubleBondCount := observation.doubleBondCount
  geometry := observation.geometry
  descriptor? := observation.descriptor?

def unrelabelRingChainMonocyclicDoubleBondBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainMonocyclicDoubleBond V policy) :
    MonocyclicPhysicalUnitBoundedIn n
      (unrelabelRingChainMonocyclicDoubleBond e observation).physical :=
  unrelabelMonocyclicPhysicalUnitBounded e observation.physical

theorem unrelabelRingChainMonocyclicDoubleBond_relabelRingChainMonocyclicDoubleBond
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93MonocyclicDoubleBondAuthorityObservation policy)
    (bounded : MonocyclicPhysicalUnitBoundedIn n observation.physical) :
    unrelabelRingChainMonocyclicDoubleBond e
        (relabelRingChainMonocyclicDoubleBond e observation bounded) = observation := by
  obtain ⟨physical, doubleBondCount, geometry, descriptor?⟩ := observation
  simp [relabelRingChainMonocyclicDoubleBond, unrelabelRingChainMonocyclicDoubleBond,
    unrelabelMonocyclicPhysicalUnit_relabelMonocyclicPhysicalUnit]

theorem relabelRingChainMonocyclicDoubleBond_unrelabelRingChainMonocyclicDoubleBond
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainMonocyclicDoubleBond V policy) :
    relabelRingChainMonocyclicDoubleBond e
        (unrelabelRingChainMonocyclicDoubleBond e observation)
        (unrelabelRingChainMonocyclicDoubleBondBounded e observation) = observation := by
  obtain ⟨physical, doubleBondCount, geometry, descriptor?⟩ := observation
  simp [relabelRingChainMonocyclicDoubleBond, unrelabelRingChainMonocyclicDoubleBond,
    unrelabelRingChainMonocyclicDoubleBondBounded,
    relabelMonocyclicPhysicalUnit_unrelabelMonocyclicPhysicalUnit]

end MonocyclicSources

section FusedSources

variable {policy : P93FusedAuthorityPolicy}

/-! ## Fused evidence mirrors -/

structure SuppliedRingChainFusionEdge (V : Type*) where
  first : V
  second : V
  deriving DecidableEq

def relabelFusionEdgeList [DecidableEq V] (e : V ≃ Fin n)
    (edges : List P93AuthorityFusionEdge)
    (bounded : ∀ edge ∈ edges, edge.first < n ∧ edge.second < n) :
    List (SuppliedRingChainFusionEdge V) :=
  edges.attach.map fun edge =>
    { first := decodeAtom e edge.1.first (bounded edge.1 edge.2).1
      second := decodeAtom e edge.1.second (bounded edge.1 edge.2).2 }

def unrelabelFusionEdgeList (e : V ≃ Fin n)
    (edges : List (SuppliedRingChainFusionEdge V)) :
    List P93AuthorityFusionEdge :=
  edges.map fun edge =>
    { first := encodeAtom e edge.first, second := encodeAtom e edge.second }

def unrelabelFusionEdgeListBounded (e : V ≃ Fin n)
    (edges : List (SuppliedRingChainFusionEdge V)) :
    ∀ edge ∈ unrelabelFusionEdgeList e edges,
      edge.first < n ∧ edge.second < n := by
  intro edge member
  rw [unrelabelFusionEdgeList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact ⟨encodeAtom_lt e presented.first, encodeAtom_lt e presented.second⟩

theorem unrelabelFusionEdgeList_relabelFusionEdgeList [DecidableEq V]
    (e : V ≃ Fin n) (edges : List P93AuthorityFusionEdge)
    (bounded : ∀ edge ∈ edges, edge.first < n ∧ edge.second < n) :
    unrelabelFusionEdgeList e (relabelFusionEdgeList e edges bounded) = edges := by
  unfold unrelabelFusionEdgeList relabelFusionEdgeList
  rw [List.map_map]
  trans edges.attach.map Subtype.val
  · apply List.map_congr_left
    intro edge _
    obtain ⟨edgeValue, edgeMember⟩ := edge
    rcases edgeValue with ⟨first, second⟩
    simp [encodeAtom_decodeAtom]
  · exact List.attach_map_subtype_val edges

theorem relabelFusionEdgeList_unrelabelFusionEdgeList [DecidableEq V]
    (e : V ≃ Fin n) (edges : List (SuppliedRingChainFusionEdge V)) :
    relabelFusionEdgeList e (unrelabelFusionEdgeList e edges)
        (unrelabelFusionEdgeListBounded e edges) = edges := by
  unfold relabelFusionEdgeList unrelabelFusionEdgeList
  rw [List.attach_map, List.map_map]
  trans edges.attach.map Subtype.val
  · apply List.map_congr_left
    intro edge _
    obtain ⟨presented, _presentedMember⟩ := edge
    rcases presented with ⟨first, second⟩
    simp [decodeAtom_encodeAtom]
  · exact List.attach_map_subtype_val edges

structure SuppliedRingChainFusedSystem (V : Type*) where
  atoms : List V
  fusionEdges : List (SuppliedRingChainFusionEdge V)
  fusionLocants : List (V × P93FusedLocant)

def FusedSystemBoundedIn (n : Nat) (system : P93AuthorityFusedSystem) : Prop :=
  (∀ atom ∈ system.atoms, atom < n) ∧
    (∀ edge ∈ system.fusionEdges, edge.first < n ∧ edge.second < n) ∧
    ∀ value ∈ system.fusionLocants, value.1 < n

def relabelFusedSystem [DecidableEq V] (e : V ≃ Fin n)
    (system : P93AuthorityFusedSystem)
    (bounded : FusedSystemBoundedIn n system) :
    SuppliedRingChainFusedSystem V where
  atoms := relabelList e system.atoms bounded.1
  fusionEdges := relabelFusionEdgeList e system.fusionEdges bounded.2.1
  fusionLocants := relabelAtomLocantList e system.fusionLocants bounded.2.2

def unrelabelFusedSystem (e : V ≃ Fin n)
    (system : SuppliedRingChainFusedSystem V) :
    P93AuthorityFusedSystem where
  atoms := unrelabelList e system.atoms
  fusionEdges := unrelabelFusionEdgeList e system.fusionEdges
  fusionLocants := unrelabelAtomLocantList e system.fusionLocants

def unrelabelFusedSystemBounded (e : V ≃ Fin n)
    (system : SuppliedRingChainFusedSystem V) :
    FusedSystemBoundedIn n (unrelabelFusedSystem e system) :=
  ⟨unrelabelList_bounded e system.atoms,
    unrelabelFusionEdgeListBounded e system.fusionEdges,
    unrelabelAtomLocantListBounded e system.fusionLocants⟩

theorem unrelabelFusedSystem_relabelFusedSystem [DecidableEq V]
    (e : V ≃ Fin n) (system : P93AuthorityFusedSystem)
    (bounded : FusedSystemBoundedIn n system) :
    unrelabelFusedSystem e (relabelFusedSystem e system bounded) = system := by
  obtain ⟨atoms, fusionEdges, fusionLocants⟩ := system
  simp only [relabelFusedSystem, unrelabelFusedSystem]
  rw [P93AuthorityFusedSystem.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · exact unrelabelList_relabelList e atoms bounded.1
  · exact unrelabelFusionEdgeList_relabelFusionEdgeList e fusionEdges bounded.2.1
  · exact unrelabelAtomLocantList_relabelAtomLocantList e fusionLocants bounded.2.2

theorem relabelFusedSystem_unrelabelFusedSystem [DecidableEq V]
    (e : V ≃ Fin n) (system : SuppliedRingChainFusedSystem V) :
    relabelFusedSystem e (unrelabelFusedSystem e system)
        (unrelabelFusedSystemBounded e system) = system := by
  obtain ⟨atoms, fusionEdges, fusionLocants⟩ := system
  simp only [relabelFusedSystem, unrelabelFusedSystem, unrelabelFusedSystemBounded]
  rw [SuppliedRingChainFusedSystem.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · exact relabelList_unrelabelList e atoms
  · exact relabelFusionEdgeList_unrelabelFusionEdgeList e fusionEdges
  · exact relabelAtomLocantList_unrelabelAtomLocantList e fusionLocants

inductive SuppliedRingChainFusedUnit (V : Type*) where
  | physical (unit : SuppliedPhysicalUnit V)
  | fusedAxis (path : List V)

def FusedUnitBoundedIn (n : Nat) : P93FusedAuthorityUnit → Prop
  | .physical unit => OrganicStereoP93AcyclicIngress.UnitBoundedIn n unit
  | .fusedAxis path => ∀ atom ∈ path, atom < n

def relabelFusedUnit [DecidableEq V] (e : V ≃ Fin n) :
    (unit : P93FusedAuthorityUnit) → FusedUnitBoundedIn n unit →
      SuppliedRingChainFusedUnit V
  | .physical unit, bounded => .physical (relabelUnit e unit bounded)
  | .fusedAxis path, bounded => .fusedAxis (relabelList e path bounded)

def unrelabelFusedUnit (e : V ≃ Fin n) :
    SuppliedRingChainFusedUnit V → P93FusedAuthorityUnit
  | .physical unit => .physical (unrelabelUnit e unit)
  | .fusedAxis path => .fusedAxis (unrelabelList e path)

def unrelabelFusedUnitBounded (e : V ≃ Fin n) :
    (unit : SuppliedRingChainFusedUnit V) →
      FusedUnitBoundedIn n (unrelabelFusedUnit e unit)
  | .physical unit => unrelabelUnitBounded e unit
  | .fusedAxis path => unrelabelList_bounded e path

theorem unrelabelFusedUnit_relabelFusedUnit [DecidableEq V] (e : V ≃ Fin n)
    (unit : P93FusedAuthorityUnit) (bounded : FusedUnitBoundedIn n unit) :
    unrelabelFusedUnit e (relabelFusedUnit e unit bounded) = unit := by
  cases unit with
  | physical physicalUnit =>
      simp [relabelFusedUnit, unrelabelFusedUnit, unrelabelUnit_relabelUnit]
  | fusedAxis path =>
      simp [relabelFusedUnit, unrelabelFusedUnit, unrelabelList_relabelList]

theorem relabelFusedUnit_unrelabelFusedUnit [DecidableEq V] (e : V ≃ Fin n)
    (unit : SuppliedRingChainFusedUnit V) :
    relabelFusedUnit e (unrelabelFusedUnit e unit)
        (unrelabelFusedUnitBounded e unit) = unit := by
  cases unit with
  | physical physicalUnit =>
      simp [relabelFusedUnit, unrelabelFusedUnit, relabelUnit_unrelabelUnit]
  | fusedAxis path =>
      simp [relabelFusedUnit, unrelabelFusedUnit, relabelList_unrelabelList]

structure SuppliedRingChainFusedCIP (V : Type*)
    (policy : P93FusedAuthorityPolicy) where
  system : SuppliedRingChainFusedSystem V
  unit : SuppliedRingChainFusedUnit V
  citation : P93FusedLocant
  descriptor : BlueBookP93.Cyclic.FusedUnitDescriptor

structure FusedCIPBoundedIn (n : Nat) (policy : P93FusedAuthorityPolicy)
    (observation : P93FusedCIPAuthorityObservation policy) : Prop where
  system : FusedSystemBoundedIn n observation.system
  unit : FusedUnitBoundedIn n observation.unit

def relabelRingChainFusedCIP [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93FusedCIPAuthorityObservation policy)
    (bounded : FusedCIPBoundedIn n policy observation) :
    SuppliedRingChainFusedCIP V policy where
  system := relabelFusedSystem e observation.system bounded.system
  unit := relabelFusedUnit e observation.unit bounded.unit
  citation := observation.citation
  descriptor := observation.descriptor

def unrelabelRingChainFusedCIP [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainFusedCIP V policy) :
    P93FusedCIPAuthorityObservation policy where
  system := unrelabelFusedSystem e observation.system
  unit := unrelabelFusedUnit e observation.unit
  citation := observation.citation
  descriptor := observation.descriptor

def unrelabelRingChainFusedCIPBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainFusedCIP V policy) :
    FusedCIPBoundedIn n policy (unrelabelRingChainFusedCIP e observation) :=
  ⟨unrelabelFusedSystemBounded e observation.system,
    unrelabelFusedUnitBounded e observation.unit⟩

theorem unrelabelRingChainFusedCIP_relabelRingChainFusedCIP [DecidableEq V]
    (e : V ≃ Fin n) (observation : P93FusedCIPAuthorityObservation policy)
    (bounded : FusedCIPBoundedIn n policy observation) :
    unrelabelRingChainFusedCIP e
        (relabelRingChainFusedCIP e observation bounded) = observation := by
  obtain ⟨system, unit, citation, descriptor⟩ := observation
  simp [relabelRingChainFusedCIP, unrelabelRingChainFusedCIP,
    unrelabelFusedSystem_relabelFusedSystem, unrelabelFusedUnit_relabelFusedUnit]

theorem relabelRingChainFusedCIP_unrelabelRingChainFusedCIP [DecidableEq V]
    (e : V ≃ Fin n) (observation : SuppliedRingChainFusedCIP V policy) :
    relabelRingChainFusedCIP e (unrelabelRingChainFusedCIP e observation)
        (unrelabelRingChainFusedCIPBounded e observation) = observation := by
  obtain ⟨system, unit, citation, descriptor⟩ := observation
  simp [relabelRingChainFusedCIP, unrelabelRingChainFusedCIP,
    unrelabelRingChainFusedCIPBounded,
    relabelFusedSystem_unrelabelFusedSystem, relabelFusedUnit_unrelabelFusedUnit]

end FusedSources

section CyclophaneSources

variable {policy : P93CyclophaneAuthorityPolicy}

/-! ## Cyclophane evidence mirrors -/

/-- Bounds on every atom reference of a planar frame, derived from its decoded record. -/
def planeFrameBoundedIn_decodePlane [DecidableEq V] (e : V ≃ Fin n)
    (native : NativePlanarFrame V) :
    PlaneFrameBoundedIn n (decodePlane e native) :=
  { pilotBound := encodeAtom_lt e native.pilotAtom
    firstBound := encodeAtom_lt e native.firstReference
    secondBound := encodeAtom_lt e native.secondReference
    inPlaneBound := encodeAtom_lt e native.inPlaneBondAtom
    outOfPlaneBound := encodeAtom_lt e native.outOfPlaneAtom
    planeAtomsBound := fun atom member =>
      unrelabelList_bounded e native.planeAtoms atom member }

theorem relabelPlane_decodePlane [DecidableEq V] (e : V ≃ Fin n)
    (native : NativePlanarFrame V) :
    relabelPlane e (decodePlane e native)
        (planeFrameBoundedIn_decodePlane e native) = native := by
  obtain ⟨planeAtoms, pilotAtom, firstReference, secondReference, inPlaneBondAtom,
    outOfPlaneAtom, torsionRestricted, planeCannotBeSymmetryPlane⟩ := native
  simp [decodePlane, relabelPlane, relabelList_unrelabelList, decodeAtom_encodeAtom]

structure SuppliedRingChainCyclophaneSystem (V : Type*) where
  atomCarrier : List V
  phaneNodes : List (Finset V)
  rings : List (List V)
  ringPhaneCycles : List (List Nat × List Nat)

def CyclophaneSystemBoundedIn (n : Nat) (system : P93AuthorityCyclophaneSystem) : Prop :=
  (∀ atom ∈ system.atomCarrier, atom < n) ∧
    (∀ node ∈ system.phaneNodes, ∀ atom ∈ node, atom < n) ∧
    ∀ ring ∈ system.rings, ∀ atom ∈ ring, atom < n

def relabelCyclophaneSystem [DecidableEq V] (e : V ≃ Fin n)
    (system : P93AuthorityCyclophaneSystem)
    (bounded : CyclophaneSystemBoundedIn n system) :
    SuppliedRingChainCyclophaneSystem V where
  atomCarrier := relabelList e system.atomCarrier bounded.1
  phaneNodes := relabelFinsetList e system.phaneNodes bounded.2.1
  rings := relabelListList e system.rings bounded.2.2
  ringPhaneCycles := system.ringPhaneCycles

def unrelabelCyclophaneSystem (e : V ≃ Fin n)
    (system : SuppliedRingChainCyclophaneSystem V) :
    P93AuthorityCyclophaneSystem where
  atomCarrier := unrelabelList e system.atomCarrier
  phaneNodes := unrelabelFinsetList e system.phaneNodes
  rings := unrelabelListList e system.rings
  ringPhaneCycles := system.ringPhaneCycles

def unrelabelCyclophaneSystemBounded (e : V ≃ Fin n)
    (system : SuppliedRingChainCyclophaneSystem V) :
    CyclophaneSystemBoundedIn n (unrelabelCyclophaneSystem e system) :=
  ⟨unrelabelList_bounded e system.atomCarrier,
    unrelabelFinsetListBounded e system.phaneNodes,
    unrelabelListListBounded e system.rings⟩

theorem unrelabelCyclophaneSystem_relabelCyclophaneSystem [DecidableEq V]
    (e : V ≃ Fin n) (system : P93AuthorityCyclophaneSystem)
    (bounded : CyclophaneSystemBoundedIn n system) :
    unrelabelCyclophaneSystem e (relabelCyclophaneSystem e system bounded) = system := by
  obtain ⟨atomCarrier, phaneNodes, rings, ringPhaneCycles⟩ := system
  simp only [relabelCyclophaneSystem, unrelabelCyclophaneSystem]
  rw [P93AuthorityCyclophaneSystem.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact unrelabelList_relabelList e atomCarrier bounded.1
  · exact unrelabelFinsetList_relabelFinsetList e phaneNodes bounded.2.1
  · exact unrelabelListList_relabelListList e rings bounded.2.2
  · rfl

theorem relabelCyclophaneSystem_unrelabelCyclophaneSystem [DecidableEq V]
    (e : V ≃ Fin n) (system : SuppliedRingChainCyclophaneSystem V) :
    relabelCyclophaneSystem e (unrelabelCyclophaneSystem e system)
        (unrelabelCyclophaneSystemBounded e system) = system := by
  obtain ⟨atomCarrier, phaneNodes, rings, ringPhaneCycles⟩ := system
  simp only [relabelCyclophaneSystem, unrelabelCyclophaneSystem,
    unrelabelCyclophaneSystemBounded]
  rw [SuppliedRingChainCyclophaneSystem.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact relabelList_unrelabelList e atomCarrier
  · exact relabelFinsetList_unrelabelFinsetList e phaneNodes
  · exact relabelListList_unrelabelListList e rings
  · rfl

structure SuppliedRingChainCyclophaneRCTReferenceCandidate (V : Type*) where
  center : V
  citation : P93AuthorityCitationToken
  namedAsSuffix : Bool
  sequencePriority : Nat

structure SuppliedRingChainCyclophaneRCTLocatedAssignment (V : Type*) where
  center : V
  citation : P93AuthorityCitationToken
  side : BlueBookP93.Cyclic.RingSide
  descriptor : BlueBookP93.Cyclic.RCTDescriptor

def relabelCyclophaneCandidate [DecidableEq V] (e : V ≃ Fin n)
    (candidate : P93CyclophaneRCTReferenceCandidate)
    (bounded : candidate.center < n) :
    SuppliedRingChainCyclophaneRCTReferenceCandidate V where
  center := decodeAtom e candidate.center bounded
  citation := candidate.citation
  namedAsSuffix := candidate.namedAsSuffix
  sequencePriority := candidate.sequencePriority

def unrelabelCyclophaneCandidate (e : V ≃ Fin n)
    (candidate : SuppliedRingChainCyclophaneRCTReferenceCandidate V) :
    P93CyclophaneRCTReferenceCandidate where
  center := encodeAtom e candidate.center
  citation := candidate.citation
  namedAsSuffix := candidate.namedAsSuffix
  sequencePriority := candidate.sequencePriority

def relabelCyclophaneCandidateList [DecidableEq V] (e : V ≃ Fin n)
    (candidates : List P93CyclophaneRCTReferenceCandidate)
    (bounded : ∀ candidate ∈ candidates, candidate.center < n) :
    List (SuppliedRingChainCyclophaneRCTReferenceCandidate V) :=
  candidates.attach.map fun candidate =>
    relabelCyclophaneCandidate e candidate.1 (bounded candidate.1 candidate.2)

def unrelabelCyclophaneCandidateList (e : V ≃ Fin n)
    (candidates : List (SuppliedRingChainCyclophaneRCTReferenceCandidate V)) :
    List P93CyclophaneRCTReferenceCandidate :=
  candidates.map (unrelabelCyclophaneCandidate e)

def unrelabelCyclophaneCandidateListBounded (e : V ≃ Fin n)
    (candidates : List (SuppliedRingChainCyclophaneRCTReferenceCandidate V)) :
    ∀ candidate ∈ unrelabelCyclophaneCandidateList e candidates, candidate.center < n := by
  intro candidate member
  rw [unrelabelCyclophaneCandidateList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact encodeAtom_lt e presented.center

theorem unrelabelCyclophaneCandidate_relabelCyclophaneCandidate [DecidableEq V]
    (e : V ≃ Fin n) (candidate : P93CyclophaneRCTReferenceCandidate)
    (bounded : candidate.center < n) :
    unrelabelCyclophaneCandidate e (relabelCyclophaneCandidate e candidate bounded) =
      candidate := by
  obtain ⟨center, citation, namedAsSuffix, sequencePriority⟩ := candidate
  simp [relabelCyclophaneCandidate, unrelabelCyclophaneCandidate, encodeAtom_decodeAtom]

theorem relabelCyclophaneCandidate_unrelabelCyclophaneCandidate [DecidableEq V]
    (e : V ≃ Fin n) (candidate : SuppliedRingChainCyclophaneRCTReferenceCandidate V) :
    relabelCyclophaneCandidate e (unrelabelCyclophaneCandidate e candidate)
        (encodeAtom_lt e candidate.center) = candidate := by
  obtain ⟨center, citation, namedAsSuffix, sequencePriority⟩ := candidate
  simp [relabelCyclophaneCandidate, unrelabelCyclophaneCandidate, decodeAtom_encodeAtom]

theorem unrelabelCyclophaneCandidateList_relabelCyclophaneCandidateList
    [DecidableEq V] (e : V ≃ Fin n)
    (candidates : List P93CyclophaneRCTReferenceCandidate)
    (bounded : ∀ candidate ∈ candidates, candidate.center < n) :
    unrelabelCyclophaneCandidateList e
        (relabelCyclophaneCandidateList e candidates bounded) = candidates := by
  unfold unrelabelCyclophaneCandidateList relabelCyclophaneCandidateList
  rw [List.map_map]
  trans candidates.attach.map Subtype.val
  · apply List.map_congr_left
    intro candidate _
    exact unrelabelCyclophaneCandidate_relabelCyclophaneCandidate e candidate.1
      (bounded candidate.1 candidate.2)
  · exact List.attach_map_subtype_val candidates

theorem relabelCyclophaneCandidateList_unrelabelCyclophaneCandidateList
    [DecidableEq V] (e : V ≃ Fin n)
    (candidates : List (SuppliedRingChainCyclophaneRCTReferenceCandidate V)) :
    relabelCyclophaneCandidateList e
        (unrelabelCyclophaneCandidateList e candidates)
        (unrelabelCyclophaneCandidateListBounded e candidates) = candidates := by
  unfold relabelCyclophaneCandidateList unrelabelCyclophaneCandidateList
  rw [List.attach_map, List.map_map]
  trans candidates.attach.map Subtype.val
  · apply List.map_congr_left
    intro candidate _
    exact relabelCyclophaneCandidate_unrelabelCyclophaneCandidate e candidate.1
  · exact List.attach_map_subtype_val candidates

def relabelCyclophaneAssignment (e : V ≃ Fin n)
    (assignment : P93CyclophaneRCTLocatedAssignment)
    (bounded : assignment.center < n) :
    SuppliedRingChainCyclophaneRCTLocatedAssignment V where
  center := decodeAtom e assignment.center bounded
  citation := assignment.citation
  side := assignment.side
  descriptor := assignment.descriptor

def unrelabelCyclophaneAssignment (e : V ≃ Fin n)
    (assignment : SuppliedRingChainCyclophaneRCTLocatedAssignment V) :
    P93CyclophaneRCTLocatedAssignment where
  center := encodeAtom e assignment.center
  citation := assignment.citation
  side := assignment.side
  descriptor := assignment.descriptor

def relabelCyclophaneAssignmentList [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List P93CyclophaneRCTLocatedAssignment)
    (bounded : ∀ assignment ∈ assignments, assignment.center < n) :
    List (SuppliedRingChainCyclophaneRCTLocatedAssignment V) :=
  assignments.attach.map fun assignment =>
    relabelCyclophaneAssignment e assignment.1 (bounded assignment.1 assignment.2)

def unrelabelCyclophaneAssignmentList (e : V ≃ Fin n)
    (assignments : List (SuppliedRingChainCyclophaneRCTLocatedAssignment V)) :
    List P93CyclophaneRCTLocatedAssignment :=
  assignments.map (unrelabelCyclophaneAssignment e)

def unrelabelCyclophaneAssignmentListBounded (e : V ≃ Fin n)
    (assignments : List (SuppliedRingChainCyclophaneRCTLocatedAssignment V)) :
    ∀ assignment ∈ unrelabelCyclophaneAssignmentList e assignments,
      assignment.center < n := by
  intro assignment member
  rw [unrelabelCyclophaneAssignmentList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact encodeAtom_lt e presented.center

theorem unrelabelCyclophaneAssignment_relabelCyclophaneAssignment [DecidableEq V]
    (e : V ≃ Fin n) (assignment : P93CyclophaneRCTLocatedAssignment)
    (bounded : assignment.center < n) :
    unrelabelCyclophaneAssignment e (relabelCyclophaneAssignment e assignment bounded) =
      assignment := by
  obtain ⟨center, citation, side, descriptor⟩ := assignment
  simp [relabelCyclophaneAssignment, unrelabelCyclophaneAssignment, encodeAtom_decodeAtom]

theorem relabelCyclophaneAssignment_unrelabelCyclophaneAssignment [DecidableEq V]
    (e : V ≃ Fin n) (assignment : SuppliedRingChainCyclophaneRCTLocatedAssignment V) :
    relabelCyclophaneAssignment e (unrelabelCyclophaneAssignment e assignment)
        (encodeAtom_lt e assignment.center) = assignment := by
  obtain ⟨center, citation, side, descriptor⟩ := assignment
  simp [relabelCyclophaneAssignment, unrelabelCyclophaneAssignment, decodeAtom_encodeAtom]

theorem unrelabelCyclophaneAssignmentList_relabelCyclophaneAssignmentList
    [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List P93CyclophaneRCTLocatedAssignment)
    (bounded : ∀ assignment ∈ assignments, assignment.center < n) :
    unrelabelCyclophaneAssignmentList e
        (relabelCyclophaneAssignmentList e assignments bounded) = assignments := by
  unfold unrelabelCyclophaneAssignmentList relabelCyclophaneAssignmentList
  rw [List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact unrelabelCyclophaneAssignment_relabelCyclophaneAssignment e assignment.1
      (bounded assignment.1 assignment.2)
  · exact List.attach_map_subtype_val assignments

theorem relabelCyclophaneAssignmentList_unrelabelCyclophaneAssignmentList
    [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (SuppliedRingChainCyclophaneRCTLocatedAssignment V)) :
    relabelCyclophaneAssignmentList e
        (unrelabelCyclophaneAssignmentList e assignments)
        (unrelabelCyclophaneAssignmentListBounded e assignments) = assignments := by
  unfold relabelCyclophaneAssignmentList unrelabelCyclophaneAssignmentList
  rw [List.attach_map, List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact relabelCyclophaneAssignment_unrelabelCyclophaneAssignment e assignment.1
  · exact List.attach_map_subtype_val assignments

inductive SuppliedRingChainCyclophaneCenterSpecification (V : Type*) where
  | cip
      (context : BlueBookP93.Acyclic.NomenclatureContext)
      (kind : BlueBookP93.Acyclic.UnitKind)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | relativeRCT
      (candidates : List (SuppliedRingChainCyclophaneRCTReferenceCandidate V))
      (selected : SuppliedRingChainCyclophaneRCTReferenceCandidate V)
      (referenceSide : BlueBookP93.Cyclic.RingSide)
      (assignments : List (SuppliedRingChainCyclophaneRCTLocatedAssignment V))

def CyclophaneSpecificationBoundedIn (n : Nat) :
    P93CyclophaneCenterSpecification → Prop
  | .cip _ _ _ => True
  | .relativeRCT candidates selected _ assignments =>
      (∀ candidate ∈ candidates, candidate.center < n) ∧
        selected.center < n ∧
        ∀ assignment ∈ assignments, assignment.center < n

def relabelCyclophaneSpecification [DecidableEq V] (e : V ≃ Fin n) :
    (specification : P93CyclophaneCenterSpecification) →
      CyclophaneSpecificationBoundedIn n specification →
        SuppliedRingChainCyclophaneCenterSpecification V
  | .cip context kind descriptor, _ => .cip context kind descriptor
  | .relativeRCT candidates selected referenceSide assignments, bounded =>
      .relativeRCT (relabelCyclophaneCandidateList e candidates bounded.1)
        (relabelCyclophaneCandidate e selected bounded.2.1)
        referenceSide
        (relabelCyclophaneAssignmentList e assignments bounded.2.2)

def unrelabelCyclophaneSpecification (e : V ≃ Fin n) :
    SuppliedRingChainCyclophaneCenterSpecification V →
      P93CyclophaneCenterSpecification
  | .cip context kind descriptor => .cip context kind descriptor
  | .relativeRCT candidates selected referenceSide assignments =>
      .relativeRCT (unrelabelCyclophaneCandidateList e candidates)
        (unrelabelCyclophaneCandidate e selected)
        referenceSide
        (unrelabelCyclophaneAssignmentList e assignments)

def unrelabelCyclophaneSpecificationBounded (e : V ≃ Fin n) :
    (specification : SuppliedRingChainCyclophaneCenterSpecification V) →
      CyclophaneSpecificationBoundedIn n
        (unrelabelCyclophaneSpecification e specification)
  | .cip _ _ _ => trivial
  | .relativeRCT candidates selected _ assignments =>
      ⟨unrelabelCyclophaneCandidateListBounded e candidates,
        encodeAtom_lt e selected.center,
        unrelabelCyclophaneAssignmentListBounded e assignments⟩

theorem unrelabelCyclophaneSpecification_relabelCyclophaneSpecification
    [DecidableEq V] (e : V ≃ Fin n)
    (specification : P93CyclophaneCenterSpecification)
    (bounded : CyclophaneSpecificationBoundedIn n specification) :
    unrelabelCyclophaneSpecification e
        (relabelCyclophaneSpecification e specification bounded) = specification := by
  cases specification with
  | cip context kind descriptor => rfl
  | relativeRCT candidates selected referenceSide assignments =>
      simp [relabelCyclophaneSpecification, unrelabelCyclophaneSpecification,
        unrelabelCyclophaneCandidateList_relabelCyclophaneCandidateList,
        unrelabelCyclophaneAssignmentList_relabelCyclophaneAssignmentList,
        unrelabelCyclophaneCandidate_relabelCyclophaneCandidate]

theorem relabelCyclophaneSpecification_unrelabelCyclophaneSpecification
    [DecidableEq V] (e : V ≃ Fin n)
    (specification : SuppliedRingChainCyclophaneCenterSpecification V) :
    relabelCyclophaneSpecification e (unrelabelCyclophaneSpecification e specification)
        (unrelabelCyclophaneSpecificationBounded e specification) = specification := by
  cases specification with
  | cip context kind descriptor => rfl
  | relativeRCT candidates selected referenceSide assignments =>
      simp [relabelCyclophaneSpecification, unrelabelCyclophaneSpecification,
        unrelabelCyclophaneSpecificationBounded,
        relabelCyclophaneCandidateList_unrelabelCyclophaneCandidateList,
        relabelCyclophaneAssignmentList_unrelabelCyclophaneAssignmentList,
        relabelCyclophaneCandidate_unrelabelCyclophaneCandidate]

structure SuppliedRingChainCyclophanePlane (V : Type*)
    (policy : P93CyclophaneAuthorityPolicy) where
  system : SuppliedRingChainCyclophaneSystem V
  unit : SuppliedPhysicalUnit V
  frame : NativePlanarFrame V
  citation : P93AuthorityCitationToken
  reference : BlueBookP93.Cyclic.CyclophanePlaneReference
  context : BlueBookP93.Acyclic.NomenclatureContext
  descriptor : BlueBookP93.Cyclic.CyclophanePlaneDescriptor

structure CyclophanePlaneBoundedIn (n : Nat) (policy : P93CyclophaneAuthorityPolicy)
    (observation : P93CyclophanePlaneAuthorityObservation policy) : Prop where
  system : CyclophaneSystemBoundedIn n observation.system
  unit : OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.unit
  frame : PlaneFrameBoundedIn n observation.frame

def relabelRingChainCyclophanePlane [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93CyclophanePlaneAuthorityObservation policy)
    (bounded : CyclophanePlaneBoundedIn n policy observation) :
    SuppliedRingChainCyclophanePlane V policy where
  system := relabelCyclophaneSystem e observation.system bounded.system
  unit := relabelUnit e observation.unit bounded.unit
  frame := relabelPlane e observation.frame bounded.frame
  citation := observation.citation
  reference := observation.reference
  context := observation.context
  descriptor := observation.descriptor

def unrelabelRingChainCyclophanePlane [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainCyclophanePlane V policy) :
    P93CyclophanePlaneAuthorityObservation policy where
  system := unrelabelCyclophaneSystem e observation.system
  unit := unrelabelUnit e observation.unit
  frame := decodePlane e observation.frame
  citation := observation.citation
  reference := observation.reference
  context := observation.context
  descriptor := observation.descriptor

def unrelabelRingChainCyclophanePlaneBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainCyclophanePlane V policy) :
    CyclophanePlaneBoundedIn n policy
      (unrelabelRingChainCyclophanePlane e observation) :=
  ⟨unrelabelCyclophaneSystemBounded e observation.system,
    unrelabelUnitBounded e observation.unit,
    planeFrameBoundedIn_decodePlane e observation.frame⟩

theorem unrelabelRingChainCyclophanePlane_relabelRingChainCyclophanePlane
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93CyclophanePlaneAuthorityObservation policy)
    (bounded : CyclophanePlaneBoundedIn n policy observation) :
    unrelabelRingChainCyclophanePlane e
        (relabelRingChainCyclophanePlane e observation bounded) = observation := by
  obtain ⟨system, unit, frame, citation, reference, context, descriptor⟩ := observation
  simp [relabelRingChainCyclophanePlane, unrelabelRingChainCyclophanePlane,
    unrelabelCyclophaneSystem_relabelCyclophaneSystem,
    unrelabelUnit_relabelUnit, decodePlane_relabelPlane]

theorem relabelRingChainCyclophanePlane_unrelabelRingChainCyclophanePlane
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainCyclophanePlane V policy) :
    relabelRingChainCyclophanePlane e
        (unrelabelRingChainCyclophanePlane e observation)
        (unrelabelRingChainCyclophanePlaneBounded e observation) = observation := by
  obtain ⟨system, unit, frame, citation, reference, context, descriptor⟩ := observation
  simp [relabelRingChainCyclophanePlane, unrelabelRingChainCyclophanePlane,
    unrelabelRingChainCyclophanePlaneBounded,
    relabelCyclophaneSystem_unrelabelCyclophaneSystem,
    relabelUnit_unrelabelUnit, relabelPlane_decodePlane]

structure SuppliedRingChainCyclophaneCenter (V : Type*)
    (policy : P93CyclophaneAuthorityPolicy) where
  system : SuppliedRingChainCyclophaneSystem V
  unit : SuppliedPhysicalUnit V
  citation : P93AuthorityCitationToken
  specification : SuppliedRingChainCyclophaneCenterSpecification V

structure CyclophaneCenterBoundedIn (n : Nat) (policy : P93CyclophaneAuthorityPolicy)
    (observation : P93CyclophaneCenterAuthorityObservation policy) : Prop where
  system : CyclophaneSystemBoundedIn n observation.system
  unit : OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.unit
  specification : CyclophaneSpecificationBoundedIn n observation.specification

def relabelRingChainCyclophaneCenter [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93CyclophaneCenterAuthorityObservation policy)
    (bounded : CyclophaneCenterBoundedIn n policy observation) :
    SuppliedRingChainCyclophaneCenter V policy where
  system := relabelCyclophaneSystem e observation.system bounded.system
  unit := relabelUnit e observation.unit bounded.unit
  citation := observation.citation
  specification :=
    relabelCyclophaneSpecification e observation.specification bounded.specification

def unrelabelRingChainCyclophaneCenter [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainCyclophaneCenter V policy) :
    P93CyclophaneCenterAuthorityObservation policy where
  system := unrelabelCyclophaneSystem e observation.system
  unit := unrelabelUnit e observation.unit
  citation := observation.citation
  specification := unrelabelCyclophaneSpecification e observation.specification

def unrelabelRingChainCyclophaneCenterBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainCyclophaneCenter V policy) :
    CyclophaneCenterBoundedIn n policy
      (unrelabelRingChainCyclophaneCenter e observation) :=
  ⟨unrelabelCyclophaneSystemBounded e observation.system,
    unrelabelUnitBounded e observation.unit,
    unrelabelCyclophaneSpecificationBounded e observation.specification⟩

theorem unrelabelRingChainCyclophaneCenter_relabelRingChainCyclophaneCenter
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93CyclophaneCenterAuthorityObservation policy)
    (bounded : CyclophaneCenterBoundedIn n policy observation) :
    unrelabelRingChainCyclophaneCenter e
        (relabelRingChainCyclophaneCenter e observation bounded) = observation := by
  obtain ⟨system, unit, citation, specification⟩ := observation
  simp [relabelRingChainCyclophaneCenter, unrelabelRingChainCyclophaneCenter,
    unrelabelCyclophaneSystem_relabelCyclophaneSystem,
    unrelabelUnit_relabelUnit,
    unrelabelCyclophaneSpecification_relabelCyclophaneSpecification]

theorem relabelRingChainCyclophaneCenter_unrelabelRingChainCyclophaneCenter
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainCyclophaneCenter V policy) :
    relabelRingChainCyclophaneCenter e
        (unrelabelRingChainCyclophaneCenter e observation)
        (unrelabelRingChainCyclophaneCenterBounded e observation) = observation := by
  obtain ⟨system, unit, citation, specification⟩ := observation
  simp [relabelRingChainCyclophaneCenter, unrelabelRingChainCyclophaneCenter,
    unrelabelRingChainCyclophaneCenterBounded,
    relabelCyclophaneSystem_unrelabelCyclophaneSystem,
    relabelUnit_unrelabelUnit,
    relabelCyclophaneSpecification_unrelabelCyclophaneSpecification]

structure SuppliedRingChainCyclophaneDoubleBond (V : Type*)
    (policy : P93CyclophaneAuthorityPolicy) where
  system : SuppliedRingChainCyclophaneSystem V
  unit : SuppliedPhysicalUnit V
  ring : List V
  phaneRing : List Nat
  citation : P93AuthorityCitationToken
  geometry : BlueBookP93.Cyclic.MonocyclicSeniorLigandGeometry
  carbonContext : BlueBookP93.Acyclic.CarbonDoubleBondContext
  context : BlueBookP93.Acyclic.NomenclatureContext
  descriptor? : Option BlueBookP93.Acyclic.Descriptor

structure CyclophaneDoubleBondBoundedIn (n : Nat) (policy : P93CyclophaneAuthorityPolicy)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy) : Prop where
  system : CyclophaneSystemBoundedIn n observation.system
  unit : OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.unit
  ring : ∀ atom ∈ observation.ring, atom < n

def relabelRingChainCyclophaneDoubleBond [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy)
    (bounded : CyclophaneDoubleBondBoundedIn n policy observation) :
    SuppliedRingChainCyclophaneDoubleBond V policy where
  system := relabelCyclophaneSystem e observation.system bounded.system
  unit := relabelUnit e observation.unit bounded.unit
  ring := relabelList e observation.ring bounded.ring
  phaneRing := observation.phaneRing
  citation := observation.citation
  geometry := observation.geometry
  carbonContext := observation.carbonContext
  context := observation.context
  descriptor? := observation.descriptor?

def unrelabelRingChainCyclophaneDoubleBond [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainCyclophaneDoubleBond V policy) :
    P93CyclophaneDoubleBondAuthorityObservation policy where
  system := unrelabelCyclophaneSystem e observation.system
  unit := unrelabelUnit e observation.unit
  ring := unrelabelList e observation.ring
  phaneRing := observation.phaneRing
  citation := observation.citation
  geometry := observation.geometry
  carbonContext := observation.carbonContext
  context := observation.context
  descriptor? := observation.descriptor?

def unrelabelRingChainCyclophaneDoubleBondBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainCyclophaneDoubleBond V policy) :
    CyclophaneDoubleBondBoundedIn n policy
      (unrelabelRingChainCyclophaneDoubleBond e observation) :=
  ⟨unrelabelCyclophaneSystemBounded e observation.system,
    unrelabelUnitBounded e observation.unit,
    unrelabelList_bounded e observation.ring⟩

theorem unrelabelRingChainCyclophaneDoubleBond_relabelRingChainCyclophaneDoubleBond
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy)
    (bounded : CyclophaneDoubleBondBoundedIn n policy observation) :
    unrelabelRingChainCyclophaneDoubleBond e
        (relabelRingChainCyclophaneDoubleBond e observation bounded) = observation := by
  obtain ⟨system, unit, ring, phaneRing, citation, geometry, carbonContext, context,
    descriptor?⟩ := observation
  simp [relabelRingChainCyclophaneDoubleBond, unrelabelRingChainCyclophaneDoubleBond,
    unrelabelCyclophaneSystem_relabelCyclophaneSystem,
    unrelabelUnit_relabelUnit, unrelabelList_relabelList]

theorem relabelRingChainCyclophaneDoubleBond_unrelabelRingChainCyclophaneDoubleBond
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainCyclophaneDoubleBond V policy) :
    relabelRingChainCyclophaneDoubleBond e
        (unrelabelRingChainCyclophaneDoubleBond e observation)
        (unrelabelRingChainCyclophaneDoubleBondBounded e observation) = observation := by
  obtain ⟨system, unit, ring, phaneRing, citation, geometry, carbonContext, context,
    descriptor?⟩ := observation
  simp [relabelRingChainCyclophaneDoubleBond, unrelabelRingChainCyclophaneDoubleBond,
    unrelabelRingChainCyclophaneDoubleBondBounded,
    relabelCyclophaneSystem_unrelabelCyclophaneSystem,
    relabelUnit_unrelabelUnit, relabelList_unrelabelList]

end CyclophaneSources

section SpiroSources

variable {policy : P93SpiroAuthorityPolicy}

/-! ## Spiro evidence mirrors -/

structure SuppliedRingChainSpiroSystem (V : Type*) where
  center : V
  firstRingInternal : List V
  secondRingInternal : List V

structure SpiroSystemBoundedIn (n : Nat) (system : P93AuthoritySpiroSystem) : Prop where
  center : system.center < n
  first : ∀ atom ∈ system.firstRingInternal, atom < n
  second : ∀ atom ∈ system.secondRingInternal, atom < n

def relabelSpiroSystem [DecidableEq V] (e : V ≃ Fin n)
    (system : P93AuthoritySpiroSystem) (bounded : SpiroSystemBoundedIn n system) :
    SuppliedRingChainSpiroSystem V where
  center := decodeAtom e system.center bounded.center
  firstRingInternal := relabelList e system.firstRingInternal bounded.first
  secondRingInternal := relabelList e system.secondRingInternal bounded.second

def unrelabelSpiroSystem (e : V ≃ Fin n)
    (system : SuppliedRingChainSpiroSystem V) :
    P93AuthoritySpiroSystem where
  center := encodeAtom e system.center
  firstRingInternal := unrelabelList e system.firstRingInternal
  secondRingInternal := unrelabelList e system.secondRingInternal

def unrelabelSpiroSystemBounded (e : V ≃ Fin n)
    (system : SuppliedRingChainSpiroSystem V) :
    SpiroSystemBoundedIn n (unrelabelSpiroSystem e system) :=
  { center := encodeAtom_lt e system.center
    first := unrelabelList_bounded e system.firstRingInternal
    second := unrelabelList_bounded e system.secondRingInternal }

theorem unrelabelSpiroSystem_relabelSpiroSystem [DecidableEq V]
    (e : V ≃ Fin n) (system : P93AuthoritySpiroSystem)
    (bounded : SpiroSystemBoundedIn n system) :
    unrelabelSpiroSystem e (relabelSpiroSystem e system bounded) = system := by
  obtain ⟨center, firstRingInternal, secondRingInternal⟩ := system
  simp [relabelSpiroSystem, unrelabelSpiroSystem,
    encodeAtom_decodeAtom, unrelabelList_relabelList]

theorem relabelSpiroSystem_unrelabelSpiroSystem [DecidableEq V]
    (e : V ≃ Fin n) (system : SuppliedRingChainSpiroSystem V) :
    relabelSpiroSystem e (unrelabelSpiroSystem e system)
        (unrelabelSpiroSystemBounded e system) = system := by
  obtain ⟨center, firstRingInternal, secondRingInternal⟩ := system
  simp [relabelSpiroSystem, unrelabelSpiroSystem, unrelabelSpiroSystemBounded,
    decodeAtom_encodeAtom, relabelList_unrelabelList]

structure SuppliedRingChainSpiroPolyhedral (V : Type*)
    (policy : P93SpiroAuthorityPolicy) where
  system : SuppliedRingChainSpiroSystem V
  unit : SuppliedPhysicalUnit V
  citation : P93AuthorityCitationToken
  coordination : BlueBookP93.Cyclic.SpiroCenterCoordination
  knowledge : BlueBookP93.Cyclic.ConfigurationKnowledge
  descriptor : PolyhedralChiralitySymbol

structure SpiroPolyhedralBoundedIn (n : Nat) (policy : P93SpiroAuthorityPolicy)
    (observation : P93SpiroPolyhedralAuthorityObservation policy) : Prop where
  system : SpiroSystemBoundedIn n observation.system
  unit : OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.unit

def relabelRingChainSpiroPolyhedral [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93SpiroPolyhedralAuthorityObservation policy)
    (bounded : SpiroPolyhedralBoundedIn n policy observation) :
    SuppliedRingChainSpiroPolyhedral V policy where
  system := relabelSpiroSystem e observation.system bounded.system
  unit := relabelUnit e observation.unit bounded.unit
  citation := observation.citation
  coordination := observation.coordination
  knowledge := observation.knowledge
  descriptor := observation.descriptor

def unrelabelRingChainSpiroPolyhedral [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainSpiroPolyhedral V policy) :
    P93SpiroPolyhedralAuthorityObservation policy where
  system := unrelabelSpiroSystem e observation.system
  unit := unrelabelUnit e observation.unit
  citation := observation.citation
  coordination := observation.coordination
  knowledge := observation.knowledge
  descriptor := observation.descriptor

def unrelabelRingChainSpiroPolyhedralBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainSpiroPolyhedral V policy) :
    SpiroPolyhedralBoundedIn n policy
      (unrelabelRingChainSpiroPolyhedral e observation) :=
  ⟨unrelabelSpiroSystemBounded e observation.system,
    unrelabelUnitBounded e observation.unit⟩

theorem unrelabelRingChainSpiroPolyhedral_relabelRingChainSpiroPolyhedral
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93SpiroPolyhedralAuthorityObservation policy)
    (bounded : SpiroPolyhedralBoundedIn n policy observation) :
    unrelabelRingChainSpiroPolyhedral e
        (relabelRingChainSpiroPolyhedral e observation bounded) = observation := by
  obtain ⟨system, unit, citation, coordination, knowledge, descriptor⟩ := observation
  simp [relabelRingChainSpiroPolyhedral, unrelabelRingChainSpiroPolyhedral,
    unrelabelSpiroSystem_relabelSpiroSystem, unrelabelUnit_relabelUnit]

theorem relabelRingChainSpiroPolyhedral_unrelabelRingChainSpiroPolyhedral
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainSpiroPolyhedral V policy) :
    relabelRingChainSpiroPolyhedral e
        (unrelabelRingChainSpiroPolyhedral e observation)
        (unrelabelRingChainSpiroPolyhedralBounded e observation) = observation := by
  obtain ⟨system, unit, citation, coordination, knowledge, descriptor⟩ := observation
  simp [relabelRingChainSpiroPolyhedral, unrelabelRingChainSpiroPolyhedral,
    unrelabelRingChainSpiroPolyhedralBounded,
    relabelSpiroSystem_unrelabelSpiroSystem, relabelUnit_unrelabelUnit]

end SpiroSources

section RingAssemblySources

variable {policy : P93RingAssemblyAuthorityPolicy}

/-! ## Ring-assembly evidence mirrors -/

structure SuppliedRingChainRingAssemblyJunction (V : Type*) where
  leftRingIndex : Nat
  rightRingIndex : Nat
  leftAtom : V
  rightAtom : V
  deriving DecidableEq

structure SuppliedRingChainRingAssembly (V : Type*) where
  rings : List (List V)
  junctions : List (SuppliedRingChainRingAssemblyJunction V)

def RingAssemblyBoundedIn (n : Nat) (assembly : P93AuthorityRingAssembly) : Prop :=
  (∀ ring ∈ assembly.rings, ∀ atom ∈ ring, atom < n) ∧
    ∀ junction ∈ assembly.junctions,
      junction.leftAtom < n ∧ junction.rightAtom < n

def relabelRingAssemblyJunction [DecidableEq V] (e : V ≃ Fin n)
    (junction : P93RingAssemblyJunction)
    (bounded : junction.leftAtom < n ∧ junction.rightAtom < n) :
    SuppliedRingChainRingAssemblyJunction V where
  leftRingIndex := junction.leftRingIndex
  rightRingIndex := junction.rightRingIndex
  leftAtom := decodeAtom e junction.leftAtom bounded.1
  rightAtom := decodeAtom e junction.rightAtom bounded.2

def unrelabelRingAssemblyJunction (e : V ≃ Fin n)
    (junction : SuppliedRingChainRingAssemblyJunction V) :
    P93RingAssemblyJunction where
  leftRingIndex := junction.leftRingIndex
  rightRingIndex := junction.rightRingIndex
  leftAtom := encodeAtom e junction.leftAtom
  rightAtom := encodeAtom e junction.rightAtom

def relabelRingAssemblyJunctionList [DecidableEq V] (e : V ≃ Fin n)
    (junctions : List P93RingAssemblyJunction)
    (bounded : ∀ junction ∈ junctions,
      junction.leftAtom < n ∧ junction.rightAtom < n) :
    List (SuppliedRingChainRingAssemblyJunction V) :=
  junctions.attach.map fun junction =>
    relabelRingAssemblyJunction e junction.1 (bounded junction.1 junction.2)

def unrelabelRingAssemblyJunctionList (e : V ≃ Fin n)
    (junctions : List (SuppliedRingChainRingAssemblyJunction V)) :
    List P93RingAssemblyJunction :=
  junctions.map (unrelabelRingAssemblyJunction e)

def unrelabelRingAssemblyJunctionListBounded (e : V ≃ Fin n)
    (junctions : List (SuppliedRingChainRingAssemblyJunction V)) :
    ∀ junction ∈ unrelabelRingAssemblyJunctionList e junctions,
      junction.leftAtom < n ∧ junction.rightAtom < n := by
  intro junction member
  rw [unrelabelRingAssemblyJunctionList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact ⟨encodeAtom_lt e presented.leftAtom, encodeAtom_lt e presented.rightAtom⟩

theorem unrelabelRingAssemblyJunction_relabelRingAssemblyJunction
    [DecidableEq V] (e : V ≃ Fin n) (junction : P93RingAssemblyJunction)
    (bounded : junction.leftAtom < n ∧ junction.rightAtom < n) :
    unrelabelRingAssemblyJunction e
        (relabelRingAssemblyJunction e junction bounded) = junction := by
  obtain ⟨leftRingIndex, rightRingIndex, leftAtom, rightAtom⟩ := junction
  simp [relabelRingAssemblyJunction, unrelabelRingAssemblyJunction, encodeAtom_decodeAtom]

theorem relabelRingAssemblyJunction_unrelabelRingAssemblyJunction
    [DecidableEq V] (e : V ≃ Fin n)
    (junction : SuppliedRingChainRingAssemblyJunction V) :
    relabelRingAssemblyJunction e (unrelabelRingAssemblyJunction e junction)
        ⟨encodeAtom_lt e junction.leftAtom, encodeAtom_lt e junction.rightAtom⟩ = junction := by
  obtain ⟨leftRingIndex, rightRingIndex, leftAtom, rightAtom⟩ := junction
  simp [relabelRingAssemblyJunction, unrelabelRingAssemblyJunction, decodeAtom_encodeAtom]

theorem unrelabelRingAssemblyJunctionList_relabelRingAssemblyJunctionList
    [DecidableEq V] (e : V ≃ Fin n) (junctions : List P93RingAssemblyJunction)
    (bounded : ∀ junction ∈ junctions,
      junction.leftAtom < n ∧ junction.rightAtom < n) :
    unrelabelRingAssemblyJunctionList e
        (relabelRingAssemblyJunctionList e junctions bounded) = junctions := by
  unfold unrelabelRingAssemblyJunctionList relabelRingAssemblyJunctionList
  rw [List.map_map]
  trans junctions.attach.map Subtype.val
  · apply List.map_congr_left
    intro junction _
    exact unrelabelRingAssemblyJunction_relabelRingAssemblyJunction e junction.1
      (bounded junction.1 junction.2)
  · exact List.attach_map_subtype_val junctions

theorem relabelRingAssemblyJunctionList_unrelabelRingAssemblyJunctionList
    [DecidableEq V] (e : V ≃ Fin n)
    (junctions : List (SuppliedRingChainRingAssemblyJunction V)) :
    relabelRingAssemblyJunctionList e
        (unrelabelRingAssemblyJunctionList e junctions)
        (unrelabelRingAssemblyJunctionListBounded e junctions) = junctions := by
  unfold relabelRingAssemblyJunctionList unrelabelRingAssemblyJunctionList
  rw [List.attach_map, List.map_map]
  trans junctions.attach.map Subtype.val
  · apply List.map_congr_left
    intro junction _
    exact relabelRingAssemblyJunction_unrelabelRingAssemblyJunction e junction.1
  · exact List.attach_map_subtype_val junctions

def relabelRingAssembly [DecidableEq V] (e : V ≃ Fin n)
    (assembly : P93AuthorityRingAssembly)
    (bounded : RingAssemblyBoundedIn n assembly) :
    SuppliedRingChainRingAssembly V where
  rings := relabelListList e assembly.rings bounded.1
  junctions := relabelRingAssemblyJunctionList e assembly.junctions bounded.2

def unrelabelRingAssembly (e : V ≃ Fin n)
    (assembly : SuppliedRingChainRingAssembly V) :
    P93AuthorityRingAssembly where
  rings := unrelabelListList e assembly.rings
  junctions := unrelabelRingAssemblyJunctionList e assembly.junctions

def unrelabelRingAssemblyBounded (e : V ≃ Fin n)
    (assembly : SuppliedRingChainRingAssembly V) :
    RingAssemblyBoundedIn n (unrelabelRingAssembly e assembly) :=
  ⟨unrelabelListListBounded e assembly.rings,
    unrelabelRingAssemblyJunctionListBounded e assembly.junctions⟩

theorem unrelabelRingAssembly_relabelRingAssembly [DecidableEq V]
    (e : V ≃ Fin n) (assembly : P93AuthorityRingAssembly)
    (bounded : RingAssemblyBoundedIn n assembly) :
    unrelabelRingAssembly e (relabelRingAssembly e assembly bounded) = assembly := by
  obtain ⟨rings, junctions⟩ := assembly
  simp only [relabelRingAssembly, unrelabelRingAssembly]
  rw [P93AuthorityRingAssembly.mk.injEq]
  refine ⟨?_, ?_⟩
  · exact unrelabelListList_relabelListList e rings bounded.1
  · exact unrelabelRingAssemblyJunctionList_relabelRingAssemblyJunctionList e
      junctions bounded.2

theorem relabelRingAssembly_unrelabelRingAssembly [DecidableEq V]
    (e : V ≃ Fin n) (assembly : SuppliedRingChainRingAssembly V) :
    relabelRingAssembly e (unrelabelRingAssembly e assembly)
        (unrelabelRingAssemblyBounded e assembly) = assembly := by
  obtain ⟨rings, junctions⟩ := assembly
  simp only [relabelRingAssembly, unrelabelRingAssembly, unrelabelRingAssemblyBounded]
  rw [SuppliedRingChainRingAssembly.mk.injEq]
  refine ⟨?_, ?_⟩
  · exact relabelListList_unrelabelListList e rings
  · exact relabelRingAssemblyJunctionList_unrelabelRingAssemblyJunctionList e junctions

structure SuppliedRingChainAxialGeometry (V : Type*) where
  axisStart : V
  axisEnd : V
  startFirst : V
  startSecond : V
  endFirst : V
  endSecond : V
  sense : StereoSense

structure AxialGeometryBoundedIn (n : Nat)
    (record : IndexedAxialGeometryObservation) : Prop where
  axisStart : record.axisStart < n
  axisEnd : record.axisEnd < n
  startFirst : record.startFirst < n
  startSecond : record.startSecond < n
  endFirst : record.endFirst < n
  endSecond : record.endSecond < n

def relabelAxialGeometry [DecidableEq V] (e : V ≃ Fin n)
    (record : IndexedAxialGeometryObservation)
    (bounded : AxialGeometryBoundedIn n record) :
    SuppliedRingChainAxialGeometry V where
  axisStart := decodeAtom e record.axisStart bounded.axisStart
  axisEnd := decodeAtom e record.axisEnd bounded.axisEnd
  startFirst := decodeAtom e record.startFirst bounded.startFirst
  startSecond := decodeAtom e record.startSecond bounded.startSecond
  endFirst := decodeAtom e record.endFirst bounded.endFirst
  endSecond := decodeAtom e record.endSecond bounded.endSecond
  sense := record.sense

def unrelabelAxialGeometry (e : V ≃ Fin n)
    (record : SuppliedRingChainAxialGeometry V) :
    IndexedAxialGeometryObservation where
  axisStart := encodeAtom e record.axisStart
  axisEnd := encodeAtom e record.axisEnd
  startFirst := encodeAtom e record.startFirst
  startSecond := encodeAtom e record.startSecond
  endFirst := encodeAtom e record.endFirst
  endSecond := encodeAtom e record.endSecond
  sense := record.sense

def unrelabelAxialGeometryBounded (e : V ≃ Fin n)
    (record : SuppliedRingChainAxialGeometry V) :
    AxialGeometryBoundedIn n (unrelabelAxialGeometry e record) :=
  { axisStart := encodeAtom_lt e record.axisStart
    axisEnd := encodeAtom_lt e record.axisEnd
    startFirst := encodeAtom_lt e record.startFirst
    startSecond := encodeAtom_lt e record.startSecond
    endFirst := encodeAtom_lt e record.endFirst
    endSecond := encodeAtom_lt e record.endSecond }

theorem unrelabelAxialGeometry_relabelAxialGeometry [DecidableEq V]
    (e : V ≃ Fin n) (record : IndexedAxialGeometryObservation)
    (bounded : AxialGeometryBoundedIn n record) :
    unrelabelAxialGeometry e (relabelAxialGeometry e record bounded) = record := by
  obtain ⟨axisStart, axisEnd, startFirst, startSecond, endFirst, endSecond, sense⟩ := record
  simp [relabelAxialGeometry, unrelabelAxialGeometry, encodeAtom_decodeAtom]

theorem relabelAxialGeometry_unrelabelAxialGeometry [DecidableEq V]
    (e : V ≃ Fin n) (record : SuppliedRingChainAxialGeometry V) :
    relabelAxialGeometry e (unrelabelAxialGeometry e record)
        (unrelabelAxialGeometryBounded e record) = record := by
  obtain ⟨axisStart, axisEnd, startFirst, startSecond, endFirst, endSecond, sense⟩ := record
  simp [relabelAxialGeometry, unrelabelAxialGeometry, unrelabelAxialGeometryBounded,
    decodeAtom_encodeAtom]

structure SuppliedRingChainRingAssemblyAxisAssignment (V : Type*) where
  junction : SuppliedRingChainRingAssemblyJunction V
  record : SuppliedRingChainAxialGeometry V
  citation : P93AuthorityCitationToken
  cipDescriptor : AxialDescriptor
  preferredDescriptor : BlueBookP93.Cyclic.RingAssemblyAxisDescriptor
  generalDescriptor : BlueBookP93.Cyclic.RingAssemblyAxisDescriptor

def RingAssemblyAxisAssignmentBoundedIn (n : Nat)
    (assignment : P93RingAssemblyAxisAssignment) : Prop :=
  assignment.junction.leftAtom < n ∧ assignment.junction.rightAtom < n ∧
    AxialGeometryBoundedIn n assignment.record

def relabelRingAssemblyAxisAssignment [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93RingAssemblyAxisAssignment)
    (bounded : RingAssemblyAxisAssignmentBoundedIn n assignment) :
    SuppliedRingChainRingAssemblyAxisAssignment V where
  junction := relabelRingAssemblyJunction e assignment.junction ⟨bounded.1, bounded.2.1⟩
  record := relabelAxialGeometry e assignment.record bounded.2.2
  citation := assignment.citation
  cipDescriptor := assignment.cipDescriptor
  preferredDescriptor := assignment.preferredDescriptor
  generalDescriptor := assignment.generalDescriptor

def unrelabelRingAssemblyAxisAssignment (e : V ≃ Fin n)
    (assignment : SuppliedRingChainRingAssemblyAxisAssignment V) :
    P93RingAssemblyAxisAssignment where
  junction := unrelabelRingAssemblyJunction e assignment.junction
  record := unrelabelAxialGeometry e assignment.record
  citation := assignment.citation
  cipDescriptor := assignment.cipDescriptor
  preferredDescriptor := assignment.preferredDescriptor
  generalDescriptor := assignment.generalDescriptor

def unrelabelRingAssemblyAxisAssignmentBounded (e : V ≃ Fin n)
    (assignment : SuppliedRingChainRingAssemblyAxisAssignment V) :
    RingAssemblyAxisAssignmentBoundedIn n
      (unrelabelRingAssemblyAxisAssignment e assignment) :=
  ⟨encodeAtom_lt e assignment.junction.leftAtom,
    encodeAtom_lt e assignment.junction.rightAtom,
    unrelabelAxialGeometryBounded e assignment.record⟩

theorem unrelabelRingAssemblyAxisAssignment_relabelRingAssemblyAxisAssignment
    [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93RingAssemblyAxisAssignment)
    (bounded : RingAssemblyAxisAssignmentBoundedIn n assignment) :
    unrelabelRingAssemblyAxisAssignment e
        (relabelRingAssemblyAxisAssignment e assignment bounded) = assignment := by
  obtain ⟨junction, record, citation, cipDescriptor, preferredDescriptor,
    generalDescriptor⟩ := assignment
  simp [relabelRingAssemblyAxisAssignment, unrelabelRingAssemblyAxisAssignment,
    unrelabelRingAssemblyJunction_relabelRingAssemblyJunction,
    unrelabelAxialGeometry_relabelAxialGeometry]

theorem relabelRingAssemblyAxisAssignment_unrelabelRingAssemblyAxisAssignment
    [DecidableEq V] (e : V ≃ Fin n)
    (assignment : SuppliedRingChainRingAssemblyAxisAssignment V) :
    relabelRingAssemblyAxisAssignment e
        (unrelabelRingAssemblyAxisAssignment e assignment)
        (unrelabelRingAssemblyAxisAssignmentBounded e assignment) = assignment := by
  obtain ⟨junction, record, citation, cipDescriptor, preferredDescriptor,
    generalDescriptor⟩ := assignment
  simp [relabelRingAssemblyAxisAssignment, unrelabelRingAssemblyAxisAssignment,
    unrelabelRingAssemblyAxisAssignmentBounded,
    relabelRingAssemblyJunction_unrelabelRingAssemblyJunction,
    relabelAxialGeometry_unrelabelAxialGeometry]

structure SuppliedRingChainRingAssemblyAxes (V : Type*)
    (policy : P93RingAssemblyAuthorityPolicy) where
  assembly : SuppliedRingChainRingAssembly V
  normalization : ChemistryNormalizationResult
  spatial : SpatialConfiguration
  assignments : List (SuppliedRingChainRingAssemblyAxisAssignment V)

structure RingAssemblyAxesBoundedIn (n : Nat) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyAxesAuthorityObservation policy) : Prop where
  assembly : RingAssemblyBoundedIn n observation.assembly
  assignments :
    ∀ assignment ∈ observation.assignments,
      RingAssemblyAxisAssignmentBoundedIn n assignment

def relabelRingChainRingAssemblyAxes [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93RingAssemblyAxesAuthorityObservation policy)
    (bounded : RingAssemblyAxesBoundedIn n policy observation) :
    SuppliedRingChainRingAssemblyAxes V policy where
  assembly := relabelRingAssembly e observation.assembly bounded.assembly
  normalization := observation.normalization
  spatial := observation.spatial
  assignments :=
    observation.assignments.attach.map fun assignment =>
      relabelRingAssemblyAxisAssignment e assignment.1
        (bounded.assignments assignment.1 assignment.2)

def unrelabelRingChainRingAssemblyAxes [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainRingAssemblyAxes V policy) :
    P93RingAssemblyAxesAuthorityObservation policy where
  assembly := unrelabelRingAssembly e observation.assembly
  normalization := observation.normalization
  spatial := observation.spatial
  assignments :=
    observation.assignments.map (unrelabelRingAssemblyAxisAssignment e)

def unrelabelRingChainRingAssemblyAxesBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainRingAssemblyAxes V policy) :
    RingAssemblyAxesBoundedIn n policy
      (unrelabelRingChainRingAssemblyAxes e observation) :=
  ⟨unrelabelRingAssemblyBounded e observation.assembly,
    fun assignment member => by
      rw [unrelabelRingChainRingAssemblyAxes, List.mem_map] at member
      rcases member with ⟨presented, _presentedMember, rfl⟩
      exact unrelabelRingAssemblyAxisAssignmentBounded e presented⟩

theorem unrelabelRingChainRingAssemblyAxes_relabelRingChainRingAssemblyAxes
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93RingAssemblyAxesAuthorityObservation policy)
    (bounded : RingAssemblyAxesBoundedIn n policy observation) :
    unrelabelRingChainRingAssemblyAxes e
        (relabelRingChainRingAssemblyAxes e observation bounded) = observation := by
  obtain ⟨assembly, normalization, spatial, assignments⟩ := observation
  simp only [relabelRingChainRingAssemblyAxes, unrelabelRingChainRingAssemblyAxes]
  rw [P93RingAssemblyAxesAuthorityObservation.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact unrelabelRingAssembly_relabelRingAssembly e assembly bounded.assembly
  · rfl
  · rfl
  · rw [List.map_map]
    trans assignments.attach.map Subtype.val
    · apply List.map_congr_left
      intro assignment _
      exact unrelabelRingAssemblyAxisAssignment_relabelRingAssemblyAxisAssignment e
        assignment.1 (bounded.assignments assignment.1 assignment.2)
    · exact List.attach_map_subtype_val assignments

theorem relabelRingChainRingAssemblyAxes_unrelabelRingChainRingAssemblyAxes
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainRingAssemblyAxes V policy) :
    relabelRingChainRingAssemblyAxes e
        (unrelabelRingChainRingAssemblyAxes e observation)
        (unrelabelRingChainRingAssemblyAxesBounded e observation) = observation := by
  obtain ⟨assembly, normalization, spatial, assignments⟩ := observation
  simp only [relabelRingChainRingAssemblyAxes, unrelabelRingChainRingAssemblyAxes,
    unrelabelRingChainRingAssemblyAxesBounded]
  rw [SuppliedRingChainRingAssemblyAxes.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact relabelRingAssembly_unrelabelRingAssembly e assembly
  · rfl
  · rfl
  · rw [List.attach_map, List.map_map]
    trans assignments.attach.map Subtype.val
    · apply List.map_congr_left
      intro assignment _
      exact relabelRingAssemblyAxisAssignment_unrelabelRingAssemblyAxisAssignment e
        assignment.1
    · exact List.attach_map_subtype_val assignments

structure SuppliedRingChainRingAssemblyCenterAssignment (V : Type*) where
  center : V
  citation : P93AuthorityCitationToken
  preferredDescriptor : BlueBookP93.Cyclic.RingAssemblyCenterDescriptor
  generalDescriptor? : Option BlueBookP93.Cyclic.RingAssemblyCenterDescriptor

def relabelRingAssemblyCenterAssignment (e : V ≃ Fin n)
    (assignment : P93RingAssemblyCenterAssignment)
    (bounded : assignment.center < n) :
    SuppliedRingChainRingAssemblyCenterAssignment V where
  center := decodeAtom e assignment.center bounded
  citation := assignment.citation
  preferredDescriptor := assignment.preferredDescriptor
  generalDescriptor? := assignment.generalDescriptor?

def unrelabelRingAssemblyCenterAssignment (e : V ≃ Fin n)
    (assignment : SuppliedRingChainRingAssemblyCenterAssignment V) :
    P93RingAssemblyCenterAssignment where
  center := encodeAtom e assignment.center
  citation := assignment.citation
  preferredDescriptor := assignment.preferredDescriptor
  generalDescriptor? := assignment.generalDescriptor?

theorem unrelabelRingAssemblyCenterAssignment_relabelRingAssemblyCenterAssignment
    [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93RingAssemblyCenterAssignment)
    (bounded : assignment.center < n) :
    unrelabelRingAssemblyCenterAssignment e
        (relabelRingAssemblyCenterAssignment e assignment bounded) = assignment := by
  obtain ⟨center, citation, preferredDescriptor, generalDescriptor?⟩ := assignment
  simp [relabelRingAssemblyCenterAssignment, unrelabelRingAssemblyCenterAssignment,
    encodeAtom_decodeAtom]

theorem relabelRingAssemblyCenterAssignment_unrelabelRingAssemblyCenterAssignment
    [DecidableEq V] (e : V ≃ Fin n)
    (assignment : SuppliedRingChainRingAssemblyCenterAssignment V) :
    relabelRingAssemblyCenterAssignment e
        (unrelabelRingAssemblyCenterAssignment e assignment)
        (encodeAtom_lt e assignment.center) = assignment := by
  obtain ⟨center, citation, preferredDescriptor, generalDescriptor?⟩ := assignment
  simp [relabelRingAssemblyCenterAssignment, unrelabelRingAssemblyCenterAssignment,
    decodeAtom_encodeAtom]

structure SuppliedRingChainRingAssemblyCenters (V : Type*)
    (policy : P93RingAssemblyAuthorityPolicy) where
  assembly : SuppliedRingChainRingAssembly V
  assignments : List (SuppliedRingChainRingAssemblyCenterAssignment V)

structure RingAssemblyCentersBoundedIn (n : Nat) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyCentersAuthorityObservation policy) : Prop where
  assembly : RingAssemblyBoundedIn n observation.assembly
  assignments : ∀ assignment ∈ observation.assignments, assignment.center < n

def relabelRingChainRingAssemblyCenters [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93RingAssemblyCentersAuthorityObservation policy)
    (bounded : RingAssemblyCentersBoundedIn n policy observation) :
    SuppliedRingChainRingAssemblyCenters V policy where
  assembly := relabelRingAssembly e observation.assembly bounded.assembly
  assignments :=
    observation.assignments.attach.map fun assignment =>
      relabelRingAssemblyCenterAssignment e assignment.1
        (bounded.assignments assignment.1 assignment.2)

def unrelabelRingChainRingAssemblyCenters [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainRingAssemblyCenters V policy) :
    P93RingAssemblyCentersAuthorityObservation policy where
  assembly := unrelabelRingAssembly e observation.assembly
  assignments :=
    observation.assignments.map (unrelabelRingAssemblyCenterAssignment e)

def unrelabelRingChainRingAssemblyCentersBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainRingAssemblyCenters V policy) :
    RingAssemblyCentersBoundedIn n policy
      (unrelabelRingChainRingAssemblyCenters e observation) :=
  ⟨unrelabelRingAssemblyBounded e observation.assembly,
    fun assignment member => by
      rw [unrelabelRingChainRingAssemblyCenters, List.mem_map] at member
      rcases member with ⟨presented, _presentedMember, rfl⟩
      exact encodeAtom_lt e presented.center⟩

theorem unrelabelRingChainRingAssemblyCenters_relabelRingChainRingAssemblyCenters
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93RingAssemblyCentersAuthorityObservation policy)
    (bounded : RingAssemblyCentersBoundedIn n policy observation) :
    unrelabelRingChainRingAssemblyCenters e
        (relabelRingChainRingAssemblyCenters e observation bounded) = observation := by
  obtain ⟨assembly, assignments⟩ := observation
  simp only [relabelRingChainRingAssemblyCenters, unrelabelRingChainRingAssemblyCenters]
  rw [P93RingAssemblyCentersAuthorityObservation.mk.injEq]
  refine ⟨?_, ?_⟩
  · exact unrelabelRingAssembly_relabelRingAssembly e assembly bounded.assembly
  · rw [List.map_map]
    trans assignments.attach.map Subtype.val
    · apply List.map_congr_left
      intro assignment _
      exact unrelabelRingAssemblyCenterAssignment_relabelRingAssemblyCenterAssignment e
        assignment.1 (bounded.assignments assignment.1 assignment.2)
    · exact List.attach_map_subtype_val assignments

theorem relabelRingChainRingAssemblyCenters_unrelabelRingChainRingAssemblyCenters
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainRingAssemblyCenters V policy) :
    relabelRingChainRingAssemblyCenters e
        (unrelabelRingChainRingAssemblyCenters e observation)
        (unrelabelRingChainRingAssemblyCentersBounded e observation) = observation := by
  obtain ⟨assembly, assignments⟩ := observation
  simp only [relabelRingChainRingAssemblyCenters, unrelabelRingChainRingAssemblyCenters,
    unrelabelRingChainRingAssemblyCentersBounded]
  rw [SuppliedRingChainRingAssemblyCenters.mk.injEq]
  refine ⟨?_, ?_⟩
  · exact relabelRingAssembly_unrelabelRingAssembly e assembly
  · rw [List.attach_map, List.map_map]
    trans assignments.attach.map Subtype.val
    · apply List.map_congr_left
      intro assignment _
      exact relabelRingAssemblyCenterAssignment_unrelabelRingAssemblyCenterAssignment e
        assignment.1
    · exact List.attach_map_subtype_val assignments

structure SuppliedRingChainRingAssemblyDoubleBondAssignment (V : Type*) where
  ringIndex : Nat
  first : V
  second : V
  citation : P93AuthorityCitationToken
  descriptor : BlueBookP93.Acyclic.Descriptor

def relabelRingAssemblyDoubleBondAssignment (e : V ≃ Fin n)
    (assignment : P93RingAssemblyDoubleBondAssignment)
    (bounded : assignment.first < n ∧ assignment.second < n) :
    SuppliedRingChainRingAssemblyDoubleBondAssignment V where
  ringIndex := assignment.ringIndex
  first := decodeAtom e assignment.first bounded.1
  second := decodeAtom e assignment.second bounded.2
  citation := assignment.citation
  descriptor := assignment.descriptor

def unrelabelRingAssemblyDoubleBondAssignment (e : V ≃ Fin n)
    (assignment : SuppliedRingChainRingAssemblyDoubleBondAssignment V) :
    P93RingAssemblyDoubleBondAssignment where
  ringIndex := assignment.ringIndex
  first := encodeAtom e assignment.first
  second := encodeAtom e assignment.second
  citation := assignment.citation
  descriptor := assignment.descriptor

theorem unrelabelRingAssemblyDoubleBondAssignment_relabelRingAssemblyDoubleBondAssignment
    [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93RingAssemblyDoubleBondAssignment)
    (bounded : assignment.first < n ∧ assignment.second < n) :
    unrelabelRingAssemblyDoubleBondAssignment e
        (relabelRingAssemblyDoubleBondAssignment e assignment bounded) = assignment := by
  obtain ⟨ringIndex, first, second, citation, descriptor⟩ := assignment
  simp [relabelRingAssemblyDoubleBondAssignment,
    unrelabelRingAssemblyDoubleBondAssignment, encodeAtom_decodeAtom]

theorem relabelRingAssemblyDoubleBondAssignment_unrelabelRingAssemblyDoubleBondAssignment
    [DecidableEq V] (e : V ≃ Fin n)
    (assignment : SuppliedRingChainRingAssemblyDoubleBondAssignment V) :
    relabelRingAssemblyDoubleBondAssignment e
        (unrelabelRingAssemblyDoubleBondAssignment e assignment)
        ⟨encodeAtom_lt e assignment.first, encodeAtom_lt e assignment.second⟩ =
      assignment := by
  obtain ⟨ringIndex, first, second, citation, descriptor⟩ := assignment
  simp [relabelRingAssemblyDoubleBondAssignment,
    unrelabelRingAssemblyDoubleBondAssignment, decodeAtom_encodeAtom]

structure SuppliedRingChainRingAssemblyDoubleBonds (V : Type*)
    (policy : P93RingAssemblyAuthorityPolicy) where
  assembly : SuppliedRingChainRingAssembly V
  assignments : List (SuppliedRingChainRingAssemblyDoubleBondAssignment V)

structure RingAssemblyDoubleBondsBoundedIn (n : Nat)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyDoubleBondsAuthorityObservation policy) : Prop where
  assembly : RingAssemblyBoundedIn n observation.assembly
  assignments :
    ∀ assignment ∈ observation.assignments,
      assignment.first < n ∧ assignment.second < n

def relabelRingChainRingAssemblyDoubleBonds [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93RingAssemblyDoubleBondsAuthorityObservation policy)
    (bounded : RingAssemblyDoubleBondsBoundedIn n policy observation) :
    SuppliedRingChainRingAssemblyDoubleBonds V policy where
  assembly := relabelRingAssembly e observation.assembly bounded.assembly
  assignments :=
    observation.assignments.attach.map fun assignment =>
      relabelRingAssemblyDoubleBondAssignment e assignment.1
        (bounded.assignments assignment.1 assignment.2)

def unrelabelRingChainRingAssemblyDoubleBonds [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainRingAssemblyDoubleBonds V policy) :
    P93RingAssemblyDoubleBondsAuthorityObservation policy where
  assembly := unrelabelRingAssembly e observation.assembly
  assignments :=
    observation.assignments.map (unrelabelRingAssemblyDoubleBondAssignment e)

def unrelabelRingChainRingAssemblyDoubleBondsBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainRingAssemblyDoubleBonds V policy) :
    RingAssemblyDoubleBondsBoundedIn n policy
      (unrelabelRingChainRingAssemblyDoubleBonds e observation) :=
  ⟨unrelabelRingAssemblyBounded e observation.assembly,
    fun assignment member => by
      rw [unrelabelRingChainRingAssemblyDoubleBonds, List.mem_map] at member
      rcases member with ⟨presented, _presentedMember, rfl⟩
      exact ⟨encodeAtom_lt e presented.first, encodeAtom_lt e presented.second⟩⟩

theorem unrelabelRingChainRingAssemblyDoubleBonds_relabelRingChainRingAssemblyDoubleBonds
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93RingAssemblyDoubleBondsAuthorityObservation policy)
    (bounded : RingAssemblyDoubleBondsBoundedIn n policy observation) :
    unrelabelRingChainRingAssemblyDoubleBonds e
        (relabelRingChainRingAssemblyDoubleBonds e observation bounded) = observation := by
  obtain ⟨assembly, assignments⟩ := observation
  simp only [relabelRingChainRingAssemblyDoubleBonds,
    unrelabelRingChainRingAssemblyDoubleBonds]
  rw [P93RingAssemblyDoubleBondsAuthorityObservation.mk.injEq]
  refine ⟨?_, ?_⟩
  · exact unrelabelRingAssembly_relabelRingAssembly e assembly bounded.assembly
  · rw [List.map_map]
    trans assignments.attach.map Subtype.val
    · apply List.map_congr_left
      intro assignment _
      exact unrelabelRingAssemblyDoubleBondAssignment_relabelRingAssemblyDoubleBondAssignment e
        assignment.1 (bounded.assignments assignment.1 assignment.2)
    · exact List.attach_map_subtype_val assignments

theorem relabelRingChainRingAssemblyDoubleBonds_unrelabelRingChainRingAssemblyDoubleBonds
    [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedRingChainRingAssemblyDoubleBonds V policy) :
    relabelRingChainRingAssemblyDoubleBonds e
        (unrelabelRingChainRingAssemblyDoubleBonds e observation)
        (unrelabelRingChainRingAssemblyDoubleBondsBounded e observation) = observation := by
  obtain ⟨assembly, assignments⟩ := observation
  simp only [relabelRingChainRingAssemblyDoubleBonds,
    unrelabelRingChainRingAssemblyDoubleBonds,
    unrelabelRingChainRingAssemblyDoubleBondsBounded]
  rw [SuppliedRingChainRingAssemblyDoubleBonds.mk.injEq]
  refine ⟨?_, ?_⟩
  · exact relabelRingAssembly_unrelabelRingAssembly e assembly
  · rw [List.attach_map, List.map_map]
    trans assignments.attach.map Subtype.val
    · apply List.map_congr_left
      intro assignment _
      exact relabelRingAssemblyDoubleBondAssignment_unrelabelRingAssemblyDoubleBondAssignment e
        assignment.1
    · exact List.attach_map_subtype_val assignments

end RingAssemblySources

/-! ## Reviewed descriptor evidence, all sixteen concrete family cases -/

/-- One concrete supplied evidence case per reviewed source evidence constructor.  Each case
retains the exact family observation (including every non-atomic field) and every extra
certificate argument of the source constructor. -/
inductive SuppliedRingChainReviewedDescriptorEvidence (V : Type*)
    (policies : P93CoupledRingChainDescriptorPolicies) where
  | acyclicCenter
      (observation : SuppliedRingChainAcyclicCenter V policies.acyclic)
  | acyclicDoubleBond
      (observation : SuppliedRingChainAcyclicDoubleBond V policies.acyclic)
  | acyclicEvenCumulene
      (observation : SuppliedRingChainAcyclicEvenCumulene V policies.acyclic)
  | acyclicOddCumulene
      (observation : SuppliedRingChainAcyclicOddCumulene V policies.acyclic)
  | monocyclicCenter
      (observation : SuppliedRingChainMonocyclicCenter V policies.monocyclic)
  | monocyclicDoubleBond
      (observation : SuppliedRingChainMonocyclicDoubleBond V policies.monocyclic)
      (citation : P93AuthorityCitationToken)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | fusedCIP
      (observation : SuppliedRingChainFusedCIP V policies.fused)
  | cyclophanePlane
      (observation : SuppliedRingChainCyclophanePlane V policies.cyclophane)
  | cyclophaneCenterCIP
      (observation : SuppliedRingChainCyclophaneCenter V policies.cyclophane)
      (context : BlueBookP93.Acyclic.NomenclatureContext)
      (kind : BlueBookP93.Acyclic.UnitKind)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | cyclophaneCenterRelative
      (observation : SuppliedRingChainCyclophaneCenter V policies.cyclophane)
      (assignment : SuppliedRingChainCyclophaneRCTLocatedAssignment V)
  | cyclophaneDoubleBond
      (observation : SuppliedRingChainCyclophaneDoubleBond V policies.cyclophane)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | spiroPolyhedral
      (observation : SuppliedRingChainSpiroPolyhedral V policies.spiro)
  | ringAssemblyAxis
      (observation : SuppliedRingChainRingAssemblyAxes V policies.ringAssembly)
      (assignment : SuppliedRingChainRingAssemblyAxisAssignment V)
  | ringAssemblyCenter
      (observation : SuppliedRingChainRingAssemblyCenters V policies.ringAssembly)
      (assignment : SuppliedRingChainRingAssemblyCenterAssignment V)
  | ringAssemblyDoubleBond
      (observation : SuppliedRingChainRingAssemblyDoubleBonds V policies.ringAssembly)
      (assignment : SuppliedRingChainRingAssemblyDoubleBondAssignment V)

/-- The atom bounds needed to relabel each evidence case.  These are all bounds required by the
concrete family codecs; the metadata-only arguments (`citation`, `descriptor`, `context`,
`kind`) carry no atom references and therefore impose no bound. -/
def EvidenceBoundedIn (n : Nat) (policies : P93CoupledRingChainDescriptorPolicies) :
    P93RingChainReviewedDescriptorEvidence policies → Prop
  | .acyclicCenter observation =>
      OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.assignment.unit
  | .acyclicDoubleBond observation =>
      OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.assignment.unit
  | .acyclicEvenCumulene observation =>
      OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.assignment.unit
  | .acyclicOddCumulene observation =>
      OrganicStereoP93AcyclicIngress.UnitBoundedIn n observation.assignment.unit
  | .monocyclicCenter observation =>
      MonocyclicPhysicalUnitBoundedIn n observation.physical
  | .monocyclicDoubleBond observation _ _ =>
      MonocyclicPhysicalUnitBoundedIn n observation.physical
  | .fusedCIP observation => FusedCIPBoundedIn n policies.fused observation
  | .cyclophanePlane observation =>
      CyclophanePlaneBoundedIn n policies.cyclophane observation
  | .cyclophaneCenterCIP observation _ _ _ =>
      CyclophaneCenterBoundedIn n policies.cyclophane observation
  | .cyclophaneCenterRelative observation assignment =>
      CyclophaneCenterBoundedIn n policies.cyclophane observation ∧ assignment.center < n
  | .cyclophaneDoubleBond observation _ =>
      CyclophaneDoubleBondBoundedIn n policies.cyclophane observation
  | .spiroPolyhedral observation =>
      SpiroPolyhedralBoundedIn n policies.spiro observation
  | .ringAssemblyAxis observation assignment =>
      RingAssemblyAxesBoundedIn n policies.ringAssembly observation ∧
        RingAssemblyAxisAssignmentBoundedIn n assignment
  | .ringAssemblyCenter observation assignment =>
      RingAssemblyCentersBoundedIn n policies.ringAssembly observation ∧
        assignment.center < n
  | .ringAssemblyDoubleBond observation assignment =>
      RingAssemblyDoubleBondsBoundedIn n policies.ringAssembly observation ∧
        assignment.first < n ∧ assignment.second < n

def relabelRingChainEvidence [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies} :
    (evidence : P93RingChainReviewedDescriptorEvidence policies) →
      EvidenceBoundedIn n policies evidence →
      SuppliedRingChainReviewedDescriptorEvidence V policies
  | .acyclicCenter observation, bounded =>
      .acyclicCenter (relabelRingChainAcyclicCenter e observation bounded)
  | .acyclicDoubleBond observation, bounded =>
      .acyclicDoubleBond (relabelRingChainAcyclicDoubleBond e observation bounded)
  | .acyclicEvenCumulene observation, bounded =>
      .acyclicEvenCumulene (relabelRingChainAcyclicEvenCumulene e observation bounded)
  | .acyclicOddCumulene observation, bounded =>
      .acyclicOddCumulene (relabelRingChainAcyclicOddCumulene e observation bounded)
  | .monocyclicCenter observation, bounded =>
      .monocyclicCenter (relabelRingChainMonocyclicCenter e observation bounded)
  | .monocyclicDoubleBond observation citation descriptor, bounded =>
      .monocyclicDoubleBond (relabelRingChainMonocyclicDoubleBond e observation bounded)
        citation descriptor
  | .fusedCIP observation, bounded =>
      .fusedCIP (relabelRingChainFusedCIP e observation bounded)
  | .cyclophanePlane observation, bounded =>
      .cyclophanePlane (relabelRingChainCyclophanePlane e observation bounded)
  | .cyclophaneCenterCIP observation context kind descriptor, bounded =>
      .cyclophaneCenterCIP (relabelRingChainCyclophaneCenter e observation bounded)
        context kind descriptor
  | .cyclophaneCenterRelative observation assignment, bounded =>
      .cyclophaneCenterRelative
        (relabelRingChainCyclophaneCenter e observation bounded.1)
        (relabelCyclophaneAssignment e assignment bounded.2)
  | .cyclophaneDoubleBond observation descriptor, bounded =>
      .cyclophaneDoubleBond
        (relabelRingChainCyclophaneDoubleBond e observation bounded) descriptor
  | .spiroPolyhedral observation, bounded =>
      .spiroPolyhedral (relabelRingChainSpiroPolyhedral e observation bounded)
  | .ringAssemblyAxis observation assignment, bounded =>
      .ringAssemblyAxis (relabelRingChainRingAssemblyAxes e observation bounded.1)
        (relabelRingAssemblyAxisAssignment e assignment bounded.2)
  | .ringAssemblyCenter observation assignment, bounded =>
      .ringAssemblyCenter (relabelRingChainRingAssemblyCenters e observation bounded.1)
        (relabelRingAssemblyCenterAssignment e assignment bounded.2)
  | .ringAssemblyDoubleBond observation assignment, bounded =>
      .ringAssemblyDoubleBond
        (relabelRingChainRingAssemblyDoubleBonds e observation bounded.1)
        (relabelRingAssemblyDoubleBondAssignment e assignment bounded.2)

def unrelabelRingChainEvidence [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies} :
    SuppliedRingChainReviewedDescriptorEvidence V policies →
      P93RingChainReviewedDescriptorEvidence policies
  | .acyclicCenter observation =>
      .acyclicCenter (unrelabelRingChainAcyclicCenter e observation)
  | .acyclicDoubleBond observation =>
      .acyclicDoubleBond (unrelabelRingChainAcyclicDoubleBond e observation)
  | .acyclicEvenCumulene observation =>
      .acyclicEvenCumulene (unrelabelRingChainAcyclicEvenCumulene e observation)
  | .acyclicOddCumulene observation =>
      .acyclicOddCumulene (unrelabelRingChainAcyclicOddCumulene e observation)
  | .monocyclicCenter observation =>
      .monocyclicCenter (unrelabelRingChainMonocyclicCenter e observation)
  | .monocyclicDoubleBond observation citation descriptor =>
      .monocyclicDoubleBond (unrelabelRingChainMonocyclicDoubleBond e observation)
        citation descriptor
  | .fusedCIP observation => .fusedCIP (unrelabelRingChainFusedCIP e observation)
  | .cyclophanePlane observation =>
      .cyclophanePlane (unrelabelRingChainCyclophanePlane e observation)
  | .cyclophaneCenterCIP observation context kind descriptor =>
      .cyclophaneCenterCIP (unrelabelRingChainCyclophaneCenter e observation)
        context kind descriptor
  | .cyclophaneCenterRelative observation assignment =>
      .cyclophaneCenterRelative
        (unrelabelRingChainCyclophaneCenter e observation)
        (unrelabelCyclophaneAssignment e assignment)
  | .cyclophaneDoubleBond observation descriptor =>
      .cyclophaneDoubleBond
        (unrelabelRingChainCyclophaneDoubleBond e observation) descriptor
  | .spiroPolyhedral observation =>
      .spiroPolyhedral (unrelabelRingChainSpiroPolyhedral e observation)
  | .ringAssemblyAxis observation assignment =>
      .ringAssemblyAxis (unrelabelRingChainRingAssemblyAxes e observation)
        (unrelabelRingAssemblyAxisAssignment e assignment)
  | .ringAssemblyCenter observation assignment =>
      .ringAssemblyCenter (unrelabelRingChainRingAssemblyCenters e observation)
        (unrelabelRingAssemblyCenterAssignment e assignment)
  | .ringAssemblyDoubleBond observation assignment =>
      .ringAssemblyDoubleBond
        (unrelabelRingChainRingAssemblyDoubleBonds e observation)
        (unrelabelRingAssemblyDoubleBondAssignment e assignment)

def unrelabelRingChainEvidenceBounded [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies}
    (evidence : SuppliedRingChainReviewedDescriptorEvidence V policies) :
    EvidenceBoundedIn n policies (unrelabelRingChainEvidence e evidence) := by
  cases evidence with
  | acyclicCenter observation =>
      exact unrelabelRingChainAcyclicCenterBounded e observation
  | acyclicDoubleBond observation =>
      exact unrelabelRingChainAcyclicDoubleBondBounded e observation
  | acyclicEvenCumulene observation =>
      exact unrelabelRingChainAcyclicEvenCumuleneBounded e observation
  | acyclicOddCumulene observation =>
      exact unrelabelRingChainAcyclicOddCumuleneBounded e observation
  | monocyclicCenter observation =>
      exact unrelabelRingChainMonocyclicCenterBounded e observation
  | monocyclicDoubleBond observation citation descriptor =>
      exact unrelabelRingChainMonocyclicDoubleBondBounded e observation
  | fusedCIP observation =>
      exact unrelabelRingChainFusedCIPBounded e observation
  | cyclophanePlane observation =>
      exact unrelabelRingChainCyclophanePlaneBounded e observation
  | cyclophaneCenterCIP observation context kind descriptor =>
      exact unrelabelRingChainCyclophaneCenterBounded e observation
  | cyclophaneCenterRelative observation assignment =>
      exact ⟨unrelabelRingChainCyclophaneCenterBounded e observation,
        encodeAtom_lt e assignment.center⟩
  | cyclophaneDoubleBond observation descriptor =>
      exact unrelabelRingChainCyclophaneDoubleBondBounded e observation
  | spiroPolyhedral observation =>
      exact unrelabelRingChainSpiroPolyhedralBounded e observation
  | ringAssemblyAxis observation assignment =>
      exact ⟨unrelabelRingChainRingAssemblyAxesBounded e observation,
        unrelabelRingAssemblyAxisAssignmentBounded e assignment⟩
  | ringAssemblyCenter observation assignment =>
      exact ⟨unrelabelRingChainRingAssemblyCentersBounded e observation,
        encodeAtom_lt e assignment.center⟩
  | ringAssemblyDoubleBond observation assignment =>
      exact ⟨unrelabelRingChainRingAssemblyDoubleBondsBounded e observation,
        encodeAtom_lt e assignment.first, encodeAtom_lt e assignment.second⟩

theorem unrelabelRingChainEvidence_relabelRingChainEvidence [DecidableEq V]
    (e : V ≃ Fin n) {policies : P93CoupledRingChainDescriptorPolicies}
    (evidence : P93RingChainReviewedDescriptorEvidence policies)
    (bounded : EvidenceBoundedIn n policies evidence) :
    unrelabelRingChainEvidence e (relabelRingChainEvidence e evidence bounded) = evidence := by
  cases evidence with
  | acyclicCenter observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainAcyclicCenter_relabelRingChainAcyclicCenter]
  | acyclicDoubleBond observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainAcyclicDoubleBond_relabelRingChainAcyclicDoubleBond]
  | acyclicEvenCumulene observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainAcyclicEvenCumulene_relabelRingChainAcyclicEvenCumulene]
  | acyclicOddCumulene observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainAcyclicOddCumulene_relabelRingChainAcyclicOddCumulene]
  | monocyclicCenter observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainMonocyclicCenter_relabelRingChainMonocyclicCenter]
  | monocyclicDoubleBond observation citation descriptor =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainMonocyclicDoubleBond_relabelRingChainMonocyclicDoubleBond]
  | fusedCIP observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainFusedCIP_relabelRingChainFusedCIP]
  | cyclophanePlane observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainCyclophanePlane_relabelRingChainCyclophanePlane]
  | cyclophaneCenterCIP observation context kind descriptor =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainCyclophaneCenter_relabelRingChainCyclophaneCenter]
  | cyclophaneCenterRelative observation assignment =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainCyclophaneCenter_relabelRingChainCyclophaneCenter,
        unrelabelCyclophaneAssignment_relabelCyclophaneAssignment]
  | cyclophaneDoubleBond observation descriptor =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainCyclophaneDoubleBond_relabelRingChainCyclophaneDoubleBond]
  | spiroPolyhedral observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainSpiroPolyhedral_relabelRingChainSpiroPolyhedral]
  | ringAssemblyAxis observation assignment =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainRingAssemblyAxes_relabelRingChainRingAssemblyAxes,
        unrelabelRingAssemblyAxisAssignment_relabelRingAssemblyAxisAssignment]
  | ringAssemblyCenter observation assignment =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainRingAssemblyCenters_relabelRingChainRingAssemblyCenters,
        unrelabelRingAssemblyCenterAssignment_relabelRingAssemblyCenterAssignment]
  | ringAssemblyDoubleBond observation assignment =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainRingAssemblyDoubleBonds_relabelRingChainRingAssemblyDoubleBonds,
        unrelabelRingAssemblyDoubleBondAssignment_relabelRingAssemblyDoubleBondAssignment]

theorem relabelRingChainEvidence_unrelabelRingChainEvidence [DecidableEq V]
    (e : V ≃ Fin n) {policies : P93CoupledRingChainDescriptorPolicies}
    (evidence : SuppliedRingChainReviewedDescriptorEvidence V policies) :
    relabelRingChainEvidence e (unrelabelRingChainEvidence e evidence)
        (unrelabelRingChainEvidenceBounded e evidence) = evidence := by
  cases evidence with
  | acyclicCenter observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainAcyclicCenter_unrelabelRingChainAcyclicCenter]
  | acyclicDoubleBond observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainAcyclicDoubleBond_unrelabelRingChainAcyclicDoubleBond]
  | acyclicEvenCumulene observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainAcyclicEvenCumulene_unrelabelRingChainAcyclicEvenCumulene]
  | acyclicOddCumulene observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainAcyclicOddCumulene_unrelabelRingChainAcyclicOddCumulene]
  | monocyclicCenter observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainMonocyclicCenter_unrelabelRingChainMonocyclicCenter]
  | monocyclicDoubleBond observation citation descriptor =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainMonocyclicDoubleBond_unrelabelRingChainMonocyclicDoubleBond]
  | fusedCIP observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainFusedCIP_unrelabelRingChainFusedCIP]
  | cyclophanePlane observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainCyclophanePlane_unrelabelRingChainCyclophanePlane]
  | cyclophaneCenterCIP observation context kind descriptor =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainCyclophaneCenter_unrelabelRingChainCyclophaneCenter]
  | cyclophaneCenterRelative observation assignment =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainCyclophaneCenter_unrelabelRingChainCyclophaneCenter,
        relabelCyclophaneAssignment_unrelabelCyclophaneAssignment]
  | cyclophaneDoubleBond observation descriptor =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainCyclophaneDoubleBond_unrelabelRingChainCyclophaneDoubleBond]
  | spiroPolyhedral observation =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainSpiroPolyhedral_unrelabelRingChainSpiroPolyhedral]
  | ringAssemblyAxis observation assignment =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainRingAssemblyAxes_unrelabelRingChainRingAssemblyAxes,
        relabelRingAssemblyAxisAssignment_unrelabelRingAssemblyAxisAssignment]
  | ringAssemblyCenter observation assignment =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainRingAssemblyCenters_unrelabelRingChainRingAssemblyCenters,
        relabelRingAssemblyCenterAssignment_unrelabelRingAssemblyCenterAssignment]
  | ringAssemblyDoubleBond observation assignment =>
      simp [relabelRingChainEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainEvidenceBounded,
        relabelRingChainRingAssemblyDoubleBonds_unrelabelRingChainRingAssemblyDoubleBonds,
        relabelRingAssemblyDoubleBondAssignment_unrelabelRingAssemblyDoubleBondAssignment]

/-! ## Descriptor assignments -/

structure SuppliedRingChainDescriptorAssignment (V : Type*)
    (policies : P93CoupledRingChainDescriptorPolicies) where
  evidence : SuppliedRingChainReviewedDescriptorEvidence V policies

def relabelRingChainDescriptorAssignment [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : P93RingChainDescriptorAssignment policies)
    (bounded : EvidenceBoundedIn n policies assignment.evidence) :
    SuppliedRingChainDescriptorAssignment V policies where
  evidence := relabelRingChainEvidence e assignment.evidence bounded

def unrelabelRingChainDescriptorAssignment [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : SuppliedRingChainDescriptorAssignment V policies) :
    P93RingChainDescriptorAssignment policies where
  evidence := unrelabelRingChainEvidence e assignment.evidence

def unrelabelRingChainDescriptorAssignmentBounded [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : SuppliedRingChainDescriptorAssignment V policies) :
    EvidenceBoundedIn n policies
      (unrelabelRingChainDescriptorAssignment e assignment).evidence :=
  unrelabelRingChainEvidenceBounded e assignment.evidence

theorem unrelabelRingChainDescriptorAssignment_relabelRingChainDescriptorAssignment
    [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : P93RingChainDescriptorAssignment policies)
    (bounded : EvidenceBoundedIn n policies assignment.evidence) :
    unrelabelRingChainDescriptorAssignment e
        (relabelRingChainDescriptorAssignment e assignment bounded) = assignment := by
  obtain ⟨evidence⟩ := assignment
  simp [relabelRingChainDescriptorAssignment, unrelabelRingChainDescriptorAssignment,
    unrelabelRingChainEvidence_relabelRingChainEvidence]

theorem relabelRingChainDescriptorAssignment_unrelabelRingChainDescriptorAssignment
    [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : SuppliedRingChainDescriptorAssignment V policies) :
    relabelRingChainDescriptorAssignment e
        (unrelabelRingChainDescriptorAssignment e assignment)
        (unrelabelRingChainDescriptorAssignmentBounded e assignment) = assignment := by
  obtain ⟨evidence⟩ := assignment
  simp [relabelRingChainDescriptorAssignment, unrelabelRingChainDescriptorAssignment,
    unrelabelRingChainDescriptorAssignmentBounded,
    relabelRingChainEvidence_unrelabelRingChainEvidence]

section CoupledObservations

variable {policy : P93CoupledRingChainAuthorityPolicy}

/-! ## The complete coupled ring-chain observation -/

/-- Lossless native encoding of a full coupled ring-chain authority observation.  Every
role-bearing field is represented: the reviewed base name and its annotated copy, the base-name
certificate (atoms and interactions with native atom references), the ordered assignment list
with concrete family evidence, the multiplicative-selection bit, the ordered repeated-component
supports, the ordered correspondence pairs, and the assignment-to-component ownership indices
(kept as exact metadata). -/
structure SuppliedCoupledRingChainObservation (V : Type*)
    (policy : P93CoupledRingChainAuthorityPolicy) where
  reviewedBaseName : P93RingChainBaseName
  baseNameCertificate : SuppliedRingChainBaseNameCertificate V
  annotatedBaseName : P93RingChainBaseName
  assignments : List (SuppliedRingChainDescriptorAssignment V policy.descriptorPolicies)
  multiplicativeSelected : Bool
  repeatedComponents : List (SuppliedRingChainRepeatedComponent V)
  componentCorrespondences : List (SuppliedRingChainComponentCorrespondence V)
  assignmentOwnerships : List P93RingChainAssignmentOwnership

/-- Bounds needed to encode an observation.  Note that correspondences require no bound here:
their hybrid source-atom representation keeps out-of-range source references explicit. -/
structure ObservationBoundedIn (n : Nat)
    (policy : P93CoupledRingChainAuthorityPolicy)
    (observation : P93CoupledRingChainAuthorityObservation policy) : Prop where
  certificate : RingChainCertificateBoundedIn n observation.baseNameCertificate
  assignments :
    ∀ assignment ∈ observation.assignments,
      EvidenceBoundedIn n policy.descriptorPolicies assignment.evidence
  components :
    ∀ component ∈ observation.repeatedComponents,
      ∀ atom ∈ component.atoms, atom < n

def relabelCoupledObservation [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (bounded : ObservationBoundedIn n policy observation) :
    SuppliedCoupledRingChainObservation V policy where
  reviewedBaseName := observation.reviewedBaseName
  baseNameCertificate :=
    relabelRingChainCertificate e observation.baseNameCertificate bounded.certificate
  annotatedBaseName := observation.annotatedBaseName
  assignments :=
    observation.assignments.attach.map fun assignment =>
      relabelRingChainDescriptorAssignment e assignment.1
        (bounded.assignments assignment.1 assignment.2)
  multiplicativeSelected := observation.multiplicativeSelected
  repeatedComponents :=
    relabelRepeatedComponentList e observation.repeatedComponents bounded.components
  componentCorrespondences :=
    relabelComponentCorrespondenceList e observation.componentCorrespondences
  assignmentOwnerships := observation.assignmentOwnerships

def unrelabelCoupledObservation [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedCoupledRingChainObservation V policy) :
    P93CoupledRingChainAuthorityObservation policy where
  reviewedBaseName := observation.reviewedBaseName
  baseNameCertificate :=
    unrelabelRingChainCertificate e observation.baseNameCertificate
  annotatedBaseName := observation.annotatedBaseName
  assignments :=
    observation.assignments.map (unrelabelRingChainDescriptorAssignment e)
  multiplicativeSelected := observation.multiplicativeSelected
  repeatedComponents :=
    unrelabelRepeatedComponentList e observation.repeatedComponents
  componentCorrespondences :=
    unrelabelComponentCorrespondenceList e observation.componentCorrespondences
  assignmentOwnerships := observation.assignmentOwnerships

def unrelabelCoupledObservationBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedCoupledRingChainObservation V policy) :
    ObservationBoundedIn n policy (unrelabelCoupledObservation e observation) :=
  { certificate :=
      unrelabelRingChainCertificateBounded e observation.baseNameCertificate
    assignments := fun assignment member => by
      rw [unrelabelCoupledObservation, List.mem_map] at member
      rcases member with ⟨presented, _presentedMember, rfl⟩
      exact unrelabelRingChainDescriptorAssignmentBounded e presented
    components := unrelabelRepeatedComponentListBounded e observation.repeatedComponents }

/-! ## Inverses of the complete observation codec -/

theorem unrelabelCoupledObservation_relabelCoupledObservation [DecidableEq V]
    (e : V ≃ Fin n) (observation : P93CoupledRingChainAuthorityObservation policy)
    (bounded : ObservationBoundedIn n policy observation) :
    unrelabelCoupledObservation e (relabelCoupledObservation e observation bounded) =
      observation := by
  obtain ⟨reviewedBaseName, baseNameCertificate, annotatedBaseName, assignments,
    multiplicativeSelected, repeatedComponents, componentCorrespondences,
    assignmentOwnerships⟩ := observation
  have assignmentEq :
      List.map (unrelabelRingChainDescriptorAssignment e)
          (List.map
            (fun assignment =>
              relabelRingChainDescriptorAssignment e assignment.1
                (bounded.assignments assignment.1 assignment.2))
            assignments.attach) = assignments := by
    rw [List.map_map]
    trans assignments.attach.map Subtype.val
    · apply List.map_congr_left
      intro assignment _
      exact unrelabelRingChainDescriptorAssignment_relabelRingChainDescriptorAssignment e
        assignment.1 (bounded.assignments assignment.1 assignment.2)
    · exact List.attach_map_subtype_val assignments
  have correspondenceEq :
      unrelabelComponentCorrespondenceList e
          (relabelComponentCorrespondenceList e componentCorrespondences) =
        componentCorrespondences :=
    unrelabelComponentCorrespondenceList_relabelComponentCorrespondenceList e
      componentCorrespondences
  simp [relabelCoupledObservation, unrelabelCoupledObservation, assignmentEq,
    unrelabelRingChainCertificate_relabelRingChainCertificate,
    unrelabelRepeatedComponentList_relabelRepeatedComponentList, correspondenceEq]

/-- Canonicality of the hybrid correspondence atoms, needed only in the native-to-source
direction.  Every unresolved reference must lie at or beyond the native cardinality, exactly as
the source-atom codec requires. -/
def CoupledObservationCanonical (e : V ≃ Fin n)
    (observation : SuppliedCoupledRingChainObservation V policy) : Prop :=
  ComponentCorrespondenceListCanonical e observation.componentCorrespondences

theorem relabelCoupledObservation_unrelabelCoupledObservation [DecidableEq V]
    (e : V ≃ Fin n) (observation : SuppliedCoupledRingChainObservation V policy)
    (canonical : CoupledObservationCanonical e observation) :
    relabelCoupledObservation e (unrelabelCoupledObservation e observation)
        (unrelabelCoupledObservationBounded e observation) = observation := by
  obtain ⟨reviewedBaseName, baseNameCertificate, annotatedBaseName, assignments,
    multiplicativeSelected, repeatedComponents, componentCorrespondences,
    assignmentOwnerships⟩ := observation
  have assignmentEq :
      List.map
          (fun assignment =>
            relabelRingChainDescriptorAssignment e assignment.1
              ((unrelabelCoupledObservationBounded e
                ⟨reviewedBaseName, baseNameCertificate, annotatedBaseName, assignments,
                  multiplicativeSelected, repeatedComponents, componentCorrespondences,
                  assignmentOwnerships⟩).assignments assignment.1 assignment.2))
          (List.attach
            (List.map (unrelabelRingChainDescriptorAssignment e) assignments)) =
        assignments := by
    rw [List.attach_map, List.map_map]
    trans assignments.attach.map Subtype.val
    · apply List.map_congr_left
      intro assignment _
      exact relabelRingChainDescriptorAssignment_unrelabelRingChainDescriptorAssignment e
        assignment.1
    · exact List.attach_map_subtype_val assignments
  have correspondenceEq :
      relabelComponentCorrespondenceList e
          (unrelabelComponentCorrespondenceList e componentCorrespondences) =
        componentCorrespondences :=
    relabelComponentCorrespondenceList_unrelabelComponentCorrespondenceList e
      componentCorrespondences canonical
  simp [relabelCoupledObservation, unrelabelCoupledObservation, assignmentEq,
    relabelRingChainCertificate_unrelabelRingChainCertificate,
    relabelRepeatedComponentList_unrelabelRepeatedComponentList,
    correspondenceEq]

/-! ## Bounds derived from the actual source-family predicates -/

theorem certificateBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (name : P93RingChainBaseName)
    (certificate : P93RingChainReviewedBaseNameCertificate)
    (valid : certificate.ValidFor source name) :
    RingChainCertificateBoundedIn source.molecule.atomCount certificate := by
  rcases valid with
    ⟨_nameValid, structurallyWellFormed, _frozenName, _frozenAtoms, frozenInteractions⟩
  rcases structurallyWellFormed with ⟨moleculeWellFormed, _spatial, _diagram⟩
  intro interaction member atom atomMember
  have sourceMember : interaction ∈ source.molecule.interactions :=
    frozenInteractions ▸ member
  have wellFormed := (SemanticInteraction.wellFormed?_eq_true_iff interaction
    source.molecule.atomCount).mp
    (List.all_eq_true.mp moleculeWellFormed interaction sourceMember)
  exact of_decide_eq_true
    (List.all_eq_true.mp wellFormed.2.2 atom atomMember)

theorem monocyclicPhysicalUnitBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93MonocyclicAuthorityPolicy)
    (physical : P93MonocyclicPhysicalUnit)
    (valid : physical.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    MonocyclicPhysicalUnitBoundedIn source.molecule.atomCount physical :=
  ⟨valid.1.2.2.1,
    OrganicStereoP93AcyclicIngress.physicalUnitBoundedIn_of_validFor source
      policy.physicalObservation
      physical.unit valid.2.2.1 spatialWellFormed⟩

theorem fusedSystemBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (system : P93AuthorityFusedSystem)
    (valid : system.MechanicallyValidFor source) :
    FusedSystemBoundedIn source.molecule.atomCount system := by
  rcases valid with
    ⟨_length, _nodup, atomsBounded, _edgesNe, _edgesNodup, edgesValid,
      _locantsNe, _locantsFstNodup, _locantsSndNodup, locantKeys, _edgeLocants⟩
  exact ⟨atomsBounded,
    fun edge member =>
      ⟨atomsBounded edge.first (edgesValid edge member).2.1,
        atomsBounded edge.second (edgesValid edge member).2.2.1⟩,
    fun value member => atomsBounded value.1 (locantKeys value member)⟩

theorem fusedUnitBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93FusedAuthorityPolicy)
    (system : P93AuthorityFusedSystem) (unit : P93FusedAuthorityUnit)
    (valid : unit.ValidFor policy source system)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    FusedUnitBoundedIn source.molecule.atomCount unit := by
  cases unit with
  | physical unit =>
      exact OrganicStereoP93AcyclicIngress.physicalUnitBoundedIn_of_validFor source
        policy.physicalObservation
        unit valid.1 spatialWellFormed
  | fusedAxis path => exact valid.2.2.1

theorem cyclophaneSystemBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (system : P93AuthorityCyclophaneSystem)
    (valid : system.MechanicallyValidFor source) :
    CyclophaneSystemBoundedIn source.molecule.atomCount system := by
  rcases valid with
    ⟨_carrierLength, _carrierNodup, carrierBounded, _nodesLength, _nodesNodup,
      nodesInCarrier, _carrierCovered, _nodesDisjoint, _ringsNe, _ringsNodup,
      ringsValid, _ringCoverage, _cyclesNe, _cyclesFstNodup, _cycles⟩
  exact ⟨carrierBounded,
    fun node member atom atomMember =>
      carrierBounded atom ((nodesInCarrier node member).2 atom atomMember),
    fun ring member atom atomMember =>
      carrierBounded atom ((ringsValid ring member).2 atom atomMember)⟩

theorem cyclophanePlaneBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93CyclophaneAuthorityPolicy)
    (observation : P93CyclophanePlaneAuthorityObservation policy)
    (valid : observation.ValidFor policy source)
    (_spatialWellFormed : source.SpatialIndicesWellFormed) :
    CyclophanePlaneBoundedIn source.molecule.atomCount policy observation := by
  rcases valid with
    ⟨systemValid, _supported, frameData, _referenceValid, _preferred, _inSystem,
      _citationValid, _citationAuthorized⟩
  rcases frameData with
    ⟨members, _spatial, _high, _low, _highPoint, _lowPoint, _inPlanePoint,
      _outOfPlanePoint, _general, unitEq, frameValid, _rest⟩
  have systemBounded :=
    cyclophaneSystemBoundedIn_of_validFor source observation.system systemValid.1
  have frameBounded :=
    planeFrameBoundedIn_of_validFor source members observation.frame frameValid
  have unitBounded :
      OrganicStereoP93AcyclicIngress.UnitBoundedIn source.molecule.atomCount
        observation.unit := by
    rw [unitEq]
    intro atom atomMember
    rcases frameValid with ⟨setEq, _length, _nodup, atomsBounded, _rest⟩
    have listMember : atom ∈ observation.frame.record.planeAtoms := by
      rw [← List.mem_toFinset, setEq]
      exact atomMember
    exact atomsBounded atom (by simp [listMember])
  exact ⟨systemBounded, unitBounded, frameBounded⟩

theorem cyclophaneCenterBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93CyclophaneAuthorityPolicy)
    (observation : P93CyclophaneCenterAuthorityObservation policy)
    (valid : observation.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    CyclophaneCenterBoundedIn source.molecule.atomCount policy observation := by
  obtain ⟨system, unit, citation, specification⟩ := observation
  rcases valid with
    ⟨systemValid, unitValid, _supported, _inSystem, _citationValid, _citationAuthorized,
      hspec⟩
  have systemBounded :=
    cyclophaneSystemBoundedIn_of_validFor source system systemValid.1
  have unitBounded :=
    OrganicStereoP93AcyclicIngress.physicalUnitBoundedIn_of_validFor source
      policy.physicalObservation unit
      unitValid spatialWellFormed
  refine ⟨systemBounded, unitBounded, ?_⟩
  cases specification with
  | cip context kind descriptor => exact trivial
  | relativeRCT candidates selected referenceSide assignments =>
      rcases hspec with
        ⟨_unitEq, _citationEq, _candidatesNe, _centersNodup, _citationsNodup,
          candidatesValid, _eligible, unique, _sideNe, _sideObserved, _assignmentsNe,
          _assignmentCentersNodup, _assignmentCitationsNodup, _candidatesCovered,
          assignmentsValid⟩
      refine ⟨?_, ?_, ?_⟩
      · intro candidate member
        exact systemBounded.1 candidate.center (candidatesValid candidate member).1
      · exact systemBounded.1 selected.center
          (candidatesValid selected unique.1.1).1
      · intro assignment member
        rcases (assignmentsValid assignment member) with
          ⟨⟨candidate, candidateMember, centerEq, _citationEq⟩, _rest⟩
        rw [centerEq]
        exact systemBounded.1 candidate.center
          (candidatesValid candidate candidateMember).1

theorem cyclophaneDoubleBondBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93CyclophaneAuthorityPolicy)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy)
    (valid : observation.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    CyclophaneDoubleBondBoundedIn source.molecule.atomCount policy observation := by
  rcases valid with
    ⟨systemValid, unitValid, _supported, _bondExists, ringMember, _phaneCycles,
      _inSystem, _ringObserved, _geometryObserved, _carbonObserved, _naming,
      _descriptorAllowed, _cisTrans, _required, _preferred, _citationValid,
      _citationAuthorized⟩
  have systemBounded :=
    cyclophaneSystemBoundedIn_of_validFor source observation.system systemValid.1
  exact ⟨systemBounded,
    OrganicStereoP93AcyclicIngress.physicalUnitBoundedIn_of_validFor source
      policy.physicalObservation
      observation.unit unitValid spatialWellFormed,
    fun atom member => systemBounded.2.2 observation.ring ringMember atom member⟩

theorem spiroSystemBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor source) :
    SpiroSystemBoundedIn source.molecule.atomCount system := by
  rcases valid with
    ⟨_nodup, atomsBounded, _firstLength, _secondLength, _firstConnected,
      _secondConnected⟩
  refine ⟨atomsBounded system.center (by simp [P93AuthoritySpiroSystem.atoms]),
    ?_, ?_⟩
  · intro atom member
    exact atomsBounded atom (by simp [P93AuthoritySpiroSystem.atoms, member])
  · intro atom member
    exact atomsBounded atom (by simp [P93AuthoritySpiroSystem.atoms, member])

theorem spiroPolyhedralBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93SpiroAuthorityPolicy)
    (observation : P93SpiroPolyhedralAuthorityObservation policy)
    (valid : observation.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    SpiroPolyhedralBoundedIn source.molecule.atomCount policy observation :=
  ⟨spiroSystemBoundedIn_of_validFor source observation.system valid.1.1,
    OrganicStereoP93AcyclicIngress.physicalUnitBoundedIn_of_validFor source
      policy.physicalObservation
      observation.unit valid.2.1 spatialWellFormed⟩

theorem ringAssemblyBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (assembly : P93AuthorityRingAssembly)
    (valid : assembly.MechanicallyValidFor source) :
    RingAssemblyBoundedIn source.molecule.atomCount assembly := by
  rcases valid with
    ⟨_length, _ringsNodup, ringsValid, _disjoint, _junctionsNe, _junctionsNodup,
      junctionsValid, _connected⟩
  refine ⟨fun ring member atom atomMember =>
    (ringsValid ring member).2.2.1 atom atomMember, ?_⟩
  intro junction member
  rcases junctionsValid junction member with
    ⟨_order, leftRing, rightRing, leftLookup, rightLookup, leftMember, rightMember,
      _bond⟩
  exact ⟨(ringsValid leftRing (List.mem_of_getElem? leftLookup)).2.2.1
      junction.leftAtom leftMember,
    (ringsValid rightRing (List.mem_of_getElem? rightLookup)).2.2.1
      junction.rightAtom rightMember⟩

theorem ringAssemblyAxisAssignmentBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyAxesAuthorityObservation policy)
    (assignment : P93RingAssemblyAxisAssignment)
    (member : assignment ∈ observation.assignments)
    (valid : observation.ValidFor policy source) :
    RingAssemblyAxisAssignmentBoundedIn source.molecule.atomCount assignment := by
  have assemblyBounded :=
    ringAssemblyBoundedIn_of_validFor source observation.assembly valid.1.1
  have assignmentValid :=
    valid.2.2.2.2.2.2.2.1 assignment member
  rcases assignmentValid with
    ⟨junctionMember, _eligible, frameValid, _cip, _judgment, _preferred, _general,
      _preferredValid, _observed, _citationValid, _authorized⟩
  have junctionBounded := assemblyBounded.2 assignment.junction junctionMember
  rcases frameValid with
    ⟨axisStartEq, axisEndEq, leftRing, rightRing, leftLookup, rightLookup,
      startFirstMember, startSecondMember, endFirstMember, endSecondMember, _rest⟩
  exact ⟨junctionBounded.1, junctionBounded.2,
    { axisStart := by rw [axisStartEq]; exact junctionBounded.1
      axisEnd := by rw [axisEndEq]; exact junctionBounded.2
      startFirst := assemblyBounded.1 leftRing (List.mem_of_getElem? leftLookup)
        assignment.record.startFirst startFirstMember
      startSecond := assemblyBounded.1 leftRing (List.mem_of_getElem? leftLookup)
        assignment.record.startSecond startSecondMember
      endFirst := assemblyBounded.1 rightRing (List.mem_of_getElem? rightLookup)
        assignment.record.endFirst endFirstMember
      endSecond := assemblyBounded.1 rightRing (List.mem_of_getElem? rightLookup)
        assignment.record.endSecond endSecondMember }⟩

theorem ringAssemblyCenterAssignmentBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyCentersAuthorityObservation policy)
    (assignment : P93RingAssemblyCenterAssignment)
    (member : assignment ∈ observation.assignments)
    (valid : observation.ValidFor policy source) :
    assignment.center < source.molecule.atomCount := by
  have assemblyBounded :=
    ringAssemblyBoundedIn_of_validFor source observation.assembly valid.1.1
  have assignmentValid := valid.2.2.2.2.1 assignment member
  rcases assignmentValid.1 with
    ⟨ringIndex, ring, lookup, centerMember, _unique⟩
  exact assemblyBounded.1 ring (List.mem_of_getElem? lookup) assignment.center
    centerMember

theorem ringAssemblyDoubleBondAssignmentBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyDoubleBondsAuthorityObservation policy)
    (assignment : P93RingAssemblyDoubleBondAssignment)
    (member : assignment ∈ observation.assignments)
    (valid : observation.ValidFor policy source) :
    assignment.first < source.molecule.atomCount ∧
      assignment.second < source.molecule.atomCount := by
  have assemblyBounded :=
    ringAssemblyBoundedIn_of_validFor source observation.assembly valid.1.1
  have assignmentValid := valid.2.2.2.2.1 assignment member
  rcases assignmentValid.1 with
    ⟨_order, ring, lookup, firstMember, secondMember, _edge, _bond⟩
  refine ⟨?_, ?_⟩
  · exact assemblyBounded.1 ring (List.mem_of_getElem? lookup) assignment.first
      firstMember
  · exact assemblyBounded.1 ring (List.mem_of_getElem? lookup) assignment.second
      secondMember

theorem ringAssemblyAxesBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyAxesAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    RingAssemblyAxesBoundedIn source.molecule.atomCount policy observation :=
  ⟨ringAssemblyBoundedIn_of_validFor source observation.assembly valid.1.1,
    fun assignment member =>
      ringAssemblyAxisAssignmentBoundedIn_of_validFor source policy observation
        assignment member valid⟩

theorem ringAssemblyCentersBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyCentersAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    RingAssemblyCentersBoundedIn source.molecule.atomCount policy observation :=
  ⟨ringAssemblyBoundedIn_of_validFor source observation.assembly valid.1.1,
    fun assignment member =>
      ringAssemblyCenterAssignmentBoundedIn_of_validFor source policy observation
        assignment member valid⟩

theorem ringAssemblyDoubleBondsBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyDoubleBondsAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    RingAssemblyDoubleBondsBoundedIn source.molecule.atomCount policy observation :=
  ⟨ringAssemblyBoundedIn_of_validFor source observation.assembly valid.1.1,
    fun assignment member =>
      ringAssemblyDoubleBondAssignmentBoundedIn_of_validFor source policy observation
        assignment member valid⟩

/-- Every reviewed descriptor evidence case is bounded by the source atom count, derived from its
own exact `ValidFor` predicate.  No bound is assumed: each family's mechanical/source validity
supplies the listed atoms, and the family physical-unit bound is derived from the physical
`ValidFor`. -/
theorem EvidenceBoundedIn.of_validFor
    (source : AuthoritativeChemicalInput)
    (policies : P93CoupledRingChainDescriptorPolicies)
    (evidence : P93RingChainReviewedDescriptorEvidence policies)
    (valid : evidence.ValidFor source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    EvidenceBoundedIn source.molecule.atomCount policies evidence := by
  cases evidence with
  | acyclicCenter observation =>
      exact OrganicStereoP93AcyclicIngress.assignmentUnitBoundedIn_of_validFor source
        observation.assignment
        valid.1 spatialWellFormed
  | acyclicDoubleBond observation =>
      exact OrganicStereoP93AcyclicIngress.assignmentUnitBoundedIn_of_validFor source
        observation.assignment
        valid.1 spatialWellFormed
  | acyclicEvenCumulene observation =>
      exact OrganicStereoP93AcyclicIngress.assignmentUnitBoundedIn_of_validFor source
        observation.assignment
        valid.1 spatialWellFormed
  | acyclicOddCumulene observation =>
      exact OrganicStereoP93AcyclicIngress.assignmentUnitBoundedIn_of_validFor source
        observation.assignment
        valid.1 spatialWellFormed
  | monocyclicCenter observation =>
      exact monocyclicPhysicalUnitBoundedIn_of_validFor source policies.monocyclic
        observation.physical valid.1 spatialWellFormed
  | monocyclicDoubleBond observation citation descriptor =>
      exact monocyclicPhysicalUnitBoundedIn_of_validFor source policies.monocyclic
        observation.physical valid.1.1 spatialWellFormed
  | fusedCIP observation =>
      exact ⟨fusedSystemBoundedIn_of_validFor source observation.system valid.1.1,
        fusedUnitBoundedIn_of_validFor source policies.fused observation.system
          observation.unit valid.2.1 spatialWellFormed⟩
  | cyclophanePlane observation =>
      exact cyclophanePlaneBoundedIn_of_validFor source policies.cyclophane
        observation valid spatialWellFormed
  | cyclophaneCenterCIP observation context kind descriptor =>
      exact cyclophaneCenterBoundedIn_of_validFor source policies.cyclophane
        observation valid.1 spatialWellFormed
  | cyclophaneCenterRelative observation assignment =>
      refine ⟨cyclophaneCenterBoundedIn_of_validFor source policies.cyclophane
        observation valid.1 spatialWellFormed, ?_⟩
      rcases valid.2 with
        ⟨candidates, selected, referenceSide, assignments, specificationEq, member⟩
      have specificationBounded :=
        (cyclophaneCenterBoundedIn_of_validFor source policies.cyclophane
          observation valid.1 spatialWellFormed).specification
      rw [specificationEq] at specificationBounded
      exact specificationBounded.2.2 assignment member
  | cyclophaneDoubleBond observation descriptor =>
      exact cyclophaneDoubleBondBoundedIn_of_validFor source policies.cyclophane
        observation valid.1 spatialWellFormed
  | spiroPolyhedral observation =>
      exact spiroPolyhedralBoundedIn_of_validFor source policies.spiro observation
        valid spatialWellFormed
  | ringAssemblyAxis observation assignment =>
      exact ⟨ringAssemblyAxesBoundedIn_of_validFor source policies.ringAssembly
          observation valid.1,
        ringAssemblyAxisAssignmentBoundedIn_of_validFor source
          policies.ringAssembly observation assignment valid.2 valid.1⟩
  | ringAssemblyCenter observation assignment =>
      exact ⟨ringAssemblyCentersBoundedIn_of_validFor source policies.ringAssembly
          observation valid.1,
        ringAssemblyCenterAssignmentBoundedIn_of_validFor source
          policies.ringAssembly observation assignment valid.2 valid.1⟩
  | ringAssemblyDoubleBond observation assignment =>
      exact ⟨ringAssemblyDoubleBondsBoundedIn_of_validFor source
          policies.ringAssembly observation valid.1,
        ringAssemblyDoubleBondAssignmentBoundedIn_of_validFor source
          policies.ringAssembly observation assignment valid.2 valid.1⟩

/-- Every field of a valid coupled observation is bounded by the source atom count.  Repeated
component supports are bounded through the multiplicative decision's own component validity. -/
theorem ObservationBoundedIn.of_validFor
    (source : AuthoritativeChemicalInput)
    (policy : P93CoupledRingChainAuthorityPolicy)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    ObservationBoundedIn source.molecule.atomCount policy observation := by
  have certificateValid :
      observation.baseNameCertificate.ValidFor source observation.reviewedBaseName :=
    valid.2.1
  have spatialWellFormed : source.SpatialIndicesWellFormed :=
    certificateValid.2.1.2.1
  have assignmentBounds :
      ∀ assignment ∈ observation.assignments,
        EvidenceBoundedIn source.molecule.atomCount policy.descriptorPolicies
          assignment.evidence := by
    intro assignment member
    exact EvidenceBoundedIn.of_validFor source policy.descriptorPolicies
      assignment.evidence
      (valid.2.2.2.2.2.2.2.1 assignment member).1 spatialWellFormed
  have componentBounds :
      ∀ component ∈ observation.repeatedComponents,
        ∀ atom ∈ component.atoms, atom < source.molecule.atomCount := by
    have componentsValid : P93RingChainRepeatedComponentsValid source
        observation.repeatedComponents := by
      have decision := valid.2.2.2.2.2.2.2.2.2.2.2
      generalize hb : observation.multiplicativeSelected = b at decision
      cases decision with
      | selected symmetryComplete => exact symmetryComplete.1
      | rejected rejection => exact rejection.componentsValid
    intro component member atom atomMember
    exact (componentsValid.2.2.1 component member).2 atom atomMember
  exact ⟨certificateBoundedIn_of_validFor source observation.reviewedBaseName
      observation.baseNameCertificate certificateValid,
    assignmentBounds, componentBounds⟩

/-! ## Ordered heterogeneous lists of coupled observations -/

def relabelCoupledObservationList [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (P93CoupledRingChainAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      ObservationBoundedIn n policy observation) :
    List (SuppliedCoupledRingChainObservation V policy) :=
  observations.attach.map fun observation =>
    relabelCoupledObservation e observation.1 (bounded observation.1 observation.2)

def unrelabelCoupledObservationList [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (SuppliedCoupledRingChainObservation V policy)) :
    List (P93CoupledRingChainAuthorityObservation policy) :=
  observations.map (unrelabelCoupledObservation e)

def unrelabelCoupledObservationListBounded [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (SuppliedCoupledRingChainObservation V policy)) :
    ∀ observation ∈ unrelabelCoupledObservationList e observations,
      ObservationBoundedIn n policy observation := by
  intro observation member
  rw [unrelabelCoupledObservationList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact unrelabelCoupledObservationBounded e presented

@[simp] theorem relabelCoupledObservationList_length [DecidableEq V]
    (e : V ≃ Fin n)
    (observations : List (P93CoupledRingChainAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      ObservationBoundedIn n policy observation) :
    (relabelCoupledObservationList e observations bounded).length =
      observations.length := by
  simp [relabelCoupledObservationList]

/-- Ordered-list inverse: order and repetitions are preserved exactly. -/
theorem unrelabelCoupledObservationList_relabelCoupledObservationList
    [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (P93CoupledRingChainAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      ObservationBoundedIn n policy observation) :
    unrelabelCoupledObservationList e
        (relabelCoupledObservationList e observations bounded) = observations := by
  unfold unrelabelCoupledObservationList relabelCoupledObservationList
  rw [List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact unrelabelCoupledObservation_relabelCoupledObservation e observation.1
      (bounded observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

/-- Native observations whose hybrid correspondence atoms are all canonical. -/
def CoupledObservationListCanonical [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (SuppliedCoupledRingChainObservation V policy)) : Prop :=
  ∀ observation ∈ observations, CoupledObservationCanonical e observation

theorem relabelCoupledObservationList_unrelabelCoupledObservationList
    [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (SuppliedCoupledRingChainObservation V policy))
    (canonical : CoupledObservationListCanonical e observations) :
    relabelCoupledObservationList e
        (unrelabelCoupledObservationList e observations)
        (unrelabelCoupledObservationListBounded e observations) = observations := by
  unfold relabelCoupledObservationList unrelabelCoupledObservationList
  rw [List.attach_map, List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact relabelCoupledObservation_unrelabelCoupledObservation e observation.1
      (canonical observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

/-! ## Correlated arbitrary sets of coupled observations -/

def relabelCoupledObservationSet [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (P93CoupledRingChainAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      ObservationBoundedIn n policy observation) :
    Set (SuppliedCoupledRingChainObservation V policy) :=
  fun presented =>
    ∃ observation, ∃ member : observation ∈ observations,
      relabelCoupledObservation e observation (bounded observation member) = presented

def unrelabelCoupledObservationSet [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (SuppliedCoupledRingChainObservation V policy)) :
    Set (P93CoupledRingChainAuthorityObservation policy) :=
  fun recovered =>
    ∃ presented ∈ observations, unrelabelCoupledObservation e presented = recovered

def unrelabelCoupledObservationSetBounded [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (SuppliedCoupledRingChainObservation V policy)) :
    ∀ observation ∈ unrelabelCoupledObservationSet e observations,
      ObservationBoundedIn n policy observation := by
  rintro recovered ⟨presented, _presentedMember, rfl⟩
  exact unrelabelCoupledObservationBounded e presented

theorem unrelabelCoupledObservationSet_relabelCoupledObservationSet
    [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (P93CoupledRingChainAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      ObservationBoundedIn n policy observation) :
    unrelabelCoupledObservationSet e
        (relabelCoupledObservationSet e observations bounded) = observations := by
  ext recovered
  constructor
  · rintro ⟨presented, ⟨observation, member, relabelEq⟩, decodeEq⟩
    rw [← relabelEq] at decodeEq
    rw [unrelabelCoupledObservation_relabelCoupledObservation] at decodeEq
    rw [← decodeEq]
    exact member
  · intro member
    exact ⟨relabelCoupledObservation e recovered (bounded recovered member),
      ⟨recovered, member, rfl⟩,
      unrelabelCoupledObservation_relabelCoupledObservation e recovered
        (bounded recovered member)⟩

theorem relabelCoupledObservation_bound_irrel [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (first second : ObservationBoundedIn n policy observation) :
    relabelCoupledObservation e observation first =
      relabelCoupledObservation e observation second := by
  cases observation
  rfl

theorem relabelCoupledObservation_congr [DecidableEq V] (e : V ≃ Fin n)
    {first second : P93CoupledRingChainAuthorityObservation policy}
    (h : first = second)
    (firstBounded : ObservationBoundedIn n policy first)
    (secondBounded : ObservationBoundedIn n policy second) :
    relabelCoupledObservation e first firstBounded =
      relabelCoupledObservation e second secondBounded := by
  cases h
  exact relabelCoupledObservation_bound_irrel e _ firstBounded secondBounded

def CoupledObservationSetCanonical [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (SuppliedCoupledRingChainObservation V policy)) : Prop :=
  ∀ observation ∈ observations, CoupledObservationCanonical e observation

theorem relabelCoupledObservationSet_unrelabelCoupledObservationSet
    [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (SuppliedCoupledRingChainObservation V policy))
    (canonical : CoupledObservationSetCanonical e observations) :
    relabelCoupledObservationSet e
        (unrelabelCoupledObservationSet e observations)
        (unrelabelCoupledObservationSetBounded e observations) = observations := by
  ext presented
  constructor
  · rintro ⟨observation, ⟨presented₀, presentedMember, decodeEq⟩, relabelEq⟩
    have presentedEq : presented = presented₀ := by
      calc
        presented =
            relabelCoupledObservation e observation
              (unrelabelCoupledObservationSetBounded e observations observation
                ⟨presented₀, presentedMember, decodeEq⟩) := relabelEq.symm
        _ = relabelCoupledObservation e
              (unrelabelCoupledObservation e presented₀)
              (unrelabelCoupledObservationBounded e presented₀) :=
            relabelCoupledObservation_congr e decodeEq.symm _ _
        _ = presented₀ :=
            relabelCoupledObservation_unrelabelCoupledObservation e presented₀
              (canonical presented₀ presentedMember)
    simpa [presentedEq] using presentedMember
  · intro member
    exact ⟨unrelabelCoupledObservation e presented,
      ⟨presented, member, rfl⟩,
      relabelCoupledObservation_unrelabelCoupledObservation e presented
        (canonical presented member)⟩

/-- **Correlated set validity at the same source and policy.**  A native observation belongs to the
image of a set exactly when its decoded record is one of the source observations; consequently its
`ValidFor` at the same source and policy is exactly the validity of that source observation. -/
theorem validFor_mem_relabelCoupledObservationSet_iff [DecidableEq V]
    (e : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    (observations : Set (P93CoupledRingChainAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      ObservationBoundedIn n policy observation)
    (presented : SuppliedCoupledRingChainObservation V policy)
    (member : presented ∈ relabelCoupledObservationSet e observations bounded) :
    (unrelabelCoupledObservation e presented).ValidFor policy source ↔
      ∃ observation, ∃ observationMember : observation ∈ observations,
        relabelCoupledObservation e observation
            (bounded observation observationMember) = presented ∧
          observation.ValidFor policy source := by
  constructor
  · intro valid
    rcases member with ⟨observation, observationMember, relabelEq⟩
    refine ⟨observation, observationMember, relabelEq, ?_⟩
    rw [← relabelEq] at valid
    rwa [unrelabelCoupledObservation_relabelCoupledObservation] at valid
  · rintro ⟨observation, observationMember, relabelEq, valid⟩
    rw [← relabelEq]
    rwa [unrelabelCoupledObservation_relabelCoupledObservation]

/-! ## Shared source context and the composable satellite -/

abbrev CoupledSourceBinding (V : Type*) [DecidableEq V] [Fintype V] :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V

theorem ObservationBoundedIn.of_validFor_binding
    [DecidableEq V] [Fintype V]
    (binding : CoupledSourceBinding V)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    ObservationBoundedIn (Fintype.card V) policy observation := by
  have bounded := ObservationBoundedIn.of_validFor binding.source policy observation valid
  rwa [binding.atomCount_eq] at bounded

/-- A raw coupled observation source: the exact source binding plus an ordered list of
`Nat`-indexed carrier observations, each valid at the bound source. -/
structure RawCoupledObservationSource (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93CoupledRingChainAuthorityPolicy) where
  binding : CoupledSourceBinding V
  observations : List (P93CoupledRingChainAuthorityObservation policy)
  valid : ∀ observation ∈ observations, observation.ValidFor policy binding.source

/-- The composable native satellite.  It carries the same graph/spatial/diagram context as the
existing molecule codec and the ordered list of native observations.  Neither an original
observation record nor an original `AuthoritativeChemicalInput` is stored here. -/
structure CoupledObservationSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93CoupledRingChainAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (SuppliedCoupledRingChainObservation V policy)

namespace CoupledObservationSatellite

variable [DecidableEq V] [Fintype V]

def toFiniteSource (satellite : CoupledObservationSatellite V policy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

end CoupledObservationSatellite

def adapt [DecidableEq V] [Fintype V]
    (raw : RawCoupledObservationSource V policy) :
    CoupledObservationSatellite V policy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := raw.observations.attach.map fun observation =>
    relabelCoupledObservation raw.binding.enumeration observation.1
      (ObservationBoundedIn.of_validFor_binding raw.binding observation.1
        (raw.valid observation.1 observation.2))

@[simp] theorem adapt_graph [DecidableEq V] [Fintype V]
    (raw : RawCoupledObservationSource V policy) :
    (adapt raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adapt_spatial? [DecidableEq V] [Fintype V]
    (raw : RawCoupledObservationSource V policy) :
    (adapt raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adapt_diagram? [DecidableEq V] [Fintype V]
    (raw : RawCoupledObservationSource V policy) :
    (adapt raw).diagram? = raw.binding.shared.diagram? := rfl

/-- The recovered source record: the exact authoritative input and the decoded observation list. -/
@[ext] structure RecoveredCoupledObservationSource
    (policy : P93CoupledRingChainAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : List (P93CoupledRingChainAuthorityObservation policy)

/-- Decode a satellite into the recovered source record.  The authoritative input is the exact
encode of the shared finite source; observations are decoded with the same enumeration. -/
def suppliedSource [DecidableEq V] [Fintype V]
    (e : V ≃ Fin (Fintype.card V))
    (satellite : CoupledObservationSatellite V policy) :
    RecoveredCoupledObservationSource policy where
  source := satellite.toFiniteSource.encode e
  observations := unrelabelCoupledObservationList e satellite.observations

/-- **Exact full source recovery.**  Adapting a raw source and decoding it returns the exact
authoritative input (through the binding's actual source equality) and the exact ordered list of
pre-existing coupled ring-chain observation records, including order and repetitions. -/
theorem suppliedSource_adapt [DecidableEq V] [Fintype V]
    (raw : RawCoupledObservationSource V policy) :
    suppliedSource raw.binding.enumeration (adapt raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredCoupledObservationSource.ext
  · exact raw.binding.encode_shared
  · change unrelabelCoupledObservationList raw.binding.enumeration
        (adapt raw).observations = raw.observations
    rw [show (adapt raw).observations = raw.observations.attach.map (fun observation =>
        relabelCoupledObservation raw.binding.enumeration observation.1
          (ObservationBoundedIn.of_validFor_binding raw.binding observation.1
            (raw.valid observation.1 observation.2))) from rfl]
    exact unrelabelCoupledObservationList_relabelCoupledObservationList
      raw.binding.enumeration raw.observations (fun observation member =>
        ObservationBoundedIn.of_validFor_binding raw.binding observation
          (raw.valid observation member))

/-- Validity is preserved for the whole recovered list at the same source and policy. -/
theorem suppliedSource_adapt_validFor [DecidableEq V] [Fintype V]
    (raw : RawCoupledObservationSource V policy)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (member : observation ∈
      (suppliedSource raw.binding.enumeration (adapt raw)).observations) :
    observation.ValidFor policy raw.binding.source := by
  have listEq : (suppliedSource raw.binding.enumeration (adapt raw)).observations =
      raw.observations := by
    simpa using congrArg (RecoveredCoupledObservationSource.observations)
      (suppliedSource_adapt raw)
  have sourceMember : observation ∈ raw.observations := by
    rw [← listEq]
    exact member
  exact raw.valid observation sourceMember

/-! ## Concrete certified-source adapter -/

def certifiedBinding (certified : CertifiedAuthoritativeChemicalInput) :
    CoupledSourceBinding (Fin certified.input.molecule.atomCount) :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding.ofCertified certified

def adaptCertified (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (P93CoupledRingChainAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor policy certified.input) :
    CoupledObservationSatellite (Fin certified.input.molecule.atomCount) policy :=
  adapt { binding := certifiedBinding certified
          observations := observations
          valid := valid }

/-- **Concrete exact recovery from a certified source.** -/
theorem suppliedSource_adaptCertified
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (P93CoupledRingChainAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor policy certified.input) :
    suppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertified certified observations valid) =
      { source := certified.input, observations := observations } :=
  suppliedSource_adapt
    { binding := certifiedBinding certified
      observations := observations
      valid := valid }

end CoupledObservations

end OrganicStereoCoupledRingChainIngress

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.EvidenceBoundedIn
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.certificateBoundedIn_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.EvidenceBoundedIn.of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.ObservationBoundedIn.of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.unrelabelCoupledObservation_relabelCoupledObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.relabelCoupledObservation_unrelabelCoupledObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.unrelabelCoupledObservationList_relabelCoupledObservationList
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.relabelCoupledObservationList_unrelabelCoupledObservationList
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.unrelabelCoupledObservationSet_relabelCoupledObservationSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.relabelCoupledObservationSet_unrelabelCoupledObservationSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.validFor_mem_relabelCoupledObservationSet_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.suppliedSource_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.suppliedSource_adapt_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress.suppliedSource_adaptCertified
