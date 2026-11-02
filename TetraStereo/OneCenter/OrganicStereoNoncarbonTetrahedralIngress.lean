import TetraStereo.OneCenter.IUPACP93NoncarbonTetrahedralAuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace OrganicStereoNoncarbonTetrahedralIngress

open TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
open BlueBookP93.NoncarbonTetrahedra

/-!
# Lossless native encoding of the P-93.2 noncarbon tetrahedral authority carriers

`IUPACP93NoncarbonTetrahedralAuthorityCarrier` defines seven source records over raw `Nat` atom
indices:

* `P93NoncarbonTetrahedralAssignment` (the plain four-ligand assignment used by the
  other-element-tetrahedra provision),
* `P93NoncarbonCitationAuthorityObservation`,
* `P93NoncarbonOnicAuthorityObservation`,
* `P93NoncarbonOxideAuthorityObservation`,
* `P93NoncarbonPhosphorusOxoAuthorityObservation`,
* `P93NoncarbonChalcogenOxoAuthorityObservation`,
* `P93NoncarbonGroup14AuthorityObservation`.

This module gives a concrete, two-sided native encoding of every one of those records over an
arbitrary finite atom type `V` with an explicit enumeration `V ≃ Fin n`, together with an ordered
tagged family that keeps the seven constructors distinct, a satellite bound to an exact source,
and exact ordered-list and arbitrary-`Set` recovery.

## What is and is not relabelled

The only fields that are atom *indices* are the frame `center`, the ordered frame `ligands`, and
the observation-specific `oxygen`.  They are relabelled through the existing
`OrganicStereoSuppliedCitationIngress` codecs (`encodeAtom`/`decodeAtom`, `relabelList`/
`unrelabelList`) and decode back to exactly the same raw `Nat` indices.

Everything else is nomenclature or family metadata and is copied literally in both directions:

* the source descriptor (a field of `policy.Descriptor`),
* the full `P93AuthorityCitationToken` (component values and prime counts are locants, never graph
  vertices),
* the complete `DescriptorCitationObservation` (`context`, `centralElement`, `locant`,
  `compoundNameNested`),
* the `OnicCenter`, `OxideCenter`, `PhosphorusOxoFamily`, `ChalcogenOxoFamily` and
  `NoncarbonGroup14Center` family tags,
* both written-bonding variants and both formal-charge arrangements.

## Bounds

Every raw atom index occurring in these records is bounded by the source validity predicate:
`P93NoncarbonTetrahedralFrame.StructurallyValidFor` bounds the center and every ligand from the
constitution graph, and each observation's `ValidFor` requires `oxygen` to be one of the frame
ligands.  The native encoder therefore derives its bounds from `ValidFor` rather than assuming
them.  There is no remaining unbounded source index in these seven records, so no unresolved
source reference is introduced.

## Source binding

`RawNoncarbonObservationSource` ties an ordered tagged family of valid source observations to a
`PhysicalFrameSourceBinding V`: the shared finite graph, spatial channel and drawing channel encode
to exactly the stored `AuthoritativeChemicalInput`.  The satellite stores only that independent
finite source and the native observations; it never stores the original observations, and the
decoder `ofNativeObservation` reads every encoded field.

## Scope

No chemical admissibility, descriptor value, citation authorisation or completeness claim is made.
No invariance under an arbitrary permutation of atom labels is claimed; every encode/decode pair
is stated at one fixed enumeration and the recovered source is the exact bound source.  The
validity recovery theorems are stated at the same policy and at the same recovered source.
-/

/-! ## Bounds derived from the actual source validity predicates -/

/-- Bounds on the two atom-indexed fields of one decoration-free four-ligand frame. -/
structure FrameBoundedIn (n : ℕ) (frame : P93NoncarbonTetrahedralFrame) : Prop where
  centerBound : frame.center < n
  ligandsBound : ∀ atom ∈ frame.ligands, atom < n

/-- The structural part of frame validity bounds the center and every ligand. -/
theorem frameBoundedIn_of_structurallyValidFor (source : AuthoritativeChemicalInput)
    (frame : P93NoncarbonTetrahedralFrame)
    (valid : P93NoncarbonTetrahedralFrame.StructurallyValidFor source frame) :
    FrameBoundedIn source.molecule.atomCount frame where
  centerBound := valid.1 frame.center (by simp)
  ligandsBound := fun atom member => valid.1 atom (by simp [member])

/-- Full frame validity implies the same bounds. -/
theorem frameBoundedIn_of_validFor (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput) (frame : P93NoncarbonTetrahedralFrame)
    (valid : P93NoncarbonTetrahedralFrame.ValidFor policy source frame) :
    FrameBoundedIn source.molecule.atomCount frame :=
  frameBoundedIn_of_structurallyValidFor source frame valid.1

/-- Assignment validity bounds the carried frame. -/
theorem assignmentFrameBoundedIn_of_validFor
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignment : P93NoncarbonTetrahedralAssignment policy)
    (valid : P93NoncarbonTetrahedralAssignment.ValidFor policy source assignment) :
    FrameBoundedIn source.molecule.atomCount assignment.frame :=
  frameBoundedIn_of_validFor policy source assignment.frame valid.1

/-! ## The seven source observation records as one tagged family

The seven constructors stay distinct: the plain assignment and each of the six family
observations is its own tag.  The `ValidFor` and `BoundedIn` dispatchers are the only generic
operations; both reduce to the corresponding record predicate on every constructor. -/

/-- One tagged P-93.2 noncarbon observation source record. -/
inductive SourceNoncarbonObservation (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  | tetrahedral (observation : P93NoncarbonTetrahedralAssignment policy)
  | citation (observation : P93NoncarbonCitationAuthorityObservation policy)
  | onic (observation : P93NoncarbonOnicAuthorityObservation policy)
  | oxide (observation : P93NoncarbonOxideAuthorityObservation policy)
  | phosphorusOxo (observation : P93NoncarbonPhosphorusOxoAuthorityObservation policy)
  | chalcogenOxo (observation : P93NoncarbonChalcogenOxoAuthorityObservation policy)
  | group14 (observation : P93NoncarbonGroup14AuthorityObservation policy)

namespace SourceNoncarbonObservation

/-- The source validity predicate of a tagged observation, dispatched on the tag. -/
def ValidFor (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput) :
    SourceNoncarbonObservation policy → Prop
  | .tetrahedral observation =>
      P93NoncarbonTetrahedralAssignment.ValidFor policy source observation
  | .citation observation =>
      P93NoncarbonCitationAuthorityObservation.ValidFor policy source observation
  | .onic observation =>
      P93NoncarbonOnicAuthorityObservation.ValidFor policy source observation
  | .oxide observation =>
      P93NoncarbonOxideAuthorityObservation.ValidFor policy source observation
  | .phosphorusOxo observation =>
      P93NoncarbonPhosphorusOxoAuthorityObservation.ValidFor policy source observation
  | .chalcogenOxo observation =>
      P93NoncarbonChalcogenOxoAuthorityObservation.ValidFor policy source observation
  | .group14 observation =>
      P93NoncarbonGroup14AuthorityObservation.ValidFor policy source observation

/-- The atom bounds of a tagged observation, dispatched on the tag.  Only the frame fields and the
observation-specific `oxygen` are atom indices. -/
def BoundedIn {policy : P93NoncarbonTetrahedralAuthorityPolicy} (n : ℕ) :
    SourceNoncarbonObservation policy → Prop
  | .tetrahedral observation => FrameBoundedIn n observation.frame
  | .citation observation => FrameBoundedIn n observation.assignment.frame
  | .onic observation => FrameBoundedIn n observation.assignment.frame
  | .oxide observation =>
      FrameBoundedIn n observation.assignment.frame ∧ observation.oxygen < n
  | .phosphorusOxo observation =>
      FrameBoundedIn n observation.assignment.frame ∧ observation.oxygen < n
  | .chalcogenOxo observation =>
      FrameBoundedIn n observation.assignment.frame ∧ observation.oxygen < n
  | .group14 observation => FrameBoundedIn n observation.assignment.frame

/-- **Bounds are derived from source validity, not assumed.**  Every atom index of every one of the
seven records is in range of the source molecule. -/
theorem boundedIn_of_validFor (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : SourceNoncarbonObservation policy)
    (valid : SourceNoncarbonObservation.ValidFor policy source observation) :
    SourceNoncarbonObservation.BoundedIn source.molecule.atomCount observation := by
  cases observation with
  | tetrahedral observation =>
      exact assignmentFrameBoundedIn_of_validFor policy source observation valid
  | citation observation =>
      exact assignmentFrameBoundedIn_of_validFor policy source observation.assignment valid.1
  | onic observation =>
      exact assignmentFrameBoundedIn_of_validFor policy source observation.assignment valid.1
  | oxide observation =>
      have valid' :
          P93NoncarbonOxideAuthorityObservation.ValidFor policy source observation := valid
      have assignmentValid :
          P93NoncarbonTetrahedralAssignment.ValidFor policy source observation.assignment :=
        valid'.1
      have frameBounded :
          FrameBoundedIn source.molecule.atomCount observation.assignment.frame :=
        assignmentFrameBoundedIn_of_validFor policy source observation.assignment assignmentValid
      exact ⟨frameBounded, frameBounded.ligandsBound observation.oxygen valid'.2.2.1⟩
  | phosphorusOxo observation =>
      have valid' :
          P93NoncarbonPhosphorusOxoAuthorityObservation.ValidFor policy source observation :=
        valid
      have assignmentValid :
          P93NoncarbonTetrahedralAssignment.ValidFor policy source observation.assignment :=
        valid'.1
      have frameBounded :
          FrameBoundedIn source.molecule.atomCount observation.assignment.frame :=
        assignmentFrameBoundedIn_of_validFor policy source observation.assignment assignmentValid
      exact ⟨frameBounded, frameBounded.ligandsBound observation.oxygen valid'.2.2.1⟩
  | chalcogenOxo observation =>
      have valid' :
          P93NoncarbonChalcogenOxoAuthorityObservation.ValidFor policy source observation :=
        valid
      have assignmentValid :
          P93NoncarbonTetrahedralAssignment.ValidFor policy source observation.assignment :=
        valid'.1
      have frameBounded :
          FrameBoundedIn source.molecule.atomCount observation.assignment.frame :=
        assignmentFrameBoundedIn_of_validFor policy source observation.assignment assignmentValid
      exact ⟨frameBounded, frameBounded.ligandsBound observation.oxygen valid'.2.2.1⟩
  | group14 observation =>
      exact assignmentFrameBoundedIn_of_validFor policy source observation.assignment valid.1

end SourceNoncarbonObservation

/-! ## The native payloads

Each native record carries exactly the corresponding source record's fields.  Only atom references
change their type from `Nat` to `V`; every other field keeps its original type and value. -/

/-- Native four-ligand frame: the ordered ligand list is preserved as a list, so order and
repetition are retained. -/
structure NativeNoncarbonFrame (V : Type*) where
  center : V
  ligands : List V

/-- Native four-ligand assignment, retaining the source descriptor literally. -/
structure NativeTetrahedralAssignment (V : Type*) (Descriptor : Type*) where
  frame : NativeNoncarbonFrame V
  descriptor : Descriptor

/-- Native citation observation.  The optional citation token and the citation-rule record are
nomenclature metadata and are copied literally. -/
structure NativeCitationObservation (V : Type*) (Descriptor : Type*) where
  assignment : NativeTetrahedralAssignment V Descriptor
  citation? : Option P93AuthorityCitationToken
  citationRule : DescriptorCitationObservation

/-- Native onic family observation. -/
structure NativeOnicObservation (V : Type*) (Descriptor : Type*) where
  assignment : NativeTetrahedralAssignment V Descriptor
  family : OnicCenter

/-- Native amine/phosphane oxide observation.  `oxygen` is an atom reference and moves with the
frame; both written bonding variants are copied literally. -/
structure NativeOxideObservation (V : Type*) (Descriptor : Type*) where
  assignment : NativeTetrahedralAssignment V Descriptor
  family : OxideCenter
  oxygen : V
  firstBonding : WrittenBondingToOxygen
  secondBonding : WrittenBondingToOxygen

/-- Native phosphorus-oxo observation. -/
structure NativePhosphorusOxoObservation (V : Type*) (Descriptor : Type*) where
  assignment : NativeTetrahedralAssignment V Descriptor
  family : PhosphorusOxoFamily
  oxygen : V
  firstWrittenAsDouble : Bool
  secondWrittenAsDouble : Bool
  firstCharges : FormalChargeArrangement
  secondCharges : FormalChargeArrangement

/-- Native chalcogen-oxo observation. -/
structure NativeChalcogenOxoObservation (V : Type*) (Descriptor : Type*) where
  assignment : NativeTetrahedralAssignment V Descriptor
  family : ChalcogenOxoFamily
  oxygen : V
  firstWrittenAsDouble : Bool
  secondWrittenAsDouble : Bool
  firstCharges : FormalChargeArrangement
  secondCharges : FormalChargeArrangement

/-- Native group-14 family observation. -/
structure NativeGroup14Observation (V : Type*) (Descriptor : Type*) where
  assignment : NativeTetrahedralAssignment V Descriptor
  family : NoncarbonGroup14Center

/-- The ordered tagged native family.  The seven constructors are distinct, so decoding preserves
which provision an observation belongs to. -/
inductive NativeNoncarbonObservation (V : Type*) (Descriptor : Type*) where
  | tetrahedral (observation : NativeTetrahedralAssignment V Descriptor)
  | citation (observation : NativeCitationObservation V Descriptor)
  | onic (observation : NativeOnicObservation V Descriptor)
  | oxide (observation : NativeOxideObservation V Descriptor)
  | phosphorusOxo (observation : NativePhosphorusOxoObservation V Descriptor)
  | chalcogenOxo (observation : NativeChalcogenOxoObservation V Descriptor)
  | group14 (observation : NativeGroup14Observation V Descriptor)

/-! ## Frame codec

The center and every ligand are encoded through the accepted supplied-citation atom codec.  The
ordered list is encoded position by position; no sorting or deduplication happens. -/

section FrameCodec

variable {V : Type*} {n : ℕ}

/-- Encode one source frame into native vertices. -/
def toNativeFrame (e : V ≃ Fin n) (frame : P93NoncarbonTetrahedralFrame)
    (bounded : FrameBoundedIn n frame) : NativeNoncarbonFrame V where
  center := decodeAtom e frame.center bounded.centerBound
  ligands := relabelList e frame.ligands bounded.ligandsBound

/-- Decode one native frame into the raw source identity. -/
def ofNativeFrame (e : V ≃ Fin n) (native : NativeNoncarbonFrame V) :
    P93NoncarbonTetrahedralFrame where
  center := encodeAtom e native.center
  ligands := unrelabelList e native.ligands

/-- Bounds of a decoded native frame.  These are consequences of `encodeAtom_lt` and the exact
ordered-list inverse, not assumptions. -/
def ofNativeFrameBounded (e : V ≃ Fin n) (native : NativeNoncarbonFrame V) :
    FrameBoundedIn n (ofNativeFrame e native) where
  centerBound := encodeAtom_lt e native.center
  ligandsBound := unrelabelList_bounded e native.ligands

@[simp] theorem ofNativeFrame_center (e : V ≃ Fin n) (native : NativeNoncarbonFrame V) :
    (ofNativeFrame e native).center = encodeAtom e native.center := rfl

@[simp] theorem ofNativeFrame_ligands (e : V ≃ Fin n) (native : NativeNoncarbonFrame V) :
    (ofNativeFrame e native).ligands = unrelabelList e native.ligands := rfl

/-- The accepted atom codec is insensitive to the particular bound proof. -/
theorem decodeAtom_bound_irrel (e : V ≃ Fin n) (value : ℕ)
    (first second : value < n) :
    decodeAtom e value first = decodeAtom e value second := by
  unfold decodeAtom
  rw [show (⟨value, first⟩ : Fin n) = ⟨value, second⟩ from Fin.ext rfl]

/-- The accepted ordered-list codec is insensitive to the particular bound proof. -/
theorem relabelList_bound_irrel (e : V ≃ Fin n) (values : List ℕ)
    (first second : ∀ value ∈ values, value < n) :
    relabelList e values first = relabelList e values second := by
  unfold relabelList
  apply List.map_congr_left
  intro value _
  exact decodeAtom_bound_irrel e value.1 (first value.1 value.2) (second value.1 value.2)

/-- Exact recovery of the raw frame. -/
theorem ofNativeFrame_toNativeFrame (e : V ≃ Fin n) (frame : P93NoncarbonTetrahedralFrame)
    (bounded : FrameBoundedIn n frame) :
    ofNativeFrame e (toNativeFrame e frame bounded) = frame := by
  obtain ⟨center, ligands⟩ := frame
  simp [ofNativeFrame, toNativeFrame, encodeAtom_decodeAtom, unrelabelList_relabelList]

/-- Exact recovery of the native frame from its raw decode. -/
theorem toNativeFrame_ofNativeFrame (e : V ≃ Fin n) (native : NativeNoncarbonFrame V) :
    toNativeFrame e (ofNativeFrame e native) (ofNativeFrameBounded e native) = native := by
  obtain ⟨center, ligands⟩ := native
  simp [ofNativeFrame, toNativeFrame, decodeAtom_encodeAtom,
    relabelList_unrelabelList]

/-- The native encoding of a frame depends on the bound proof only through its truth. -/
theorem toNativeFrame_bound_irrel (e : V ≃ Fin n) (frame : P93NoncarbonTetrahedralFrame)
    (first second : FrameBoundedIn n frame) :
    toNativeFrame e frame first = toNativeFrame e frame second := by
  obtain ⟨centerBound₁, ligandsBound₁⟩ := first
  obtain ⟨centerBound₂, ligandsBound₂⟩ := second
  have centerEq : decodeAtom e frame.center centerBound₁ =
      decodeAtom e frame.center centerBound₂ :=
    decodeAtom_bound_irrel e frame.center centerBound₁ centerBound₂
  have ligandsEq : relabelList e frame.ligands ligandsBound₁ =
      relabelList e frame.ligands ligandsBound₂ :=
    relabelList_bound_irrel e frame.ligands ligandsBound₁ ligandsBound₂
  simp only [toNativeFrame, centerEq, ligandsEq]

end FrameCodec

/-! ## Assignment codec

The descriptor is a source-nomenclature field and is copied literally. -/

section AssignmentCodec

variable {V : Type*} {n : ℕ}

/-- Encode one source assignment into native vertices. -/
def toNativeAssignment (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (assignment : P93NoncarbonTetrahedralAssignment policy)
    (bounded : FrameBoundedIn n assignment.frame) :
    NativeTetrahedralAssignment V policy.Descriptor where
  frame := toNativeFrame e assignment.frame bounded
  descriptor := assignment.descriptor

/-- Decode one native assignment into the raw source record. -/
def ofNativeAssignment (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeTetrahedralAssignment V policy.Descriptor) :
    P93NoncarbonTetrahedralAssignment policy where
  frame := ofNativeFrame e native.frame
  descriptor := native.descriptor

/-- Bounds of a decoded native assignment. -/
def ofNativeAssignmentBounded (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeTetrahedralAssignment V policy.Descriptor) :
    FrameBoundedIn n (ofNativeAssignment e policy native).frame :=
  ofNativeFrameBounded e native.frame

@[simp] theorem ofNativeAssignment_frame (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeTetrahedralAssignment V policy.Descriptor) :
    (ofNativeAssignment e policy native).frame = ofNativeFrame e native.frame := rfl

@[simp] theorem ofNativeAssignment_descriptor (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeTetrahedralAssignment V policy.Descriptor) :
    (ofNativeAssignment e policy native).descriptor = native.descriptor := rfl

/-- Exact recovery of the raw assignment, including its descriptor. -/
theorem ofNativeAssignment_toNativeAssignment (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (assignment : P93NoncarbonTetrahedralAssignment policy)
    (bounded : FrameBoundedIn n assignment.frame) :
    ofNativeAssignment e policy (toNativeAssignment e policy assignment bounded) = assignment := by
  obtain ⟨frame, descriptor⟩ := assignment
  simp [ofNativeAssignment, toNativeAssignment, ofNativeFrame_toNativeFrame]

/-- Exact recovery of the native assignment from its raw decode. -/
theorem toNativeAssignment_ofNativeAssignment (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeTetrahedralAssignment V policy.Descriptor) :
    toNativeAssignment e policy (ofNativeAssignment e policy native)
        (ofNativeAssignmentBounded e policy native) = native := by
  obtain ⟨frame, descriptor⟩ := native
  simp [ofNativeAssignment, toNativeAssignment,
    toNativeFrame_ofNativeFrame]

/-- The native encoding of an assignment depends on the bound proof only through its truth. -/
theorem toNativeAssignment_bound_irrel (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (assignment : P93NoncarbonTetrahedralAssignment policy)
    (first second : FrameBoundedIn n assignment.frame) :
    toNativeAssignment e policy assignment first =
      toNativeAssignment e policy assignment second := by
  obtain ⟨frame, descriptor⟩ := assignment
  have frameEq : toNativeFrame e frame first = toNativeFrame e frame second :=
    toNativeFrame_bound_irrel e frame first second
  simp only [toNativeAssignment, frameEq]

end AssignmentCodec

/-! ## The six family-observation codecs

Every field other than the frame and `oxygen` is copied literally.  The citation token is raw
printed syntax (component values and primes) and is never treated as an atom index. -/

section ObservationCodecs

variable {V : Type*} {n : ℕ}

/-! ### Citation observation -/

/-- Encode one citation observation. -/
def toNativeCitation (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonCitationAuthorityObservation policy)
    (bounded : FrameBoundedIn n observation.assignment.frame) :
    NativeCitationObservation V policy.Descriptor where
  assignment := toNativeAssignment e policy observation.assignment bounded
  citation? := observation.citation?
  citationRule := observation.citationRule

/-- Decode one citation observation. -/
def ofNativeCitation (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeCitationObservation V policy.Descriptor) :
    P93NoncarbonCitationAuthorityObservation policy where
  assignment := ofNativeAssignment e policy native.assignment
  citation? := native.citation?
  citationRule := native.citationRule

/-- Bounds of a decoded citation observation. -/
def ofNativeCitationBounded (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeCitationObservation V policy.Descriptor) :
    FrameBoundedIn n (ofNativeCitation e policy native).assignment.frame :=
  ofNativeAssignmentBounded e policy native.assignment

@[simp] theorem ofNativeCitation_citation? (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeCitationObservation V policy.Descriptor) :
    (ofNativeCitation e policy native).citation? = native.citation? := rfl

/-- The citation-rule record, including its locant kind, central-element family and nesting flag,
is copied literally by the decoder. -/
@[simp] theorem ofNativeCitation_citationRule (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeCitationObservation V policy.Descriptor) :
    (ofNativeCitation e policy native).citationRule = native.citationRule := rfl

/-- Exact recovery of the raw citation observation. -/
theorem ofNativeCitation_toNativeCitation (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonCitationAuthorityObservation policy)
    (bounded : FrameBoundedIn n observation.assignment.frame) :
    ofNativeCitation e policy (toNativeCitation e policy observation bounded) = observation := by
  obtain ⟨assignment, citationToken, citationRule⟩ := observation
  simp [ofNativeCitation, toNativeCitation, ofNativeAssignment_toNativeAssignment]

/-- Exact recovery of the native citation observation. -/
theorem toNativeCitation_ofNativeCitation (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeCitationObservation V policy.Descriptor) :
    toNativeCitation e policy (ofNativeCitation e policy native)
        (ofNativeCitationBounded e policy native) = native := by
  obtain ⟨assignment, citationToken, citationRule⟩ := native
  simp [ofNativeCitation, toNativeCitation,
    toNativeAssignment_ofNativeAssignment]

/-- Bound irrelevance for the citation encoding. -/
theorem toNativeCitation_bound_irrel (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonCitationAuthorityObservation policy)
    (first second : FrameBoundedIn n observation.assignment.frame) :
    toNativeCitation e policy observation first =
      toNativeCitation e policy observation second := by
  obtain ⟨assignment, citationToken, citationRule⟩ := observation
  have assignmentEq : toNativeAssignment e policy assignment first =
      toNativeAssignment e policy assignment second :=
    toNativeAssignment_bound_irrel e policy assignment first second
  simp only [toNativeCitation, assignmentEq]

/-! ### Onic observation -/

/-- Encode one onic observation. -/
def toNativeOnic (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonOnicAuthorityObservation policy)
    (bounded : FrameBoundedIn n observation.assignment.frame) :
    NativeOnicObservation V policy.Descriptor where
  assignment := toNativeAssignment e policy observation.assignment bounded
  family := observation.family

/-- Decode one onic observation. -/
def ofNativeOnic (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeOnicObservation V policy.Descriptor) :
    P93NoncarbonOnicAuthorityObservation policy where
  assignment := ofNativeAssignment e policy native.assignment
  family := native.family

/-- Bounds of a decoded onic observation. -/
def ofNativeOnicBounded (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeOnicObservation V policy.Descriptor) :
    FrameBoundedIn n (ofNativeOnic e policy native).assignment.frame :=
  ofNativeAssignmentBounded e policy native.assignment

/-- The onic family tag is copied literally. -/
@[simp] theorem ofNativeOnic_family (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeOnicObservation V policy.Descriptor) :
    (ofNativeOnic e policy native).family = native.family := rfl

/-- Exact recovery of the raw onic observation. -/
theorem ofNativeOnic_toNativeOnic (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonOnicAuthorityObservation policy)
    (bounded : FrameBoundedIn n observation.assignment.frame) :
    ofNativeOnic e policy (toNativeOnic e policy observation bounded) = observation := by
  obtain ⟨assignment, family⟩ := observation
  simp [ofNativeOnic, toNativeOnic, ofNativeAssignment_toNativeAssignment]

/-- Exact recovery of the native onic observation. -/
theorem toNativeOnic_ofNativeOnic (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeOnicObservation V policy.Descriptor) :
    toNativeOnic e policy (ofNativeOnic e policy native)
        (ofNativeOnicBounded e policy native) = native := by
  obtain ⟨assignment, family⟩ := native
  simp [ofNativeOnic, toNativeOnic,
    toNativeAssignment_ofNativeAssignment]

/-- Bound irrelevance for the onic encoding. -/
theorem toNativeOnic_bound_irrel (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonOnicAuthorityObservation policy)
    (first second : FrameBoundedIn n observation.assignment.frame) :
    toNativeOnic e policy observation first = toNativeOnic e policy observation second := by
  obtain ⟨assignment, family⟩ := observation
  have assignmentEq : toNativeAssignment e policy assignment first =
      toNativeAssignment e policy assignment second :=
    toNativeAssignment_bound_irrel e policy assignment first second
  simp only [toNativeOnic, assignmentEq]

/-! ### Amine/phosphane oxide observation -/

/-- Encode one oxide observation.  `oxygen` is an atom reference; both written bonding variants are
copied literally. -/
def toNativeOxide (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonOxideAuthorityObservation policy)
    (bounded : FrameBoundedIn n observation.assignment.frame ∧ observation.oxygen < n) :
    NativeOxideObservation V policy.Descriptor where
  assignment := toNativeAssignment e policy observation.assignment bounded.1
  family := observation.family
  oxygen := decodeAtom e observation.oxygen bounded.2
  firstBonding := observation.firstBonding
  secondBonding := observation.secondBonding

/-- Decode one oxide observation. -/
def ofNativeOxide (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeOxideObservation V policy.Descriptor) :
    P93NoncarbonOxideAuthorityObservation policy where
  assignment := ofNativeAssignment e policy native.assignment
  family := native.family
  oxygen := encodeAtom e native.oxygen
  firstBonding := native.firstBonding
  secondBonding := native.secondBonding

/-- Bounds of a decoded oxide observation. -/
def ofNativeOxideBounded (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeOxideObservation V policy.Descriptor) :
    FrameBoundedIn n (ofNativeOxide e policy native).assignment.frame ∧
      (ofNativeOxide e policy native).oxygen < n :=
  ⟨ofNativeAssignmentBounded e policy native.assignment, encodeAtom_lt e native.oxygen⟩

/-- The oxide family tag is copied literally. -/
@[simp] theorem ofNativeOxide_family (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeOxideObservation V policy.Descriptor) :
    (ofNativeOxide e policy native).family = native.family := rfl

/-- The decoded oxide oxygen is the accepted atom decoder applied to the encoded oxygen. -/
@[simp] theorem ofNativeOxide_oxygen (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeOxideObservation V policy.Descriptor) :
    (ofNativeOxide e policy native).oxygen = encodeAtom e native.oxygen := rfl

/-- Both written bonding variants are read back literally. -/
@[simp] theorem ofNativeOxide_firstBonding (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeOxideObservation V policy.Descriptor) :
    (ofNativeOxide e policy native).firstBonding = native.firstBonding := rfl

@[simp] theorem ofNativeOxide_secondBonding (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeOxideObservation V policy.Descriptor) :
    (ofNativeOxide e policy native).secondBonding = native.secondBonding := rfl

/-- Exact recovery of the raw oxide observation. -/
theorem ofNativeOxide_toNativeOxide (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonOxideAuthorityObservation policy)
    (bounded : FrameBoundedIn n observation.assignment.frame ∧ observation.oxygen < n) :
    ofNativeOxide e policy (toNativeOxide e policy observation bounded) = observation := by
  obtain ⟨assignment, family, oxygen, firstBonding, secondBonding⟩ := observation
  obtain ⟨frameBounded, oxygenBounded⟩ := bounded
  simp [ofNativeOxide, toNativeOxide, ofNativeAssignment_toNativeAssignment,
    encodeAtom_decodeAtom]

/-- Exact recovery of the native oxide observation. -/
theorem toNativeOxide_ofNativeOxide (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeOxideObservation V policy.Descriptor) :
    toNativeOxide e policy (ofNativeOxide e policy native)
        (ofNativeOxideBounded e policy native) = native := by
  obtain ⟨assignment, family, oxygen, firstBonding, secondBonding⟩ := native
  simp [ofNativeOxide, toNativeOxide,
    toNativeAssignment_ofNativeAssignment, decodeAtom_encodeAtom]

/-- Bound irrelevance for the oxide encoding. -/
theorem toNativeOxide_bound_irrel (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonOxideAuthorityObservation policy)
    (first second : FrameBoundedIn n observation.assignment.frame ∧ observation.oxygen < n) :
    toNativeOxide e policy observation first = toNativeOxide e policy observation second := by
  obtain ⟨assignment, family, oxygen, firstBonding, secondBonding⟩ := observation
  obtain ⟨firstFrame, firstOxygen⟩ := first
  obtain ⟨secondFrame, secondOxygen⟩ := second
  have assignmentEq : toNativeAssignment e policy assignment firstFrame =
      toNativeAssignment e policy assignment secondFrame :=
    toNativeAssignment_bound_irrel e policy assignment firstFrame secondFrame
  have oxygenEq : decodeAtom e oxygen firstOxygen = decodeAtom e oxygen secondOxygen :=
    decodeAtom_bound_irrel e oxygen firstOxygen secondOxygen
  simp only [toNativeOxide, assignmentEq, oxygenEq]

/-! ### Phosphorus-oxo observation -/

/-- Encode one phosphorus-oxo observation. -/
def toNativePhosphorusOxo (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonPhosphorusOxoAuthorityObservation policy)
    (bounded : FrameBoundedIn n observation.assignment.frame ∧ observation.oxygen < n) :
    NativePhosphorusOxoObservation V policy.Descriptor where
  assignment := toNativeAssignment e policy observation.assignment bounded.1
  family := observation.family
  oxygen := decodeAtom e observation.oxygen bounded.2
  firstWrittenAsDouble := observation.firstWrittenAsDouble
  secondWrittenAsDouble := observation.secondWrittenAsDouble
  firstCharges := observation.firstCharges
  secondCharges := observation.secondCharges

/-- Decode one phosphorus-oxo observation. -/
def ofNativePhosphorusOxo (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativePhosphorusOxoObservation V policy.Descriptor) :
    P93NoncarbonPhosphorusOxoAuthorityObservation policy where
  assignment := ofNativeAssignment e policy native.assignment
  family := native.family
  oxygen := encodeAtom e native.oxygen
  firstWrittenAsDouble := native.firstWrittenAsDouble
  secondWrittenAsDouble := native.secondWrittenAsDouble
  firstCharges := native.firstCharges
  secondCharges := native.secondCharges

/-- Bounds of a decoded phosphorus-oxo observation. -/
def ofNativePhosphorusOxoBounded (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativePhosphorusOxoObservation V policy.Descriptor) :
    FrameBoundedIn n (ofNativePhosphorusOxo e policy native).assignment.frame ∧
      (ofNativePhosphorusOxo e policy native).oxygen < n :=
  ⟨ofNativeAssignmentBounded e policy native.assignment, encodeAtom_lt e native.oxygen⟩

@[simp] theorem ofNativePhosphorusOxo_family (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativePhosphorusOxoObservation V policy.Descriptor) :
    (ofNativePhosphorusOxo e policy native).family = native.family := rfl

@[simp] theorem ofNativePhosphorusOxo_oxygen (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativePhosphorusOxoObservation V policy.Descriptor) :
    (ofNativePhosphorusOxo e policy native).oxygen = encodeAtom e native.oxygen := rfl

/-- Exact recovery of the raw phosphorus-oxo observation, including both written bond orders and
both formal-charge arrangements. -/
theorem ofNativePhosphorusOxo_toNativePhosphorusOxo (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonPhosphorusOxoAuthorityObservation policy)
    (bounded : FrameBoundedIn n observation.assignment.frame ∧ observation.oxygen < n) :
    ofNativePhosphorusOxo e policy
        (toNativePhosphorusOxo e policy observation bounded) = observation := by
  obtain ⟨assignment, family, oxygen, firstWrittenAsDouble, secondWrittenAsDouble,
    firstCharges, secondCharges⟩ := observation
  obtain ⟨frameBounded, oxygenBounded⟩ := bounded
  simp [ofNativePhosphorusOxo, toNativePhosphorusOxo,
    ofNativeAssignment_toNativeAssignment, encodeAtom_decodeAtom]

/-- Exact recovery of the native phosphorus-oxo observation. -/
theorem toNativePhosphorusOxo_ofNativePhosphorusOxo (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativePhosphorusOxoObservation V policy.Descriptor) :
    toNativePhosphorusOxo e policy (ofNativePhosphorusOxo e policy native)
        (ofNativePhosphorusOxoBounded e policy native) = native := by
  obtain ⟨assignment, family, oxygen, firstWrittenAsDouble, secondWrittenAsDouble,
    firstCharges, secondCharges⟩ := native
  simp [ofNativePhosphorusOxo, toNativePhosphorusOxo,
    toNativeAssignment_ofNativeAssignment, decodeAtom_encodeAtom]

/-- Bound irrelevance for the phosphorus-oxo encoding. -/
theorem toNativePhosphorusOxo_bound_irrel (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonPhosphorusOxoAuthorityObservation policy)
    (first second : FrameBoundedIn n observation.assignment.frame ∧ observation.oxygen < n) :
    toNativePhosphorusOxo e policy observation first =
      toNativePhosphorusOxo e policy observation second := by
  obtain ⟨assignment, family, oxygen, firstWrittenAsDouble, secondWrittenAsDouble,
    firstCharges, secondCharges⟩ := observation
  obtain ⟨firstFrame, firstOxygen⟩ := first
  obtain ⟨secondFrame, secondOxygen⟩ := second
  have assignmentEq : toNativeAssignment e policy assignment firstFrame =
      toNativeAssignment e policy assignment secondFrame :=
    toNativeAssignment_bound_irrel e policy assignment firstFrame secondFrame
  have oxygenEq : decodeAtom e oxygen firstOxygen = decodeAtom e oxygen secondOxygen :=
    decodeAtom_bound_irrel e oxygen firstOxygen secondOxygen
  simp only [toNativePhosphorusOxo, assignmentEq, oxygenEq]

/-! ### Chalcogen-oxo observation -/

/-- Encode one chalcogen-oxo observation. -/
def toNativeChalcogenOxo (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonChalcogenOxoAuthorityObservation policy)
    (bounded : FrameBoundedIn n observation.assignment.frame ∧ observation.oxygen < n) :
    NativeChalcogenOxoObservation V policy.Descriptor where
  assignment := toNativeAssignment e policy observation.assignment bounded.1
  family := observation.family
  oxygen := decodeAtom e observation.oxygen bounded.2
  firstWrittenAsDouble := observation.firstWrittenAsDouble
  secondWrittenAsDouble := observation.secondWrittenAsDouble
  firstCharges := observation.firstCharges
  secondCharges := observation.secondCharges

/-- Decode one chalcogen-oxo observation. -/
def ofNativeChalcogenOxo (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeChalcogenOxoObservation V policy.Descriptor) :
    P93NoncarbonChalcogenOxoAuthorityObservation policy where
  assignment := ofNativeAssignment e policy native.assignment
  family := native.family
  oxygen := encodeAtom e native.oxygen
  firstWrittenAsDouble := native.firstWrittenAsDouble
  secondWrittenAsDouble := native.secondWrittenAsDouble
  firstCharges := native.firstCharges
  secondCharges := native.secondCharges

/-- Bounds of a decoded chalcogen-oxo observation. -/
def ofNativeChalcogenOxoBounded (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeChalcogenOxoObservation V policy.Descriptor) :
    FrameBoundedIn n (ofNativeChalcogenOxo e policy native).assignment.frame ∧
      (ofNativeChalcogenOxo e policy native).oxygen < n :=
  ⟨ofNativeAssignmentBounded e policy native.assignment, encodeAtom_lt e native.oxygen⟩

@[simp] theorem ofNativeChalcogenOxo_family (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeChalcogenOxoObservation V policy.Descriptor) :
    (ofNativeChalcogenOxo e policy native).family = native.family := rfl

@[simp] theorem ofNativeChalcogenOxo_oxygen (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeChalcogenOxoObservation V policy.Descriptor) :
    (ofNativeChalcogenOxo e policy native).oxygen = encodeAtom e native.oxygen := rfl

/-- Exact recovery of the raw chalcogen-oxo observation. -/
theorem ofNativeChalcogenOxo_toNativeChalcogenOxo (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonChalcogenOxoAuthorityObservation policy)
    (bounded : FrameBoundedIn n observation.assignment.frame ∧ observation.oxygen < n) :
    ofNativeChalcogenOxo e policy
        (toNativeChalcogenOxo e policy observation bounded) = observation := by
  obtain ⟨assignment, family, oxygen, firstWrittenAsDouble, secondWrittenAsDouble,
    firstCharges, secondCharges⟩ := observation
  obtain ⟨frameBounded, oxygenBounded⟩ := bounded
  simp [ofNativeChalcogenOxo, toNativeChalcogenOxo,
    ofNativeAssignment_toNativeAssignment, encodeAtom_decodeAtom]

/-- Exact recovery of the native chalcogen-oxo observation. -/
theorem toNativeChalcogenOxo_ofNativeChalcogenOxo (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeChalcogenOxoObservation V policy.Descriptor) :
    toNativeChalcogenOxo e policy (ofNativeChalcogenOxo e policy native)
        (ofNativeChalcogenOxoBounded e policy native) = native := by
  obtain ⟨assignment, family, oxygen, firstWrittenAsDouble, secondWrittenAsDouble,
    firstCharges, secondCharges⟩ := native
  simp [ofNativeChalcogenOxo, toNativeChalcogenOxo,
    toNativeAssignment_ofNativeAssignment, decodeAtom_encodeAtom]

/-- Bound irrelevance for the chalcogen-oxo encoding. -/
theorem toNativeChalcogenOxo_bound_irrel (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonChalcogenOxoAuthorityObservation policy)
    (first second : FrameBoundedIn n observation.assignment.frame ∧ observation.oxygen < n) :
    toNativeChalcogenOxo e policy observation first =
      toNativeChalcogenOxo e policy observation second := by
  obtain ⟨assignment, family, oxygen, firstWrittenAsDouble, secondWrittenAsDouble,
    firstCharges, secondCharges⟩ := observation
  obtain ⟨firstFrame, firstOxygen⟩ := first
  obtain ⟨secondFrame, secondOxygen⟩ := second
  have assignmentEq : toNativeAssignment e policy assignment firstFrame =
      toNativeAssignment e policy assignment secondFrame :=
    toNativeAssignment_bound_irrel e policy assignment firstFrame secondFrame
  have oxygenEq : decodeAtom e oxygen firstOxygen = decodeAtom e oxygen secondOxygen :=
    decodeAtom_bound_irrel e oxygen firstOxygen secondOxygen
  simp only [toNativeChalcogenOxo, assignmentEq, oxygenEq]

/-! ### Group-14 observation -/

/-- Encode one group-14 observation. -/
def toNativeGroup14 (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonGroup14AuthorityObservation policy)
    (bounded : FrameBoundedIn n observation.assignment.frame) :
    NativeGroup14Observation V policy.Descriptor where
  assignment := toNativeAssignment e policy observation.assignment bounded
  family := observation.family

/-- Decode one group-14 observation. -/
def ofNativeGroup14 (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeGroup14Observation V policy.Descriptor) :
    P93NoncarbonGroup14AuthorityObservation policy where
  assignment := ofNativeAssignment e policy native.assignment
  family := native.family

/-- Bounds of a decoded group-14 observation. -/
def ofNativeGroup14Bounded (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeGroup14Observation V policy.Descriptor) :
    FrameBoundedIn n (ofNativeGroup14 e policy native).assignment.frame :=
  ofNativeAssignmentBounded e policy native.assignment

/-- The group-14 family tag is copied literally. -/
@[simp] theorem ofNativeGroup14_family (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeGroup14Observation V policy.Descriptor) :
    (ofNativeGroup14 e policy native).family = native.family := rfl

/-- Exact recovery of the raw group-14 observation. -/
theorem ofNativeGroup14_toNativeGroup14 (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonGroup14AuthorityObservation policy)
    (bounded : FrameBoundedIn n observation.assignment.frame) :
    ofNativeGroup14 e policy (toNativeGroup14 e policy observation bounded) = observation := by
  obtain ⟨assignment, family⟩ := observation
  simp [ofNativeGroup14, toNativeGroup14, ofNativeAssignment_toNativeAssignment]

/-- Exact recovery of the native group-14 observation. -/
theorem toNativeGroup14_ofNativeGroup14 (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeGroup14Observation V policy.Descriptor) :
    toNativeGroup14 e policy (ofNativeGroup14 e policy native)
        (ofNativeGroup14Bounded e policy native) = native := by
  obtain ⟨assignment, family⟩ := native
  simp [ofNativeGroup14, toNativeGroup14,
    toNativeAssignment_ofNativeAssignment]

/-- Bound irrelevance for the group-14 encoding. -/
theorem toNativeGroup14_bound_irrel (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : P93NoncarbonGroup14AuthorityObservation policy)
    (first second : FrameBoundedIn n observation.assignment.frame) :
    toNativeGroup14 e policy observation first =
      toNativeGroup14 e policy observation second := by
  obtain ⟨assignment, family⟩ := observation
  have assignmentEq : toNativeAssignment e policy assignment first =
      toNativeAssignment e policy assignment second :=
    toNativeAssignment_bound_irrel e policy assignment first second
  simp only [toNativeGroup14, assignmentEq]

end ObservationCodecs

/-! ## The tagged observation codec

The seven constructors remain distinct in both directions.  The bound argument of the encoder is
`SourceNoncarbonObservation.BoundedIn`, dispatched on the same tag, so the tagged encoder is a
single function over the concrete record shapes. -/

section TaggedCodec

variable {V : Type*} {n : ℕ}

/-- Encode one tagged source observation.  The provision tag is preserved. -/
def toNativeObservation (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : SourceNoncarbonObservation policy)
    (bounded : SourceNoncarbonObservation.BoundedIn n observation) :
    NativeNoncarbonObservation V policy.Descriptor :=
  match observation, bounded with
  | .tetrahedral o, b => .tetrahedral (toNativeAssignment e policy o b)
  | .citation o, b => .citation (toNativeCitation e policy o b)
  | .onic o, b => .onic (toNativeOnic e policy o b)
  | .oxide o, b => .oxide (toNativeOxide e policy o b)
  | .phosphorusOxo o, b => .phosphorusOxo (toNativePhosphorusOxo e policy o b)
  | .chalcogenOxo o, b => .chalcogenOxo (toNativeChalcogenOxo e policy o b)
  | .group14 o, b => .group14 (toNativeGroup14 e policy o b)

/-- Decode one tagged native observation into the raw source record of the same provision. -/
def ofNativeObservation (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) :
    NativeNoncarbonObservation V policy.Descriptor → SourceNoncarbonObservation policy
  | .tetrahedral o => .tetrahedral (ofNativeAssignment e policy o)
  | .citation o => .citation (ofNativeCitation e policy o)
  | .onic o => .onic (ofNativeOnic e policy o)
  | .oxide o => .oxide (ofNativeOxide e policy o)
  | .phosphorusOxo o => .phosphorusOxo (ofNativePhosphorusOxo e policy o)
  | .chalcogenOxo o => .chalcogenOxo (ofNativeChalcogenOxo e policy o)
  | .group14 o => .group14 (ofNativeGroup14 e policy o)

/-- Bounds of a decoded tagged observation, dispatched on the native tag. -/
def ofNativeObservationBounded (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeNoncarbonObservation V policy.Descriptor) :
    SourceNoncarbonObservation.BoundedIn n (ofNativeObservation e policy native) :=
  match native with
  | .tetrahedral o => ofNativeAssignmentBounded e policy o
  | .citation o => ofNativeCitationBounded e policy o
  | .onic o => ofNativeOnicBounded e policy o
  | .oxide o => ofNativeOxideBounded e policy o
  | .phosphorusOxo o => ofNativePhosphorusOxoBounded e policy o
  | .chalcogenOxo o => ofNativeChalcogenOxoBounded e policy o
  | .group14 o => ofNativeGroup14Bounded e policy o

/-! ### Constructor dispatch lemmas

These are the equation lemmas of the two tagged functions, stated so that every provision is
visible as its own case. -/

@[simp] theorem toNativeObservation_tetrahedral (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : P93NoncarbonTetrahedralAssignment policy)
    (bounded : FrameBoundedIn n o.frame) :
    toNativeObservation e policy (.tetrahedral o) bounded =
      .tetrahedral (toNativeAssignment e policy o bounded) := rfl

@[simp] theorem toNativeObservation_citation (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : P93NoncarbonCitationAuthorityObservation policy)
    (bounded : FrameBoundedIn n o.assignment.frame) :
    toNativeObservation e policy (.citation o) bounded =
      .citation (toNativeCitation e policy o bounded) := rfl

@[simp] theorem toNativeObservation_onic (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : P93NoncarbonOnicAuthorityObservation policy)
    (bounded : FrameBoundedIn n o.assignment.frame) :
    toNativeObservation e policy (.onic o) bounded =
      .onic (toNativeOnic e policy o bounded) := rfl

@[simp] theorem toNativeObservation_oxide (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : P93NoncarbonOxideAuthorityObservation policy)
    (bounded : FrameBoundedIn n o.assignment.frame ∧ o.oxygen < n) :
    toNativeObservation e policy (.oxide o) bounded =
      .oxide (toNativeOxide e policy o bounded) := rfl

@[simp] theorem toNativeObservation_phosphorusOxo (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : P93NoncarbonPhosphorusOxoAuthorityObservation policy)
    (bounded : FrameBoundedIn n o.assignment.frame ∧ o.oxygen < n) :
    toNativeObservation e policy (.phosphorusOxo o) bounded =
      .phosphorusOxo (toNativePhosphorusOxo e policy o bounded) := rfl

@[simp] theorem toNativeObservation_chalcogenOxo (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : P93NoncarbonChalcogenOxoAuthorityObservation policy)
    (bounded : FrameBoundedIn n o.assignment.frame ∧ o.oxygen < n) :
    toNativeObservation e policy (.chalcogenOxo o) bounded =
      .chalcogenOxo (toNativeChalcogenOxo e policy o bounded) := rfl

@[simp] theorem toNativeObservation_group14 (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : P93NoncarbonGroup14AuthorityObservation policy)
    (bounded : FrameBoundedIn n o.assignment.frame) :
    toNativeObservation e policy (.group14 o) bounded =
      .group14 (toNativeGroup14 e policy o bounded) := rfl

@[simp] theorem ofNativeObservation_tetrahedral (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : NativeTetrahedralAssignment V policy.Descriptor) :
    ofNativeObservation e policy (.tetrahedral o) =
      .tetrahedral (ofNativeAssignment e policy o) := rfl

@[simp] theorem ofNativeObservation_citation (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : NativeCitationObservation V policy.Descriptor) :
    ofNativeObservation e policy (.citation o) =
      .citation (ofNativeCitation e policy o) := rfl

@[simp] theorem ofNativeObservation_onic (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : NativeOnicObservation V policy.Descriptor) :
    ofNativeObservation e policy (.onic o) =
      .onic (ofNativeOnic e policy o) := rfl

@[simp] theorem ofNativeObservation_oxide (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : NativeOxideObservation V policy.Descriptor) :
    ofNativeObservation e policy (.oxide o) =
      .oxide (ofNativeOxide e policy o) := rfl

@[simp] theorem ofNativeObservation_phosphorusOxo (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : NativePhosphorusOxoObservation V policy.Descriptor) :
    ofNativeObservation e policy (.phosphorusOxo o) =
      .phosphorusOxo (ofNativePhosphorusOxo e policy o) := rfl

@[simp] theorem ofNativeObservation_chalcogenOxo (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : NativeChalcogenOxoObservation V policy.Descriptor) :
    ofNativeObservation e policy (.chalcogenOxo o) =
      .chalcogenOxo (ofNativeChalcogenOxo e policy o) := rfl

@[simp] theorem ofNativeObservation_group14 (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (o : NativeGroup14Observation V policy.Descriptor) :
    ofNativeObservation e policy (.group14 o) =
      .group14 (ofNativeGroup14 e policy o) := rfl

/-! ### Exact inverses of the tagged codec -/

/-- **Exact record inverse.**  Decoding the encoding of any tagged source observation returns that
same observation, with the same provision constructor and every field unchanged. -/
theorem ofNativeObservation_toNativeObservation (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : SourceNoncarbonObservation policy)
    (bounded : SourceNoncarbonObservation.BoundedIn n observation) :
    ofNativeObservation e policy (toNativeObservation e policy observation bounded) =
      observation := by
  cases observation with
  | tetrahedral o =>
      show SourceNoncarbonObservation.tetrahedral
          (ofNativeAssignment e policy (toNativeAssignment e policy o bounded)) =
        SourceNoncarbonObservation.tetrahedral o
      rw [ofNativeAssignment_toNativeAssignment]
  | citation o =>
      show SourceNoncarbonObservation.citation
          (ofNativeCitation e policy (toNativeCitation e policy o bounded)) =
        SourceNoncarbonObservation.citation o
      rw [ofNativeCitation_toNativeCitation]
  | onic o =>
      show SourceNoncarbonObservation.onic
          (ofNativeOnic e policy (toNativeOnic e policy o bounded)) =
        SourceNoncarbonObservation.onic o
      rw [ofNativeOnic_toNativeOnic]
  | oxide o =>
      show SourceNoncarbonObservation.oxide
          (ofNativeOxide e policy (toNativeOxide e policy o bounded)) =
        SourceNoncarbonObservation.oxide o
      rw [ofNativeOxide_toNativeOxide]
  | phosphorusOxo o =>
      show SourceNoncarbonObservation.phosphorusOxo
          (ofNativePhosphorusOxo e policy (toNativePhosphorusOxo e policy o bounded)) =
        SourceNoncarbonObservation.phosphorusOxo o
      rw [ofNativePhosphorusOxo_toNativePhosphorusOxo]
  | chalcogenOxo o =>
      show SourceNoncarbonObservation.chalcogenOxo
          (ofNativeChalcogenOxo e policy (toNativeChalcogenOxo e policy o bounded)) =
        SourceNoncarbonObservation.chalcogenOxo o
      rw [ofNativeChalcogenOxo_toNativeChalcogenOxo]
  | group14 o =>
      show SourceNoncarbonObservation.group14
          (ofNativeGroup14 e policy (toNativeGroup14 e policy o bounded)) =
        SourceNoncarbonObservation.group14 o
      rw [ofNativeGroup14_toNativeGroup14]

/-- **Exact native inverse.**  Encoding the decode of any native tagged observation returns that
same native observation, including its provision constructor. -/
theorem toNativeObservation_ofNativeObservation (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (native : NativeNoncarbonObservation V policy.Descriptor) :
    toNativeObservation e policy (ofNativeObservation e policy native)
        (ofNativeObservationBounded e policy native) = native := by
  cases native with
  | tetrahedral o =>
      show NativeNoncarbonObservation.tetrahedral
          (toNativeAssignment e policy (ofNativeAssignment e policy o)
            (ofNativeAssignmentBounded e policy o)) =
        NativeNoncarbonObservation.tetrahedral o
      rw [toNativeAssignment_ofNativeAssignment]
  | citation o =>
      show NativeNoncarbonObservation.citation
          (toNativeCitation e policy (ofNativeCitation e policy o)
            (ofNativeCitationBounded e policy o)) =
        NativeNoncarbonObservation.citation o
      rw [toNativeCitation_ofNativeCitation]
  | onic o =>
      show NativeNoncarbonObservation.onic
          (toNativeOnic e policy (ofNativeOnic e policy o)
            (ofNativeOnicBounded e policy o)) =
        NativeNoncarbonObservation.onic o
      rw [toNativeOnic_ofNativeOnic]
  | oxide o =>
      show NativeNoncarbonObservation.oxide
          (toNativeOxide e policy (ofNativeOxide e policy o)
            (ofNativeOxideBounded e policy o)) =
        NativeNoncarbonObservation.oxide o
      rw [toNativeOxide_ofNativeOxide]
  | phosphorusOxo o =>
      show NativeNoncarbonObservation.phosphorusOxo
          (toNativePhosphorusOxo e policy (ofNativePhosphorusOxo e policy o)
            (ofNativePhosphorusOxoBounded e policy o)) =
        NativeNoncarbonObservation.phosphorusOxo o
      rw [toNativePhosphorusOxo_ofNativePhosphorusOxo]
  | chalcogenOxo o =>
      show NativeNoncarbonObservation.chalcogenOxo
          (toNativeChalcogenOxo e policy (ofNativeChalcogenOxo e policy o)
            (ofNativeChalcogenOxoBounded e policy o)) =
        NativeNoncarbonObservation.chalcogenOxo o
      rw [toNativeChalcogenOxo_ofNativeChalcogenOxo]
  | group14 o =>
      show NativeNoncarbonObservation.group14
          (toNativeGroup14 e policy (ofNativeGroup14 e policy o)
            (ofNativeGroup14Bounded e policy o)) =
        NativeNoncarbonObservation.group14 o
      rw [toNativeGroup14_ofNativeGroup14]

/-- The tagged encoder depends on the bound proof only through its truth. -/
theorem toNativeObservation_bound_irrel (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : SourceNoncarbonObservation policy)
    (first second : SourceNoncarbonObservation.BoundedIn n observation) :
    toNativeObservation e policy observation first =
      toNativeObservation e policy observation second := by
  cases observation with
  | tetrahedral o =>
      show NativeNoncarbonObservation.tetrahedral
          (toNativeAssignment e policy o first) =
        NativeNoncarbonObservation.tetrahedral (toNativeAssignment e policy o second)
      exact congrArg NativeNoncarbonObservation.tetrahedral
        (toNativeAssignment_bound_irrel e policy o first second)
  | citation o =>
      show NativeNoncarbonObservation.citation (toNativeCitation e policy o first) =
        NativeNoncarbonObservation.citation (toNativeCitation e policy o second)
      exact congrArg NativeNoncarbonObservation.citation
        (toNativeCitation_bound_irrel e policy o first second)
  | onic o =>
      show NativeNoncarbonObservation.onic (toNativeOnic e policy o first) =
        NativeNoncarbonObservation.onic (toNativeOnic e policy o second)
      exact congrArg NativeNoncarbonObservation.onic
        (toNativeOnic_bound_irrel e policy o first second)
  | oxide o =>
      show NativeNoncarbonObservation.oxide (toNativeOxide e policy o first) =
        NativeNoncarbonObservation.oxide (toNativeOxide e policy o second)
      exact congrArg NativeNoncarbonObservation.oxide
        (toNativeOxide_bound_irrel e policy o first second)
  | phosphorusOxo o =>
      show NativeNoncarbonObservation.phosphorusOxo
          (toNativePhosphorusOxo e policy o first) =
        NativeNoncarbonObservation.phosphorusOxo (toNativePhosphorusOxo e policy o second)
      exact congrArg NativeNoncarbonObservation.phosphorusOxo
        (toNativePhosphorusOxo_bound_irrel e policy o first second)
  | chalcogenOxo o =>
      show NativeNoncarbonObservation.chalcogenOxo
          (toNativeChalcogenOxo e policy o first) =
        NativeNoncarbonObservation.chalcogenOxo (toNativeChalcogenOxo e policy o second)
      exact congrArg NativeNoncarbonObservation.chalcogenOxo
        (toNativeChalcogenOxo_bound_irrel e policy o first second)
  | group14 o =>
      show NativeNoncarbonObservation.group14 (toNativeGroup14 e policy o first) =
        NativeNoncarbonObservation.group14 (toNativeGroup14 e policy o second)
      exact congrArg NativeNoncarbonObservation.group14
        (toNativeGroup14_bound_irrel e policy o first second)

/-- The tagged encoder respects equality of source observations, independently of how the two
bound witnesses were obtained. -/
theorem toNativeObservation_congr (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    {first second : SourceNoncarbonObservation policy} (equal : first = second)
    (firstBounded : SourceNoncarbonObservation.BoundedIn n first)
    (secondBounded : SourceNoncarbonObservation.BoundedIn n second) :
    toNativeObservation e policy first firstBounded =
      toNativeObservation e policy second secondBounded := by
  cases equal
  exact toNativeObservation_bound_irrel e policy first firstBounded secondBounded

/-- **Same-source validity recovery for one record.**  Encoding a valid source observation and
decoding it again returns a record valid at exactly the same policy and source. -/
theorem ofNativeObservation_toNativeObservation_validFor (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : SourceNoncarbonObservation policy)
    (bounded : SourceNoncarbonObservation.BoundedIn n observation)
    (valid : SourceNoncarbonObservation.ValidFor policy source observation) :
    SourceNoncarbonObservation.ValidFor policy source
      (ofNativeObservation e policy (toNativeObservation e policy observation bounded)) := by
  rwa [ofNativeObservation_toNativeObservation]

end TaggedCodec

/-! ## The ordered observation-list codec

The list is encoded position by position through `List.attach`; order, multiplicity and each
concrete provision constructor are preserved.  Repetitions are retained because nothing is
deduplicated and no set is taken. -/

section ListCodec

variable {V : Type*} {n : ℕ}

/-- Encode an ordered list of source observations, using each member's own derived bound. -/
def toNativeObservations (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observations : List (SourceNoncarbonObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceNoncarbonObservation.BoundedIn n observation) :
    List (NativeNoncarbonObservation V policy.Descriptor) :=
  observations.attach.map fun observation =>
    toNativeObservation e policy observation.1 (bounded observation.1 observation.2)

/-- Decode an ordered list of native observations. -/
def ofNativeObservations (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observations : List (NativeNoncarbonObservation V policy.Descriptor)) :
    List (SourceNoncarbonObservation policy) :=
  observations.map (ofNativeObservation e policy)

/-- Every decoded element of a native list satisfies the explicit bounds. -/
def ofNativeObservationsBounded (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observations : List (NativeNoncarbonObservation V policy.Descriptor)) :
    ∀ observation ∈ ofNativeObservations e policy observations,
      SourceNoncarbonObservation.BoundedIn n observation := by
  intro observation member
  rw [ofNativeObservations, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact ofNativeObservationBounded e policy presented

@[simp] theorem toNativeObservations_length (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observations : List (SourceNoncarbonObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceNoncarbonObservation.BoundedIn n observation) :
    (toNativeObservations e policy observations bounded).length = observations.length := by
  simp [toNativeObservations]

@[simp] theorem ofNativeObservations_length (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observations : List (NativeNoncarbonObservation V policy.Descriptor)) :
    (ofNativeObservations e policy observations).length = observations.length := by
  simp [ofNativeObservations]

/-- **Exact ordered-list inverse.**  Decoding an encoded list returns exactly the original list:
the same length, the same order, the same repeated entries and the same provision constructor for
every position. -/
theorem ofNativeObservations_toNativeObservations (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observations : List (SourceNoncarbonObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceNoncarbonObservation.BoundedIn n observation) :
    ofNativeObservations e policy (toNativeObservations e policy observations bounded) =
      observations := by
  unfold ofNativeObservations toNativeObservations
  rw [List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact ofNativeObservation_toNativeObservation e policy observation.1
      (bounded observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

/-- Encoding a decoded list returns the supplied native list. -/
theorem toNativeObservations_ofNativeObservations (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observations : List (NativeNoncarbonObservation V policy.Descriptor)) :
    toNativeObservations e policy (ofNativeObservations e policy observations)
        (ofNativeObservationsBounded e policy observations) = observations := by
  unfold toNativeObservations ofNativeObservations
  rw [List.attach_map, List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact toNativeObservation_ofNativeObservation e policy observation.1
  · exact List.attach_map_subtype_val observations

/-- **Same-source validity for the whole recovered list.**  Every decoded observation of an
encoded list of source-valid observations is valid at the same policy and source. -/
theorem ofNativeObservations_toNativeObservations_validFor (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observations : List (SourceNoncarbonObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceNoncarbonObservation.BoundedIn n observation)
    (valid : ∀ observation ∈ observations,
      SourceNoncarbonObservation.ValidFor policy source observation) :
    ∀ observation ∈
        ofNativeObservations e policy (toNativeObservations e policy observations bounded),
      SourceNoncarbonObservation.ValidFor policy source observation := by
  intro observation member
  rw [ofNativeObservations_toNativeObservations e policy observations bounded] at member
  exact valid observation member

end ListCodec

/-! ## The correlated observation-set codec

A set of source observations has no order, but its members remain correlated with their own bounds
and provision constructors.  The image and preimage below are exact inverses on both sides. -/

section SetCodec

variable {V : Type*} {n : ℕ}

/-- Image of a correlated set of source observations. -/
def toNativeObservationSet (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observations : Set (SourceNoncarbonObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceNoncarbonObservation.BoundedIn n observation) :
    Set (NativeNoncarbonObservation V policy.Descriptor) :=
  fun presented =>
    ∃ observation, ∃ member : observation ∈ observations,
      toNativeObservation e policy observation (bounded observation member) = presented

/-- Preimage of a set of native observations. -/
def ofNativeObservationSet (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observations : Set (NativeNoncarbonObservation V policy.Descriptor)) :
    Set (SourceNoncarbonObservation policy) :=
  fun recovered =>
    ∃ presented ∈ observations,
      ofNativeObservation e policy presented = recovered

/-- Every decoded element of a native set satisfies the explicit bounds. -/
def ofNativeObservationSetBounded (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observations : Set (NativeNoncarbonObservation V policy.Descriptor)) :
    ∀ observation ∈ ofNativeObservationSet e policy observations,
      SourceNoncarbonObservation.BoundedIn n observation := by
  rintro recovered ⟨presented, _presentedMember, rfl⟩
  exact ofNativeObservationBounded e policy presented

/-- **Exact set inverse on the source side.**  Decoding the image of a correlated set returns
exactly that set, for an arbitrary (not necessarily finite or ordered) set. -/
theorem ofNativeObservationSet_toNativeObservationSet (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observations : Set (SourceNoncarbonObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceNoncarbonObservation.BoundedIn n observation) :
    ofNativeObservationSet e policy (toNativeObservationSet e policy observations bounded) =
      observations := by
  ext recovered
  constructor
  · rintro ⟨presented, ⟨observation, member, encodeEq⟩, decodeEq⟩
    rw [← encodeEq] at decodeEq
    rw [ofNativeObservation_toNativeObservation] at decodeEq
    rw [← decodeEq]
    exact member
  · intro member
    exact ⟨toNativeObservation e policy recovered (bounded recovered member),
      ⟨recovered, member, rfl⟩,
      ofNativeObservation_toNativeObservation e policy recovered (bounded recovered member)⟩

/-- **Exact set inverse on the native side.**  Encoding the preimage of a native set returns
exactly that set. -/
theorem toNativeObservationSet_ofNativeObservationSet (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observations : Set (NativeNoncarbonObservation V policy.Descriptor)) :
    toNativeObservationSet e policy (ofNativeObservationSet e policy observations)
        (ofNativeObservationSetBounded e policy observations) = observations := by
  ext presented
  constructor
  · rintro ⟨recovered, ⟨presented₀, presentedMember, decodeEq⟩, encodeEq⟩
    have obsEq : ofNativeObservation e policy presented = recovered := by
      have := congrArg (ofNativeObservation e policy) encodeEq.symm
      rwa [ofNativeObservation_toNativeObservation] at this
    have decodeEq' : ofNativeObservation e policy presented₀ =
        ofNativeObservation e policy presented := by
      rw [decodeEq, ← obsEq]
    have key : toNativeObservation e policy (ofNativeObservation e policy presented₀)
        (ofNativeObservationBounded e policy presented₀) = presented := by
      calc
        toNativeObservation e policy (ofNativeObservation e policy presented₀)
            (ofNativeObservationBounded e policy presented₀) =
          toNativeObservation e policy (ofNativeObservation e policy presented)
            (ofNativeObservationBounded e policy presented) :=
          toNativeObservation_congr e policy decodeEq' _ _
        _ = presented := toNativeObservation_ofNativeObservation e policy presented
    have presentedEq : presented = presented₀ := by
      rw [← key, toNativeObservation_ofNativeObservation]
    simpa [presentedEq] using presentedMember
  · intro member
    exact ⟨ofNativeObservation e policy presented,
      ⟨presented, member, rfl⟩,
      toNativeObservation_ofNativeObservation e policy presented⟩

/-- **Correlated validity for a set.**  A native observation belongs to the image of a set exactly
when its decoded record is one of the source observations; consequently its `ValidFor` at the same
source and policy is exactly the validity of that source observation.  No claim of permutation
invariance is made. -/
theorem validFor_mem_toNativeObservationSet_iff (e : V ≃ Fin n)
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observations : Set (SourceNoncarbonObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceNoncarbonObservation.BoundedIn n observation)
    (presented : NativeNoncarbonObservation V policy.Descriptor)
    (member : presented ∈ toNativeObservationSet e policy observations bounded) :
    SourceNoncarbonObservation.ValidFor policy source
        (ofNativeObservation e policy presented) ↔
      ∃ observation, ∃ observationMember : observation ∈ observations,
        toNativeObservation e policy observation (bounded observation observationMember) =
          presented ∧ SourceNoncarbonObservation.ValidFor policy source observation := by
  constructor
  · intro valid
    rcases member with ⟨observation, observationMember, encodeEq⟩
    refine ⟨observation, observationMember, encodeEq, ?_⟩
    rw [← encodeEq] at valid
    rwa [ofNativeObservation_toNativeObservation] at valid
  · rintro ⟨observation, observationMember, encodeEq, valid⟩
    rw [← encodeEq]
    rwa [ofNativeObservation_toNativeObservation]

end SetCodec

/-! ## Source binding and the composable satellite

The binding is the accepted physical-frame source binding: the shared graph, coordinate channel and
drawing channel encode to exactly the stored authoritative input.  The satellite stores that
independent finite source and the native observations only; it never stores the original source
observations or the original `AuthoritativeChemicalInput`. -/

variable {V : Type*} {policy : P93NoncarbonTetrahedralAuthorityPolicy}

/-- The accepted source binding from `OrganicStereoP93PhysicalFrameIngress`. -/
abbrev NoncarbonSourceBinding (V : Type*) [DecidableEq V] [Fintype V] :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V

/-- Bounds of a tagged observation derived from its actual validity and the exact source binding.
The atom count of the binding is the cardinality of the vertex type by exact graph equality. -/
theorem SourceNoncarbonObservation.boundedIn_of_validFor_binding
    [DecidableEq V] [Fintype V]
    (binding : NoncarbonSourceBinding V)
    (observation : SourceNoncarbonObservation policy)
    (valid : SourceNoncarbonObservation.ValidFor policy binding.source observation) :
    SourceNoncarbonObservation.BoundedIn (Fintype.card V) observation := by
  have bounded := SourceNoncarbonObservation.boundedIn_of_validFor policy binding.source
    observation valid
  rwa [binding.atomCount_eq] at bounded

/-- A raw noncarbon tetrahedral observation source: the exact source binding plus an ordered list
of raw `Nat`-indexed carrier observations, each valid at the bound source. -/
structure RawNoncarbonObservationSource (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  binding : NoncarbonSourceBinding V
  observations : List (SourceNoncarbonObservation policy)
  valid : ∀ observation ∈ observations,
    SourceNoncarbonObservation.ValidFor policy binding.source observation

/-- The composable native satellite.  It carries the same graph/spatial/diagram source context as
the molecule codec and the ordered list of native observations.  No original observation and no
original `AuthoritativeChemicalInput` is stored here. -/
structure NoncarbonObservationSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (NativeNoncarbonObservation V policy.Descriptor)

namespace NoncarbonObservationSatellite

variable [DecidableEq V] [Fintype V]

/-- The shared finite source, with the observations intentionally excluded. -/
def toFiniteSource (satellite : NoncarbonObservationSatellite V policy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

end NoncarbonObservationSatellite

/-- Adapt a raw source into the satellite: keep the exact shared finite source and encode every
observation, deriving the atom bounds from its actual `ValidFor`. -/
def adapt [DecidableEq V] [Fintype V]
    (raw : RawNoncarbonObservationSource V policy) :
    NoncarbonObservationSatellite V policy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := raw.observations.attach.map fun observation =>
    toNativeObservation raw.binding.enumeration policy observation.1
      (SourceNoncarbonObservation.boundedIn_of_validFor_binding raw.binding observation.1
        (raw.valid observation.1 observation.2))

@[simp] theorem adapt_graph [DecidableEq V] [Fintype V]
    (raw : RawNoncarbonObservationSource V policy) :
    (adapt raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adapt_spatial? [DecidableEq V] [Fintype V]
    (raw : RawNoncarbonObservationSource V policy) :
    (adapt raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adapt_diagram? [DecidableEq V] [Fintype V]
    (raw : RawNoncarbonObservationSource V policy) :
    (adapt raw).diagram? = raw.binding.shared.diagram? := rfl

/-- The exact recovered source record: the recovered authoritative input and the decoded ordered
observation list. -/
@[ext] structure RecoveredNoncarbonObservationSource
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : List (SourceNoncarbonObservation policy)

/-- Decode a satellite into the recovered source record.  The authoritative input is the exact
encode of the shared finite source; the observations are decoded with the same enumeration. -/
def suppliedSource [DecidableEq V] [Fintype V]
    (e : V ≃ Fin (Fintype.card V))
    (satellite : NoncarbonObservationSatellite V policy) :
    RecoveredNoncarbonObservationSource policy where
  source := satellite.toFiniteSource.encode e
  observations := ofNativeObservations e policy satellite.observations

/-- The decoded observation list of the adapted satellite is exactly the original list. -/
theorem decodedObservations_adapt [DecidableEq V] [Fintype V]
    (raw : RawNoncarbonObservationSource V policy) :
    ofNativeObservations raw.binding.enumeration policy (adapt raw).observations =
      raw.observations := by
  show ofNativeObservations raw.binding.enumeration policy
      (raw.observations.attach.map fun observation =>
        toNativeObservation raw.binding.enumeration policy observation.1
          (SourceNoncarbonObservation.boundedIn_of_validFor_binding raw.binding observation.1
            (raw.valid observation.1 observation.2))) = raw.observations
  exact ofNativeObservations_toNativeObservations raw.binding.enumeration policy
    raw.observations (fun observation member =>
      SourceNoncarbonObservation.boundedIn_of_validFor_binding raw.binding observation
        (raw.valid observation member))

/-- The shared finite source of the adapted satellite encodes to exactly the bound source. -/
theorem adapt_source_eq [DecidableEq V] [Fintype V]
    (raw : RawNoncarbonObservationSource V policy) :
    (adapt raw).toFiniteSource.encode raw.binding.enumeration = raw.binding.source :=
  raw.binding.encode_shared

/-- The atom count of the adapted source is the cardinality of the vertex type. -/
theorem adapt_atomCount_eq [DecidableEq V] [Fintype V]
    (raw : RawNoncarbonObservationSource V policy) :
    ((adapt raw).toFiniteSource.encode raw.binding.enumeration).molecule.atomCount =
      Fintype.card V := by
  rw [adapt_source_eq]
  exact raw.binding.atomCount_eq

/-- **Exact full source recovery.**  Adapting a raw source and decoding it returns the exact
authoritative input (through the binding's actual source equality) and the exact ordered list of
pre-existing noncarbon tetrahedral observation records. -/
theorem suppliedSource_adapt [DecidableEq V] [Fintype V]
    (raw : RawNoncarbonObservationSource V policy) :
    suppliedSource raw.binding.enumeration (adapt raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredNoncarbonObservationSource.ext
  · simpa using raw.binding.encode_shared
  · exact decodedObservations_adapt raw

/-- Every observation of the recovered list is valid at the same recovered source and policy. -/
theorem suppliedSource_adapt_validFor [DecidableEq V] [Fintype V]
    (raw : RawNoncarbonObservationSource V policy)
    (observation : SourceNoncarbonObservation policy)
    (member : observation ∈ (suppliedSource raw.binding.enumeration (adapt raw)).observations) :
    SourceNoncarbonObservation.ValidFor policy raw.binding.source observation := by
  have listEq : (suppliedSource raw.binding.enumeration (adapt raw)).observations =
      raw.observations := by
    simpa using congrArg (RecoveredNoncarbonObservationSource.observations)
      (suppliedSource_adapt raw)
  exact raw.valid observation (listEq ▸ member)

/-! ## The correlated set-valued satellite

The same source binding and the same shared physical source, but the payload is now an arbitrary
correlated set of observations rather than an ordered list.  The exact set inverse above is what
makes the recovered set equal to the original one. -/

/-- A raw set-valued noncarbon observation source. -/
structure RawNoncarbonObservationSetSource (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  binding : NoncarbonSourceBinding V
  observations : Set (SourceNoncarbonObservation policy)
  valid : ∀ observation ∈ observations,
    SourceNoncarbonObservation.ValidFor policy binding.source observation

/-- The set-valued composable native satellite. -/
structure NoncarbonObservationSetSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : Set (NativeNoncarbonObservation V policy.Descriptor)

namespace NoncarbonObservationSetSatellite

variable [DecidableEq V] [Fintype V]

/-- The shared finite source, with the observations intentionally excluded. -/
def toFiniteSource (satellite : NoncarbonObservationSetSatellite V policy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

end NoncarbonObservationSetSatellite

/-- Adapt a raw set-valued source into the set-valued satellite. -/
def adaptSet [DecidableEq V] [Fintype V]
    (raw : RawNoncarbonObservationSetSource V policy) :
    NoncarbonObservationSetSatellite V policy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := toNativeObservationSet raw.binding.enumeration policy raw.observations
    (fun observation member =>
      SourceNoncarbonObservation.boundedIn_of_validFor_binding raw.binding observation
        (raw.valid observation member))

/-- The exact recovered set-valued source record. -/
@[ext] structure RecoveredNoncarbonObservationSetSource
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : Set (SourceNoncarbonObservation policy)

/-- Decode a set-valued satellite into the recovered source record. -/
def suppliedSetSource [DecidableEq V] [Fintype V]
    (e : V ≃ Fin (Fintype.card V))
    (satellite : NoncarbonObservationSetSatellite V policy) :
    RecoveredNoncarbonObservationSetSource policy where
  source := satellite.toFiniteSource.encode e
  observations := ofNativeObservationSet e policy satellite.observations

/-- **Exact set-valued source recovery.**  Adapting a raw set-valued source and decoding it returns
the exact authoritative input and the exact correlated set of pre-existing records. -/
theorem suppliedSetSource_adaptSet [DecidableEq V] [Fintype V]
    (raw : RawNoncarbonObservationSetSource V policy) :
    suppliedSetSource raw.binding.enumeration (adaptSet raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredNoncarbonObservationSetSource.ext
  · simpa using raw.binding.encode_shared
  · change ofNativeObservationSet raw.binding.enumeration policy
        (toNativeObservationSet raw.binding.enumeration policy raw.observations
          (fun observation member =>
            SourceNoncarbonObservation.boundedIn_of_validFor_binding raw.binding observation
              (raw.valid observation member))) = raw.observations
    exact ofNativeObservationSet_toNativeObservationSet raw.binding.enumeration policy
      raw.observations (fun observation member =>
        SourceNoncarbonObservation.boundedIn_of_validFor_binding raw.binding observation
          (raw.valid observation member))

/-- Every observation of the recovered set is valid at the same recovered source and policy. -/
theorem suppliedSetSource_adaptSet_validFor [DecidableEq V] [Fintype V]
    (raw : RawNoncarbonObservationSetSource V policy)
    (observation : SourceNoncarbonObservation policy)
    (member :
      observation ∈ (suppliedSetSource raw.binding.enumeration (adaptSet raw)).observations) :
    SourceNoncarbonObservation.ValidFor policy raw.binding.source observation := by
  have setEq : (suppliedSetSource raw.binding.enumeration (adaptSet raw)).observations =
      raw.observations := by
    simpa using congrArg (RecoveredNoncarbonObservationSetSource.observations)
      (suppliedSetSource_adaptSet raw)
  exact raw.valid observation (setEq ▸ member)

/-! ## The concrete certified-source adapter -/

/-- The concrete binding of a certified authoritative input, reusing the existing molecule codec's
certified binding. -/
def certifiedBinding (certified : CertifiedAuthoritativeChemicalInput) :
    NoncarbonSourceBinding (Fin certified.input.molecule.atomCount) :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding.ofCertified certified

/-- Adapt a certified source together with an ordered list of valid carrier observations. -/
def adaptCertified (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceNoncarbonObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceNoncarbonObservation.ValidFor policy certified.input observation) :
    NoncarbonObservationSatellite (Fin certified.input.molecule.atomCount) policy :=
  adapt { binding := certifiedBinding certified
          observations := observations
          valid := valid }

/-- **Concrete exact recovery from a certified source.** -/
theorem suppliedSource_adaptCertified
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceNoncarbonObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceNoncarbonObservation.ValidFor policy certified.input observation) :
    suppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertified certified observations valid) =
      { source := certified.input, observations := observations } :=
  suppliedSource_adapt
    { binding := certifiedBinding certified
      observations := observations
      valid := valid }

end OrganicStereoNoncarbonTetrahedralIngress

end TetraStereo.OneCenter
