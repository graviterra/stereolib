/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily
import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace TetraStereo.OneCenter
namespace OrganicStereoObservationCommonIndexBridge

open OrganicStereoOrderedObservationFamily
open BlueBookP94
open BlueBookP94.CoordinateTwistInOut
open BlueBookP94.CoordinateTorsion

/-!
# One source-indexed observation index derived from the common graph encoding

The ordered observation family of `OrganicStereoOrderedObservationFamily` is parameterized by a
certified source `source` and an independent finite atom label type `V`.  Its source adapters take
an *explicit* equivalence `SourceAtomIndex source ≃ V`.  The mixed-source assembly, however, ties a
supplied source to a common finite graph `graph : FiniteAtomInteractionHypergraph V` and one
enumeration `enumeration : V ≃ Fin (Fintype.card V)` by the actual equality

  `source.input.molecule = graph.encode enumeration`.

This module derives the missing common index from that equality alone.  It does **not** accept a
supplied equivalence as a hypothesis: the source atom count is proved equal to `Fintype.card V`
from the graph equality (`source_atomCount_eq_encoded`), and the bijection
`commonIndexEquiv : SourceAtomIndex source ≃ V` is constructed from that count equality and the
same enumeration (`finCongr … |>.trans enumeration.symm`).

On top of that derived bijection the module exposes:

* `commonPointAt`, the source-coordinate resolver mirroring
  `EncodedCoordinateObservation.pointAt`, with exact source lookup
  (`commonPointAt_eq_source_lookup`), absence (`commonPointAt_eq_none_iff`), presence
  (`commonPointAt_eq_some_iff`, `commonPointAt_eq_getElem`) and the key bridge statement
  `commonPointAt_commonIndex`: resolving at the common label of a source index returns exactly the
  source-indexed position at that index;
* `commonVirtualPointAt` and the ledger-level `commonVirtualPointLedgerLookup`, with exact recovery
  of `VirtualTorsionPointLedger.lookup` for both primitive virtual participant kinds
  (`commonVirtualPointAt_ofSource`, `commonVirtualPointAt_ofSource_isSome`,
  `commonVirtualPointAt_ofSource_eq_none_iff`) and the first-match duplicate semantics of `lookup`
  (`commonVirtualPointLedgerLookup_cons_self`, `commonVirtualPointLedgerLookup_cons_of_ne`,
  `commonVirtualPointLedgerLookup_eq_none_iff`);
* bridgehead and directed-participant lookup (`commonBridgeheadAt`,
  `commonDirectedParticipantAt`, `commonParticipantOwnerIndex`), each proved exact on source
  adapters;
* the same derived map for the finite conformer collection
  (`commonFiniteConformerCollection`) and a coherence theorem
  `common_conformer_coordinate_index_agree` stating that conformer atom indexing and raw P-94
  coordinate payload references both read a source index through the *same* derived bijection;
* relabelling compatibility for `r : V ≃ W`, using the correspondingly transported enumeration
  `relabelEnumeration r enumeration` and the existing `relabelGraph r graph`.  The transported
  graph encoding is proved equal to the original encoding (`relabelGraph_encode`), so the source
  equality transports, and the derived bijection transports pointwise
  (`commonIndexEquiv_relabel_apply`).  Every compatibility theorem is stated at that transported
  enumeration; this module never quantifies over an enumeration unrelated to the relabelling.

## What is deliberately not changed

The retained `SpatialConfiguration` is the literal source-indexed list; no length or atom-count
equality is imposed and every resolver is `Option`-valued, so a missing position stays `none`
(`commonPointAt_eq_none_iff`).  The opaque `State` and `Framework` carriers are copied verbatim by
the existing relabelling functions; the projection lemmas in the last section record that they are
not internally relabelled.  No chemical interpretation, descriptor, population or completeness
claim is produced.
-/

/-! ## The source atom count derived from the actual graph equality -/

variable {V W : Type*} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]
variable {State Framework : Type*}
variable {source : CertifiedAuthoritativeChemicalInput}

/-- The certified source's atom count is the cardinality of the common atom label type.  This is a
theorem derived from the actual equality `source.input.molecule = graph.encode enumeration` and the
existing `FiniteAtomInteractionHypergraph.encode_atomCount`; it is not an extra hypothesis. -/
theorem source_atomCount_eq_encoded (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration) :
    source.input.molecule.atomCount = Fintype.card V := by
  rw [h]
  exact graph.encode_atomCount enumeration

/-- The common index bijection derived from the certified source and the common graph encoding.
`SourceAtomIndex source` is definitionally `Fin source.input.molecule.atomCount`; the source count
equality above casts it to `Fin (Fintype.card V)` and the supplied enumeration identifies that with
`V`.  No equivalence is supplied by the caller. -/
def commonIndexEquiv (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration) :
    SourceAtomIndex source ≃ V :=
  (finCongr (source_atomCount_eq_encoded graph enumeration source h)).trans enumeration.symm

/-- The inverse common index at a native label `v` is the source index whose number is exactly the
enumeration number of `v`.  In particular the resolver below reads the source position list at
`(enumeration v).val`. -/
@[simp] theorem commonIndexEquiv_symm_apply_val (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration) (v : V) :
    ((commonIndexEquiv graph enumeration source h).symm v).val = (enumeration v).val := by
  simp [commonIndexEquiv]

/-- Applying the enumeration to the common index of a source index returns the cast source index
number.  This records that the derived bijection and the graph encoding use the same enumeration. -/
@[simp] theorem enumeration_commonIndexEquiv (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration) (index : SourceAtomIndex source) :
    enumeration (commonIndexEquiv graph enumeration source h index) =
      finCongr (source_atomCount_eq_encoded graph enumeration source h) index := by
  simp [commonIndexEquiv]

/-- The common index is a two-sided inverse of the source-to-label map. -/
@[simp] theorem commonIndexEquiv_symm_apply_self (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration) (v : V) :
    commonIndexEquiv graph enumeration source h
        ((commonIndexEquiv graph enumeration source h).symm v) = v :=
  Equiv.apply_symm_apply _ v

/-! ## Relabelling the enumeration and the common graph

The only enumeration admitted on a relabelled type `W` is the image of the supplied enumeration
under the same bijection: `relabelEnumeration r enumeration`.  The graph is transported by the
existing `relabelGraph`, and the two transports are proved to encode the same molecule.
-/

/-- The enumeration transported along `r : V ≃ W`.  It is the composite of `r.symm`, the supplied
enumeration, and the cardinality identification `Fintype.card V = Fintype.card W`. -/
def relabelEnumeration (r : V ≃ W) (enumeration : V ≃ Fin (Fintype.card V)) :
    W ≃ Fin (Fintype.card W) where
  toFun w := finCongr (Fintype.card_congr r) (enumeration (r.symm w))
  invFun index := r (enumeration.symm ((finCongr (Fintype.card_congr r)).symm index))
  left_inv w := by simp
  right_inv index := by simp

/-- At a transported label the transported enumeration is the cardinality cast of the original
enumeration. -/
theorem relabelEnumeration_apply (r : V ≃ W) (enumeration : V ≃ Fin (Fintype.card V))
    (w : W) :
    relabelEnumeration r enumeration w =
      finCongr (Fintype.card_congr r) (enumeration (r.symm w)) := rfl

/-- The inverse of the transported enumeration at a transported index. -/
theorem relabelEnumeration_symm_apply (r : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V)) (index : Fin (Fintype.card W)) :
    (relabelEnumeration r enumeration).symm index =
      r (enumeration.symm ((finCongr (Fintype.card_congr r)).symm index)) := rfl

/-- The transported enumeration keeps the original enumeration number at every transported
label. -/
@[simp] theorem relabelEnumeration_apply_val (r : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V)) (w : W) :
    (relabelEnumeration r enumeration w).val = (enumeration (r.symm w)).val := by
  rw [relabelEnumeration_apply, finCongr_apply_coe]

/-- Relabelling a common graph and then encoding at the transported enumeration is exactly the
original encoding.  Only atom labels move; atom data, interaction order and interaction kinds are
copied. -/
theorem relabelGraph_encode (r : V ≃ W) (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (relabelGraph r graph).encode (relabelEnumeration r enumeration) =
      graph.encode enumeration := by
  change SemanticMolecule.mk
      (List.ofFn fun i : Fin (Fintype.card W) =>
        graph.atomData (r.symm ((relabelEnumeration r enumeration).symm i)))
      ((graph.interactions.map (relabelInteractionEdge r)).map
        (FiniteAtomInteractionHypergraph.encodeInteraction (relabelEnumeration r enumeration))) =
    SemanticMolecule.mk
      (List.ofFn fun i : Fin (Fintype.card V) => graph.atomData (enumeration.symm i))
      (graph.interactions.map (FiniteAtomInteractionHypergraph.encodeInteraction enumeration))
  have atoms : List.ofFn (fun i : Fin (Fintype.card W) =>
        graph.atomData (r.symm ((relabelEnumeration r enumeration).symm i))) =
      List.ofFn (fun i : Fin (Fintype.card V) => graph.atomData (enumeration.symm i)) := by
    simp only [relabelEnumeration_symm_apply, Equiv.symm_apply_apply]
    exact (List.ofFn_congr (Fintype.card_congr r)
      (fun i => graph.atomData (enumeration.symm i))).symm
  have interactions :
      (graph.interactions.map (relabelInteractionEdge r)).map
          (FiniteAtomInteractionHypergraph.encodeInteraction
            (relabelEnumeration r enumeration)) =
        graph.interactions.map (FiniteAtomInteractionHypergraph.encodeInteraction enumeration) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro edge _
    obtain ⟨participants, kind⟩ := edge
    simp [relabelInteractionEdge, FiniteAtomInteractionHypergraph.encodeInteraction,
      List.map_map, Function.comp_def, relabelEnumeration_apply, finCongr_apply_coe]
  rw [atoms, interactions]

/-- The source equality transported along a relabelling, with the correspondingly transported
graph and enumeration. -/
def relabelMoleculeEq (r : V ≃ W) (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration) :
    source.input.molecule =
      (relabelGraph r graph).encode (relabelEnumeration r enumeration) :=
  h.trans (relabelGraph_encode r graph enumeration).symm

/-- The derived common index transports pointwise along `r`: the index derived from the
relabelled graph and transported enumeration is the `r`-image of the original derived index. -/
theorem commonIndexEquiv_relabel_apply (r : V ≃ W) (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration) (index : SourceAtomIndex source) :
    commonIndexEquiv (relabelGraph r graph) (relabelEnumeration r enumeration) source
        (relabelMoleculeEq r graph enumeration source h) index =
      r (commonIndexEquiv graph enumeration source h index) := by
  unfold commonIndexEquiv
  simp only [Equiv.trans_apply, relabelEnumeration_symm_apply]
  have idxEq : (finCongr (Fintype.card_congr r)).symm
        (finCongr (source_atomCount_eq_encoded (relabelGraph r graph)
          (relabelEnumeration r enumeration) source
          (relabelMoleculeEq r graph enumeration source h)) index) =
      finCongr (source_atomCount_eq_encoded graph enumeration source h) index := by
    apply Fin.ext
    simp [finCongr_symm_apply_coe, finCongr_apply_coe]
  rw [idxEq]

/-! ## The common-index coordinate resolver -/

/-- Evaluate a retained source-indexed coordinate observation at a native atom label through the
derived common index.  The observation's `SpatialConfiguration` is read literally; only the label is
decoded.  The result is `Option`-valued, so arbitrary source list lengths remain admitted. -/
def commonPointAt (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V) (atom : V) :
    Option CartesianPoint3 :=
  EncodedCoordinateObservation.pointAt (commonIndexEquiv graph enumeration source h) observation atom

/-- Definitional reading of the common resolver through the existing
`EncodedCoordinateObservation.pointAt_eq_source_lookup`: it is the source position list lookup at
the enumeration number of the native label. -/
@[simp] theorem commonPointAt_eq_source_lookup (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V) (atom : V) :
    commonPointAt graph enumeration source h observation atom =
      observation.spatial.positions[(enumeration atom).val]? := by
  show EncodedCoordinateObservation.pointAt (commonIndexEquiv graph enumeration source h)
    observation atom = _
  rw [EncodedCoordinateObservation.pointAt_eq_source_lookup,
    commonIndexEquiv_symm_apply_val]

/-- A missing source position stays `none`: no coordinate is fabricated and no global list-length
equality is assumed. -/
theorem commonPointAt_eq_none_iff (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V) (atom : V) :
    commonPointAt graph enumeration source h observation atom = none ↔
      observation.spatial.positions.length ≤ (enumeration atom).val := by
  rw [commonPointAt_eq_source_lookup, List.getElem?_eq_none_iff]

/-- A present source position is returned exactly, with no recomputation. -/
theorem commonPointAt_eq_some_iff (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V) (atom : V)
    (point : CartesianPoint3) :
    commonPointAt graph enumeration source h observation atom = some point ↔
      ∃ bound : (enumeration atom).val < observation.spatial.positions.length,
        observation.spatial.positions[(enumeration atom).val] = point := by
  rw [commonPointAt_eq_source_lookup, List.getElem?_eq_some_iff]

/-- Exact positional reading when the source list has a position at the decoded atom. -/
theorem commonPointAt_eq_getElem (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V) (atom : V)
    (bound : (enumeration atom).val < observation.spatial.positions.length) :
    commonPointAt graph enumeration source h observation atom =
      some observation.spatial.positions[(enumeration atom).val] := by
  rw [commonPointAt_eq_source_lookup]
  exact List.getElem?_eq_getElem bound

/-- **The common-index bridge.**  Resolving at the common label of a source index returns exactly
the source position at that index.  This is the statement that makes the derived bijection the
single interpretation map for coordinate payload references. -/
theorem commonPointAt_commonIndex (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V) (index : SourceAtomIndex source) :
    commonPointAt graph enumeration source h observation
        (commonIndexEquiv graph enumeration source h index) =
      observation.spatial.positions[index.val]? := by
  rw [commonPointAt_eq_source_lookup]
  simp [enumeration_commonIndexEquiv]

/-! ## Source adapters and exact coordinate recovery -/

/-- Adapt one actual `CoordinateInOutObservation` at the derived common index.  Every atom
reference in the payload is transported by the same derived bijection. -/
def commonCoordinateObservation (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount) :
    EncodedCoordinateObservation Framework V :=
  EncodedCoordinateObservation.ofSource (commonIndexEquiv graph enumeration source h)
    observation bridgeheadBound participantBound virtualBound

/-- **Native-label recovery.**  The source-adapted coordinate observation evaluated at an
arbitrary native label returns exactly the original source-indexed positional lookup at that
label's enumeration number.  The retained list is not reindexed or normalized. -/
@[simp] theorem commonCoordinateObservation_pointAt_nativeLabel
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (v : V) :
    commonPointAt graph enumeration source h
        (commonCoordinateObservation graph enumeration source h observation
          bridgeheadBound participantBound virtualBound) v =
      observation.spatial.positions[(enumeration v).val]? := by
  rw [commonPointAt_eq_source_lookup]
  rfl

/-- Source-index form of native-label recovery, reusing the existing
`EncodedCoordinateObservation.pointAt_ofSource`. -/
theorem commonCoordinateObservation_pointAt_sourceIndex
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (index : SourceAtomIndex source) :
    commonPointAt graph enumeration source h
        (commonCoordinateObservation graph enumeration source h observation
          bridgeheadBound participantBound virtualBound)
        (commonIndexEquiv graph enumeration source h index) =
      observation.spatial.positions[index.val]? := by
  show EncodedCoordinateObservation.pointAt (commonIndexEquiv graph enumeration source h)
      (EncodedCoordinateObservation.ofSource (commonIndexEquiv graph enumeration source h)
        observation bridgeheadBound participantBound virtualBound)
      (commonIndexEquiv graph enumeration source h index) = _
  exact EncodedCoordinateObservation.pointAt_ofSource
    (commonIndexEquiv graph enumeration source h) observation bridgeheadBound
    participantBound virtualBound index

/-- Bounded source-atom form of native-label recovery, reusing
`EncodedCoordinateObservation.pointAt_ofSource_encodeIndex`. -/
theorem commonCoordinateObservation_pointAt_sourceAtom
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (atom : ℕ) (bound : atom < source.input.molecule.atomCount) :
    commonPointAt graph enumeration source h
        (commonCoordinateObservation graph enumeration source h observation
          bridgeheadBound participantBound virtualBound)
        (encodeIndex (commonIndexEquiv graph enumeration source h) atom bound) =
      observation.spatial.positions[atom]? := by
  show EncodedCoordinateObservation.pointAt (commonIndexEquiv graph enumeration source h)
      (EncodedCoordinateObservation.ofSource (commonIndexEquiv graph enumeration source h)
        observation bridgeheadBound participantBound virtualBound)
      (encodeIndex (commonIndexEquiv graph enumeration source h) atom bound) = _
  exact EncodedCoordinateObservation.pointAt_ofSource_encodeIndex
    (commonIndexEquiv graph enumeration source h) observation bridgeheadBound
    participantBound virtualBound atom bound

/-! ## Bridgehead and directed-participant lookup -/

/-- Resolve the coordinate at the encoded bridgehead label. -/
def commonBridgeheadAt (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V) : Option CartesianPoint3 :=
  commonPointAt graph enumeration source h observation observation.bridgehead

/-- Exact bridgehead recovery on a source-adapted observation: the resolver at the encoded
bridgehead label returns the original source bridgehead position. -/
@[simp] theorem commonBridgeheadAt_ofSource (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount) :
    commonBridgeheadAt graph enumeration source h
        (commonCoordinateObservation graph enumeration source h observation
          bridgeheadBound participantBound virtualBound) =
      observation.spatial.positions[observation.bridgehead]? := by
  show EncodedCoordinateObservation.pointAt (commonIndexEquiv graph enumeration source h)
      (EncodedCoordinateObservation.ofSource (commonIndexEquiv graph enumeration source h)
        observation bridgeheadBound participantBound virtualBound)
      (encodeIndex (commonIndexEquiv graph enumeration source h) observation.bridgehead
        bridgeheadBound) = _
  exact EncodedCoordinateObservation.pointAt_bridgehead_ofSource
    (commonIndexEquiv graph enumeration source h) observation bridgeheadBound
    participantBound virtualBound

/-- Resolve the coordinate at the atom owner of an encoded directed participant.  `participantOwner`
is the existing owner map: the ordinary atom, the lone-pair centre, or the duplicate's original
atom. -/
def commonDirectedParticipantAt (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V) : Option CartesianPoint3 :=
  commonPointAt graph enumeration source h observation
    (participantOwner observation.directedParticipant)

/-- Exact directed-participant owner recovery on a source-adapted observation, for all three
primitive participant kinds. -/
@[simp] theorem commonDirectedParticipantAt_ofSource (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount) :
    commonDirectedParticipantAt graph enumeration source h
        (commonCoordinateObservation graph enumeration source h observation
          bridgeheadBound participantBound virtualBound) =
      observation.spatial.positions[participantOwner observation.directedParticipant]? := by
  show EncodedCoordinateObservation.pointAt (commonIndexEquiv graph enumeration source h)
      (EncodedCoordinateObservation.ofSource (commonIndexEquiv graph enumeration source h)
        observation bridgeheadBound participantBound virtualBound)
      (participantOwner (encodeParticipant (commonIndexEquiv graph enumeration source h)
        observation.directedParticipant participantBound)) = _
  exact EncodedCoordinateObservation.pointAt_directedParticipant_ofSource
    (commonIndexEquiv graph enumeration source h) observation bridgeheadBound
    participantBound virtualBound

/-- The source atom index that a native encoded participant owner denotes. -/
def commonParticipantOwnerIndex (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (participant : TorsionParticipant V) : SourceAtomIndex source :=
  (commonIndexEquiv graph enumeration source h).symm (participantOwner participant)

/-- The decoded owner index reads the source position list at the enumeration number of the
participant's owner label. -/
@[simp] theorem commonParticipantOwnerIndex_val (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (participant : TorsionParticipant V) :
    (commonParticipantOwnerIndex graph enumeration source h participant).val =
      (enumeration (participantOwner participant)).val :=
  commonIndexEquiv_symm_apply_val graph enumeration source h (participantOwner participant)

/-- Encode a bounded source torsion participant at the derived common index. -/
def commonEncodedParticipant (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (participant : TorsionParticipant ℕ)
    (bound : P94ConformationUnit.ParticipantBounded participant
      source.input.molecule.atomCount) : TorsionParticipant V :=
  encodeParticipant (commonIndexEquiv graph enumeration source h) participant bound

/-- The encoded participant's owner is the common label of the source participant's owner. -/
@[simp] theorem commonEncodedParticipant_owner (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (participant : TorsionParticipant ℕ)
    (bound : P94ConformationUnit.ParticipantBounded participant
      source.input.molecule.atomCount) :
    participantOwner (commonEncodedParticipant graph enumeration source h participant bound) =
      commonIndexEquiv graph enumeration source h
        ⟨participantOwner participant, participantOwner_bound bound⟩ :=
  participantOwner_encodeParticipant (commonIndexEquiv graph enumeration source h)
    participant bound

/-! ## Virtual points: lookup, duplicates and exact source recovery -/

/-- Look up one encoded virtual point in an explicit encoded ledger.  This is the encoded mirror of
`VirtualTorsionPointLedger.lookup`; it returns the first matching entry and `none` when no entry
matches. -/
def commonVirtualPointLedgerLookup (ledger : List (EncodedVirtualTorsionPoint V))
    (participant : EncodedVirtualTorsionParticipant V) : Option CartesianPoint3 :=
  EncodedVirtualTorsionPoint.lookup ledger participant

/-- First-match semantics: a head entry naming the queried participant is returned immediately. -/
@[simp] theorem commonVirtualPointLedgerLookup_cons_self
    (entry : EncodedVirtualTorsionPoint V) (rest : List (EncodedVirtualTorsionPoint V)) :
    commonVirtualPointLedgerLookup (entry :: rest) entry.participant = some entry.point := by
  simp [commonVirtualPointLedgerLookup, EncodedVirtualTorsionPoint.lookup]

/-- A non-matching head entry is skipped, so later entries (including later duplicates of a
different participant) are still scanned in order. -/
@[simp] theorem commonVirtualPointLedgerLookup_cons_of_ne
    (entry : EncodedVirtualTorsionPoint V) (rest : List (EncodedVirtualTorsionPoint V))
    (participant : EncodedVirtualTorsionParticipant V)
    (ne : entry.participant ≠ participant) :
    commonVirtualPointLedgerLookup (entry :: rest) participant =
      commonVirtualPointLedgerLookup rest participant := by
  simp [commonVirtualPointLedgerLookup, EncodedVirtualTorsionPoint.lookup, ne]

/-- A participant that occurs nowhere in the ledger stays missing (`none`); no point is
fabricated. -/
theorem commonVirtualPointLedgerLookup_eq_none_iff
    (ledger : List (EncodedVirtualTorsionPoint V))
    (participant : EncodedVirtualTorsionParticipant V) :
    commonVirtualPointLedgerLookup ledger participant = none ↔
      ∀ entry ∈ ledger, entry.participant ≠ participant := by
  induction ledger with
  | nil => simp [commonVirtualPointLedgerLookup, EncodedVirtualTorsionPoint.lookup]
  | cons head tail ih =>
      by_cases same : head.participant = participant
      · subst participant
        simp [commonVirtualPointLedgerLookup, EncodedVirtualTorsionPoint.lookup]
      · rw [commonVirtualPointLedgerLookup_cons_of_ne head tail participant same]
        rw [ih]
        simp [same]

/-- Evaluate the retained encoded virtual-point ledger at an encoded participant through the common
context.  The ledger is the literal source ledger with only participant labels transported. -/
def commonVirtualPointAt (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V)
    (participant : EncodedVirtualTorsionParticipant V) : Option CartesianPoint3 :=
  EncodedCoordinateObservation.virtualPointAt observation participant

/-- The common virtual-point resolver is exactly the first-match ledger lookup. -/
theorem commonVirtualPointAt_eq_ledger (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V)
    (participant : EncodedVirtualTorsionParticipant V) :
    commonVirtualPointAt graph enumeration source h observation participant =
      commonVirtualPointLedgerLookup observation.virtualPoints participant := rfl

/-- Encode a bounded primitive virtual participant at the derived common index. -/
def commonVirtualParticipant (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (participant : VirtualTorsionParticipant)
    (bound : VirtualParticipantBounded participant source.input.molecule.atomCount) :
    EncodedVirtualTorsionParticipant V :=
  encodeVirtualParticipant (commonIndexEquiv graph enumeration source h) participant bound

/-- A lone-pair phantom's common label is the common index of its source centre. -/
@[simp] theorem commonVirtualParticipant_lonePair (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration) (center : ℕ)
    (bound : center < source.input.molecule.atomCount) :
    commonVirtualParticipant graph enumeration source h (.lonePair center) bound =
      .lonePair (commonIndexEquiv graph enumeration source h ⟨center, bound⟩) := rfl

/-- A multiple-bond duplicate's common label is the common index of its source original atom. -/
@[simp] theorem commonVirtualParticipant_duplicateAtom
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration) (original : ℕ)
    (bound : original < source.input.molecule.atomCount) :
    commonVirtualParticipant graph enumeration source h (.duplicateAtom original) bound =
      .duplicateAtom (commonIndexEquiv graph enumeration source h ⟨original, bound⟩) := rfl

/-- **Source ingress virtual-point recovery.**  Looking up a source-adapted encoded participant in
the source-adapted ledger returns exactly the source `VirtualTorsionPointLedger.lookup`, for both
primitive virtual participant kinds and including the first-match duplicate semantics. -/
@[simp] theorem commonVirtualPointAt_ofSource (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (participant : VirtualTorsionParticipant)
    (participantBound' : VirtualParticipantBounded participant
      source.input.molecule.atomCount) :
    commonVirtualPointAt graph enumeration source h
        (commonCoordinateObservation graph enumeration source h observation
          bridgeheadBound participantBound virtualBound)
        (encodeVirtualParticipant (commonIndexEquiv graph enumeration source h)
          participant participantBound') =
      VirtualTorsionPointLedger.lookup observation.virtualPoints participant := by
  show EncodedCoordinateObservation.virtualPointAt
      (EncodedCoordinateObservation.ofSource (commonIndexEquiv graph enumeration source h)
        observation bridgeheadBound participantBound virtualBound)
      (encodeVirtualParticipant (commonIndexEquiv graph enumeration source h)
        participant participantBound') = _
  exact EncodedCoordinateObservation.virtualPointAt_ofSource
    (commonIndexEquiv graph enumeration source h) observation bridgeheadBound
    participantBound virtualBound participant participantBound'

/-- The present-versus-absent status of a virtual-point lookup is preserved exactly. -/
@[simp] theorem commonVirtualPointAt_ofSource_isSome (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (participant : VirtualTorsionParticipant)
    (participantBound' : VirtualParticipantBounded participant
      source.input.molecule.atomCount) :
    (commonVirtualPointAt graph enumeration source h
        (commonCoordinateObservation graph enumeration source h observation
          bridgeheadBound participantBound virtualBound)
        (encodeVirtualParticipant (commonIndexEquiv graph enumeration source h)
          participant participantBound')).isSome =
      (VirtualTorsionPointLedger.lookup observation.virtualPoints participant).isSome := by
  show (EncodedCoordinateObservation.virtualPointAt
      (EncodedCoordinateObservation.ofSource (commonIndexEquiv graph enumeration source h)
        observation bridgeheadBound participantBound virtualBound)
      (encodeVirtualParticipant (commonIndexEquiv graph enumeration source h)
        participant participantBound')).isSome =
    (VirtualTorsionPointLedger.lookup observation.virtualPoints participant).isSome
  exact EncodedCoordinateObservation.virtualPointAt_ofSource_isSome
    (commonIndexEquiv graph enumeration source h) observation bridgeheadBound
    participantBound virtualBound participant participantBound'

/-- A missing source virtual participant stays `none` on the encoded side. -/
theorem commonVirtualPointAt_ofSource_eq_none_iff
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (participant : VirtualTorsionParticipant)
    (participantBound' : VirtualParticipantBounded participant
      source.input.molecule.atomCount) :
    commonVirtualPointAt graph enumeration source h
        (commonCoordinateObservation graph enumeration source h observation
          bridgeheadBound participantBound virtualBound)
        (encodeVirtualParticipant (commonIndexEquiv graph enumeration source h)
          participant participantBound') = none ↔
      VirtualTorsionPointLedger.lookup observation.virtualPoints participant = none := by
  rw [commonVirtualPointAt_ofSource]

/-! ## The same derived map for finite conformer atom indexing -/

/-- Decode an ordered observation family to the actual source-indexed finite conformer collection
through the derived common index.  Conformers are actual functions on `SourceAtomIndex source`, so
both their atom indexing and the coordinate payload references read the same derived bijection. -/
def commonFiniteConformerCollection (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (family : OrderedObservationFamily source V State Framework) :
    FiniteConformerCollection source :=
  OrderedObservationFamily.toFiniteConformerCollection
    (commonIndexEquiv graph enumeration source h) family

/-- The common conformer collection retains the family's declared scope. -/
@[simp] theorem commonFiniteConformerCollection_scope
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (family : OrderedObservationFamily source V State Framework) :
    (commonFiniteConformerCollection graph enumeration source h family).scope =
      family.scope := rfl

/-- The common conformer collection retains the family's declared count, order and
multiplicity. -/
@[simp] theorem commonFiniteConformerCollection_count
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (family : OrderedObservationFamily source V State Framework) :
    (commonFiniteConformerCollection graph enumeration source h family).count =
      family.count := rfl

/-- Reading the common conformer collection at a source index returns the family conformer at the
common label of that index. -/
@[simp] theorem commonFiniteConformerCollection_conformer
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (family : OrderedObservationFamily source V State Framework)
    (index : Fin family.count) (sourceIndex : SourceAtomIndex source) :
    (commonFiniteConformerCollection graph enumeration source h family).conformer
        index sourceIndex =
      family.conformer index (commonIndexEquiv graph enumeration source h sourceIndex) := by
  simp [commonFiniteConformerCollection]

/-- Native-label reading of the common conformer collection: at the source index inverse to a
native label, the conformer value is the family value at that label. -/
@[simp] theorem commonFiniteConformerCollection_conformer_native
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (family : OrderedObservationFamily source V State Framework)
    (index : Fin family.count) (v : V) :
    (commonFiniteConformerCollection graph enumeration source h family).conformer index
        ((commonIndexEquiv graph enumeration source h).symm v) =
      family.conformer index v := by
  simp [commonFiniteConformerCollection]

/-- Exact conformer-collection ingress through the derived index, reusing the existing upstream
inverse. -/
@[simp] theorem commonFiniteConformerCollection_ofFiniteConformerCollection
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (collection : FiniteConformerCollection source) (wellScoped : collection.WellScoped) :
    commonFiniteConformerCollection graph enumeration source h
        (OrderedObservationFamily.ofFiniteConformerCollection
          (State := State) (Framework := Framework)
          (commonIndexEquiv graph enumeration source h) collection wellScoped) =
      collection :=
  OrderedObservationFamily.toFiniteConformerCollection_ofFiniteConformerCollection
    (commonIndexEquiv graph enumeration source h) collection wellScoped

/-- **One derived map for both channels.**  Finite conformer atom indexing and raw P-94 coordinate
payload references read a source index through the same derived common bijection: the conformer
collection's value at a source index is the family value at the common label, and the coordinate
resolver at that same common label is the source position at the same index. -/
theorem common_conformer_coordinate_index_agree
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (family : OrderedObservationFamily source V State Framework)
    (observation : EncodedCoordinateObservation Framework V)
    (index : Fin family.count) (sourceIndex : SourceAtomIndex source) :
    (commonFiniteConformerCollection graph enumeration source h family).conformer index
        sourceIndex =
        family.conformer index (commonIndexEquiv graph enumeration source h sourceIndex) ∧
      commonPointAt graph enumeration source h observation
          (commonIndexEquiv graph enumeration source h sourceIndex) =
        observation.spatial.positions[sourceIndex.val]? :=
  ⟨commonFiniteConformerCollection_conformer graph enumeration source h family index sourceIndex,
    commonPointAt_commonIndex graph enumeration source h observation sourceIndex⟩

/-! ## Compatibility with relabelling `V ≃ W` -/

/-- **Coordinate resolver compatibility.**  Relabelling the observation along `r` and using the
correspondingly transported enumeration and graph does not change the resolved source coordinate:
at a relabelled native label the result is the original result at the inverse label. -/
@[simp] theorem commonPointAt_relabel (r : V ≃ W) (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V) (w : W) :
    commonPointAt (relabelGraph r graph) (relabelEnumeration r enumeration) source
        (relabelMoleculeEq r graph enumeration source h)
        (EncodedCoordinateObservation.relabel r observation) w =
      commonPointAt graph enumeration source h observation (r.symm w) := by
  rw [commonPointAt_eq_source_lookup, commonPointAt_eq_source_lookup]
  congr 1

/-- The relabel compatibility stated at an original native label. -/
@[simp] theorem commonPointAt_relabel_apply (r : V ≃ W)
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V) (v : V) :
    commonPointAt (relabelGraph r graph) (relabelEnumeration r enumeration) source
        (relabelMoleculeEq r graph enumeration source h)
        (EncodedCoordinateObservation.relabel r observation) (r v) =
      commonPointAt graph enumeration source h observation v := by
  simpa using
    commonPointAt_relabel r graph enumeration source h observation (r v)

/-- **Virtual-point resolver compatibility.**  Relabelled participants in the relabelled ledger
resolve to exactly the same coordinate. -/
@[simp] theorem commonVirtualPointAt_relabel (r : V ≃ W)
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (source : CertifiedAuthoritativeChemicalInput)
    (h : source.input.molecule = graph.encode enumeration)
    (observation : EncodedCoordinateObservation Framework V)
    (participant : EncodedVirtualTorsionParticipant V) :
    commonVirtualPointAt (relabelGraph r graph) (relabelEnumeration r enumeration) source
        (relabelMoleculeEq r graph enumeration source h)
        (EncodedCoordinateObservation.relabel r observation)
        (EncodedVirtualTorsionParticipant.relabel r participant) =
      commonVirtualPointAt graph enumeration source h observation participant :=
  EncodedCoordinateObservation.virtualPointAt_relabel observation r participant

/-- The ledger-level first-match lookup is compatible with relabelling. -/
@[simp] theorem commonVirtualPointLedgerLookup_relabel (r : V ≃ W)
    (ledger : List (EncodedVirtualTorsionPoint V))
    (participant : EncodedVirtualTorsionParticipant V) :
    commonVirtualPointLedgerLookup (ledger.map (EncodedVirtualTorsionPoint.relabel r))
        (EncodedVirtualTorsionParticipant.relabel r participant) =
      commonVirtualPointLedgerLookup ledger participant :=
  EncodedVirtualTorsionPoint.lookup_relabel r ledger participant

/-! ## Opaque carriers are copied, not internally relabelled

The relabelling functions of the observation family move only explicit atom references.  The
projection lemmas below record that the opaque `State`/`Framework` carriers, their relations and
predicates, and the exact geometric payloads are copied verbatim.
-/

/-- The encoded coordinate observation's `Framework` value is copied by relabelling. -/
@[simp] theorem coordinateRelabel_framework (r : V ≃ W)
    (observation : EncodedCoordinateObservation Framework V) :
    (EncodedCoordinateObservation.relabel r observation).framework = observation.framework := rfl

/-- The exact spatial payload is copied by relabelling; it is not reindexed. -/
@[simp] theorem coordinateRelabel_spatial (r : V ≃ W)
    (observation : EncodedCoordinateObservation Framework V) :
    (EncodedCoordinateObservation.relabel r observation).spatial = observation.spatial := rfl

/-- The exact interior point is copied by relabelling. -/
@[simp] theorem coordinateRelabel_interior (r : V ≃ W)
    (observation : EncodedCoordinateObservation Framework V) :
    (EncodedCoordinateObservation.relabel r observation).interior = observation.interior := rfl

/-- The conformer-pair `State` relation is copied by relabelling. -/
@[simp] theorem conformerPairRelabel_singleBondRotation (r : V ≃ W)
    (record : ConformerPairObservation V State) :
    (ConformerPairObservation.relabel r record).singleBondRotation =
      record.singleBondRotation := rfl

/-- The conformer-pair retained states are copied by relabelling. -/
@[simp] theorem conformerPairRelabel_first (r : V ≃ W)
    (record : ConformerPairObservation V State) :
    (ConformerPairObservation.relabel r record).first = record.first := rfl

/-- The conformer-pair second retained state is copied by relabelling. -/
@[simp] theorem conformerPairRelabel_second (r : V ≃ W)
    (record : ConformerPairObservation V State) :
    (ConformerPairObservation.relabel r record).second = record.second := rfl

/-- The twist rotation relation is copied by relabelling. -/
@[simp] theorem twistRelabel_singleBondRotation (r : V ≃ W)
    (record : TwistObservation V State) :
    (TwistObservation.relabel r record).singleBondRotation = record.singleBondRotation := rfl

/-- The twist endpoint-distinctness relation is copied by relabelling. -/
@[simp] theorem twistRelabel_endpointConformationsDistinct (r : V ≃ W)
    (record : TwistObservation V State) :
    (TwistObservation.relabel r record).endpointConformationsDistinct =
      record.endpointConformationsDistinct := rfl

/-- The twist boat predicate is copied by relabelling. -/
@[simp] theorem twistRelabel_isBoatState (r : V ≃ W) (record : TwistObservation V State) :
    (TwistObservation.relabel r record).isBoatState = record.isBoatState := rfl

/-- The twist chair predicate is copied by relabelling. -/
@[simp] theorem twistRelabel_isChairState (r : V ≃ W) (record : TwistObservation V State) :
    (TwistObservation.relabel r record).isChairState = record.isChairState := rfl

/-- The twist candidate state is copied by relabelling. -/
@[simp] theorem twistRelabel_candidate (r : V ≃ W) (record : TwistObservation V State) :
    (TwistObservation.relabel r record).candidate = record.candidate := rfl

/-- The twist first leg is copied by relabelling. -/
@[simp] theorem twistRelabel_firstLeg (r : V ≃ W) (record : TwistObservation V State) :
    (TwistObservation.relabel r record).firstLeg = record.firstLeg := rfl

/-- The twist second leg is copied by relabelling. -/
@[simp] theorem twistRelabel_secondLeg (r : V ≃ W) (record : TwistObservation V State) :
    (TwistObservation.relabel r record).secondLeg = record.secondLeg := rfl

/-- The in/out site's `Framework` value is copied by relabelling. -/
@[simp] theorem inOutSiteRelabel_framework (r : V ≃ W)
    (site : EncodedInOutSite Framework V) :
    (EncodedInOutSite.relabel r site).framework = site.framework := rfl

/-- The supplied bridge-length proposition is copied by relabelling. -/
@[simp] theorem inOutSiteRelabel_bridgeLongEnough (r : V ≃ W)
    (site : EncodedInOutSite Framework V) :
    (EncodedInOutSite.relabel r site).bridgeLongEnough = site.bridgeLongEnough := rfl

/-- The supplied direction is copied by relabelling. -/
@[simp] theorem inOutSiteRelabel_direction (r : V ≃ W)
    (site : EncodedInOutSite Framework V) :
    (EncodedInOutSite.relabel r site).direction = site.direction := rfl

/-- The paired in/out bicyclic-framework proposition is copied by relabelling. -/
@[simp] theorem inOutDataRelabel_bicyclicSystem (r : V ≃ W)
    (record : InOutObservationData Framework V) :
    (InOutObservationData.relabel r record).bicyclicSystem = record.bicyclicSystem := rfl

/-! ### Payload channel projections

These projections record that relabelling never invents or removes a channel: an absent channel
stays absent, and each present channel is relabelled by its own atom-only transport.
-/

@[simp] theorem payloadRelabel_conformerPair? (r : V ≃ W)
    (payload : ObservationPayload V State Framework) :
    (ObservationPayload.relabel r payload).conformerPair? =
      payload.conformerPair?.map (ConformerPairObservation.relabel r) := rfl

@[simp] theorem payloadRelabel_torsion? (r : V ≃ W)
    (payload : ObservationPayload V State Framework) :
    (ObservationPayload.relabel r payload).torsion? =
      payload.torsion?.map (TorsionObservation.relabel r) := rfl

@[simp] theorem payloadRelabel_twist? (r : V ≃ W)
    (payload : ObservationPayload V State Framework) :
    (ObservationPayload.relabel r payload).twist? =
      payload.twist?.map (TwistObservation.relabel r) := rfl

@[simp] theorem payloadRelabel_inOut? (r : V ≃ W)
    (payload : ObservationPayload V State Framework) :
    (ObservationPayload.relabel r payload).inOut? =
      payload.inOut?.map (InOutObservationData.relabel r) := rfl

@[simp] theorem payloadRelabel_coordinateInOut? (r : V ≃ W)
    (payload : ObservationPayload V State Framework) :
    (ObservationPayload.relabel r payload).coordinateInOut? =
      payload.coordinateInOut?.map (CoordinateInOutData.relabel r) := rfl

/-- An absent observation channel stays absent after relabelling. -/
theorem payloadRelabel_absent_channel (r : V ≃ W)
    (payload : ObservationPayload V State Framework)
    (absent : payload.coordinateInOut? = none) :
    (ObservationPayload.relabel r payload).coordinateInOut? = none := by
  rw [payloadRelabel_coordinateInOut?, absent]
  rfl

end OrganicStereoObservationCommonIndexBridge
end TetraStereo.OneCenter
