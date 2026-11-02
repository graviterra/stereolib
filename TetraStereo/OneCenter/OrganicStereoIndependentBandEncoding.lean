/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.OneCenter.OrganicStereoFiniteEncoding
import TetraStereo.OneCenter.OrganicStereoEmbeddedBands

/-!
# Independent finite band attachments encoded at one certified source

`OrganicStereoEmbeddedBands` supplies ribbon bands (`Band`) as independently geometric objects:
each band carries its own continuous strip map, exact seam gluing, modulo-seam injectivity and
surface.  It also supplies `CertifiedPartialBand source`, a partial attachment ledger that keeps
the *whole* certified source and the *whole* real source geometry while attaching only
`attachmentCount` ledger entries to one band.  That module, however, starts from an already
certified source and an already encoded partial band.

This module closes the gap in the other direction.  The independent input is

* an arbitrary finite atom-labelled interaction hypergraph `graph` on a finite label type `V`,
* one full real conformation `MolecularConformation V = V → EuclideanSpace ℝ (Fin 3)`,
* an arbitrary finite band index type `bandIndex` (possibly empty, possibly repeating the same
  geometric band),
* for each band index `b` a `Band` geometry, a finite attachment type `Attachment b`, an atom map
  `atom b : Attachment b → V`, a parameter map `parameter b : Attachment b → RibbonDomain` and the
  exact positional equation `(band b).strip (parameter b a) = conformation (atom b a)`.

There is no coverage condition: no band must carry every source atom, attachment types may be
empty, and several attachment records (of one band or of different bands) may name the same source
atom.  Records are retained individually, so attachment multiplicity is preserved.

Given an explicit enumeration `enumeration : V ≃ Fin (Fintype.card V)`, the module builds, for each
`b`, a genuine `CertifiedPartialBand (graph.certifiedEncoding enumeration)`.  The *same*
enumeration is used for the certified source and for the retained whole-source conformation: the
certified source's atom index is `Fin atomCount`, which the finite encoding proves equal to
`Fintype.card V`, and `sourceIndexEquiv` is the resulting explicit bijection
`V ≃ SourceAtomIndex`.  Attachment indices of each band are enumerated by an explicit equivalence
`Attachment b ≃ Fin n` (in the family API, `Fintype.equivFin`).

Main results:

* exact source preservation: the retained source is literally
  `graph.certifiedEncoding enumeration`; its atom count, interaction count, atom data and
  interaction kinds are those of the graph;
* whole-geometry recovery: reading the retained conformation back through `sourceIndexEquiv`
  returns the supplied `conformation` at every label, whether or not that label is attached to any
  band;
* band preservation: surface, seam mode, seam gluing, seam classes, strip map and every attachment
  parameter are literally those of the supplied band;
* attachment preservation: each record's `V` label is recovered exactly, and the ledger has one
  entry per attachment record (`attachmentCount = n`, indexed by the supplied equivalence), so two
  records naming the same atom remain two entries;
* inverse recovery: `decodeBandAttachment` and `decodeConformation` recover the input data;
* enumeration invariance: changing the enumeration of `V` or of an attachment type only relabels
  indices; the decoded `V`-level geometry, atoms and parameters are unchanged.

Nothing here constructs a `Band`, claims that a band exists, classifies bands, or infers chirality
from a seam mode.  Every theorem is conditional on the supplied band geometry and attachment data.
In particular the empty attachment type is allowed and produces an empty ledger, but no physical
existence statement is made.
-/

open TetraStereo.OneCenter.OrganicStereoEmbeddedBands

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace OrganicStereoIndependentBandEncoding

noncomputable section

/-! ## The independent input -/

/-- Independent band attachment data over one finite atom-label type `V` and one whole real
conformation.  Every band carries its own geometry and its own finite attachment type; no band is
required to cover `V`, and attachment records are not identified even when they name the same atom
or the same parameter point. -/
structure IndependentBandAttachment (V : Type) [DecidableEq V] [Fintype V] where
  /-- The independently specified finite atom-labelled interaction hypergraph. -/
  graph : FiniteAtomInteractionHypergraph V
  /-- One full real conformation, with exactly one point per atom label. -/
  conformation : MolecularConformation V
  /-- The finite type of band indices. -/
  bandIndex : Type
  /-- Finiteness of the band index type. -/
  fintypeBandIndex : Fintype bandIndex
  /-- The geometric band attached to each index. -/
  band : bandIndex → Band
  /-- The finite attachment record type of each band. -/
  Attachment : bandIndex → Type
  /-- Finiteness of every attachment type. -/
  fintypeAttachment : ∀ b, Fintype (Attachment b)
  /-- The source atom label named by each attachment record. -/
  atom : ∀ b, Attachment b → V
  /-- The band parameter point named by each attachment record. -/
  parameter : ∀ b, Attachment b → RibbonDomain
  /-- Exact positional agreement of every attachment record with the supplied conformation. -/
  agreement : ∀ b (entry : Attachment b),
    (band b).strip (parameter b entry) = conformation (atom b entry)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Projections of an explicitly constructed partial band

`CertifiedPartialBand.ofGeometry` is the existing constructor of the partial ledger.  The
projection lemmas below are definitional; they are stated so that the constructors of this module
can be evaluated by rewriting rather than by unfolding the whole structure. -/

section OfGeometry

variable {source : CertifiedAuthoritativeChemicalInput}

/-- The geometry projection of an explicit partial band is the supplied geometry. -/
@[simp] theorem partialBand_ofGeometry_geometry (geometry : RealSourceGeometry source)
    (band : Band) (count : ℕ) (atom : Fin count → CertifiedSourceIndex source)
    (parameter : Fin count → RibbonDomain)
    (agreement : ∀ entry : Fin count,
      band.strip (parameter entry) = geometry.conformation (atom entry)) :
    (CertifiedPartialBand.ofGeometry source geometry band count atom parameter
      agreement).geometry = geometry := rfl

/-- The band projection of an explicit partial band is the supplied band. -/
@[simp] theorem partialBand_ofGeometry_band (geometry : RealSourceGeometry source)
    (band : Band) (count : ℕ) (atom : Fin count → CertifiedSourceIndex source)
    (parameter : Fin count → RibbonDomain)
    (agreement : ∀ entry : Fin count,
      band.strip (parameter entry) = geometry.conformation (atom entry)) :
    (CertifiedPartialBand.ofGeometry source geometry band count atom parameter
      agreement).band = band := rfl

/-- The ledger length of an explicit partial band is the supplied count. -/
@[simp] theorem partialBand_ofGeometry_attachmentCount (geometry : RealSourceGeometry source)
    (band : Band) (count : ℕ) (atom : Fin count → CertifiedSourceIndex source)
    (parameter : Fin count → RibbonDomain)
    (agreement : ∀ entry : Fin count,
      band.strip (parameter entry) = geometry.conformation (atom entry)) :
    (CertifiedPartialBand.ofGeometry source geometry band count atom parameter
      agreement).attachmentCount = count := rfl

/-- The ledger atom of an explicit partial band is the supplied atom map. -/
@[simp] theorem partialBand_ofGeometry_atom (geometry : RealSourceGeometry source)
    (band : Band) (count : ℕ) (atom : Fin count → CertifiedSourceIndex source)
    (parameter : Fin count → RibbonDomain)
    (agreement : ∀ entry : Fin count,
      band.strip (parameter entry) = geometry.conformation (atom entry))
    (entry : Fin count) :
    (CertifiedPartialBand.ofGeometry source geometry band count atom parameter
      agreement).atom entry = atom entry := rfl

/-- The ledger parameter of an explicit partial band is the supplied parameter map. -/
@[simp] theorem partialBand_ofGeometry_parameter (geometry : RealSourceGeometry source)
    (band : Band) (count : ℕ) (atom : Fin count → CertifiedSourceIndex source)
    (parameter : Fin count → RibbonDomain)
    (agreement : ∀ entry : Fin count,
      band.strip (parameter entry) = geometry.conformation (atom entry))
    (entry : Fin count) :
    (CertifiedPartialBand.ofGeometry source geometry band count atom parameter
      agreement).parameter entry = parameter entry := rfl

end OfGeometry

/-! ## The source index bijection determined by one enumeration -/

/-- The explicit bijection between the independent atom labels `V` and the certified source's own
atom index type.  It is the supplied enumeration composed with the cardinality identification
proved by the finite encoding, so the graph and the retained conformation are read through the
same enumeration. -/
noncomputable def sourceIndexEquiv (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    V ≃ CertifiedSourceIndex (graph.certifiedEncoding enumeration) :=
  enumeration.trans (finCongr (graph.encode_atomCount enumeration).symm)

/-- The source index attached to a label has exactly the enumeration value of that label. -/
@[simp] theorem sourceIndexEquiv_apply_val (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (v : V) :
    ((sourceIndexEquiv graph enumeration v).val) = (enumeration v).val := rfl

/-- The source index bijection is a left inverse of its own inverse. -/
@[simp] theorem sourceIndexEquiv_symm_apply_self (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (v : V) :
    (sourceIndexEquiv graph enumeration).symm (sourceIndexEquiv graph enumeration v) = v :=
  Equiv.symm_apply_apply _ _

/-- Decoding a source index after encoding a label returns that label. -/
@[simp] theorem sourceIndexEquiv_apply_symm (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (index : CertifiedSourceIndex (graph.certifiedEncoding enumeration)) :
    sourceIndexEquiv graph enumeration ((sourceIndexEquiv graph enumeration).symm index) = index :=
  Equiv.apply_symm_apply _ _

/-! ## The whole-source geometry indexed by the certified source -/

/-- The whole supplied conformation, indexed by the certified source's own atom indices through
the same enumeration.  Every source label, attached to a band or not, keeps its exact position. -/
noncomputable def sourceGeometry (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V) :
    RealSourceGeometry (graph.certifiedEncoding enumeration) :=
  RealSourceGeometry.ofConformation (graph.certifiedEncoding enumeration)
    (fun index => conformation ((sourceIndexEquiv graph enumeration).symm index))

/-- Reading the retained whole-source geometry back through `sourceIndexEquiv` returns exactly the
supplied conformation at every independent atom label. -/
@[simp] theorem sourceGeometry_conformation_apply (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V) (v : V) :
    (sourceGeometry graph enumeration conformation).conformation
      (sourceIndexEquiv graph enumeration v) = conformation v := by
  simp [sourceGeometry]

/-! ## The core constructor: one band becomes one certified partial band -/

/-- Encode the attachment data of one band as a `CertifiedPartialBand` at the certified source
`graph.certifiedEncoding enumeration`.

The attachment record type `A` is finite of cardinality `n` by the supplied equivalence
`attachmentEnumeration : A ≃ Fin n` (callers with a `Fintype` instance use `Fintype.equivFin`).
The same enumeration of `V` is used for the certified source and for the retained conformation.
The band itself, its surface, its seam data and every parameter point are copied literally. -/
noncomputable def encodeBand (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    CertifiedPartialBand (graph.certifiedEncoding enumeration) :=
  CertifiedPartialBand.ofGeometry (graph.certifiedEncoding enumeration)
    (sourceGeometry graph enumeration conformation) G n
    (fun entry => sourceIndexEquiv graph enumeration (atom (attachmentEnumeration.symm entry)))
    (fun entry => parameter (attachmentEnumeration.symm entry))
    (fun entry => by
      simpa [sourceGeometry] using agreement (attachmentEnumeration.symm entry))

/-! ### Band geometry, surface and seam data -/

/-- The encoded ledger carries literally the supplied band. -/
@[simp] theorem encodeBand_band (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
      attachmentEnumeration).band = G := rfl

/-- The encoded ledger's whole-source geometry is the supplied conformation read through the same
enumeration. -/
@[simp] theorem encodeBand_geometry (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
      attachmentEnumeration).geometry = sourceGeometry graph enumeration conformation := rfl

/-- The seam mode of the encoded band is exactly the seam mode of the supplied band. -/
@[simp] theorem encodeBand_mode (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
      attachmentEnumeration).band.mode = G.mode := rfl

/-- The whole band surface is preserved literally. -/
@[simp] theorem encodeBand_surface (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
      attachmentEnumeration).band.surface = G.surface := rfl

/-- The exact seam gluing of the supplied band is retained: seam classes are unchanged. -/
theorem encodeBand_seamRel_iff (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (x y : RibbonDomain) :
    SeamRel (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).band.mode x y ↔ SeamRel G.mode x y := by
  rw [encodeBand_band]

/-- The explicit seam gluing equation of the supplied band is retained. -/
theorem encodeBand_seam_gluing (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (s : unitInterval) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).band.strip ((1 : unitInterval), s) =
      (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).band.strip ((0 : unitInterval), G.mode.glue s) := by
  rw [encodeBand_band]
  exact G.seam s

/-! ### Attachment records: parameters, atoms and multiplicity -/

/-- The ledger length is exactly the number of attachment records. -/
@[simp] theorem encodeBand_attachmentCount (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
      attachmentEnumeration).attachmentCount = n := rfl

/-- Each attachment record occupies its own ledger entry, indexed by the supplied equivalence. -/
theorem encodeBand_entries_bijective (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    Function.Bijective (fun a : A =>
      (attachmentEnumeration a : Fin
        (encodeBand graph enumeration conformation G A atom parameter agreement n
          attachmentEnumeration).attachmentCount)) := by
  simpa using attachmentEnumeration.bijective

/-- The parameter point of a ledger entry is exactly the supplied parameter of that record. -/
@[simp] theorem encodeBand_parameter (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a : A) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
      attachmentEnumeration).parameter (attachmentEnumeration a) = parameter a := by
  simp [encodeBand]

/-- The ledger atom of an entry is the certified source index of exactly the supplied label. -/
@[simp] theorem encodeBand_atom (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a : A) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).atom (attachmentEnumeration a) =
      sourceIndexEquiv graph enumeration (atom a) := by
  simp [encodeBand]

/-- Decoding the ledger atom of an entry through the same enumeration returns the supplied label
exactly.  No atom label is reinterpreted by the encoding. -/
theorem encodeBand_atom_decode (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a : A) :
    (sourceIndexEquiv graph enumeration).symm
        ((encodeBand graph enumeration conformation G A atom parameter agreement n
          attachmentEnumeration).atom (attachmentEnumeration a)) = atom a := by
  simp [encodeBand]

/-- Two ledger entries name the same certified source index exactly when the two attachment
records name the same atom label.  In particular distinct records of one atom stay distinct
entries with the same index. -/
theorem encodeBand_atom_eq_iff (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a₁ a₂ : A) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).atom (attachmentEnumeration a₁) =
      (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).atom (attachmentEnumeration a₂) ↔ atom a₁ = atom a₂ := by
  rw [encodeBand_atom, encodeBand_atom]
  constructor
  · intro equal
    exact (sourceIndexEquiv graph enumeration).injective equal
  · intro equal
    rw [equal]

/-- Two ledger parameters coincide exactly when the two supplied records name the same parameter
point.  This holds for distinct records as well. -/
theorem encodeBand_parameter_eq_iff (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a₁ a₂ : A) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).parameter (attachmentEnumeration a₁) =
      (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).parameter (attachmentEnumeration a₂) ↔
      parameter a₁ = parameter a₂ := by
  simp [encodeBand]

/-- Two distinct attachment records naming the same atom remain two distinct ledger entries.  The
encoding preserves record multiplicity even when atom labels repeat. -/
theorem encodeBand_same_atom_separate_records (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) {a₁ a₂ : A}
    (sameAtom : atom a₁ = atom a₂) (distinct : a₁ ≠ a₂) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).atom (attachmentEnumeration a₁) =
        (encodeBand graph enumeration conformation G A atom parameter agreement n
          attachmentEnumeration).atom (attachmentEnumeration a₂) ∧
      attachmentEnumeration a₁ ≠ attachmentEnumeration a₂ := by
  refine ⟨?_, fun equal => distinct (attachmentEnumeration.injective equal)⟩
  rw [encodeBand_atom, encodeBand_atom, sameAtom]

/-- The ledger entry of a record satisfies exactly the positional agreement of the constructed
partial band. -/
theorem encodeBand_agreement (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a : A) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).band.strip
        ((encodeBand graph enumeration conformation G A atom parameter agreement n
          attachmentEnumeration).parameter (attachmentEnumeration a)) =
      (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).geometry.conformation
        ((encodeBand graph enumeration conformation G A atom parameter agreement n
          attachmentEnumeration).atom (attachmentEnumeration a)) :=
  (encodeBand graph enumeration conformation G A atom parameter agreement n
    attachmentEnumeration).agreement (attachmentEnumeration a)

/-- The strip image of an attached parameter is exactly the supplied real position of its atom. -/
theorem encodeBand_strip_conformation (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a : A) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).band.strip (parameter a) = conformation (atom a) :=
  agreement a

/-- Every attached real position lies on the retained band surface. -/
theorem encodeBand_attached_mem_surface (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a : A) :
    conformation (atom a) ∈
      (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).band.surface := by
  rw [encodeBand_band]
  exact ⟨parameter a, agreement a⟩

/-- Attached positions coincide exactly when their parameters are seam-related, with the seam
mode of the supplied band. -/
theorem encodeBand_attached_eq_iff_seamRel (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a₁ a₂ : A) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).geometry.conformation
        ((encodeBand graph enumeration conformation G A atom parameter agreement n
          attachmentEnumeration).atom (attachmentEnumeration a₁)) =
      (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).geometry.conformation
        ((encodeBand graph enumeration conformation G A atom parameter agreement n
          attachmentEnumeration).atom (attachmentEnumeration a₂)) ↔
      SeamRel (encodeBand graph enumeration conformation G A atom parameter agreement n
          attachmentEnumeration).band.mode
        ((encodeBand graph enumeration conformation G A atom parameter agreement n
          attachmentEnumeration).parameter (attachmentEnumeration a₁))
        ((encodeBand graph enumeration conformation G A atom parameter agreement n
          attachmentEnumeration).parameter (attachmentEnumeration a₂)) :=
  (encodeBand graph enumeration conformation G A atom parameter agreement n
    attachmentEnumeration).attached_eq_iff_seamRel _ _

/-- An empty attachment type is a legal input; the resulting ledger has length zero. -/
theorem encodeBand_fin_zero_attachmentCount (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (atom : Fin 0 → V) (parameter : Fin 0 → RibbonDomain)
    (agreement : ∀ a : Fin 0, G.strip (parameter a) = conformation (atom a)) :
    (encodeBand graph enumeration conformation G (Fin 0) atom parameter agreement 0
      (Equiv.refl (Fin 0))).attachmentCount = 0 := rfl

/-! ### Whole-source preservation and geometry recovery -/

/-- The encoded partial band retains exactly the certified source of the graph. -/
@[simp] theorem encodeBand_sourceOf (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
      attachmentEnumeration).sourceOf = graph.certifiedEncoding enumeration := rfl

/-- The retained authoritative input is exactly the encoded graph. -/
@[simp] theorem encodeBand_sourceOf_input (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
      attachmentEnumeration).sourceOf.input =
      graph.encodeAuthoritative enumeration := rfl

/-- The retained source atom count is the cardinality of the independent atom type. -/
theorem encodeBand_sourceOf_atomCount (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
      attachmentEnumeration).sourceOf.input.molecule.atomCount = Fintype.card V :=
  graph.encode_atomCount enumeration

/-- The retained source interaction count is the source graph's interaction count. -/
theorem encodeBand_sourceOf_interactions_length (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
      attachmentEnumeration).sourceOf.input.molecule.interactions.length =
      graph.interactions.length :=
  graph.encode_interactions_length enumeration

/-- The retained source carries exactly the graph's atom data at every enumeration index. -/
theorem encodeBand_sourceOf_atomAt (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (index : Fin (Fintype.card V)) :
    listGet? (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).sourceOf.input.molecule.atoms index.val =
      some (graph.atomData (enumeration.symm index)) :=
  graph.certifiedEncoding_atomAt enumeration index

/-- The retained source's ordered interaction kinds are exactly the graph's interaction kinds,
including any `.other` authority codes. -/
theorem encodeBand_sourceOf_interactionKinds (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).sourceOf.input.molecule.interactions.map
        SemanticInteraction.kind =
      graph.interactions.map (fun edge => edge.2) :=
  graph.encode_interactionKinds enumeration

/-- Every source atom of the graph remains present in the retained whole source, including atoms
that no band attaches. -/
theorem encodeBand_sourceOf_atom_present (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) {sourceAtomLabel : SemanticAtom}
    (member : sourceAtomLabel ∈
      (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).sourceOf.input.molecule.atoms) :
    ∃ index : CertifiedSourceIndex
        (encodeBand graph enumeration conformation G A atom parameter agreement n
          attachmentEnumeration).sourceOf,
      sourceAtom (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).sourceOf index = sourceAtomLabel :=
  (encodeBand graph enumeration conformation G A atom parameter agreement n
    attachmentEnumeration).offband_atom_present member

/-- The retained whole-source geometry, read through the same enumeration, is exactly the supplied
conformation at every atom label.  This includes every attachment-free (off-band) atom, so no
coverage of `V` by the bands is assumed. -/
theorem encodeBand_geometry_apply (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (v : V) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).geometry.conformation
        (sourceIndexEquiv graph enumeration v) = conformation v := by
  rw [encodeBand_geometry]
  exact sourceGeometry_conformation_apply graph enumeration conformation v

/-! ### Inverse recovery -/

/-- Decode a retained whole-source geometry back to a conformation on the independent labels. -/
def decodeConformation (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (X : CertifiedPartialBand (graph.certifiedEncoding enumeration)) : MolecularConformation V :=
  fun v => X.geometry.conformation (sourceIndexEquiv graph enumeration v)

/-- The decoder recovers the supplied conformation exactly, at every atom label. -/
theorem decodeConformation_encodeBand (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    decodeConformation graph enumeration
      (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration) = conformation := by
  funext v
  exact encodeBand_geometry_apply graph enumeration conformation G A atom parameter agreement n
    attachmentEnumeration v

/-- Decode the attachment records of a ledger: each record's independent atom label and band
parameter. -/
def decodeBandAttachment (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (A : Type)
    (X : CertifiedPartialBand (graph.certifiedEncoding enumeration))
    (attachmentEnumeration : A ≃ Fin X.attachmentCount) : A → V × RibbonDomain :=
  fun a =>
    ((sourceIndexEquiv graph enumeration).symm (X.atom (attachmentEnumeration a)),
      X.parameter (attachmentEnumeration a))

/-- Decoding the ledger recovers each attachment record exactly: atom label and parameter point. -/
theorem decodeBandAttachment_encodeBand (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a : A) :
    decodeBandAttachment graph enumeration A
      (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration) attachmentEnumeration a = (atom a, parameter a) := by
  simp [decodeBandAttachment, encodeBand]

/-- Full record recovery: the band, the atom label and the parameter point of one record are all
returned exactly by the decoders. -/
theorem encodeBand_decode_triple (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a : A) :
    ((sourceIndexEquiv graph enumeration).symm
        ((encodeBand graph enumeration conformation G A atom parameter agreement n
          attachmentEnumeration).atom (attachmentEnumeration a)),
      (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).parameter (attachmentEnumeration a),
      (encodeBand graph enumeration conformation G A atom parameter agreement n
        attachmentEnumeration).band) = (atom a, parameter a, G) := by
  simp [encodeBand]

/-- Decoding the retained band record recovers exactly the supplied band. -/
theorem encodeBand_toRecord_toBand (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n
      attachmentEnumeration).toRecord.toBand = G := by
  rw [CertifiedPartialBand.toRecord_toBand, encodeBand_band]

/-! ### Enumeration invariance -/

/-- Changing the enumeration of an attachment type only relabels ledger indices: the atom index
of a record is independent of the chosen equivalence. -/
theorem encodeBand_atom_relabel (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (first second : A ≃ Fin n) (a : A) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n second).atom
        (second a) =
      (encodeBand graph enumeration conformation G A atom parameter agreement n first).atom
        (first a) := by
  rw [encodeBand_atom, encodeBand_atom]

/-- Changing the enumeration of an attachment type only relabels ledger indices: the parameter
point of a record is independent of the chosen equivalence. -/
theorem encodeBand_parameter_relabel (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (first second : A ≃ Fin n) (a : A) :
    (encodeBand graph enumeration conformation G A atom parameter agreement n second).parameter
        (second a) =
      (encodeBand graph enumeration conformation G A atom parameter agreement n first).parameter
        (first a) := by
  rw [encodeBand_parameter, encodeBand_parameter]

/-- Changing the enumeration of `V` does not change the recovered whole-source geometry at the
independent labels. -/
theorem encodeBand_geometry_apply_relabel (graph : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (v : V) :
    (encodeBand graph second conformation G A atom parameter agreement n
        attachmentEnumeration).geometry.conformation (sourceIndexEquiv graph second v) =
      (encodeBand graph first conformation G A atom parameter agreement n
        attachmentEnumeration).geometry.conformation (sourceIndexEquiv graph first v) := by
  rw [encodeBand_geometry_apply, encodeBand_geometry_apply]

/-- Changing the enumeration of `V` only relabels source indices: the decoded atom label of a
record is the same in both encodings. -/
theorem encodeBand_atom_decode_relabel (graph : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a : A) :
    (sourceIndexEquiv graph second).symm
        ((encodeBand graph second conformation G A atom parameter agreement n
          attachmentEnumeration).atom (attachmentEnumeration a)) =
      (sourceIndexEquiv graph first).symm
        ((encodeBand graph first conformation G A atom parameter agreement n
          attachmentEnumeration).atom (attachmentEnumeration a)) := by
  rw [encodeBand_atom_decode, encodeBand_atom_decode]

/-- Changing the enumeration of `V` leaves every attachment parameter literally unchanged. -/
theorem encodeBand_parameter_enumeration_invariant (graph : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) (a : A) :
    (encodeBand graph second conformation G A atom parameter agreement n
        attachmentEnumeration).parameter (attachmentEnumeration a) =
      (encodeBand graph first conformation G A atom parameter agreement n
        attachmentEnumeration).parameter (attachmentEnumeration a) := by
  rw [encodeBand_parameter, encodeBand_parameter]

/-- Changing the enumeration of `V` leaves the retained band and its seam mode literally
unchanged. -/
theorem encodeBand_band_enumeration_invariant (graph : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V)
    (G : Band) (A : Type) (atom : A → V) (parameter : A → RibbonDomain)
    (agreement : ∀ a : A, G.strip (parameter a) = conformation (atom a))
    (n : ℕ) (attachmentEnumeration : A ≃ Fin n) :
    (encodeBand graph second conformation G A atom parameter agreement n
        attachmentEnumeration).band =
        (encodeBand graph first conformation G A atom parameter agreement n
          attachmentEnumeration).band ∧
      (encodeBand graph second conformation G A atom parameter agreement n
        attachmentEnumeration).band.mode =
        (encodeBand graph first conformation G A atom parameter agreement n
          attachmentEnumeration).band.mode :=
  ⟨rfl, rfl⟩

/-! ## The finite family over all band indices -/

/-- The enumeration of the finite band index type. -/
noncomputable def bandEnumeration (input : IndependentBandAttachment V) :
    input.bandIndex ≃ Fin (@Fintype.card input.bandIndex input.fintypeBandIndex) :=
  @Fintype.equivFin input.bandIndex input.fintypeBandIndex

/-- The `Fintype`-based enumeration of one band's attachment records. -/
noncomputable def attachmentEnumeration (input : IndependentBandAttachment V)
    (b : input.bandIndex) :
    input.Attachment b ≃
      Fin (@Fintype.card (input.Attachment b) (input.fintypeAttachment b)) :=
  @Fintype.equivFin (input.Attachment b) (input.fintypeAttachment b)

/-- Encode the attachment data of every band index as a certified partial band at the one
certified source.  No band is required to cover the atom type, and the construction is available
for an empty band index type. -/
noncomputable def encodeFamily (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) :
    CertifiedPartialBand (input.graph.certifiedEncoding enumeration) :=
  encodeBand input.graph enumeration input.conformation (input.band b) (input.Attachment b)
    (input.atom b) (input.parameter b) (input.agreement b)
    (@Fintype.card (input.Attachment b) (input.fintypeAttachment b))
    (attachmentEnumeration input b)

/-- The family retains each supplied band literally. -/
@[simp] theorem encodeFamily_band (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) :
    (encodeFamily input enumeration b).band = input.band b := rfl

/-- Each family member retains the whole-source geometry of the input. -/
@[simp] theorem encodeFamily_geometry (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) :
    (encodeFamily input enumeration b).geometry =
      sourceGeometry input.graph enumeration input.conformation := rfl

/-- Each family member's ledger length is the cardinality of that band's attachment type. -/
@[simp] theorem encodeFamily_attachmentCount (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) :
    (encodeFamily input enumeration b).attachmentCount =
      @Fintype.card (input.Attachment b) (input.fintypeAttachment b) := rfl

/-- Every family member retains exactly the certified source. -/
@[simp] theorem encodeFamily_sourceOf (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) :
    (encodeFamily input enumeration b).sourceOf =
      input.graph.certifiedEncoding enumeration := rfl

/-- Each family member's seam mode is the supplied band's seam mode. -/
@[simp] theorem encodeFamily_mode (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) :
    (encodeFamily input enumeration b).band.mode = (input.band b).mode := rfl

/-- Each family member's surface is the supplied band's surface. -/
@[simp] theorem encodeFamily_surface (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) :
    (encodeFamily input enumeration b).band.surface = (input.band b).surface := rfl

/-- Each attachment record's parameter is recovered exactly. -/
@[simp] theorem encodeFamily_parameter (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex)
    (a : input.Attachment b) :
    (encodeFamily input enumeration b).parameter (attachmentEnumeration input b a) =
      input.parameter b a := by
  simp [encodeFamily, encodeBand]

/-- Each attachment record's source index is exactly the enumeration of its atom label. -/
@[simp] theorem encodeFamily_atom (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex)
    (a : input.Attachment b) :
    (encodeFamily input enumeration b).atom (attachmentEnumeration input b a) =
      sourceIndexEquiv input.graph enumeration (input.atom b a) := by
  simp [encodeFamily, encodeBand]

/-- Decoding each attachment record through the same enumeration returns its atom label. -/
theorem encodeFamily_atom_decode (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex)
    (a : input.Attachment b) :
    (sourceIndexEquiv input.graph enumeration).symm
        ((encodeFamily input enumeration b).atom (attachmentEnumeration input b a)) =
      input.atom b a := by
  simp [encodeFamily, encodeBand]

/-- The attachment decoder recovers every family record exactly: atom label and parameter. -/
theorem decodeBandAttachment_encodeFamily (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex)
    (a : input.Attachment b) :
    decodeBandAttachment input.graph enumeration (input.Attachment b)
      (encodeFamily input enumeration b) (attachmentEnumeration input b) a =
      (input.atom b a, input.parameter b a) := by
  simp [decodeBandAttachment, encodeFamily, encodeBand]

/-- The conformation decoder recovers the whole supplied conformation from every family member. -/
theorem decodeConformation_encodeFamily (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) :
    decodeConformation input.graph enumeration (encodeFamily input enumeration b) =
      input.conformation := by
  funext v
  rw [decodeConformation, encodeFamily_geometry]
  exact sourceGeometry_conformation_apply input.graph enumeration input.conformation v

/-- Each family member recovers the whole supplied conformation at every atom label. -/
theorem encodeFamily_geometry_apply (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) (v : V) :
    (encodeFamily input enumeration b).geometry.conformation
        (sourceIndexEquiv input.graph enumeration v) = input.conformation v := by
  rw [encodeFamily_geometry]
  exact sourceGeometry_conformation_apply input.graph enumeration input.conformation v

/-- Every attached real position lies on its band's surface. -/
theorem encodeFamily_attached_mem_surface (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex)
    (a : input.Attachment b) :
    input.conformation (input.atom b a) ∈ (encodeFamily input enumeration b).band.surface := by
  rw [encodeFamily_band]
  exact ⟨input.parameter b a, input.agreement b a⟩

/-- Attached positions of one band coincide exactly when their parameters are seam-related, with
the preserved seam mode. -/
theorem encodeFamily_attached_eq_iff_seamRel (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex)
    (a₁ a₂ : input.Attachment b) :
    (encodeFamily input enumeration b).geometry.conformation
        ((encodeFamily input enumeration b).atom (attachmentEnumeration input b a₁)) =
      (encodeFamily input enumeration b).geometry.conformation
        ((encodeFamily input enumeration b).atom (attachmentEnumeration input b a₂)) ↔
      SeamRel (encodeFamily input enumeration b).band.mode
        ((encodeFamily input enumeration b).parameter (attachmentEnumeration input b a₁))
        ((encodeFamily input enumeration b).parameter (attachmentEnumeration input b a₂)) :=
  (encodeFamily input enumeration b).attached_eq_iff_seamRel _ _

/-- Changing the source enumeration of the family leaves each member's retained band unchanged. -/
theorem encodeFamily_band_enumeration_invariant (input : IndependentBandAttachment V)
    (first second : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) :
    (encodeFamily input second b).band = (encodeFamily input first b).band := rfl

/-- Changing the source enumeration of the family leaves each member's parameter unchanged. -/
theorem encodeFamily_parameter_enumeration_invariant (input : IndependentBandAttachment V)
    (first second : V ≃ Fin (Fintype.card V)) (b : input.bandIndex)
    (a : input.Attachment b) :
    (encodeFamily input second b).parameter (attachmentEnumeration input b a) =
      (encodeFamily input first b).parameter (attachmentEnumeration input b a) := by
  rw [encodeFamily_parameter, encodeFamily_parameter]

/-- Changing the source enumeration of the family leaves the decoded atom label of each record
unchanged. -/
theorem encodeFamily_atom_decode_enumeration_invariant (input : IndependentBandAttachment V)
    (first second : V ≃ Fin (Fintype.card V)) (b : input.bandIndex)
    (a : input.Attachment b) :
    (sourceIndexEquiv input.graph second).symm
        ((encodeFamily input second b).atom (attachmentEnumeration input b a)) =
      (sourceIndexEquiv input.graph first).symm
        ((encodeFamily input first b).atom (attachmentEnumeration input b a)) := by
  rw [encodeFamily_atom_decode, encodeFamily_atom_decode]

/-- Changing the source enumeration of the family leaves the recovered whole-source geometry
unchanged at every atom label. -/
theorem encodeFamily_geometry_apply_enumeration_invariant (input : IndependentBandAttachment V)
    (first second : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) (v : V) :
    (encodeFamily input second b).geometry.conformation
        (sourceIndexEquiv input.graph second v) =
      (encodeFamily input first b).geometry.conformation
        (sourceIndexEquiv input.graph first v) := by
  rw [encodeFamily_geometry_apply, encodeFamily_geometry_apply]

/-- Enumerate the whole family by `Fin (Fintype.card bandIndex)`, as requested for a finite band
type.  The band type may be empty or may repeat one geometric band at several indices. -/
noncomputable def encodeAll (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin (@Fintype.card input.bandIndex input.fintypeBandIndex)) :
    CertifiedPartialBand (input.graph.certifiedEncoding enumeration) :=
  encodeFamily input enumeration ((bandEnumeration input).symm index)

/-- The enumerated family is the band family composed with the inverse band enumeration. -/
@[simp] theorem encodeAll_band (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin (@Fintype.card input.bandIndex input.fintypeBandIndex)) :
    (encodeAll input enumeration index).band =
      input.band ((bandEnumeration input).symm index) := rfl

/-- Every band index occurs in the `Fin`-enumerated family: the enumeration loses no band. -/
theorem encodeAll_complete (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) :
    ∃ index : Fin (@Fintype.card input.bandIndex input.fintypeBandIndex),
      encodeAll input enumeration index = encodeFamily input enumeration b := by
  refine ⟨bandEnumeration input b, ?_⟩
  simp [encodeAll]

/-- The `Fin`-enumerated family preserves every band's ledger length. -/
theorem encodeAll_attachmentCount (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin (@Fintype.card input.bandIndex input.fintypeBandIndex)) :
    (encodeAll input enumeration index).attachmentCount =
      @Fintype.card (input.Attachment ((bandEnumeration input).symm index))
        (input.fintypeAttachment ((bandEnumeration input).symm index)) := rfl

/-! ### Bundled encoded family: whole source and geometry retained once

`encodeAll` is a bare `Fin`-indexed family of partial bands.  When the band type is empty that
family has no member from which to recover the whole source or the whole conformation.  The bundle
below retains the certified source, the whole-source geometry, and the explicit label indexing as
part of the encoding itself, independently of the finite band family.  The finite family is stored
alongside, enumerated by `Fin bandCount`; original band indices are recovered through the explicit
`bandIndexEquiv`, so no literal inverse of an erased index type is claimed. -/

/-- A bundled encoding of one whole independent band-attachment input.  The certified source and
the whole-source geometry are stored once, separately from the finite band family, so the bundle
still contains the full source and conformation when `bandCount = 0`. -/
structure EncodedBandFamily (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) where
  /-- The certified source, retained once for the whole family. -/
  source : CertifiedAuthoritativeChemicalInput
  /-- The retained source is exactly the certified encoding of the input graph. -/
  source_eq : source = input.graph.certifiedEncoding enumeration
  /-- The whole-source geometry, retained once and covering every atom label. -/
  geometry : RealSourceGeometry source
  /-- Explicit indexing of the independent labels into the retained source. -/
  indexEquiv : V ≃ CertifiedSourceIndex source
  /-- The retained geometry reproduces the supplied conformation at every label. -/
  geometry_agrees : ∀ v : V, geometry.conformation (indexEquiv v) = input.conformation v
  /-- Number of encoded bands.  Zero is allowed. -/
  bandCount : ℕ
  /-- Explicit enumeration of the original band indices by `Fin bandCount`. -/
  bandIndexEquiv : Fin bandCount ≃ input.bandIndex
  /-- The finite family of partial bands over the one retained source. -/
  band : Fin bandCount → CertifiedPartialBand source
  /-- Each encoded band is the corresponding supplied geometric band. -/
  band_eq : ∀ index : Fin bandCount,
    (band index).band = input.band (bandIndexEquiv index)
  /-- Each encoded band's ledger length is the corresponding attachment type's cardinality. -/
  band_attachmentCount : ∀ index : Fin bandCount,
    (band index).attachmentCount =
      @Fintype.card (input.Attachment (bandIndexEquiv index))
        (input.fintypeAttachment (bandIndexEquiv index))

namespace EncodedBandFamily

variable {input : IndependentBandAttachment V} {enumeration : V ≃ Fin (Fintype.card V)}

/-- Decode the retained whole-source geometry back to the independent atom labels. -/
def decodeConformation (F : EncodedBandFamily input enumeration) : MolecularConformation V :=
  fun v => F.geometry.conformation (F.indexEquiv v)

/-- The bundle's decoder returns exactly the supplied conformation.  This is independent of the
number of bands, in particular of whether `bandCount` is zero. -/
theorem decodeConformation_eq (F : EncodedBandFamily input enumeration) :
    F.decodeConformation = input.conformation := by
  funext v
  exact F.geometry_agrees v

/-- The retained source is exactly the certified encoding of the input graph. -/
theorem source_recovery (F : EncodedBandFamily input enumeration) :
    F.source = input.graph.certifiedEncoding enumeration :=
  F.source_eq

/-- The retained whole-source geometry recovers the supplied position at every atom label. -/
theorem geometry_apply (F : EncodedBandFamily input enumeration) (v : V) :
    F.geometry.conformation (F.indexEquiv v) = input.conformation v :=
  F.geometry_agrees v

/-- Every input band index is represented in the finite family through the explicit enumeration. -/
theorem band_complete (F : EncodedBandFamily input enumeration) (b : input.bandIndex) :
    ∃ index : Fin F.bandCount, F.bandIndexEquiv index = b :=
  ⟨F.bandIndexEquiv.symm b, F.bandIndexEquiv.apply_symm_apply b⟩

end EncodedBandFamily

/-- Bundle the whole input: the certified source, the whole-source geometry, and the explicit label
indexing are retained once, together with the `Fin`-enumerated band family. -/
noncomputable def encodeBundled (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    EncodedBandFamily input enumeration where
  source := input.graph.certifiedEncoding enumeration
  source_eq := rfl
  geometry := sourceGeometry input.graph enumeration input.conformation
  indexEquiv := sourceIndexEquiv input.graph enumeration
  geometry_agrees := by
    intro v
    exact sourceGeometry_conformation_apply input.graph enumeration input.conformation v
  bandCount := @Fintype.card input.bandIndex input.fintypeBandIndex
  bandIndexEquiv := (bandEnumeration input).symm
  band := fun index => encodeAll input enumeration index
  band_eq := by
    intro index
    exact encodeAll_band input enumeration index
  band_attachmentCount := by
    intro index
    exact encodeAll_attachmentCount input enumeration index

@[simp] theorem encodeBundled_source (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (encodeBundled input enumeration).source = input.graph.certifiedEncoding enumeration := rfl

@[simp] theorem encodeBundled_geometry (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (encodeBundled input enumeration).geometry =
      sourceGeometry input.graph enumeration input.conformation := rfl

@[simp] theorem encodeBundled_indexEquiv (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (encodeBundled input enumeration).indexEquiv =
      sourceIndexEquiv input.graph enumeration := rfl

@[simp] theorem encodeBundled_bandCount (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (encodeBundled input enumeration).bandCount =
      @Fintype.card input.bandIndex input.fintypeBandIndex := rfl

@[simp] theorem encodeBundled_bandIndexEquiv (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (encodeBundled input enumeration).bandIndexEquiv = (bandEnumeration input).symm := rfl

@[simp] theorem encodeBundled_band (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin (@Fintype.card input.bandIndex input.fintypeBandIndex)) :
    (encodeBundled input enumeration).band index = encodeAll input enumeration index := rfl

/-- Each bundled band is exactly the corresponding member of the independent band family, so all
per-band preservation and recovery theorems apply unchanged. -/
theorem encodeBundled_band_eq_encodeFamily (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (b : input.bandIndex) :
    (encodeBundled input enumeration).band (bandEnumeration input b) =
      encodeFamily input enumeration b := by
  simp [encodeBundled, encodeAll]

/-- Whole-source recovery from the bundle, independent of the number of bands. -/
theorem encodeBundled_source_recovery (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (encodeBundled input enumeration).source = input.graph.certifiedEncoding enumeration :=
  EncodedBandFamily.source_recovery _

/-- Whole-geometry recovery from the bundle at every atom label, independent of the number of
bands and therefore valid also when there are no bands. -/
theorem encodeBundled_geometry_apply (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (v : V) :
    (encodeBundled input enumeration).geometry.conformation
        ((encodeBundled input enumeration).indexEquiv v) = input.conformation v :=
  EncodedBandFamily.geometry_apply _ v

/-- The bundle's decoder recovers the supplied conformation exactly. -/
theorem encodeBundled_decodeConformation (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (encodeBundled input enumeration).decodeConformation = input.conformation :=
  EncodedBandFamily.decodeConformation_eq _

/-- Retained atom count of the bundled source. -/
theorem encodeBundled_source_atomCount (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (encodeBundled input enumeration).source.input.molecule.atomCount = Fintype.card V :=
  input.graph.encode_atomCount enumeration

/-- Retained interaction count of the bundled source. -/
theorem encodeBundled_source_interactions_length (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (encodeBundled input enumeration).source.input.molecule.interactions.length =
      input.graph.interactions.length :=
  input.graph.encode_interactions_length enumeration

/-- Retained atom data of the bundled source at every enumeration index. -/
theorem encodeBundled_source_atomAt (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (index : Fin (Fintype.card V)) :
    listGet? (encodeBundled input enumeration).source.input.molecule.atoms index.val =
      some (input.graph.atomData (enumeration.symm index)) :=
  input.graph.certifiedEncoding_atomAt enumeration index

/-- Retained interaction kinds of the bundled source. -/
theorem encodeBundled_source_interactionKinds (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (encodeBundled input enumeration).source.input.molecule.interactions.map
        SemanticInteraction.kind =
      input.graph.interactions.map (fun edge => edge.2) :=
  input.graph.encode_interactionKinds enumeration

/-- The empty-band case: with no band index at all, the bundle still has zero bands and still
retains and recovers the entire certified source and the entire conformation. -/
theorem encodeBundled_empty_recovery (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) [IsEmpty input.bandIndex] (v : V) :
    (encodeBundled input enumeration).bandCount = 0 ∧
      (encodeBundled input enumeration).source = input.graph.certifiedEncoding enumeration ∧
      (encodeBundled input enumeration).geometry.conformation
        ((encodeBundled input enumeration).indexEquiv v) = input.conformation v := by
  refine ⟨?_, encodeBundled_source_recovery input enumeration, ?_⟩
  · rw [encodeBundled_bandCount]
    exact @Fintype.card_eq_zero input.bandIndex input.fintypeBandIndex ‹IsEmpty input.bandIndex›
  · exact encodeBundled_geometry_apply input enumeration v

end

end OrganicStereoIndependentBandEncoding
end OneCenter
end TetraStereo
