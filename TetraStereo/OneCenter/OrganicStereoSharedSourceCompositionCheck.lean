import TetraStereo.OneCenter.OrganicStereoSourceDataResidueAssembly
import TetraStereo.OneCenter.OrganicStereoLosslessDrawingBatchIngress
import TetraStereo.OneCenter.OrganicStereoBiochemicalAnnotationIngress
import TetraStereo.OneCenter.OrganicStereoCarbohydrateAnnotationIngress
import TetraStereo.OneCenter.OrganicStereoLipidAnnotationIngress
import TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress
import TetraStereo.OneCenter.OrganicStereoRetinoidHydrogenIngress
import TetraStereo.OneCenter.OrganicStereoRepeatResidueConstruction
import TetraStereo.OneCenter.OrganicStereoFischerChainSourceIngress

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoMolecularCanonicalTransport
open OrganicStereoSpatialSupportMolecularAssembly

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]
variable {Locant : Type*}

/-!
# One common request carrying residue source data, extra fragments and a drawing batch

This module composes three already-approved channels on **one and the same** actual
`OrganicMolecularEvidence V` request and one common enumeration
`eV : V ≃ Fin (Fintype.card V)`:

* the source-bound residue channel with ordered per-residue `FragmentSourceDatum` lists
  (`sourceDataAttachedRequest`);
* an additional ordered `List (FragmentAnnotation V)` appended after the request's existing
  fragment channel (`appendFragments`; the generic carrier inhabited by natural-product,
  carbohydrate, lipid, biochemical, hydrogen/repeat and other leaf outputs);
* one optional graph-bound lossless drawing batch (`attachSourceDrawingBatch`).

The composition is a single canonical assembly.  The output-only residue decoder, fragment decoder
and drawing decoder are all applied to that one actual canonical record, and the existing
request-level inverse shows that the original graph, conformation, electronic, path, band, role,
drawing, cage and frame channels are retained.  No chemical classifier, decoder assumption or raw
source-wrapper injectivity is added.
-/

/-! ## Literal ordered fragment append -/

/-- Append an ordered fragment list after a request's existing fragment channel.  This is a
literal structure update: no deduplication, sorting or interpretation is performed. -/
def appendFragments (request : OrganicMolecularEvidence V)
    (fragments : List (FragmentAnnotation V)) : OrganicMolecularEvidence V :=
  { request with fragments := request.fragments ++ fragments }

@[simp] theorem appendFragments_fragments (request : OrganicMolecularEvidence V)
    (fragments : List (FragmentAnnotation V)) :
    (appendFragments request fragments).fragments = request.fragments ++ fragments := rfl

@[simp] theorem appendFragments_graph (request : OrganicMolecularEvidence V)
    (fragments : List (FragmentAnnotation V)) :
    (appendFragments request fragments).graph = request.graph := rfl

@[simp] theorem appendFragments_conformation (request : OrganicMolecularEvidence V)
    (fragments : List (FragmentAnnotation V)) :
    (appendFragments request fragments).conformation = request.conformation := rfl

@[simp] theorem appendFragments_conventions (request : OrganicMolecularEvidence V)
    (fragments : List (FragmentAnnotation V)) :
    (appendFragments request fragments).conventions = request.conventions := rfl

@[simp] theorem appendFragments_residueLedger? (request : OrganicMolecularEvidence V)
    (fragments : List (FragmentAnnotation V)) :
    (appendFragments request fragments).residueLedger? = request.residueLedger? := rfl

/-! ## The two composition stages and the common request -/

/-- Stage one: the source-data-attached request with the additional ordered fragment list
appended.  The residue channel, graph and every non-fragment channel are the source-data ones. -/
def sharedFragmentRequest (codec : LocantCodec Locant) (eV : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V)) : OrganicMolecularEvidence V :=
  appendFragments
    (sourceDataAttachedRequest codec eV request ledger cover sourceData supported) extraFragments

/-- Stage two: the same request with exactly one fresh lossless drawing-source record appended.
`batch? = none` leaves the fresh cue channel absent, `some batch` (including an empty batch) makes
it present. -/
def sharedComposedRequest (codec : LocantCodec Locant) (eV : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) : OrganicMolecularEvidence V :=
  attachSourceDrawingBatch
    (sharedFragmentRequest codec eV request ledger cover sourceData supported extraFragments) batch?

@[simp] theorem sharedFragmentRequest_fragments (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V)) :
    (sharedFragmentRequest codec eV request ledger cover sourceData supported
        extraFragments).fragments = request.fragments ++ extraFragments := rfl

@[simp] theorem sharedFragmentRequest_graph (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V)) :
    (sharedFragmentRequest codec eV request ledger cover sourceData supported
        extraFragments).graph = request.graph := rfl

@[simp] theorem sharedFragmentRequest_conventions (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V)) :
    (sharedFragmentRequest codec eV request ledger cover sourceData supported
        extraFragments).conventions = request.conventions := rfl

@[simp] theorem sharedFragmentRequest_residueLedger? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V)) :
    (sharedFragmentRequest codec eV request ledger cover sourceData supported
        extraFragments).residueLedger? =
      some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) := rfl

@[simp] theorem sharedComposedRequest_fragments (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
        batch?).fragments = request.fragments ++ extraFragments := rfl

@[simp] theorem sharedComposedRequest_graph (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
        batch?).graph = request.graph := rfl

@[simp] theorem sharedComposedRequest_conventions (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
        batch?).conventions = request.conventions ++ [freshDrawingSource batch?] := rfl

@[simp] theorem sharedComposedRequest_residueLedger? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
        batch?).residueLedger? =
      some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) := rfl

/-- **One common request, three channels.**  The residue channel is the derived source-data
channel, the ordered fragment list is the original list followed by the extra list, and the
convention channel is the original list followed by the single fresh drawing record.  Every other
original channel is retained literally. -/
theorem sharedComposedRequest_retention (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
        batch?).residueLedger? =
        some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).graph = request.graph ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).conformation = request.conformation ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).rationalPositions? = request.rationalPositions? ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).electronic? = request.electronic? ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).paths? = request.paths? ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).bands? = request.bands? ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).roles = request.roles ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).diagram? = request.diagram? ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).diagramPartial? = request.diagramPartial? ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).diagramIncidence = request.diagramIncidence ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).cages = request.cages ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).frames = request.frames ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).fragments = request.fragments ++ extraFragments ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).conventions = request.conventions ++ [freshDrawingSource batch?] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Explicit fresh and existing-ledger policies -/

/-- Fresh ledger case: the request carries no residue channel (`none` is explicit), and the
composed request carries exactly the derived source-data channel.  The intermediate source-data
attachment satisfies the existing `SourceDataAttachmentPolicy`. -/
theorem sharedComposedRequest_fresh_ledger (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph))
    (fresh : request.residueLedger? = none) :
    request.residueLedger? = none ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).residueLedger? =
        some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) ∧
      SourceDataAttachmentPolicy request
        (sourceDataAttachedRequest codec eV request ledger cover sourceData supported)
        (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) :=
  ⟨fresh, rfl, attachSourceDataResidueLedgerRequest_policy request _⟩

/-- Existing-ledger case: a previously supplied optional ledger is **superseded**, not merged, in
the single `residueLedger?` field; the actual attachment policy records every other retained
channel.  The later fragment append and drawing attachment retain that derived channel. -/
theorem sharedComposedRequest_existing_ledger (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph))
    (old : ResidueLedgerChannel V) (existing : request.residueLedger? = some old) :
    request.residueLedger? = some old ∧
      (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
          batch?).residueLedger? =
        some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) ∧
      SourceDataAttachmentPolicy request
        (sourceDataAttachedRequest codec eV request ledger cover sourceData supported)
        (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) :=
  ⟨existing, rfl, attachSourceDataResidueLedgerRequest_policy request _⟩

/-! ## The single actual canonical output -/

/-- The actual canonical output of the one common composed request. -/
def sharedComposedCanonicalOutput (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    CanonicalOrganicMolecularRepresentation V :=
  canonicalAssemble eV
    (sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments batch?)

/-- The canonical output graph is the common relabelling of the original request graph. -/
theorem sharedComposedCanonicalOutput_graph (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
        extraFragments batch?).state.graph = relabelGraph eV request.graph := by
  unfold sharedComposedCanonicalOutput
  rw [canonicalAssemble_state_graph, sharedComposedRequest_graph]

/-! ## Decoder one: the residue channel and its ordered source-data lists -/

/-- General output-only residue-channel readback for any request. -/
theorem sourceDataResidueChannel?_canonicalAssemble (eV : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    sourceDataResidueChannel? (canonicalAssemble eV request) = request.residueLedger? := by
  unfold sourceDataResidueChannel?
  rw [canonicalDecode_canonicalAssemble]
  exact (assemble_annotation_projections request).2.2.2.2.2.2.2.2.1

/-- The existing canonical-output-only residue decoder recovers the full source-data channel. -/
theorem sharedComposedCanonicalOutput_residueChannel? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    sourceDataResidueChannel?
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?) =
      some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) := by
  unfold sharedComposedCanonicalOutput
  rw [sourceDataResidueChannel?_canonicalAssemble, sharedComposedRequest_residueLedger?]

/-- Every ordered per-residue source-data list is recovered from the same actual output.  The
equality is at the list-of-lists level, so order, multiplicity and every datum payload are
retained. -/
theorem sharedComposedCanonicalOutput_sourceDataLists (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    decodedSourceDataLists?
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?) = some (List.ofFn sourceData) := by
  unfold decodedSourceDataLists?
  rw [sharedComposedCanonicalOutput_residueChannel?]
  simp only [Option.map_some, Option.some.injEq]
  apply List.ofFn_inj.mpr
  funext index
  exact sourceDataBoundChannel_residue_sourceData codec eV request.graph ledger cover sourceData
    supported index

/-- Positional ordered source-data readback at every residue (duplicates preserved). -/
theorem sharedComposedCanonicalOutput_sourceDataAt (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) (index : Fin ledger.residueCount) :
    (decodedSourceDataLists?
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?)).bind (fun lists => lists[index.val]?) =
      some (sourceData index) := by
  rw [sharedComposedCanonicalOutput_sourceDataLists, Option.bind_some, List.getElem?_ofFn,
    dif_pos index.isLt]

/-! ## Decoder two: the appended ordered fragment channel -/

/-- Canonical-output-only fragment decoder: it reads only the actual canonical record through the
existing full request decoder, never an original request or leaf payload. -/
def decodedComposedFragments (canonical : CanonicalOrganicMolecularRepresentation V) :
    List (FragmentAnnotation V) :=
  (decode (canonicalDecode canonical)).fragments

/-- The fragment decoder recovers the original list followed by the extra list, in order and with
multiplicity. -/
theorem decodedComposedFragments_sharedComposedCanonicalOutput (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    decodedComposedFragments
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?) = request.fragments ++ extraFragments := by
  unfold decodedComposedFragments sharedComposedCanonicalOutput
  rw [decode_canonicalAssemble, sharedComposedRequest_fragments]

/-- The original fragment channel is the exact prefix of the recovered list. -/
theorem decodedComposedFragments_sharedComposedCanonicalOutput_oldPrefix
    (codec : LocantCodec Locant) (eV : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (decodedComposedFragments
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?)).take request.fragments.length = request.fragments := by
  rw [decodedComposedFragments_sharedComposedCanonicalOutput, List.take_left]

/-- The extra fragment list is the exact suffix, selected at the explicit external boundary
`request.fragments.length`. -/
theorem decodedComposedFragments_sharedComposedCanonicalOutput_newSuffix
    (codec : LocantCodec Locant) (eV : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (decodedComposedFragments
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?)).drop request.fragments.length = extraFragments := by
  rw [decodedComposedFragments_sharedComposedCanonicalOutput, List.drop_left]

/-! ## Decoder three: the optional lossless drawing batch -/

/-- The existing canonical-output-only drawing decoder recovers the exact prior convention
channel and the optional compiled batch payload from the same actual output. -/
theorem sharedComposedCanonicalOutput_drawing (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    decodeDrawingBatchFromCanonical
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?) =
      (request.conventions,
        batch?.map (fun batch =>
          ({ glyphs := compileSuppliedGlyphs request.graph batch.glyphs,
             crossings := compileBatchCrossings request.graph batch.glyphs 0 batch.crossings } :
            DecodedDrawingBatch V))) := by
  unfold sharedComposedCanonicalOutput sharedComposedRequest
  rw [decodeDrawingBatchFromCanonical_canonicalAssemble, sharedFragmentRequest_conventions]
  rfl

/-- The prior convention channel is recovered exactly. -/
theorem sharedComposedCanonicalOutput_priorConventions (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (decodeDrawingBatchFromCanonical
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?)).1 = request.conventions := by
  rw [sharedComposedCanonicalOutput_drawing]

/-- Genuine absence is retained: no supplied batch decodes to `none`, not to an empty payload. -/
theorem sharedComposedCanonicalOutput_drawing_none (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V)) :
    (decodeDrawingBatchFromCanonical
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments none)).2 = none := by
  rw [sharedComposedCanonicalOutput_drawing]
  rfl

/-- A supplied empty batch is retained as present-empty (`some {glyphs := [], crossings := []}`),
distinct from absence. -/
theorem sharedComposedCanonicalOutput_drawing_present_empty (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V)) :
    (decodeDrawingBatchFromCanonical
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments
          (some (⟨[], []⟩ : SuppliedDrawingBatch request.graph)))).2 =
      some ({ glyphs := [], crossings := [] } : DecodedDrawingBatch V) := by
  rw [sharedComposedCanonicalOutput_drawing]
  simp [compileSuppliedGlyphs, compileBatchCrossings, compileSuppliedCrossings]

/-! ## Joint recovery and original-channel retention -/

/-- The existing request-level inverse applied to the composed request. -/
theorem sharedComposedCanonicalOutput_decode (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?)) =
      sharedComposedRequest codec eV request ledger cover sourceData supported extraFragments
        batch? := by
  unfold sharedComposedCanonicalOutput
  exact decode_canonicalAssemble eV _

/-- The output-only decode retains every original non-annotated physical/channel field. -/
theorem sharedComposedCanonicalOutput_retains_original (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).graph = request.graph ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).conformation = request.conformation ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).rationalPositions? = request.rationalPositions? ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).electronic? = request.electronic? ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).paths? = request.paths? ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).bands? = request.bands? ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).roles = request.roles ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).cages = request.cages ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).frames = request.frames := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [sharedComposedCanonicalOutput_decode] <;> rfl

/-- **Joint composition result.**  The single actual canonical output supports, simultaneously:

* the existing residue-channel decoder, recovering the full source-data channel;
* the ordered source-data-list decoder (all residues, duplicates and payloads preserved);
* the appended ordered fragment channel with its exact old prefix and new suffix;
* the existing drawing decoder, recovering the prior convention channel and the optional compiled
  batch (`none` versus present-empty retained separately by the dedicated theorems above);
* the original graph, conformation, electronic, path, band, role, cage and frame channels.

No decoder receives the original request; the specification facts are stated separately. -/
theorem sharedComposedCanonicalOutput_recovery (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    sourceDataResidueChannel?
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?) =
        some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) ∧
      decodedSourceDataLists?
          (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
            extraFragments batch?) = some (List.ofFn sourceData) ∧
      (∀ index : Fin ledger.residueCount,
        (decodedSourceDataLists?
            (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
              extraFragments batch?)).bind (fun lists => lists[index.val]?) =
          some (sourceData index)) ∧
      decodedComposedFragments
          (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
            extraFragments batch?) = request.fragments ++ extraFragments ∧
      (decodedComposedFragments
          (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
            extraFragments batch?)).take request.fragments.length = request.fragments ∧
      (decodedComposedFragments
          (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
            extraFragments batch?)).drop request.fragments.length = extraFragments ∧
      decodeDrawingBatchFromCanonical
          (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
            extraFragments batch?) =
        (request.conventions,
          batch?.map (fun batch =>
            ({ glyphs := compileSuppliedGlyphs request.graph batch.glyphs,
               crossings := compileBatchCrossings request.graph batch.glyphs 0 batch.crossings } :
              DecodedDrawingBatch V))) ∧
      (decodeDrawingBatchFromCanonical
          (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
            extraFragments batch?)).1 = request.conventions ∧
      ((decode (canonicalDecode
          (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
            extraFragments batch?))).graph = request.graph ∧
        (decode (canonicalDecode
          (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
            extraFragments batch?))).conformation = request.conformation ∧
        (decode (canonicalDecode
          (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
            extraFragments batch?))).electronic? = request.electronic? ∧
        (decode (canonicalDecode
          (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
            extraFragments batch?))).paths? = request.paths? ∧
        (decode (canonicalDecode
          (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
            extraFragments batch?))).bands? = request.bands? ∧
        (decode (canonicalDecode
          (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
            extraFragments batch?))).roles = request.roles) := by
  refine ⟨sharedComposedCanonicalOutput_residueChannel? codec eV request ledger cover sourceData
      supported extraFragments batch?,
    sharedComposedCanonicalOutput_sourceDataLists codec eV request ledger cover sourceData
      supported extraFragments batch?, ?_,
    decodedComposedFragments_sharedComposedCanonicalOutput codec eV request ledger cover sourceData
      supported extraFragments batch?,
    decodedComposedFragments_sharedComposedCanonicalOutput_oldPrefix codec eV request ledger cover
      sourceData supported extraFragments batch?,
    decodedComposedFragments_sharedComposedCanonicalOutput_newSuffix codec eV request ledger cover
      sourceData supported extraFragments batch?,
    sharedComposedCanonicalOutput_drawing codec eV request ledger cover sourceData supported
      extraFragments batch?,
    sharedComposedCanonicalOutput_priorConventions codec eV request ledger cover sourceData
      supported extraFragments batch?, ?_⟩
  · intro index
    exact sharedComposedCanonicalOutput_sourceDataAt codec eV request ledger cover sourceData
      supported extraFragments batch? index
  · have retained := sharedComposedCanonicalOutput_retains_original codec eV request ledger cover
      sourceData supported extraFragments batch?
    exact ⟨retained.1, retained.2.1, retained.2.2.2.1, retained.2.2.2.2.1,
      retained.2.2.2.2.2.1, retained.2.2.2.2.2.2.1⟩

/-- The actual output decode carries exactly the derived channel, the appended fragment list and
the augmented convention channel, while retaining the original request's other fields.  The
intermediate source-data attachment policy is included explicitly. -/
theorem sharedComposedCanonicalOutput_decode_policy (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).residueLedger? =
        some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).graph = request.graph ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).conformation = request.conformation ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).electronic? = request.electronic? ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).paths? = request.paths? ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).bands? = request.bands? ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).roles = request.roles ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).fragments = request.fragments ++ extraFragments ∧
      (decode (canonicalDecode
        (sharedComposedCanonicalOutput codec eV request ledger cover sourceData supported
          extraFragments batch?))).conventions =
        request.conventions ++ [freshDrawingSource batch?] ∧
      SourceDataAttachmentPolicy request
        (sourceDataAttachedRequest codec eV request ledger cover sourceData supported)
        (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, attachSourceDataResidueLedgerRequest_policy request _⟩
  all_goals
    rw [sharedComposedCanonicalOutput_decode]
    rfl

/-! ## Same-ledger `oldData ++ newData` specialization

This reuses the already-approved same-ledger append endpoint of
`OrganicStereoSourceDataResidueAssembly`: no second ledger or encoding is introduced.  The explicit
input tie `request.residueLedger? = some (sourceDataBoundChannel ... oldData oldSupported)` states
that the existing residue annotations are on the *same* actual ledger, so `oldData` is retained as
the exact prefix rather than replaced. -/

/-- The common composed request specialized to the existing same-ledger append policy.  The
residue channel carries `oldData i ++ newData i` at every residue of the one actual ledger. -/
def sharedComposedSameLedgerRequest (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger newData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) : OrganicMolecularEvidence V :=
  sharedComposedRequest codec eV request ledger cover
    (fun index => oldData index ++ newData index)
    (sourceDataSupported_append request.graph eV ledger oldData newData oldSupported newSupported)
    extraFragments batch?

/-- The actual canonical output of the same-ledger specialization. -/
def sharedComposedSameLedgerCanonicalOutput (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger newData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    CanonicalOrganicMolecularRepresentation V :=
  sharedComposedCanonicalOutput codec eV request ledger cover
    (fun index => oldData index ++ newData index)
    (sourceDataSupported_append request.graph eV ledger oldData newData oldSupported newSupported)
    extraFragments batch?

/-- **Same-ledger composition beside existing residue annotations.**  Under the explicit
structural tie to the old channel on the same actual ledger, the one actual canonical output:

* carries the coexisting channel (old links/support/bindings/hierarchy unchanged);
* decodes every ordered list as `oldData i ++ newData i`;
* recovers `oldData` as the exact prefix and `newData` as the exact suffix at every residue;
* simultaneously recovers the appended fragment channel and the prior drawing conventions.

This is the same composition result as `sharedComposedCanonicalOutput_recovery`, instantiated with
`sourceDataSupported_append`; no assumption about any output decoder is made. -/
theorem sharedComposedSameLedgerCanonicalOutput_recovery (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger newData)
    (extraFragments : List (FragmentAnnotation V))
    (batch? : Option (SuppliedDrawingBatch request.graph))
    (existing : request.residueLedger? =
      some (sourceDataBoundChannel codec eV request.graph ledger cover oldData oldSupported)) :
    request.residueLedger? =
        some (sourceDataBoundChannel codec eV request.graph ledger cover oldData oldSupported) ∧
      sourceDataResidueChannel?
          (sharedComposedSameLedgerCanonicalOutput codec eV request ledger cover oldData newData
            oldSupported newSupported extraFragments batch?) =
        some (sourceDataCoexistingChannel codec eV request.graph ledger cover oldData newData
          oldSupported newSupported) ∧
      decodedSourceDataLists?
          (sharedComposedSameLedgerCanonicalOutput codec eV request ledger cover oldData newData
            oldSupported newSupported extraFragments batch?) =
        some (List.ofFn fun index : Fin ledger.residueCount => oldData index ++ newData index) ∧
      (∀ index : Fin ledger.residueCount,
        Option.map (fun data => data.take (oldData index).length)
            ((decodedSourceDataLists?
              (sharedComposedSameLedgerCanonicalOutput codec eV request ledger cover oldData newData
                oldSupported newSupported extraFragments batch?)).bind
              (fun lists => lists[index.val]?)) = some (oldData index) ∧
        Option.map (fun data => data.drop (oldData index).length)
            ((decodedSourceDataLists?
              (sharedComposedSameLedgerCanonicalOutput codec eV request ledger cover oldData newData
                oldSupported newSupported extraFragments batch?)).bind
              (fun lists => lists[index.val]?)) = some (newData index)) ∧
      decodedComposedFragments
          (sharedComposedSameLedgerCanonicalOutput codec eV request ledger cover oldData newData
            oldSupported newSupported extraFragments batch?) =
        request.fragments ++ extraFragments ∧
      (decodeDrawingBatchFromCanonical
          (sharedComposedSameLedgerCanonicalOutput codec eV request ledger cover oldData newData
            oldSupported newSupported extraFragments batch?)).1 = request.conventions := by
  refine ⟨existing, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [sharedComposedSameLedgerCanonicalOutput, sourceDataCoexistingChannel] using
      sharedComposedCanonicalOutput_residueChannel? codec eV request ledger cover
        (fun index => oldData index ++ newData index)
        (sourceDataSupported_append request.graph eV ledger oldData newData oldSupported newSupported)
        extraFragments batch?
  · simpa [sharedComposedSameLedgerCanonicalOutput] using
      sharedComposedCanonicalOutput_sourceDataLists codec eV request ledger cover
        (fun index => oldData index ++ newData index)
        (sourceDataSupported_append request.graph eV ledger oldData newData oldSupported newSupported)
        extraFragments batch?
  · intro index
    have hAt := sharedComposedCanonicalOutput_sourceDataAt codec eV request ledger cover
      (fun index => oldData index ++ newData index)
      (sourceDataSupported_append request.graph eV ledger oldData newData oldSupported newSupported)
      extraFragments batch? index
    constructor
    · simpa [sharedComposedSameLedgerCanonicalOutput, List.take_left] using
        congrArg (Option.map (fun data => data.take (oldData index).length)) hAt
    · simpa [sharedComposedSameLedgerCanonicalOutput, List.drop_left] using
        congrArg (Option.map (fun data => data.drop (oldData index).length)) hAt
  · simpa [sharedComposedSameLedgerCanonicalOutput] using
      decodedComposedFragments_sharedComposedCanonicalOutput codec eV request ledger cover
        (fun index => oldData index ++ newData index)
        (sourceDataSupported_append request.graph eV ledger oldData newData oldSupported newSupported)
        extraFragments batch?
  · simpa [sharedComposedSameLedgerCanonicalOutput] using
      sharedComposedCanonicalOutput_priorConventions codec eV request ledger cover
        (fun index => oldData index ++ newData index)
        (sourceDataSupported_append request.graph eV ledger oldData newData oldSupported newSupported)
        extraFragments batch?

end

end TetraStereo.OneCenter

/-! The composed-channel, output-only recovery and retention results are kernel checked. -/
assert_kernel_only TetraStereo.OneCenter.sharedComposedRequest_retention
assert_kernel_only TetraStereo.OneCenter.sharedComposedRequest_fresh_ledger
assert_kernel_only TetraStereo.OneCenter.sharedComposedRequest_existing_ledger
assert_kernel_only TetraStereo.OneCenter.sharedComposedCanonicalOutput_graph
assert_kernel_only TetraStereo.OneCenter.sharedComposedCanonicalOutput_residueChannel?
assert_kernel_only TetraStereo.OneCenter.sharedComposedCanonicalOutput_sourceDataLists
assert_kernel_only TetraStereo.OneCenter.sharedComposedCanonicalOutput_sourceDataAt
assert_kernel_only TetraStereo.OneCenter.decodedComposedFragments_sharedComposedCanonicalOutput
assert_kernel_only TetraStereo.OneCenter.decodedComposedFragments_sharedComposedCanonicalOutput_oldPrefix
assert_kernel_only TetraStereo.OneCenter.decodedComposedFragments_sharedComposedCanonicalOutput_newSuffix
assert_kernel_only TetraStereo.OneCenter.sharedComposedCanonicalOutput_drawing
assert_kernel_only TetraStereo.OneCenter.sharedComposedCanonicalOutput_priorConventions
assert_kernel_only TetraStereo.OneCenter.sharedComposedCanonicalOutput_drawing_none
assert_kernel_only TetraStereo.OneCenter.sharedComposedCanonicalOutput_drawing_present_empty
assert_kernel_only TetraStereo.OneCenter.sharedComposedCanonicalOutput_decode
assert_kernel_only TetraStereo.OneCenter.sharedComposedCanonicalOutput_retains_original
assert_kernel_only TetraStereo.OneCenter.sharedComposedCanonicalOutput_recovery
assert_kernel_only TetraStereo.OneCenter.sharedComposedCanonicalOutput_decode_policy
assert_kernel_only TetraStereo.OneCenter.sharedComposedSameLedgerCanonicalOutput_recovery
