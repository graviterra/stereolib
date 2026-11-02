import TetraStereo.OneCenter.OrganicStereoAuthorityMixedSourceAssembly
import TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly
import TetraStereo.OneCenter.OrganicStereoAuthoritativeInformationIngress
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

open OrganicStereoMolecularEvidenceAssembly

namespace OrganicStereoCertifiedSourceCoreCompletion

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-!
# Certified authoritative source completion of the independent molecular core

This module supplies the missing bridge from the *old* authoritative source vocabulary
(`CertifiedAuthoritativeChemicalInput`, `AuthoritativeChemicalInput`) to the *current* joint
independent molecular core (`OrganicMolecularEvidence`).

For an arbitrary certified input `certified`, the existing ingress
`CertifiedAuthoritativeChemicalInput.decode` produces an independent-label finite source over
`Fin certified.input.molecule.atomCount`.  The construction below turns that source into an actual
`OrganicMolecularEvidence`:

* the interaction graph is the decoded graph;
* the shared real conformation is the actual `canonicalConformation` of the decoded source (the
  existing declaration `TetraStereo.OneCenter.canonicalConformation`, with its membership lemma
  `canonicalConformation_mem` supplying the whole-state rational-position agreement);
* the optional rational spatial channel is the decoded `spatial?` channel (`none` stays `none`,
  `some` stays `some`);
* the optional drawing channel is the decoded `diagram?` channel (`none` stays `none`, `some`
  stays `some`, including every ordered bond occurrence and every atom-parity token);
* every unrelated optional channel (electronic inventory, bond paths, bands, roles, partial
  drawing positions, incidence ledger, fragments, conventions, cages, residue ledger, frames) is
  genuinely absent or empty.  These absences are witnesses that nothing was smuggled in, not
  chemical judgments.

The main results are:

* `recoveredSource_constructedCore`: the **existing** upstream `recoveredSource` of the
  constructed core at the identity enumeration is exactly `certified.input`;
* `recoveredSource_constructedCore_structurallyWellFormed`: that recovered source is actually
  structurally well formed (the certificate is transported, never re-derived from chemistry);
* `decoded_core_source`: the same equality still holds **after** the actual canonical transport
  `canonicalAssemble` followed by `decodedCore`.

No original certified input, source record or request is stored inside the constructed core, and
no inverse, agreement or codec-round-trip premise is assumed: all three equalities are derived
from the existing `encode_decode` and `decode_canonicalAssemble` theorems.

The construction is representation-only.  It never claims chemical admissibility, IUPAC
applicability, descriptor values or an executable CIP decision.
-/

/-! ## The constructed independent molecular core -/

/-- The independent molecular core of a certified authoritative input.  The atom carrier is the
decoded atom carrier `Fin atomCount`; the graph, rational spatial channel and drawing channel are
copied literally from the existing `CertifiedAuthoritativeChemicalInput.decode` ingress; the shared
conformation is the existing canonical conformation of that source.  All unrelated optional
channels are absent/empty. -/
def constructedCore (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicMolecularEvidence (Fin certified.input.molecule.atomCount) where
  graph := (CertifiedAuthoritativeChemicalInput.decode certified).graph
  conformation := canonicalConformation (CertifiedAuthoritativeChemicalInput.decode certified)
  rationalPositions? := (CertifiedAuthoritativeChemicalInput.decode certified).spatial?
  rationalPositions_valid :=
    canonicalConformation_mem (CertifiedAuthoritativeChemicalInput.decode certified)
  electronic? := none
  electronic_unpaired := by
    intro evidence present
    cases present
  paths? := none
  paths_graph_eq := by
    intro family present
    cases present
  paths_conformation_eq := by
    intro family present
    cases present
  bands? := none
  bands_graph_eq := by
    intro bands present
    cases present
  bands_conformation_eq := by
    intro bands present
    cases present
  roles := []
  role_valid := by
    intro annotation member
    simp at member
  diagram? := (CertifiedAuthoritativeChemicalInput.decode certified).diagram?
  diagramPartial? := none
  diagramIncidence := []
  diagram_valid := by
    intro row member
    simp at member
  fragments := []
  conventions := []
  cages := []
  residueLedger? := none
  frames := []

/-- The identity enumeration on the constructed atom carrier.  It is the existing
`identityEnumeration` of the decoded atom count, so re-encoding at it preserves the underlying
natural index. -/
def constructedEnumeration (certified : CertifiedAuthoritativeChemicalInput) :
    Fin certified.input.molecule.atomCount ≃
      Fin (Fintype.card (Fin certified.input.molecule.atomCount)) :=
  identityEnumeration certified.input.molecule.atomCount

@[simp] theorem constructedEnumeration_apply_val
    (certified : CertifiedAuthoritativeChemicalInput)
    (index : Fin certified.input.molecule.atomCount) :
    (constructedEnumeration certified index).val = index.val := rfl

@[simp] theorem constructedEnumeration_symm_apply_val
    (certified : CertifiedAuthoritativeChemicalInput)
    (index : Fin (Fintype.card (Fin certified.input.molecule.atomCount))) :
    ((constructedEnumeration certified).symm index).val = index.val := rfl

/-! ## The reconstructed authoritative source

`recoveredSource` is the upstream reconstructed-source map: it is the existing
`OrganicStereoAuthorityMixedSourceAssembly.recoveredAcyclicSource`, i.e. the encoding of the
core's finite source (graph, optional rational coordinates, optional drawing data) at the supplied
enumeration.  This is exactly the definition abbreviated upstream as
`recoveredSource`; it is re-exported here under the stable name so
that this module depends only on the accepted lower-level assembly (`OrganicStereoAllAuthorityEntries`
is currently under repair elsewhere and is not imported).  Because the alias is definitional, any
downstream occurrence of the upstream name is definitionally equal to this one. -/
abbrev recoveredSource (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : AuthoritativeChemicalInput :=
  OrganicStereoAuthorityMixedSourceAssembly.recoveredAcyclicSource core enumeration

/-! ## Definitional projections of the constructed core -/

/-- The constructed graph is exactly the decoded graph. -/
@[simp] theorem constructedCore_graph (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).graph =
      (CertifiedAuthoritativeChemicalInput.decode certified).graph := rfl

/-- The constructed conformation is the existing canonical conformation of the decoded source. -/
@[simp] theorem constructedCore_conformation
    (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).conformation =
      canonicalConformation (CertifiedAuthoritativeChemicalInput.decode certified) := rfl

/-- The constructed rational spatial channel is exactly the decoded spatial channel. -/
@[simp] theorem constructedCore_rationalPositions?
    (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).rationalPositions? =
      (CertifiedAuthoritativeChemicalInput.decode certified).spatial? := rfl

/-- The constructed drawing channel is exactly the decoded drawing channel. -/
@[simp] theorem constructedCore_diagram?
    (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).diagram? =
      (CertifiedAuthoritativeChemicalInput.decode certified).diagram? := rfl

/-- The constructed electronic channel is absent. -/
@[simp] theorem constructedCore_electronic?
    (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).electronic? = none := rfl

/-- The constructed bond-path channel is absent. -/
@[simp] theorem constructedCore_paths?
    (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).paths? = none := rfl

/-- The constructed band channel is absent. -/
@[simp] theorem constructedCore_bands?
    (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).bands? = none := rfl

/-- The constructed ordered role ledger is empty. -/
@[simp] theorem constructedCore_roles (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).roles = [] := rfl

/-- The constructed sparse partial drawing positions are absent. -/
@[simp] theorem constructedCore_diagramPartial?
    (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).diagramPartial? = none := rfl

/-- The constructed sparse incidence ledger is empty. -/
@[simp] theorem constructedCore_diagramIncidence
    (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).diagramIncidence = [] := rfl

/-- The constructed fragment channel is empty. -/
@[simp] theorem constructedCore_fragments (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).fragments = [] := rfl

/-- The constructed drawing-convention channel is empty. -/
@[simp] theorem constructedCore_conventions (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).conventions = [] := rfl

/-- The constructed cage-annotation channel is empty. -/
@[simp] theorem constructedCore_cages (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).cages = [] := rfl

/-- The constructed residue ledger is absent. -/
@[simp] theorem constructedCore_residueLedger?
    (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).residueLedger? = none := rfl

/-- The constructed frame-annotation channel is empty. -/
@[simp] theorem constructedCore_frames (certified : CertifiedAuthoritativeChemicalInput) :
    (constructedCore certified).frames = [] := rfl

/-! ## The finite source carried by the constructed core -/

/-- The finite source of the constructed core is exactly the decoded source.  This is the
definitional graph/spatial/diagram tie: the core carries precisely the decoded channels and no
others. -/
theorem coreFiniteSource_constructedCore (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource (constructedCore certified) =
      CertifiedAuthoritativeChemicalInput.decode certified := rfl

/-- The constructed core's finite source graph is the decoded graph. -/
theorem coreFiniteSource_constructedCore_graph
    (certified : CertifiedAuthoritativeChemicalInput) :
    (OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource
      (constructedCore certified)).graph =
      (CertifiedAuthoritativeChemicalInput.decode certified).graph := by
  rw [coreFiniteSource_constructedCore]

/-- The constructed core's finite source spatial channel is the decoded spatial channel. -/
theorem coreFiniteSource_constructedCore_spatial?
    (certified : CertifiedAuthoritativeChemicalInput) :
    (OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource
      (constructedCore certified)).spatial? =
      (CertifiedAuthoritativeChemicalInput.decode certified).spatial? := by
  rw [coreFiniteSource_constructedCore]

/-- The constructed core's finite source drawing channel is the decoded drawing channel. -/
theorem coreFiniteSource_constructedCore_diagram?
    (certified : CertifiedAuthoritativeChemicalInput) :
    (OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource
      (constructedCore certified)).diagram? =
      (CertifiedAuthoritativeChemicalInput.decode certified).diagram? := by
  rw [coreFiniteSource_constructedCore]

/-! ## Recovery of the certified input through the existing `recoveredSource` -/

/-- **Main reconstruction theorem.**  The existing upstream `recoveredSource` of the constructed
core at the identity enumeration is exactly the certified input.  The proof is the existing
`encode_decode` round trip, not a new codec and not an assumed inverse. -/
theorem recoveredSource_constructedCore (certified : CertifiedAuthoritativeChemicalInput) :
    recoveredSource (constructedCore certified)
        (constructedEnumeration certified) = certified.input := by
  unfold recoveredSource
    OrganicStereoAuthorityMixedSourceAssembly.recoveredAcyclicSource
  rw [coreFiniteSource_constructedCore]
  simpa [constructedEnumeration] using
    CertifiedAuthoritativeChemicalInput.encode_decode certified

/-- The molecule projection of the recovered source is the certified molecule. -/
theorem recoveredSource_constructedCore_molecule
    (certified : CertifiedAuthoritativeChemicalInput) :
    (recoveredSource (constructedCore certified)
        (constructedEnumeration certified)).molecule = certified.input.molecule := by
  rw [recoveredSource_constructedCore]

/-- The spatial projection of the recovered source is the certified spatial channel, with
`none`/`some` preserved exactly. -/
theorem recoveredSource_constructedCore_spatial?
    (certified : CertifiedAuthoritativeChemicalInput) :
    (recoveredSource (constructedCore certified)
        (constructedEnumeration certified)).spatial? = certified.input.spatial? := by
  rw [recoveredSource_constructedCore]

/-- The drawing projection of the recovered source is the certified drawing channel, with
`none`/`some` preserved exactly and every bond/parity occurrence retained. -/
theorem recoveredSource_constructedCore_diagram?
    (certified : CertifiedAuthoritativeChemicalInput) :
    (recoveredSource (constructedCore certified)
        (constructedEnumeration certified)).diagram? = certified.input.diagram? := by
  rw [recoveredSource_constructedCore]

/-- The recovered source is structurally well formed.  The certificate is the certified input's
own structural certificate, transported along the exact recovery equality; no chemical judgment is
derived. -/
theorem recoveredSource_constructedCore_structurallyWellFormed
    (certified : CertifiedAuthoritativeChemicalInput) :
    (recoveredSource (constructedCore certified)
        (constructedEnumeration certified)).StructurallyWellFormed := by
  rw [recoveredSource_constructedCore]
  exact certified.structurallyWellFormed

/-- The recovered source, packaged with its transported structural certificate.  This is a
certified authoritative input whose `input` is exactly the original input. -/
def recoveredCertified (certified : CertifiedAuthoritativeChemicalInput) :
    CertifiedAuthoritativeChemicalInput where
  input := recoveredSource (constructedCore certified)
    (constructedEnumeration certified)
  structurallyWellFormed := recoveredSource_constructedCore_structurallyWellFormed certified

/-- The recovered certified record carries exactly the original authenticated input. -/
@[simp] theorem recoveredCertified_input (certified : CertifiedAuthoritativeChemicalInput) :
    (recoveredCertified certified).input = certified.input :=
  recoveredSource_constructedCore certified

/-! ## Preservation of absent and present optional channels -/

/-- If the certified input supplies no rational positions, the constructed core's rational channel
is absent; no coordinate is invented. -/
theorem constructedCore_rationalPositions?_eq_none
    (certified : CertifiedAuthoritativeChemicalInput)
    (absent : certified.input.spatial? = none) :
    (constructedCore certified).rationalPositions? = none := by
  rw [constructedCore_rationalPositions?]
  exact CertifiedAuthoritativeChemicalInput.decode_spatial?_eq_none certified absent

/-- If the certified input supplies rational positions, the constructed core's rational channel is
the exact decoded coordinate function (the same function whose pointwise agreement with the
canonical conformation is the core's validity field). -/
theorem constructedCore_rationalPositions?_eq_some
    (certified : CertifiedAuthoritativeChemicalInput) (spatial : SpatialConfiguration)
    (present : certified.input.spatial? = some spatial) :
    (constructedCore certified).rationalPositions? =
      some (decodeSpatial spatial certified.input.molecule.atomCount
        (spatialFits_of_wf certified.input certified.structurallyWellFormed.2.1 spatial
          present)) := by
  rw [constructedCore_rationalPositions?]
  exact decodeSpatial?_some certified.input
    certified.structurallyWellFormed.2.1 spatial present

/-- If the certified input supplies no drawing configuration, the constructed core's drawing
channel is absent. -/
theorem constructedCore_diagram?_eq_none
    (certified : CertifiedAuthoritativeChemicalInput)
    (absent : certified.input.diagram? = none) :
    (constructedCore certified).diagram? = none := by
  rw [constructedCore_diagram?]
  exact CertifiedAuthoritativeChemicalInput.decode_diagram?_eq_none certified absent

/-- If the certified input supplies a drawing configuration, the constructed core's drawing channel
is the exact decoded source drawing, whose endpoint bounds and parity/atom bounds are derived from
the certified structural certificate. -/
theorem constructedCore_diagram?_eq_some
    (certified : CertifiedAuthoritativeChemicalInput) (diagram : DiagramConfiguration)
    (present : certified.input.diagram? = some diagram) :
    (constructedCore certified).diagram? =
      some (decodeDiagram diagram certified.input.molecule.atomCount
        (diagramPositionsFits_of_wf certified.input certified.structurallyWellFormed.2.2
          diagram present)
        (diagramBondOk_of_wf certified.input certified.structurallyWellFormed.2.2 diagram present)
        (diagramAtomOk_of_wf certified.input certified.structurallyWellFormed.2.2 diagram
          present)) := by
  rw [constructedCore_diagram?]
  exact decodeDiagram?_some certified.input
    certified.structurallyWellFormed.2.2 diagram present

/-- Every decoded drawing bond has distinct endpoints.  The endpoints are genuine atom labels of
the constructed carrier (their bounds come from the certified source), and their distinctness is
the certified `DiagramIndicesWellFormed` condition, not an extra assumption. -/
theorem constructedCore_diagram_endpointDistinct
    (certified : CertifiedAuthoritativeChemicalInput) :
    ∀ diagram, (constructedCore certified).diagram? = some diagram →
      diagram.EndpointDistinct := by
  intro diagram present
  rw [constructedCore_diagram?, CertifiedAuthoritativeChemicalInput.decode_diagram?] at present
  cases observed : certified.input.diagram? with
  | none =>
      rw [decodeDiagram?_none certified.input certified.structurallyWellFormed.2.2 observed]
        at present
      cases present
  | some sourceDiagram =>
      rw [decodeDiagram?_some certified.input certified.structurallyWellFormed.2.2 sourceDiagram
        observed] at present
      cases present
      intro bond member
      have bondsOk : sourceDiagram.bonds.all (fun bond =>
          decide (bond.source < certified.input.molecule.atomCount) &&
            decide (bond.target < certified.input.molecule.atomCount) &&
              decide (bond.source ≠ bond.target)) = true :=
        diagramBondOk_of_wf certified.input certified.structurallyWellFormed.2.2 sourceDiagram
          observed
      have member' : bond ∈ sourceDiagram.bonds.pmap
          (fun bond (bound : bond ∈ sourceDiagram.bonds) =>
            decodeDiagramBond certified.input.molecule.atomCount bond
              (diagramBond_source_lt bondsOk bound)
              (diagramBond_target_lt bondsOk bound))
          (fun _ bound => bound) := member
      rw [List.mem_pmap] at member'
      obtain ⟨sourceBond, sourceMember, equal⟩ := member'
      rw [← equal]
      intro same
      have checked := List.all_eq_true.mp bondsOk sourceBond sourceMember
      simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at checked
      exact checked.2 (congrArg Fin.val same)

/-! ## The zero-atom source -/

/-- The construction preserves the empty source: when the certified input has no atoms, the
constructed carrier is empty and the source round trip still holds.  In particular no coordinate
is invented for an atom that does not exist. -/
theorem constructedCore_empty_source (certified : CertifiedAuthoritativeChemicalInput)
    (empty : certified.input.molecule.atomCount = 0) :
    (Fin certified.input.molecule.atomCount → False) ∧
      recoveredSource (constructedCore certified)
        (constructedEnumeration certified) = certified.input := by
  refine ⟨?_, recoveredSource_constructedCore certified⟩
  intro atom
  rw [empty] at atom
  exact Fin.elim0 atom

/-! ## Exact recovery after the canonical transport -/

/-- The canonical assembly of the constructed core decodes back to the constructed core.  This is
the existing `decode_canonicalAssemble` inverse applied to the constructed request; no equality is
supplied as a premise. -/
theorem decodedCore_canonicalAssemble_constructedCore
    (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicStereoSpatialSupportMolecularAssembly.decodedCore
        (OrganicStereoMolecularCanonicalTransport.canonicalAssemble
          (constructedEnumeration certified) (constructedCore certified)) =
      constructedCore certified :=
  OrganicStereoMolecularCanonicalTransport.decode_canonicalAssemble
    (constructedEnumeration certified) (constructedCore certified)

/-- **Reconstruction after canonical transport.**  Recovering the source from the core obtained by
the actual `canonicalAssemble` / `decodedCore` pipeline returns the certified input exactly. -/
theorem decoded_core_source (certified : CertifiedAuthoritativeChemicalInput) :
    recoveredSource
        (OrganicStereoSpatialSupportMolecularAssembly.decodedCore
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble
            (constructedEnumeration certified) (constructedCore certified)))
        (constructedEnumeration certified) = certified.input := by
  rw [decodedCore_canonicalAssemble_constructedCore]
  exact recoveredSource_constructedCore certified

/-- The molecule projection after canonical transport is the certified molecule. -/
theorem decoded_core_source_molecule (certified : CertifiedAuthoritativeChemicalInput) :
    (recoveredSource
        (OrganicStereoSpatialSupportMolecularAssembly.decodedCore
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble
            (constructedEnumeration certified) (constructedCore certified)))
        (constructedEnumeration certified)).molecule = certified.input.molecule := by
  rw [decoded_core_source]

/-- The spatial projection after canonical transport is the certified spatial channel. -/
theorem decoded_core_source_spatial? (certified : CertifiedAuthoritativeChemicalInput) :
    (recoveredSource
        (OrganicStereoSpatialSupportMolecularAssembly.decodedCore
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble
            (constructedEnumeration certified) (constructedCore certified)))
        (constructedEnumeration certified)).spatial? = certified.input.spatial? := by
  rw [decoded_core_source]

/-- The drawing projection after canonical transport is the certified drawing channel. -/
theorem decoded_core_source_diagram? (certified : CertifiedAuthoritativeChemicalInput) :
    (recoveredSource
        (OrganicStereoSpatialSupportMolecularAssembly.decodedCore
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble
            (constructedEnumeration certified) (constructedCore certified)))
        (constructedEnumeration certified)).diagram? = certified.input.diagram? := by
  rw [decoded_core_source]

/-- The source after canonical transport is structurally well formed. -/
theorem decoded_core_source_structurallyWellFormed
    (certified : CertifiedAuthoritativeChemicalInput) :
    (recoveredSource
        (OrganicStereoSpatialSupportMolecularAssembly.decodedCore
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble
            (constructedEnumeration certified) (constructedCore certified)))
        (constructedEnumeration certified)).StructurallyWellFormed := by
  rw [decoded_core_source]
  exact certified.structurallyWellFormed

/-- The decoded core's finite source is exactly the decoded ingress source. -/
theorem decoded_core_finiteSource (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource
        (OrganicStereoSpatialSupportMolecularAssembly.decodedCore
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble
            (constructedEnumeration certified) (constructedCore certified))) =
      CertifiedAuthoritativeChemicalInput.decode certified := by
  rw [decodedCore_canonicalAssemble_constructedCore, coreFiniteSource_constructedCore]

/-- The decoded core's graph channel is the decoded ingress graph. -/
theorem decoded_core_finiteSource_graph (certified : CertifiedAuthoritativeChemicalInput) :
    (OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource
        (OrganicStereoSpatialSupportMolecularAssembly.decodedCore
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble
            (constructedEnumeration certified) (constructedCore certified)))).graph =
      (CertifiedAuthoritativeChemicalInput.decode certified).graph := by
  rw [decoded_core_finiteSource]

/-- The decoded core's spatial channel is the decoded ingress spatial channel. -/
theorem decoded_core_finiteSource_spatial? (certified : CertifiedAuthoritativeChemicalInput) :
    (OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource
        (OrganicStereoSpatialSupportMolecularAssembly.decodedCore
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble
            (constructedEnumeration certified) (constructedCore certified)))).spatial? =
      (CertifiedAuthoritativeChemicalInput.decode certified).spatial? := by
  rw [decoded_core_finiteSource]

/-- The decoded core's drawing channel is the decoded ingress drawing channel. -/
theorem decoded_core_finiteSource_diagram? (certified : CertifiedAuthoritativeChemicalInput) :
    (OrganicStereoAuthorityMixedSourceAssembly.coreFiniteSource
        (OrganicStereoSpatialSupportMolecularAssembly.decodedCore
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble
            (constructedEnumeration certified) (constructedCore certified)))).diagram? =
      (CertifiedAuthoritativeChemicalInput.decode certified).diagram? := by
  rw [decoded_core_finiteSource]

/-! ## Generic uncertified sources with explicit well-formedness -/

/-- The construction for an arbitrary structurally well-formed authoritative input.  The
well-formedness certificate is an explicit hypothesis; no chemical admissibility is claimed or
derived. -/
def constructedCoreOfWellFormed (input : AuthoritativeChemicalInput)
    (wellFormed : input.StructurallyWellFormed) :
    OrganicMolecularEvidence (Fin input.molecule.atomCount) :=
  constructedCore ⟨input, wellFormed⟩

/-- The generic construction recovers its own structural input exactly. -/
theorem recoveredSource_constructedCoreOfWellFormed (input : AuthoritativeChemicalInput)
    (wellFormed : input.StructurallyWellFormed) :
    recoveredSource
        (constructedCoreOfWellFormed input wellFormed)
        (identityEnumeration input.molecule.atomCount) = input :=
  recoveredSource_constructedCore ⟨input, wellFormed⟩

/-- The construction for an arbitrary finite source whose encoding at the supplied enumeration is
structurally well formed.  Every obligation is the explicit well-formedness hypothesis; the
construction is representation-only. -/
def constructedCoreOfFiniteSource (source : OrganicFiniteSource V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (wellFormed : (source.encode enumeration).StructurallyWellFormed) :
    OrganicMolecularEvidence (Fin (source.encode enumeration).molecule.atomCount) :=
  constructedCore ⟨source.encode enumeration, wellFormed⟩

/-- The generic finite-source construction recovers the encoded source exactly. -/
theorem recoveredSource_constructedCoreOfFiniteSource (source : OrganicFiniteSource V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (wellFormed : (source.encode enumeration).StructurallyWellFormed) :
    recoveredSource
        (constructedCoreOfFiniteSource source enumeration wellFormed)
        (identityEnumeration (source.encode enumeration).molecule.atomCount) =
      source.encode enumeration :=
  recoveredSource_constructedCore ⟨source.encode enumeration, wellFormed⟩

/-! ## Kernel-authority assertions for the decisive endpoints -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCertifiedSourceCoreCompletion.recoveredSource_constructedCore

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCertifiedSourceCoreCompletion.recoveredSource_constructedCore_structurallyWellFormed

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCertifiedSourceCoreCompletion.decoded_core_source

end

end OrganicStereoCertifiedSourceCoreCompletion

end TetraStereo.OneCenter
