import TetraStereo.OneCenter.OrganicStereoCertifiedSourceCoreCompletion
import TetraStereo.OneCenter.OrganicStereoNativeP94SourceContext
import TetraStereo.OneCenter.IUPACRemaining71P94ReviewedSemantics
import TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries
import TetraStereo.OneCenter.IUPACP94SourcePackageNonvacuity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false






























































namespace TetraStereo.OneCenter

open OrganicStereoCertifiedSourceCoreCompletion
open OrganicStereoNativeP94SourceContext
open OrganicStereoP94AuthorityObservationIngress
open OrganicStereoMolecularEvidenceAssembly
open IUPACNormativeProvision

namespace OrganicStereoP94NativeRowAdmission

noncomputable section

variable {policy : P94AuthorityPolicy}

/-! ## The common constructed molecular core -/

/-- The common molecular core used by every closed row: the approved constructed core of the
certified source.  It does not depend on the row. -/
abbrev rowCore (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicMolecularEvidence (Fin certified.input.molecule.atomCount) :=
  constructedCore certified

/-- The common enumeration used by every closed row: the approved identity enumeration of the
constructed core.  It does not depend on the row. -/
abbrev rowEnumeration (certified : CertifiedAuthoritativeChemicalInput) :
    Fin certified.input.molecule.atomCount ≃
      Fin (Fintype.card (Fin certified.input.molecule.atomCount)) :=
  constructedEnumeration certified

/-- The genuine source/molecule tie, derived from the approved exact reconstruction
`recoveredSource_constructedCore`; it is not a caller-supplied equality. -/
theorem rowCore_graph_eq (certified : CertifiedAuthoritativeChemicalInput) :
    certified.input.molecule =
      (rowCore certified).graph.encode (rowEnumeration certified) := by
  have h := congrArg AuthoritativeChemicalInput.molecule
    (recoveredSource_constructedCore certified)
  exact h.symm

/-! ## The existing encoded payload -/

/-- The approved encoded P-94 authority payload at the constructed core.  All atom bounds and
certificate witnesses are derived inside `ofAuthorityValid` from the actual judge; no bound is
assumed. -/
abbrev rowEncoded (certified : CertifiedAuthoritativeChemicalInput)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidFor policy certified.input) :
    EncodedP94AuthorityObservation policy certified
      (Fin certified.input.molecule.atomCount) :=
  EncodedP94AuthorityObservation.ofAuthorityValid
    (nativeSourceAtomResolver (rowCore certified).graph (rowEnumeration certified)
      certified (rowCore_graph_eq certified))
    observation valid

/-- The existing encoder's exact round trip: the encoded payload decodes to the original
observation at the derived resolver. -/
theorem rowEncoded_toAuthority (certified : CertifiedAuthoritativeChemicalInput)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidFor policy certified.input) :
    (rowEncoded certified observation valid).toAuthority
        (nativeSourceAtomResolver (rowCore certified).graph (rowEnumeration certified)
          certified (rowCore_graph_eq certified)) = observation :=
  EncodedP94AuthorityObservation.toAuthority_ofAuthorityValid _ observation valid

/-- The encoded payload is valid for the certified source at the derived resolver. -/
theorem rowEncoded_valid (certified : CertifiedAuthoritativeChemicalInput)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidFor policy certified.input) :
    (EncodedP94AuthorityObservation.toAuthority
      (nativeSourceAtomResolver (rowCore certified).graph (rowEnumeration certified)
        certified (rowCore_graph_eq certified))
      (rowEncoded certified observation valid)).ValidFor policy certified.input := by
  rw [rowEncoded_toAuthority certified observation valid]
  exact valid

/-! ## The row-uniform admission -/

/-- **One row-uniform native admission.**  Every actual closed row uses the same existing native
payload type; `row` only appears in the type of the explicit actual judge hypothesis. -/
def admitP94ClosedRow (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    NativeAuthorityObservation (rowCore certified).graph (rowEnumeration certified) policy :=
  encodeNativeAuthorityObservation (rowCore certified).graph (rowEnumeration certified)
    certified (rowCore_graph_eq certified)
    (rowEncoded certified observation valid.1)
    (rowEncoded_valid certified observation valid.1)

/-- Decode a native P-94 payload using only the graph, enumeration, policy and native output.  It
is the existing decoder, not a second implementation. -/
abbrev decodeP94ClosedRow {V : Type} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    {policy : P94AuthorityPolicy}
    (native : NativeAuthorityObservation graph enumeration policy) :
    RecoveredNativeAuthority policy :=
  decodeNativeAuthorityObservation graph enumeration native

/-! ## Exact recovery of the source and of the whole observation -/

/-- The paired round trip of the existing native codec applied to the row-uniform admission. -/
theorem decode_admit_pair (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).source = certified ∧
      (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).observation =
        EncodedP94AuthorityObservation.toAuthority
          (nativeSourceAtomResolver (rowCore certified).graph (rowEnumeration certified)
            certified (rowCore_graph_eq certified))
          (rowEncoded certified observation valid.1) := by
  unfold admitP94ClosedRow decodeP94ClosedRow
  exact decodeNativeAuthorityObservation_encodeNativeAuthorityObservation
    (rowCore certified).graph (rowEnumeration certified)
    certified (rowCore_graph_eq certified)
    (rowEncoded certified observation valid.1)
    (rowEncoded_valid certified observation valid.1)

/-- **Exact source recovery.**  The native decoder reconstructs exactly the certified source from
the native context. -/
theorem decode_admit_source (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).source = certified :=
  (decode_admit_pair certified row observation valid).1

/-- **Exact observation recovery.**  The native decoder reconstructs exactly the original
authority observation, including every source-relative geometry/rotation/path relation field. -/
theorem decode_admit_observation (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).observation = observation := by
  have h := (decode_admit_pair certified row observation valid).2
  rw [h, rowEncoded_toAuthority certified observation valid.1]

/-- **Exact provision recovery.**  The decoded claim keeps the original manifest provision. -/
theorem decode_admit_claim_provision (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).observation.claim.provision =
      row.provision := by
  rw [decode_admit_observation certified row observation valid]
  exact valid.2

/-! ## Field-level preservation -/

@[simp] theorem decode_admit_molecule (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).observation.molecule =
      observation.molecule := by
  rw [decode_admit_observation certified row observation valid]

@[simp] theorem decode_admit_evidence (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).observation.evidence =
      observation.evidence := by
  rw [decode_admit_observation certified row observation valid]

@[simp] theorem decode_admit_claim (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).observation.claim =
      observation.claim := by
  rw [decode_admit_observation certified row observation valid]

@[simp] theorem decode_admit_inOutCertificate? (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).observation.inOutCertificate? =
      observation.inOutCertificate? := by
  rw [decode_admit_observation certified row observation valid]

/-- The decoded whole authoritative input is exactly the certified input. -/
theorem decode_admit_source_input (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).source.input = certified.input := by
  rw [decode_admit_source certified row observation valid]

/-- The decoded molecule is exactly the certified molecule. -/
theorem decode_admit_source_molecule (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).source.input.molecule =
      certified.input.molecule := by
  rw [decode_admit_source certified row observation valid]

/-- The decoded rational spatial channel is exactly the certified channel, with absence and
presence preserved. -/
theorem decode_admit_source_spatial? (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).source.input.spatial? =
      certified.input.spatial? := by
  rw [decode_admit_source certified row observation valid]

/-- The decoded drawing channel is exactly the certified channel, including every ordered bond
and atom-parity occurrence. -/
theorem decode_admit_source_diagram? (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).source.input.diagram? =
      certified.input.diagram? := by
  rw [decode_admit_source certified row observation valid]

/-- The decoded source channels are exactly the certified source channels. -/
theorem decode_admit_source_channels (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
          (admitP94ClosedRow certified row observation valid)).source.input.molecule =
        certified.input.molecule ∧
      (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
          (admitP94ClosedRow certified row observation valid)).source.input.spatial? =
        certified.input.spatial? ∧
      (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
          (admitP94ClosedRow certified row observation valid)).source.input.diagram? =
        certified.input.diagram? :=
  ⟨decode_admit_source_molecule certified row observation valid,
    decode_admit_source_spatial? certified row observation valid,
    decode_admit_source_diagram? certified row observation valid⟩

/-! ## Recovered actual judgments -/

/-- The decoded observation is valid for the decoded source. -/
theorem decode_admit_valid (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).observation.ValidFor policy
      (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).source.input := by
  rw [decode_admit_observation certified row observation valid,
    decode_admit_source certified row observation valid]
  exact valid.1

/-- The decoded observation satisfies exactly the original row-specific authority statement. -/
theorem decode_admit_validForProvision (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).observation.ValidForProvision policy
      row.provision
      (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).source.input := by
  rw [decode_admit_observation certified row observation valid,
    decode_admit_source certified row observation valid]
  exact valid

/-- **Recovered actual reference judge.**  The decoded source and observation satisfy the exact
manifest-row judge of the actual reference, with no extra condition. -/
theorem decode_admit_reference_judges (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (row.reference policy).Judges
      (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).source.input
      (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).observation := by
  simpa only [IUPACNormativeProvision.Remaining71P94AuthorityRow.reference,
    IUPACNormativeProvision.p94ProvisionReference] using
    decode_admit_validForProvision certified row observation valid

/-- **Recovered actual applicability.**  The row reference is applicable at the decoded source,
witnessed by the decoded observation and the recovered judge. -/
theorem decode_admit_reference_applicable (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (row.reference policy).Applicable
      (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
        (admitP94ClosedRow certified row observation valid)).source.input := by
  refine ⟨(decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
      (admitP94ClosedRow certified row observation valid)).observation, ?_⟩
  simpa only [IUPACNormativeProvision.Remaining71P94AuthorityRow.reference,
    IUPACNormativeProvision.p94ProvisionReference] using
    decode_admit_validForProvision certified row observation valid

/-! ## All twelve actual closed rows -/

/-- The actual closed-row enumeration has exactly twelve rows (existing theorem). -/
theorem all_closedRows_length : Remaining71P94AuthorityRow.all.length = 12 :=
  Remaining71P94AuthorityRow.all_length

/-- **All twelve actual closed rows, uniformly.**  For every member of the actual closed-row
enumeration and every observation satisfying the corresponding actual row judge, the same
row-uniform admission constructs an existing native payload whose decode returns the exact
source, observation and provision. -/
theorem all_closedRows_native_admission (certified : CertifiedAuthoritativeChemicalInput)
    (observation : P94AuthorityObservation policy)
    (row : Remaining71P94AuthorityRow)
    (member : row ∈ Remaining71P94AuthorityRow.all)
    (valid : observation.ValidForProvision policy row.provision certified.input) :
    (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
          (admitP94ClosedRow certified row observation valid)).source = certified ∧
      (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
          (admitP94ClosedRow certified row observation valid)).observation = observation ∧
      (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
          (admitP94ClosedRow certified row observation valid)).observation.claim.provision =
        row.provision ∧
      (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
          (admitP94ClosedRow certified row observation valid)).observation.ValidForProvision
        policy row.provision
        (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
          (admitP94ClosedRow certified row observation valid)).source.input :=
  ⟨decode_admit_source certified row observation valid,
    decode_admit_observation certified row observation valid,
    decode_admit_claim_provision certified row observation valid,
    decode_admit_validForProvision certified row observation valid⟩

/-! ## Extensionality of the existing native payload

Used only to identify the two presentations of the same existing encoder output; the two
proposition-valued `valid` proofs are identified by proof irrelevance.  The statement is posed at
one fixed native context and payload, which is exactly the concrete situation produced by the two
presentations of `encodeNativeAuthorityObservation`. -/

theorem nativeAuthorityObservation_ext_concrete {V : Type} [DecidableEq V] [Fintype V]
    {graph : FiniteAtomInteractionHypergraph V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    {policy : P94AuthorityPolicy}
    (context : NativeSourceContext graph enumeration)
    (payload : EncodedP94AuthorityObservation policy
      (decodeSourceContext graph enumeration context) V)
    (firstValid secondValid : (payload.toAuthority
      (nativeSourceAtomResolver graph enumeration
        (decodeSourceContext graph enumeration context) rfl)).ValidFor
      policy (decodeSourceContext graph enumeration context).input) :
    (⟨context, payload, firstValid⟩ : NativeAuthorityObservation graph enumeration policy) =
      ⟨context, payload, secondValid⟩ := by
  rw [Subsingleton.elim firstValid secondValid]

/-! ## Correspondence with the union's existing `.p94` branch

The admitted native payload is not a second payload codec: it is exactly the `.p94` payload that
`OrganicStereoAllAuthorityEntries.encodeEntry` produces, and decoding through the union branch
returns the original raw `.p94` entry.  The unused tag/state parameters are instantiated at
`PUnit`; the P-94 payload itself is independent of them. -/

section UnionCorrespondence

open OrganicStereoAllAuthorityEntries

variable {policies : OrganicStereoAllAuthorityEntries.AllAuthorityPolicies}

/-- The raw union entry type at the constructed core, with the unused type parameters at
`PUnit`. -/
abbrev UnionRawEntry (certified : CertifiedAuthoritativeChemicalInput) : Type :=
  OrganicStereoAllAuthorityEntries.RawEntry
    (V := Fin certified.input.molecule.atomCount)
    PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit
    policies (rowCore certified) (rowEnumeration certified)

/-- The native union entry type at the constructed core, with the unused type parameters at
`PUnit`. -/
abbrev UnionNativeEntry (certified : CertifiedAuthoritativeChemicalInput) : Type :=
  OrganicStereoAllAuthorityEntries.NativeEntry
    (V := Fin certified.input.molecule.atomCount)
    PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit PUnit
    policies (rowCore certified) (rowEnumeration certified)

/-- The actual raw `.p94` union entry whose branch is the adapter target. -/
abbrev unionP94Entry (certified : CertifiedAuthoritativeChemicalInput)
    (graph_eq : certified.input.molecule =
      (rowCore certified).graph.encode (rowEnumeration certified))
    (observation : P94AuthorityObservation policies.policy94)
    (valid : observation.ValidFor policies.policy94 certified.input) :
    UnionRawEntry (policies := policies) certified :=
  OrganicStereoAllAuthorityEntries.RawEntry.p94 certified graph_eq observation valid

/-- **The adapter is the union's `.p94` branch.**  Encoding the raw `.p94` entry with the existing
union encoder yields exactly the admitted native payload. -/
theorem union_encodeEntry_p94_eq_admit (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policies.policy94)
    (valid : observation.ValidForProvision policies.policy94 row.provision certified.input) :
    OrganicStereoAllAuthorityEntries.encodeEntry (rowCore certified) (rowEnumeration certified)
        (recoveredSource_constructedCore_structurallyWellFormed certified)
        (unionP94Entry certified (rowCore_graph_eq certified) observation valid.1) =
      OrganicStereoAllAuthorityEntries.NativeEntry.p94
        (admitP94ClosedRow (policy := policies.policy94) certified row observation valid) := by
  unfold unionP94Entry
  simp only [OrganicStereoAllAuthorityEntries.encodeEntry]
  unfold admitP94ClosedRow rowEncoded
    OrganicStereoNativeP94SourceContext.encodeNativeAuthorityObservation
  apply congrArg OrganicStereoAllAuthorityEntries.NativeEntry.p94
  exact nativeAuthorityObservation_ext_concrete _ _ _ _

/-- **Decoding through the union branch returns the original raw `.p94` entry.**  This consumes
the union's existing exact entry inverse; the admitted payload's decode is not re-derived. -/
theorem union_decodeEntry_admit (certified : CertifiedAuthoritativeChemicalInput)
    (row : Remaining71P94AuthorityRow)
    (observation : P94AuthorityObservation policies.policy94)
    (valid : observation.ValidForProvision policies.policy94 row.provision certified.input) :
    OrganicStereoAllAuthorityEntries.decodeEntry (rowCore certified) (rowEnumeration certified)
        (OrganicStereoAllAuthorityEntries.NativeEntry.p94
          (admitP94ClosedRow (policy := policies.policy94) certified row observation valid) :
            UnionNativeEntry (policies := policies) certified) =
      (OrganicStereoAllAuthorityEntries.RawEntry.p94 certified
        (rowCore_graph_eq certified) observation valid.1 :
          UnionRawEntry (policies := policies) certified) := by
  rw [← union_encodeEntry_p94_eq_admit certified row observation valid]
  exact OrganicStereoAllAuthorityEntries.decodeEntry_encodeEntry
    (rowCore certified) (rowEnumeration certified)
    (recoveredSource_constructedCore_structurallyWellFormed certified)
    (unionP94Entry certified (rowCore_graph_eq certified) observation valid.1)

end UnionCorrespondence

/-! ## Concrete nonvacuity from the existing 35-atom source package -/

section Nonvacuity

/-- **Concrete nonvacuity of the native row admission for every closed row.**  Each witness is
produced by the existing
`P94SourcePackageNonvacuity.Remaining71P94AuthorityRow.schema_reference_nonvacuous` theorem over
the existing 35-atom P-94 source package; no atom list is duplicated here. -/
theorem closedRow_native_admission_nonvacuous (row : Remaining71P94AuthorityRow) :
    ∃ (certified : CertifiedAuthoritativeChemicalInput)
      (observation : P94AuthorityObservation p94SourcePackageSchemaPolicy)
      (valid : observation.ValidForProvision p94SourcePackageSchemaPolicy row.provision
        certified.input),
      (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
          (admitP94ClosedRow certified row observation valid)).source = certified ∧
        (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
          (admitP94ClosedRow certified row observation valid)).observation = observation ∧
        (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
          (admitP94ClosedRow certified row observation valid)).observation.claim.provision =
            row.provision ∧
        (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
          (admitP94ClosedRow certified row observation valid)).observation.ValidForProvision
            p94SourcePackageSchemaPolicy row.provision
            (decodeP94ClosedRow (rowCore certified).graph (rowEnumeration certified)
              (admitP94ClosedRow certified row observation valid)).source.input := by
  obtain ⟨input, observation, wellFormed, _applicable, judged⟩ :=
    P94SourcePackageNonvacuity.Remaining71P94AuthorityRow.schema_reference_nonvacuous row
  let certified : CertifiedAuthoritativeChemicalInput :=
    ⟨input, wellFormed⟩
  have hcert : certified.input = input := rfl
  have valid : observation.ValidForProvision p94SourcePackageSchemaPolicy row.provision
      certified.input := by
    rw [hcert]
    simpa only [IUPACNormativeProvision.Remaining71P94AuthorityRow.reference,
      IUPACNormativeProvision.p94ProvisionReference] using judged
  exact ⟨certified, observation, valid,
    decode_admit_source certified row observation valid,
    decode_admit_observation certified row observation valid,
    decode_admit_claim_provision certified row observation valid,
    decode_admit_validForProvision certified row observation valid⟩

end Nonvacuity

end

end OrganicStereoP94NativeRowAdmission

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.rowCore_graph_eq
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.rowEncoded
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.rowEncoded_toAuthority
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.rowEncoded_valid
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.admitP94ClosedRow
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.decode_admit_source
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.decode_admit_observation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.decode_admit_claim_provision
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.decode_admit_evidence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.decode_admit_inOutCertificate?
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.decode_admit_source_channels
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.decode_admit_validForProvision
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.decode_admit_reference_judges
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.decode_admit_reference_applicable
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.all_closedRows_native_admission
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.union_encodeEntry_p94_eq_admit
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.union_decodeEntry_admit
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP94NativeRowAdmission.closedRow_native_admission_nonvacuous
