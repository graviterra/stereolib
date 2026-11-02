import TetraStereo.Engine.HostModuleCompiler

set_option autoImplicit false

namespace TetraStereoGenerated
namespace Tests
namespace HostModuleCompilerClaims

open TetraStereo.Engine
open TetraStereo.OneCenter

noncomputable section

/-!
  Standalone fixture for the target-claim theorems emitted by
  `HostOfficialStereoCertificateTarget`.

  After the bounded rule-major migration, `OfficialStereoRequest.outcome` is
  `Option Ordering`, projected from `OfficialStereoRequest.certificate :
  Option CIPTraceCertificate`.  The generator therefore emits:

  * `computedComparison`:
    `(<request>).outcome = (<request>).outcome`, proved by `rfl`.  This is
    compatibility reflexivity only; it asserts no comparison value.
  * `comparison expected`:
    `TetraStereo.Engine.OfficialStereoTransactionClaim <request> expected`,
    i.e. `<request>.outcome = some expected`, proved by `rfl` when the
    generated request's bounded certificate reduces.
  * `refusal reason`:
    `TetraStereo.Engine.OfficialStereoRefusalClaim <request> reason`, i.e.
    `<request>.certificateReady = false ∧
      <request>.officialRefusalReason? = some reason`.

  For a request produced from a host-supplied `MoleculeGraph`, the bounded
  comparison does not reduce in the kernel (the detector chooses a ligand
  order through the noncomputable `Fintype.equivOfCardEq`), so the two literal
  forms cannot be proved by `rfl` there.  The checks below isolate the exact
  proof obligations: they start from the request's *actual* certificate and
  derive the emitted claim.  Every step is a kernel-checked consequence of the
  migrated transaction API; no result is assumed and no additional axiom,
  `sorry`, `unsafe`, or `native_decide` is introduced.
-/

/-! ## Compatibility reflexivity (`computedComparison`) -/

/-- Exact body of a generated `computedComparison` target-claim theorem.  It is
well-typed for every request and does not evaluate the bounded comparison. -/
theorem generated_computedComparison_claim (request : OfficialStereoRequest) :
    request.outcome = request.outcome :=
  rfl

/-- The compatibility expression is the projection of one bounded certificate,
not a separately computed total ordering. -/
theorem generated_computedComparison_claim_eq_certificate_map
    (request : OfficialStereoRequest) :
    request.outcome = request.certificate.map CIPTraceCertificate.outcome :=
  OfficialStereoRequest.outcome_eq_certificate_map request

/-! ## Literal comparison (`comparison expected`) -/

/-- The emitted literal comparison claim follows from the request's actual
bounded certificate: the expected value is a real `Ordering` obtained from a
`some` certificate, never a substitute for `none`. -/
theorem generated_comparison_claim_of_certificate
    (request : OfficialStereoRequest) {cert : CIPTraceCertificate}
    (hcert : request.certificate = some cert) :
    OfficialStereoTransactionClaim request cert.outcome := by
  unfold OfficialStereoTransactionClaim
  exact OfficialStereoRequest.outcome_eq_some_outcome_of_certificate_eq_some request hcert

/-- A concrete literal target: if the request's certificate exhibits
`Ordering.gt`, the emitted `comparison Ordering.gt` claim holds. -/
theorem generated_comparison_gt_claim_of_certificate
    (request : OfficialStereoRequest) {cert : CIPTraceCertificate}
    (hcert : request.certificate = some cert) (houtcome : cert.outcome = Ordering.gt) :
    OfficialStereoTransactionClaim request Ordering.gt := by
  unfold OfficialStereoTransactionClaim
  rw [OfficialStereoRequest.outcome_eq_some_outcome_of_certificate_eq_some request hcert,
    houtcome]

/-- A claim that is not certificate-backed justifies no literal comparison: the
expected value must come from an actual certificate. -/
theorem generated_comparison_claim_has_certificate
    (request : OfficialStereoRequest) {expected : Ordering}
    (h : OfficialStereoTransactionClaim request expected) :
    ∃ cert, request.certificate = some cert ∧ cert.outcome = expected := by
  unfold OfficialStereoTransactionClaim at h
  exact OfficialStereoRequest.certificate_eq_some_of_outcome_eq_some request h

/-! ## Literal refusal (`refusal reason`) -/

/-- A `none` certificate — the bounded root-key compile failed, or the
completed-key gate refused — justifies exactly `implementationLimit`, never a
Rule 3/4/5 descriptor-context reason.  Both conjuncts are derived from the same
request field. -/
theorem generated_refusal_implementationLimit_claim_of_certificate_eq_none
    (request : OfficialStereoRequest) (hcert : request.certificate = none) :
    OfficialStereoRefusalClaim request RefusalReason.implementationLimit := by
  unfold OfficialStereoRefusalClaim
  exact
    ⟨(OfficialStereoRequest.certificateReady_eq_false_iff request).mpr (Or.inl hcert),
      OfficialStereoRequest.officialRefusalReason_eq_some_implementationLimit_of_certificate_eq_none
        request hcert⟩

/-- A completed but unresolved tie justifies `unresolvedOfficialPriorities`. -/
theorem generated_refusal_unresolvedOfficialPriorities_claim_of_outcome_eq
    (request : OfficialStereoRequest) {cert : CIPTraceCertificate}
    (hcert : request.certificate = some cert) (htie : cert.outcome = Ordering.eq) :
    OfficialStereoRefusalClaim request RefusalReason.unresolvedOfficialPriorities := by
  have hout : request.outcome = some Ordering.eq := by
    rw [OfficialStereoRequest.outcome_eq_some_outcome_of_certificate_eq_some request hcert,
      htie]
  unfold OfficialStereoRefusalClaim
  exact
    ⟨(OfficialStereoRequest.certificateReady_eq_false_iff request).mpr
        (Or.inr ⟨cert, hcert, htie⟩),
      OfficialStereoRequest.officialRefusalReason_eq_some_unresolvedOfficialPriorities_of_outcome_eq
        request hout⟩

/-- A decisive certificate is not a refusal at all; an emitted refusal claim
cannot be instantiated with an arbitrary reason for it. -/
theorem generated_refusal_reason_eq_none_of_decisive_certificate
    (request : OfficialStereoRequest) {cert : CIPTraceCertificate}
    (hcert : request.certificate = some cert) (hdecisive : cert.outcome ≠ Ordering.eq) :
    request.officialRefusalReason? = none :=
  OfficialStereoRequest.officialRefusalReason_eq_none_of_outcome_ne_eq request hcert hdecisive

/-! ## Exact emitter strings -/

/-- The compatibility target emits the optional-outcome reflexivity, not
`OfficialStereoTransactionClaim` applied to an `Option Ordering`. -/
theorem emitted_computedComparison_statement (requestExpr : String) :
    HostOfficialStereoCertificateTarget.computedComparison.statement requestExpr =
      "(" ++ requestExpr ++ ").outcome = (" ++ requestExpr ++ ").outcome" :=
  rfl

/-- The literal comparison target still emits the declared `Ordering`. -/
theorem emitted_comparison_statement (requestExpr : String) (expected : Ordering) :
    (HostOfficialStereoCertificateTarget.comparison expected).statement requestExpr =
      "TetraStereo.Engine.OfficialStereoTransactionClaim " ++ requestExpr ++ " " ++
        orderingExpr expected :=
  rfl

/-- The literal refusal target still emits the declared reason. -/
theorem emitted_refusal_statement (requestExpr : String) (reason : RefusalReason) :
    (HostOfficialStereoCertificateTarget.refusal reason).statement requestExpr =
      "TetraStereo.Engine.OfficialStereoRefusalClaim " ++ requestExpr ++ " " ++
        refusalReasonExpr reason :=
  rfl

/-- The `implementationLimit` rendering used when the bounded certificate is
`none`, with no context-derived fallback. -/
theorem emitted_implementationLimit_reason :
    refusalReasonExpr RefusalReason.implementationLimit =
      "TetraStereo.Engine.RefusalReason.implementationLimit" :=
  rfl

/-- Proof-term rendering is unchanged: reflexivity, a single equation, and a
two-conjunct check respectively. -/
theorem emitted_proofTerms :
    HostOfficialStereoCertificateTarget.computedComparison.proofTerm = "  rfl" ∧
      (∀ expected : Ordering,
        (HostOfficialStereoCertificateTarget.comparison expected).proofTerm = "  rfl") ∧
        (∀ reason : RefusalReason,
          (HostOfficialStereoCertificateTarget.refusal reason).proofTerm = "  ⟨rfl, rfl⟩") :=
  ⟨rfl, fun _ => rfl, fun _ => rfl⟩

end
end HostModuleCompilerClaims
end Tests
end TetraStereoGenerated
