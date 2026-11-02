/-
  Regression for the actual generated certificate sources of the preserved original
  `C(F)(O)(N)Cl` automatic-bridge example and of the concrete `CCl4` refusal.

  The two live registries legitimately use different renderers and therefore produce
  different theorem names for the same `C(F)(O)(N)Cl` molecule:

  * `TetraStereo.Examples.CertificateExportRegistry` registers the checked wrapper
    artifact, rendered by `LeanTheoremExport.source` as
    `auto_bridge_official_stereo_checked`;
  * `TetraStereo.CLI.CertificateSourceRegistry` registers the compact host-query
    entry, rendered by `OfficialStereoHostQuerySourceSpec.theoremExport` as
    `auto_bridge_official_stereo_query_checked`.

  No byte equality between those two texts is asserted.  Each one is proved equal to
  its own full exact rendered text.  The `CCl4` entry is the real refusal artifact
  produced from the actual computed tie, rendered through
  `PublicOfficialStereoTheoremPlan.refusalTheoremExport`.

  Every equality below is closed by kernel reduction (`rfl`) of the actual registry
  value, so the literals are not merely documented prose: they are the values the
  registries really render.  The literal files emitted next to this module are exactly
  `source ++ "\n"` for the three exported modules.
-/

import TetraStereo.Examples.CertificateExportRegistry
import TetraStereo.CLI.CertificateSourceRegistry
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace GeneratedCertificateValidation

/-! ## Exact expected rendered texts

`LeanTheoremExport.source` joins
`importLines ++ [""] ++ options ++ [""] ++ namespaceOpenLines ++ [""] ++
  theoremLines ++ [""] ++ namespaceCloseLines`
with `"\n"`.  With `options = []` this yields two blank lines between the imports and
the namespace block; with `options = ["set_option maxHeartbeats 1000000"]` it yields
one blank line on each side of the option line. -/

/-- Exact text registered by `CertificateExportRegistry.autoBridgeCheckedEntry`
(the checked wrapper for the actual prepared `C(F)(O)(N)Cl` transaction). -/
def expectedAutoBridgeCheckedSource : String :=
  "import TetraStereo.Engine.OfficialStereoBuilder\n" ++
  "import TetraStereo.Examples.OfficialStereoBuilder\n" ++
  "\n" ++
  "\n" ++
  "namespace TetraStereo\n" ++
  "namespace Examples\n" ++
  "namespace GeneratedCertificates\n" ++
  "\n" ++
  "theorem auto_bridge_official_stereo_checked : " ++
    "TetraStereo.Examples.OfficialStereoBuilder.autoBridgePrepared.exportEntry.artifact.claim := by\n" ++
  "  exact TetraStereo.Examples.OfficialStereoBuilder.autoBridgePrepared_checked\n" ++
  "\n" ++
  "end GeneratedCertificates\n" ++
  "end Examples\n" ++
  "end TetraStereo"

/-- Exact text registered by `CertificateSourceRegistry.autoBridgeCheckedSourceEntry`
(the checked host-query theorem for the actual `autoBridgeQuery`). -/
def expectedAutoBridgeQuerySource : String :=
  "import TetraStereo.Examples.OfficialStereoBuilder\n" ++
  "\n" ++
  "set_option maxHeartbeats 1000000\n" ++
  "\n" ++
  "namespace TetraStereo\n" ++
  "namespace Examples\n" ++
  "namespace GeneratedCertificates\n" ++
  "\n" ++
  "theorem auto_bridge_official_stereo_query_checked : " ++
    "TetraStereo.Engine.OfficialStereoHostQueryClaim " ++
      "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeQuery := by\n" ++
  "  exact TetraStereo.Engine.officialStereoHostQueryClaim_checked " ++
    "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeQuery " ++
      "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeHostQueryBuilds\n" ++
  "\n" ++
  "end GeneratedCertificates\n" ++
  "end Examples\n" ++
  "end TetraStereo"

/-- Exact text of the real `CCl4` refusal artifact registered by
`CertificateExportRegistry` (`ccl4Refusal.artifact.source`). -/
def expectedCcl4RefusalSource : String :=
  "import TetraStereo.Engine.OfficialStereoBuilder\n" ++
  "import TetraStereo.OneCenter.OfficialUniformTerminalLigandTie\n" ++
  "import TetraStereo.Examples.OfficialStereoBuilder\n" ++
  "\n" ++
  "\n" ++
  "namespace TetraStereo\n" ++
  "namespace Examples\n" ++
  "namespace GeneratedCertificates\n" ++
  "\n" ++
  "theorem ccl4_official_stereo_refusal : " ++
    "TetraStereo.Engine.OfficialStereoRefusalClaim " ++
      "TetraStereo.Examples.OfficialStereoBuilder.ccl4Request " ++
        "TetraStereo.Engine.RefusalReason.unresolvedOfficialPriorities := by\n" ++
  "  exact TetraStereo.Examples.OfficialStereoBuilder.ccl4Request_refusal_claim\n" ++
  "\n" ++
  "end GeneratedCertificates\n" ++
  "end Examples\n" ++
  "end TetraStereo"

/-- Exact text registered by the CLI source registry for the real `CCl4` refusal
artifact.  The CLI renderer wraps an artifact claim into a standalone theorem, so its
theorem name differs from the Examples-registry artifact source above. -/
def expectedCliCcl4ClaimSource : String :=
  "import TetraStereo.Examples.OfficialStereoBuilder\n" ++
  "\n" ++
  "\n" ++
  "namespace TetraStereo\n" ++
  "namespace Examples\n" ++
  "namespace GeneratedCertificates\n" ++
  "\n" ++
  "theorem ccl4_official_stereo_refusal_artifact_checked : " ++
    "TetraStereo.Examples.OfficialStereoBuilder.ccl4Refusal.artifact.claim := by\n" ++
  "  exact TetraStereo.Examples.OfficialStereoBuilder.ccl4Refusal_checked\n" ++
  "\n" ++
  "end GeneratedCertificates\n" ++
  "end Examples\n" ++
  "end TetraStereo"

/-! ## The registered artifacts carry the actual checked claims

These theorems make explicit that the exported wrapper claim is the prepared builder
artifact's own claim (record update preserves it), and that the `CCl4` artifact claim
is the genuine refusal claim obtained from the actual computed tie. -/

/-- The wrapper's claim is literally the prepared transaction artifact's claim. -/
theorem autoBridgeCheckedArtifact_claim_eq_prepared :
    _root_.TetraStereo.Examples.OfficialStereoBuilder.autoBridgeCheckedArtifact.claim =
      _root_.TetraStereo.Examples.OfficialStereoBuilder.autoBridgePrepared.exportEntry.artifact.claim :=
  rfl

/-- The prepared builder artifact's claim is checked. -/
theorem autoBridgeCheckedEntry_artifact_checked :
    _root_.TetraStereo.Examples.CertificateExportRegistry.autoBridgeCheckedEntry.artifact.claim :=
  _root_.TetraStereo.Examples.CertificateExportRegistry.autoBridgeCheckedEntry_claim

/-- The `CCl4` artifact's subject is the genuine refusal claim for the actual request. -/
theorem ccl4Refusal_artifact_subject_eq :
    _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4Refusal.artifact.claim =
      _root_.TetraStereo.Engine.OfficialStereoRefusalClaim
        _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4Request
        _root_.TetraStereo.Engine.RefusalReason.unresolvedOfficialPriorities :=
  rfl

/-- The real `CCl4` refusal artifact is checked. -/
theorem ccl4Refusal_artifact_checked :
    _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4Refusal.artifact.claim :=
  _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4Refusal_checked

/-! ## Exact rendered sources -/

/-- The Examples-registry wrapper source is exactly its full rendered text. -/
theorem autoBridgeCheckedEntry_source_eq :
    _root_.TetraStereo.Examples.CertificateExportRegistry.autoBridgeCheckedEntry.source =
      expectedAutoBridgeCheckedSource :=
  rfl

/-- The CLI-registry host-query source is exactly its full rendered text. -/
theorem autoBridgeCheckedSourceEntry_source_eq :
    _root_.TetraStereo.CLI.CertificateSourceRegistry.autoBridgeCheckedSourceEntry.source =
      expectedAutoBridgeQuerySource :=
  rfl

/-- Generic renderer bridge for a compiled refusal artifact. -/
theorem compileOfficialStereoRefusal_source_eq
    (request : _root_.TetraStereo.Engine.OfficialStereoRequest)
    (reason : _root_.TetraStereo.Engine.RefusalReason)
    (proof : _root_.TetraStereo.Engine.OfficialStereoRefusalClaim request reason) :
    (_root_.TetraStereo.Engine.compileOfficialStereoRefusal request reason proof).source =
      (request.theoremPlan.refusalTheoremExport reason).source :=
  rfl


theorem ccl4Request_theoremPlan_eq :
    _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4Request.theoremPlan =
      _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4OfficialTheoremPlan := by
  rw [_root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4Request_eq_concrete]
  rfl

/-- The registered `CCl4` artifact is literally the artifact compiled from the actual
extracted request and the actual computed refusal claim. -/
theorem ccl4Refusal_artifact_eq_compile :
    _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4Refusal.artifact =
      _root_.TetraStereo.Engine.compileOfficialStereoRefusal
        _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4Request
        _root_.TetraStereo.Engine.RefusalReason.unresolvedOfficialPriorities
        _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4Request_refusal_claim :=
  rfl




theorem ccl4Refusal_artifact_source_eq :
    _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4Refusal.artifact.source =
      expectedCcl4RefusalSource := by
  rw [ccl4Refusal_artifact_eq_compile]
  rw [compileOfficialStereoRefusal_source_eq]
  rw [ccl4Request_theoremPlan_eq]
  rfl

/-! ## Live proof references

The rendered proof terms name the live checked theorems; the retired
`autoBridgeRequest_refusal_claim` appears nowhere in the registries or the rendered
texts.  Together with the exact source equalities above, these theorems rule out a
stale reference by construction. -/

/-- The wrapper export uses the checked prepared-transaction theorem. -/
theorem autoBridgeCheckedTheoremExport_theoremName :
    _root_.TetraStereo.Examples.OfficialStereoBuilder.autoBridgeCheckedTheoremExport.theoremName =
      "auto_bridge_official_stereo_checked" :=
  rfl

/-- The wrapper export's proof term is the live checked prepared proof. -/
theorem autoBridgeCheckedTheoremExport_proofTerm :
    _root_.TetraStereo.Examples.OfficialStereoBuilder.autoBridgeCheckedTheoremExport.proofTerm =
      "  exact TetraStereo.Examples.OfficialStereoBuilder.autoBridgePrepared_checked" :=
  rfl

/-- The `CCl4` export theorem name. -/
theorem ccl4OfficialTheoremPlan_theoremName :
    _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4OfficialTheoremPlan.theoremName =
      "ccl4_official_stereo_refusal" :=
  rfl

/-- The `CCl4` export proof term is the live refusal proof derived from the computed tie. -/
theorem ccl4OfficialTheoremPlan_proofTerm :
    _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4OfficialTheoremPlan.proofTerm =
      "  exact TetraStereo.Examples.OfficialStereoBuilder.ccl4Request_refusal_claim" :=
  rfl

/-! ## Registry positions

The preserved example sits at index 14 and the `CCl4` refusal at index 15 of both
sixteen-entry registries.  The source regressions compose the registered entry with the
exact-text theorems above; the `CCl4` artifact source is reached through the
projection-safe artifact-source relation (no evaluation of the extracted request is
needed to select the registered entry). -/

/-- Examples registry, index 14: the checked wrapper entry. -/
theorem publicDemoCertificates_position14_key :
    (_root_.TetraStereo.Examples.CertificateExportRegistry.publicDemoCertificates[14]?).map
        (fun entry => entry.key) = some "auto-bridge-official-stereo-checked" :=
  rfl

/-- Examples registry, index 15: the real `CCl4` refusal entry. -/
theorem publicDemoCertificates_position15_key :
    (_root_.TetraStereo.Examples.CertificateExportRegistry.publicDemoCertificates[15]?).map
        (fun entry => entry.key) = some "ccl4-official-stereo-refusal" :=
  rfl

/-- CLI registry, index 14: the checked host-query entry. -/
theorem publicDemoCertificateSources_position14_key :
    (_root_.TetraStereo.CLI.CertificateSourceRegistry.publicDemoCertificateSources[14]?).map
        (fun entry => entry.key) = some "auto-bridge-official-stereo-checked" :=
  rfl

/-- CLI registry, index 15: the real `CCl4` refusal entry. -/
theorem publicDemoCertificateSources_position15_key :
    (_root_.TetraStereo.CLI.CertificateSourceRegistry.publicDemoCertificateSources[15]?).map
        (fun entry => entry.key) = some "ccl4-official-stereo-refusal" :=
  rfl

/-- Examples registry, index 14: the registered source is the checked wrapper text. -/
theorem publicDemoCertificates_position14_source :
    (_root_.TetraStereo.Examples.CertificateExportRegistry.publicDemoCertificates[14]?).map
        (fun entry => entry.source) = some expectedAutoBridgeCheckedSource := by
  have h :
      (_root_.TetraStereo.Examples.CertificateExportRegistry.publicDemoCertificates[14]?).map
          (fun entry => entry.source) =
        some _root_.TetraStereo.Examples.CertificateExportRegistry.autoBridgeCheckedEntry.source :=
    rfl
  rw [h, autoBridgeCheckedEntry_source_eq]

/-- Examples registry, index 15: the registered source is the real `CCl4` refusal text. -/
theorem publicDemoCertificates_position15_source :
    (_root_.TetraStereo.Examples.CertificateExportRegistry.publicDemoCertificates[15]?).map
        (fun entry => entry.source) = some expectedCcl4RefusalSource := by
  have h :
      (_root_.TetraStereo.Examples.CertificateExportRegistry.publicDemoCertificates[15]?).map
          (fun entry => entry.source) =
        some _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4Refusal.artifact.source :=
    rfl
  rw [h, ccl4Refusal_artifact_source_eq]

/-- CLI registry, index 14: the registered source is the host-query text. -/
theorem publicDemoCertificateSources_position14_source :
    (_root_.TetraStereo.CLI.CertificateSourceRegistry.publicDemoCertificateSources[14]?).map
        (fun entry => entry.source) = some expectedAutoBridgeQuerySource := by
  have h :
      (_root_.TetraStereo.CLI.CertificateSourceRegistry.publicDemoCertificateSources[14]?).map
          (fun entry => entry.source) =
        some _root_.TetraStereo.CLI.CertificateSourceRegistry.autoBridgeCheckedSourceEntry.source :=
    rfl
  rw [h, autoBridgeCheckedSourceEntry_source_eq]

/-- CLI registry, index 15: the registered source is the artifact-claim wrapper text.
This uses the CLI registry renderer, which differs from the Examples artifact renderer
above; no byte equality between the two `CCl4` texts is asserted. -/
theorem publicDemoCertificateSources_position15_source :
    (_root_.TetraStereo.CLI.CertificateSourceRegistry.publicDemoCertificateSources[15]?).map
        (fun entry => entry.source) = some expectedCliCcl4ClaimSource :=
  rfl

/-! ## Main regression and kernel-authority guards -/

/-- The three generated modules root compiles separately are exactly the texts the two
live registries render: the checked wrapper, the checked host query, and the genuine
`CCl4` refusal artifact. -/
theorem generatedCertificateSources_exact :
    _root_.TetraStereo.Examples.CertificateExportRegistry.autoBridgeCheckedEntry.source =
        expectedAutoBridgeCheckedSource ∧
      _root_.TetraStereo.CLI.CertificateSourceRegistry.autoBridgeCheckedSourceEntry.source =
        expectedAutoBridgeQuerySource ∧
      _root_.TetraStereo.Examples.OfficialStereoBuilder.ccl4Refusal.artifact.source =
        expectedCcl4RefusalSource :=
  ⟨autoBridgeCheckedEntry_source_eq, autoBridgeCheckedSourceEntry_source_eq,
    ccl4Refusal_artifact_source_eq⟩

assert_kernel_only autoBridgeCheckedEntry_source_eq
assert_kernel_only autoBridgeCheckedSourceEntry_source_eq
assert_kernel_only ccl4Request_theoremPlan_eq
assert_kernel_only ccl4Refusal_artifact_source_eq
assert_kernel_only autoBridgeCheckedEntry_artifact_checked
assert_kernel_only ccl4Refusal_artifact_checked
assert_kernel_only generatedCertificateSources_exact

end GeneratedCertificateValidation
end Examples
end TetraStereo
