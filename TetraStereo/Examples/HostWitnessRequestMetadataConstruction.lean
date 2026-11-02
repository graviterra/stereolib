import TetraStereo.Engine.HostAnalysisRequestBuilder
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Engine
namespace HostMoleculeAnalysisRequest

/-! ### Structural metadata of successful witness-request construction

`HostMoleculeAnalysisRequest.witnessRequest?` is an `Option` do-block: it first selects a
molecule-specific target witness, then a coverage source request, and finally builds a
`HostMoleculeTargetWitnessRequest` literal whose `key`, `fileName`, `definitionName`,
`coverageTheoremName`, and `theoremName` fields are *by construction* the canonical fields of
the selected witness.

The lemmas below state that fact once, generically over the molecule analysis request and the
output target.  They let downstream fixture modules prove the canonical-name fields of a
successfully selected request by `Option.some` injectivity instead of re-reducing the whole
fixture witness list in every field proof.

This module is registered at `TetraStereo/Examples/HostWitnessRequestMetadataConstruction.lean`
but deliberately lives in the generic `TetraStereo.Engine.HostMoleculeAnalysisRequest` namespace
and imports only `TetraStereo.Engine.HostAnalysisRequestBuilder` plus `TetraStereo.KernelOnly`
(no `Examples` dependencies), so fixture modules can import it without an import cycle. -/

/-- The exact target-witness request record that `witnessRequest?` builds from one selected
target witness and one coverage source request.

This is the right-hand side of the constructor branch of `witnessRequest?`, with the two
`let`-bound intermediates of that definition inlined. -/
def constructedWitnessRequest (request : HostMoleculeAnalysisRequest)
    (witness : HostMoleculeTargetWitness) (coverageSource : HostOfficialStereoRequest) :
    HostMoleculeTargetWitnessRequest where
  key := witness.expectedPackageKey
  description :=
    request.description ++ ": molecule-specific target certificate for " ++
      witness.targetKeySuffix
  witness := witness
  fileName := witness.expectedFileName
  namespacePath := request.witnessNamespacePath
  definitionName := witness.expectedDefinitionName
  theoremName := witness.expectedTheoremName
  coverageSourceModule := coverageSource.moduleName
  coverageSourcePacketName :=
    HostAnalysisSuiteRequest.officialCoveragePacketName coverageSource
  coverageSourceAnnotationsName :=
    HostAnalysisSuiteRequest.officialCoverageAnnotationsName coverageSource
  coverageSourceBlueprintName :=
    HostAnalysisSuiteRequest.officialCoverageBlueprintName coverageSource
  coverageSourceOwnerName :=
    HostAnalysisSuiteRequest.officialCoverageOwnerRequestKeyName coverageSource
  coverageTheoremName := witness.expectedCoverageTheoremName
  dependencyTheoremNames := request.claimTheoremsForKeys witness.theoremFamilyKeys
  imports :=
    request.witnessImportsForKeys coverageSource.moduleName witness.theoremFamilyKeys

/-- Whenever both constructor inputs are present, `witnessRequest?` returns exactly
`constructedWitnessRequest`.  The proof is a structural case analysis; no concrete fixture is
evaluated. -/
theorem witnessRequest?_eq_some_constructed
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {witness : HostMoleculeTargetWitness} {coverageSource : HostOfficialStereoRequest}
    (hw :
      target.witness? request.key request.detectorCoverage request.packet request.annotations =
        some witness)
    (hc : request.coverageSourceRequest? = some coverageSource) :
    request.witnessRequest? target =
      some (constructedWitnessRequest request witness coverageSource) := by
  simp [HostMoleculeAnalysisRequest.witnessRequest?, constructedWitnessRequest, hw, hc]

/-- **Structural canonical-metadata theorem.**  If `witnessRequest?` succeeds and returns
`result`, then the five package-identity fields of `result` are the canonical ones derived from
`result.witness`.  No equality between the desired names and the constructed record is assumed:
the result is obtained by case analysis on the two constructor inputs and `Option.some`
injectivity. -/
theorem witnessRequest?_canonicalFields
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    result.key = result.witness.expectedPackageKey ∧
      result.fileName = result.witness.expectedFileName ∧
      result.definitionName = result.witness.expectedDefinitionName ∧
      result.coverageTheoremName = result.witness.expectedCoverageTheoremName ∧
      result.theoremName = result.witness.expectedTheoremName := by
  cases hw :
      target.witness? request.key request.detectorCoverage request.packet request.annotations with
  | none =>
      simp [HostMoleculeAnalysisRequest.witnessRequest?, hw] at h
  | some witness =>
      cases hc : request.coverageSourceRequest? with
      | none =>
          simp [HostMoleculeAnalysisRequest.witnessRequest?, hw, hc] at h
      | some coverageSource =>
          have hsome := witnessRequest?_eq_some_constructed request target hw hc
          rw [hsome] at h
          simp only [Option.some.injEq] at h
          subst result
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Canonical package key of a successfully selected witness request. -/
theorem witnessRequest?_key
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    result.key = result.witness.expectedPackageKey :=
  (witnessRequest?_canonicalFields request target h).1

/-- Canonical generated file name of a successfully selected witness request. -/
theorem witnessRequest?_fileName
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    result.fileName = result.witness.expectedFileName :=
  (witnessRequest?_canonicalFields request target h).2.1

/-- Canonical generated definition name of a successfully selected witness request. -/
theorem witnessRequest?_definitionName
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    result.definitionName = result.witness.expectedDefinitionName :=
  (witnessRequest?_canonicalFields request target h).2.2.1

/-- Canonical generated coverage-theorem name of a successfully selected witness request. -/
theorem witnessRequest?_coverageTheoremName
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    result.coverageTheoremName = result.witness.expectedCoverageTheoremName :=
  (witnessRequest?_canonicalFields request target h).2.2.2.1

/-- Canonical generated checked-theorem name of a successfully selected witness request. -/
theorem witnessRequest?_theoremName
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    result.theoremName = result.witness.expectedTheoremName :=
  (witnessRequest?_canonicalFields request target h).2.2.2.2

/-- **`getD` fallback specialization.**  If the fallback request used by `getD` is not ready but
the selected value is, then the option lookup cannot have been `none`: `witnessRequest?` must
have succeeded, and the selected value is exactly the result of that successful construction. -/
theorem witnessRequest?_eq_some_getD_of_getD_witness_ready
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    (fallback : HostMoleculeTargetWitnessRequest)
    (hfallback : fallback.witness.ready = false)
    (hready : ((request.witnessRequest? target).getD fallback).witness.ready = true) :
    request.witnessRequest? target =
      some ((request.witnessRequest? target).getD fallback) := by
  cases h : request.witnessRequest? target with
  | none =>
      rw [h] at hready
      simp [hfallback] at hready
  | some result =>
      simp

/-- Canonical definition name of the value selected by `getD`, from fallback unreadiness and
selected readiness. -/
theorem witnessRequest?_getD_definitionName
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    (fallback : HostMoleculeTargetWitnessRequest)
    (hfallback : fallback.witness.ready = false)
    (hready : ((request.witnessRequest? target).getD fallback).witness.ready = true) :
    ((request.witnessRequest? target).getD fallback).definitionName =
      ((request.witnessRequest? target).getD fallback).witness.expectedDefinitionName :=
  witnessRequest?_definitionName request target
    (witnessRequest?_eq_some_getD_of_getD_witness_ready request target fallback hfallback hready)

/-- Canonical coverage-theorem name of the value selected by `getD`, from fallback unreadiness
and selected readiness. -/
theorem witnessRequest?_getD_coverageTheoremName
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    (fallback : HostMoleculeTargetWitnessRequest)
    (hfallback : fallback.witness.ready = false)
    (hready : ((request.witnessRequest? target).getD fallback).witness.ready = true) :
    ((request.witnessRequest? target).getD fallback).coverageTheoremName =
      ((request.witnessRequest? target).getD fallback).witness.expectedCoverageTheoremName :=
  witnessRequest?_coverageTheoremName request target
    (witnessRequest?_eq_some_getD_of_getD_witness_ready request target fallback hfallback hready)

/-- Canonical checked-theorem name of the value selected by `getD`, from fallback unreadiness and
selected readiness. -/
theorem witnessRequest?_getD_theoremName
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    (fallback : HostMoleculeTargetWitnessRequest)
    (hfallback : fallback.witness.ready = false)
    (hready : ((request.witnessRequest? target).getD fallback).witness.ready = true) :
    ((request.witnessRequest? target).getD fallback).theoremName =
      ((request.witnessRequest? target).getD fallback).witness.expectedTheoremName :=
  witnessRequest?_theoremName request target
    (witnessRequest?_eq_some_getD_of_getD_witness_ready request target fallback hfallback hready)

assert_kernel_only witnessRequest?_eq_some_constructed
assert_kernel_only witnessRequest?_canonicalFields
assert_kernel_only witnessRequest?_key
assert_kernel_only witnessRequest?_fileName
assert_kernel_only witnessRequest?_definitionName
assert_kernel_only witnessRequest?_coverageTheoremName
assert_kernel_only witnessRequest?_theoremName
assert_kernel_only witnessRequest?_eq_some_getD_of_getD_witness_ready
assert_kernel_only witnessRequest?_getD_definitionName
assert_kernel_only witnessRequest?_getD_coverageTheoremName
assert_kernel_only witnessRequest?_getD_theoremName

end HostMoleculeAnalysisRequest
end Engine
end TetraStereo
