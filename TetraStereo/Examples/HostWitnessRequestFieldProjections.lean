import TetraStereo.Examples.HostWitnessRequestMetadataConstruction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Engine
namespace HostMoleculeAnalysisRequest

/-! ### Generic field projections for successful witness-request construction

`HostMoleculeAnalysisRequest.witnessRequest?` selects one target witness and one coverage
source request and then fills a `HostMoleculeTargetWitnessRequest` literal.  The companion
module `HostWitnessRequestMetadataConstruction` already records the *package-identity* fields
(`key`, `fileName`, `definitionName`, `coverageTheoremName`, `theoremName`) of a successful
selection.

This module adds the remaining constructor fields, once and generically:
`description`, `namespacePath`, `options`, `dependencyTheoremNames`, `imports`, and the five
coverage-source fields `coverageSourceModule`, `coverageSourcePacketName`,
`coverageSourceAnnotationsName`, `coverageSourceBlueprintName`, `coverageSourceOwnerName`.

Every proof is a structural case split on `target.witness?` and
`request.coverageSourceRequest?`, followed by `Option.some` injectivity and `rfl`.  No fixture
witness list, no concrete molecule analysis request, and no assumed equality about the
selected record is unfolded or postulated.  Downstream modules can therefore rewrite the
fields of a successfully constructed request through these opaque constants instead of
re-reducing the whole fixture search. -/

/-- **Constructor-input decomposition.**  A successful `witnessRequest?` selection exposes the
exact target witness and coverage source request that produced it, together with the equation
`result = constructedWitnessRequest request witness coverageSource`.

The two input-selection hypotheses are *derived*, not assumed: the proof case-splits on
`target.witness?` and `request.coverageSourceRequest?` and in each `none` branch derives a
contradiction from the success hypothesis. -/
theorem witnessRequest?_exists_constructed
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    ∃ (witness : HostMoleculeTargetWitness) (coverageSource : HostOfficialStereoRequest),
      target.witness? request.key request.detectorCoverage request.packet request.annotations =
          some witness ∧
        request.coverageSourceRequest? = some coverageSource ∧
          result = constructedWitnessRequest request witness coverageSource := by
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
          exact ⟨witness, coverageSource, rfl, rfl, h.symm⟩

/-- **All-fields theorem.**  Every field of a successfully selected witness request is the
corresponding field of the constructor literal built from the selected target witness and
coverage source request.

This is the single reusable fact downstream fixture modules should invoke; the individual
projections below are its components. -/
theorem witnessRequest?_allFields
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    ∃ (witness : HostMoleculeTargetWitness) (coverageSource : HostOfficialStereoRequest),
      target.witness? request.key request.detectorCoverage request.packet request.annotations =
          some witness ∧
        request.coverageSourceRequest? = some coverageSource ∧
          result.key = witness.expectedPackageKey ∧
            result.description =
                request.description ++ ": molecule-specific target certificate for " ++
                  witness.targetKeySuffix ∧
              result.witness = witness ∧
                result.fileName = witness.expectedFileName ∧
                  result.namespacePath = request.witnessNamespacePath ∧
                    result.definitionName = witness.expectedDefinitionName ∧
                      result.theoremName = witness.expectedTheoremName ∧
                        result.coverageSourceModule = coverageSource.moduleName ∧
                          result.coverageSourcePacketName =
                              HostAnalysisSuiteRequest.officialCoveragePacketName
                                coverageSource ∧
                            result.coverageSourceAnnotationsName =
                                HostAnalysisSuiteRequest.officialCoverageAnnotationsName
                                  coverageSource ∧
                              result.coverageSourceBlueprintName =
                                  HostAnalysisSuiteRequest.officialCoverageBlueprintName
                                    coverageSource ∧
                                result.coverageSourceOwnerName =
                                    HostAnalysisSuiteRequest.officialCoverageOwnerRequestKeyName
                                      coverageSource ∧
                                  result.coverageTheoremName =
                                      witness.expectedCoverageTheoremName ∧
                                    result.dependencyTheoremNames =
                                        request.claimTheoremsForKeys witness.theoremFamilyKeys ∧
                                      result.imports =
                                          request.witnessImportsForKeys coverageSource.moduleName
                                            witness.theoremFamilyKeys ∧
                                        result.options =
                                          ["set_option maxHeartbeats 1000000",
                                            "set_option maxRecDepth 10000"] := by
  obtain ⟨witness, coverageSource, hw, hc, heq⟩ :=
    witnessRequest?_exists_constructed request target h
  subst result
  exact ⟨witness, coverageSource, hw, hc, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The selected witness stored in the result is exactly the witness selected by `target.witness?`.

The success hypothesis already forces `coverageSourceRequest?` to succeed, so the proof only
case-splits on the target-witness lookup. -/
theorem witnessRequest?_witness_of_witness?
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest} {witness : HostMoleculeTargetWitness}
    (h : request.witnessRequest? target = some result)
    (hw :
      target.witness? request.key request.detectorCoverage request.packet request.annotations =
        some witness) :
    result.witness = witness := by
  cases hc : request.coverageSourceRequest? with
  | none =>
      simp [HostMoleculeAnalysisRequest.witnessRequest?, hw, hc] at h
  | some coverageSource =>
      have hsome := witnessRequest?_eq_some_constructed request target hw hc
      rw [hsome] at h
      simp only [Option.some.injEq] at h
      subst result
      rfl

/-- **Target-side fields.**  Description, namespace path, options, dependency theorem names and
imports of a successfully selected witness request, expressed through `result.witness` and
`result.coverageSourceModule` so that no separate existential witness is needed. -/
theorem witnessRequest?_targetFields
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    result.description =
        request.description ++ ": molecule-specific target certificate for " ++
          result.witness.targetKeySuffix ∧
      result.namespacePath = request.witnessNamespacePath ∧
        result.options = ["set_option maxHeartbeats 1000000",
          "set_option maxRecDepth 10000"] ∧
          result.dependencyTheoremNames =
              request.claimTheoremsForKeys result.witness.theoremFamilyKeys ∧
            result.imports =
              request.witnessImportsForKeys result.coverageSourceModule
                result.witness.theoremFamilyKeys := by
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

/-- Canonical generated description of a successfully selected witness request. -/
theorem witnessRequest?_description
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    result.description =
      request.description ++ ": molecule-specific target certificate for " ++
        result.witness.targetKeySuffix :=
  (witnessRequest?_targetFields request target h).1

/-- Canonical namespace path of a successfully selected witness request. -/
theorem witnessRequest?_namespacePath
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    result.namespacePath = request.witnessNamespacePath :=
  (witnessRequest?_targetFields request target h).2.1

/-- Default `options` of a successfully selected witness request. -/
theorem witnessRequest?_options
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    result.options =
      ["set_option maxHeartbeats 1000000", "set_option maxRecDepth 10000"] :=
  (witnessRequest?_targetFields request target h).2.2.1

/-- Canonical dependency theorem names of a successfully selected witness request. -/
theorem witnessRequest?_dependencyTheoremNames
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    result.dependencyTheoremNames =
      request.claimTheoremsForKeys result.witness.theoremFamilyKeys :=
  (witnessRequest?_targetFields request target h).2.2.2.1

/-- Canonical import list of a successfully selected witness request. -/
theorem witnessRequest?_imports
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result) :
    result.imports =
      request.witnessImportsForKeys result.coverageSourceModule
        result.witness.theoremFamilyKeys :=
  (witnessRequest?_targetFields request target h).2.2.2.2

/-- **`getD` form of the description projection.**  The pattern matches a request defined as
`(request.witnessRequest? target).getD fallback` (the shape used by the index-eleven witness
module), so callers can rewrite the selected request's field without supplying the
intermediate `some` equation by hand: it is derived from fallback unreadiness and selected
readiness, as in `witnessRequest?_eq_some_getD_of_getD_witness_ready`. -/
theorem witnessRequest?_getD_description
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    (fallback : HostMoleculeTargetWitnessRequest)
    (hfallback : fallback.witness.ready = false)
    (hready : ((request.witnessRequest? target).getD fallback).witness.ready = true) :
    ((request.witnessRequest? target).getD fallback).description =
      request.description ++ ": molecule-specific target certificate for " ++
        ((request.witnessRequest? target).getD fallback).witness.targetKeySuffix :=
  witnessRequest?_description request target
    (witnessRequest?_eq_some_getD_of_getD_witness_ready request target fallback hfallback hready)

/-- `getD` form of the namespace-path projection. -/
theorem witnessRequest?_getD_namespacePath
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    (fallback : HostMoleculeTargetWitnessRequest)
    (hfallback : fallback.witness.ready = false)
    (hready : ((request.witnessRequest? target).getD fallback).witness.ready = true) :
    ((request.witnessRequest? target).getD fallback).namespacePath =
      request.witnessNamespacePath :=
  witnessRequest?_namespacePath request target
    (witnessRequest?_eq_some_getD_of_getD_witness_ready request target fallback hfallback hready)

/-- `getD` form of the options projection. -/
theorem witnessRequest?_getD_options
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    (fallback : HostMoleculeTargetWitnessRequest)
    (hfallback : fallback.witness.ready = false)
    (hready : ((request.witnessRequest? target).getD fallback).witness.ready = true) :
    ((request.witnessRequest? target).getD fallback).options =
      ["set_option maxHeartbeats 1000000", "set_option maxRecDepth 10000"] :=
  witnessRequest?_options request target
    (witnessRequest?_eq_some_getD_of_getD_witness_ready request target fallback hfallback hready)

/-- `getD` form of the dependency-theorem-name projection. -/
theorem witnessRequest?_getD_dependencyTheoremNames
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    (fallback : HostMoleculeTargetWitnessRequest)
    (hfallback : fallback.witness.ready = false)
    (hready : ((request.witnessRequest? target).getD fallback).witness.ready = true) :
    ((request.witnessRequest? target).getD fallback).dependencyTheoremNames =
      request.claimTheoremsForKeys
        ((request.witnessRequest? target).getD fallback).witness.theoremFamilyKeys :=
  witnessRequest?_dependencyTheoremNames request target
    (witnessRequest?_eq_some_getD_of_getD_witness_ready request target fallback hfallback hready)

/-- `getD` form of the import-list projection. -/
theorem witnessRequest?_getD_imports
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    (fallback : HostMoleculeTargetWitnessRequest)
    (hfallback : fallback.witness.ready = false)
    (hready : ((request.witnessRequest? target).getD fallback).witness.ready = true) :
    ((request.witnessRequest? target).getD fallback).imports =
      request.witnessImportsForKeys
        ((request.witnessRequest? target).getD fallback).coverageSourceModule
        ((request.witnessRequest? target).getD fallback).witness.theoremFamilyKeys :=
  witnessRequest?_imports request target
    (witnessRequest?_eq_some_getD_of_getD_witness_ready request target fallback hfallback hready)

/-- **Coverage-source fields.**  If the coverage source request selected by
`request.coverageSourceRequest?` is `coverageSource`, then the five coverage-source fields of a
successfully selected witness request are the canonical names derived from that record.

The selection equality `hc` is a hypothesis, not an assumed field equality: the proof
case-splits on `target.witness?`, and the `none` branch is contradictory. -/
theorem witnessRequest?_coverageFields_of_coverageSourceRequest
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result)
    {coverageSource : HostOfficialStereoRequest}
    (hc : request.coverageSourceRequest? = some coverageSource) :
    result.coverageSourceModule = coverageSource.moduleName ∧
      result.coverageSourcePacketName =
          HostAnalysisSuiteRequest.officialCoveragePacketName coverageSource ∧
        result.coverageSourceAnnotationsName =
            HostAnalysisSuiteRequest.officialCoverageAnnotationsName coverageSource ∧
          result.coverageSourceBlueprintName =
              HostAnalysisSuiteRequest.officialCoverageBlueprintName coverageSource ∧
            result.coverageSourceOwnerName =
              HostAnalysisSuiteRequest.officialCoverageOwnerRequestKeyName coverageSource := by
  cases hw :
      target.witness? request.key request.detectorCoverage request.packet request.annotations with
  | none =>
      simp [HostMoleculeAnalysisRequest.witnessRequest?, hw] at h
  | some witness =>
      have hsome := witnessRequest?_eq_some_constructed request target hw hc
      rw [hsome] at h
      simp only [Option.some.injEq] at h
      subst result
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Canonical coverage-source module name of a successfully selected witness request. -/
theorem witnessRequest?_coverageSourceModule_of_coverageSourceRequest
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result)
    {coverageSource : HostOfficialStereoRequest}
    (hc : request.coverageSourceRequest? = some coverageSource) :
    result.coverageSourceModule = coverageSource.moduleName :=
  (witnessRequest?_coverageFields_of_coverageSourceRequest request target h hc).1

/-- Canonical coverage-source packet declaration name of a successfully selected witness
request. -/
theorem witnessRequest?_coverageSourcePacketName_of_coverageSourceRequest
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result)
    {coverageSource : HostOfficialStereoRequest}
    (hc : request.coverageSourceRequest? = some coverageSource) :
    result.coverageSourcePacketName =
      HostAnalysisSuiteRequest.officialCoveragePacketName coverageSource :=
  (witnessRequest?_coverageFields_of_coverageSourceRequest request target h hc).2.1

/-- Canonical coverage-source annotations declaration name of a successfully selected witness
request. -/
theorem witnessRequest?_coverageSourceAnnotationsName_of_coverageSourceRequest
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result)
    {coverageSource : HostOfficialStereoRequest}
    (hc : request.coverageSourceRequest? = some coverageSource) :
    result.coverageSourceAnnotationsName =
      HostAnalysisSuiteRequest.officialCoverageAnnotationsName coverageSource :=
  (witnessRequest?_coverageFields_of_coverageSourceRequest request target h hc).2.2.1

/-- Canonical coverage-source blueprint declaration name of a successfully selected witness
request. -/
theorem witnessRequest?_coverageSourceBlueprintName_of_coverageSourceRequest
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result)
    {coverageSource : HostOfficialStereoRequest}
    (hc : request.coverageSourceRequest? = some coverageSource) :
    result.coverageSourceBlueprintName =
      HostAnalysisSuiteRequest.officialCoverageBlueprintName coverageSource :=
  (witnessRequest?_coverageFields_of_coverageSourceRequest request target h hc).2.2.2.1

/-- Canonical coverage-source owner-key declaration name of a successfully selected witness
request. -/
theorem witnessRequest?_coverageSourceOwnerName_of_coverageSourceRequest
    (request : HostMoleculeAnalysisRequest) (target : HostStereochemicalOutputTarget)
    {result : HostMoleculeTargetWitnessRequest}
    (h : request.witnessRequest? target = some result)
    {coverageSource : HostOfficialStereoRequest}
    (hc : request.coverageSourceRequest? = some coverageSource) :
    result.coverageSourceOwnerName =
      HostAnalysisSuiteRequest.officialCoverageOwnerRequestKeyName coverageSource :=
  (witnessRequest?_coverageFields_of_coverageSourceRequest request target h hc).2.2.2.2

end HostMoleculeAnalysisRequest

namespace HostMoleculeTargetWitnessRequest

/-- **Field decomposition of `validateMetadataShape`.**  The fourteen validators that make up
`HostMoleculeTargetWitnessRequest.validateMetadataShape` can be discharged one field at a time.
A caller that has already proved each individual validator for a concrete request obtains the
whole `Except String Unit` computation without ever unfolding the request itself: the proof
below only unfolds the validator definition, never the request value.

This is the generic replacement for a monolithic closing `rfl` over a fixture-selected
request: each premise mentions exactly one field (or one derived field predicate), so a
downstream module can rewrite that field through the projection lemmas above and reduce only
the small resulting term. -/
theorem validateMetadataShape_eq_ok_of_fields
    (request : HostMoleculeTargetWitnessRequest)
    (hkey : request.key ≠ "")
    (hdescription : request.description ≠ "")
    (hnamespacePath : validateNamespacePath "namespacePath" request.namespacePath = .ok ())
    (himports : validateModuleNames "imports" request.imports = .ok ())
    (hoptions : validateOptionLines "options" request.options = .ok ())
    (hfileName : validateImportableLeanFileName "fileName" request.fileName = .ok ())
    (hgeneratedNames :
      validateLeanNames "generated target-witness names" request.generatedLeanNames = .ok ())
    (hcoverageSourceModule :
      validateModuleNames "coverageSourceModule" [request.coverageSourceModule] = .ok ())
    (hcoverageSourcePacketName :
      validateModuleNames "coverageSourcePacketName" [request.coverageSourcePacketName] =
        .ok ())
    (hcoverageSourceAnnotationsName :
      validateModuleNames "coverageSourceAnnotationsName"
        [request.coverageSourceAnnotationsName] = .ok ())
    (hcoverageSourceBlueprintName :
      validateModuleNames "coverageSourceBlueprintName" [request.coverageSourceBlueprintName] =
        .ok ())
    (hcoverageSourceOwnerName :
      validateModuleNames "coverageSourceOwnerName" [request.coverageSourceOwnerName] =
        .ok ())
    (hcoverageSourceOwnerCanonical :
      (request.coverageSourceOwnerName == request.expectedCoverageSourceOwnerName) = true)
    (hcoverageSourceNamesReady : request.coverageSourceNamesReady = true) :
    request.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp [requireHostRequestShape, hkey, hdescription, hnamespacePath, himports, hoptions,
    hfileName, hgeneratedNames, hcoverageSourceModule, hcoverageSourcePacketName,
    hcoverageSourceAnnotationsName, hcoverageSourceBlueprintName, hcoverageSourceOwnerName,
    hcoverageSourceOwnerCanonical, hcoverageSourceNamesReady]
  rfl

assert_kernel_only validateMetadataShape_eq_ok_of_fields

end HostMoleculeTargetWitnessRequest

namespace HostMoleculeAnalysisRequest

assert_kernel_only witnessRequest?_exists_constructed
assert_kernel_only witnessRequest?_allFields
assert_kernel_only witnessRequest?_witness_of_witness?
assert_kernel_only witnessRequest?_targetFields
assert_kernel_only witnessRequest?_description
assert_kernel_only witnessRequest?_namespacePath
assert_kernel_only witnessRequest?_options
assert_kernel_only witnessRequest?_dependencyTheoremNames
assert_kernel_only witnessRequest?_imports
assert_kernel_only witnessRequest?_getD_description
assert_kernel_only witnessRequest?_getD_namespacePath
assert_kernel_only witnessRequest?_getD_options
assert_kernel_only witnessRequest?_getD_dependencyTheoremNames
assert_kernel_only witnessRequest?_getD_imports
assert_kernel_only witnessRequest?_coverageFields_of_coverageSourceRequest
assert_kernel_only witnessRequest?_coverageSourceModule_of_coverageSourceRequest
assert_kernel_only witnessRequest?_coverageSourcePacketName_of_coverageSourceRequest
assert_kernel_only witnessRequest?_coverageSourceAnnotationsName_of_coverageSourceRequest
assert_kernel_only witnessRequest?_coverageSourceBlueprintName_of_coverageSourceRequest
assert_kernel_only witnessRequest?_coverageSourceOwnerName_of_coverageSourceRequest

end HostMoleculeAnalysisRequest
end Engine
end TetraStereo
