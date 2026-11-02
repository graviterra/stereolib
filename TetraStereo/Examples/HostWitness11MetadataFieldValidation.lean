import TetraStereo.Examples.HostAnalysisRequestKernelWitness11Names
import TetraStereo.Examples.HostAnalysisRequestKernelWitness11CoverageMetadata
import TetraStereo.Examples.HostWitnessRequestFieldProjections
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestKernelProof

open Engine
open OneCenter
open HostAnalysisRequestBuilder

noncomputable section

/-! ### Memory-safe metadata validation for the index-eleven witness

This module replaces the monolithic closing `rfl` of
`witness11ViaRequest.validateMetadataShape` with fourteen separately compiled validator
premises.

**Diagnosed failure mode.**  `witness11ViaRequest` is definitionally
`(broadSurfaceMoleculeAnalysisRequest.witnessRequest? witness11OutputTarget).getD
fallbackWitnessRequest`.  Any proof step that normalizes the whole request — a closing `rfl`, a
`simp` over the validator, or an accidental defeq check between the `getD` term and the named
definition — makes the kernel reduce the entire broad-surface fixture witness list inside the
final metadata module.  On top of the imported environments that reduction crossed the 6 GiB
aggregate bound (exit `-15`, cgroup `memory.max = 6442450944`).

**Isolation strategy.**  The proof below never reduces `witnessRequest?` for the fixture:

* `witness11FieldValidation_selected_getD` is a direct application of the compiled generic `getD`
  selection lemma, stated in exactly the lemma's `getD` shape so the elaborator has no defeq
  obligation against the named definition (measured: seconds, no bound pressure).
* `witness11FieldValidation_eq_getD` is the definitional equation proved by `rfl`; the kernel
  only unfolds the `witness11ViaRequest` definition, after which both sides are syntactically
  identical, so no `Option.getD` computation runs.
* `witness11FieldValidation_selected` rewrites the first equation along this definitional
  equation by syntactic rewriting only.
* `witnessRequest?_allFields` (compiled, approved generic helper) exposes the constructor fields
  of the selected request.  The selected witness is identified with the opaque
  `witness11WitnessSnapshot` through `witness11ViaRequest_witness`; the coverage source is
  identified with the concrete official-center request through the `head?` computation
  `witness11FieldValidation_coverageSelected` (no molecule or graph analysis).
* Each of the fourteen validator premises is a separate compiled theorem.  The `rfl`/`decide`
  ones reduce only over the small snapshot strings and lists.  The import/name and coverage
  facts are consumed from the already-GREEN split modules as opaque constants.
* The exported theorem is a direct application of
  `validateMetadataShape_eq_ok_of_fields` to the fourteen premises; there is no shared
  fourteen-hole tactic goal and no reduction of the request.

No field success is assumed: every premise is proved.  The exported statement is unchanged:
`witness11ViaRequest.validateMetadataShape = .ok ()`. -/

/-- The compiled generic `getD` selection lemma, kept in its native `getD` shape. -/
theorem witness11FieldValidation_selected_getD :
    broadSurfaceMoleculeAnalysisRequest.witnessRequest? witness11OutputTarget =
      some ((broadSurfaceMoleculeAnalysisRequest.witnessRequest? witness11OutputTarget).getD
        fallbackWitnessRequest) :=
  HostMoleculeAnalysisRequest.witnessRequest?_eq_some_getD_of_getD_witness_ready
    broadSurfaceMoleculeAnalysisRequest witness11OutputTarget fallbackWitnessRequest
    witness11FallbackRequest_not_ready witness11ViaRequest_ready

/-- `witness11ViaRequest` is definitionally the `getD` selection.  Only the definition is
unfolded; the witness search is not run. -/
theorem witness11FieldValidation_eq_getD :
    witness11ViaRequest =
      (broadSurfaceMoleculeAnalysisRequest.witnessRequest? witness11OutputTarget).getD
        fallbackWitnessRequest := by
  rfl

/-- The generic selection lemma stated for the named definition, by syntactic rewriting. -/
theorem witness11FieldValidation_selected :
    broadSurfaceMoleculeAnalysisRequest.witnessRequest? witness11OutputTarget =
      some witness11ViaRequest := by
  rw [witness11FieldValidation_selected_getD, witness11FieldValidation_eq_getD.symm]



theorem witness11FieldValidation_coverageSelected :
    broadSurfaceMoleculeAnalysisRequest.coverageSourceRequest? =
      some (broadSurfaceMoleculeAnalysisRequest.officialStereoRequest
        broadSurfaceOfficialCenterTarget) := by
  rfl

/- `validateMetadataShape` premise 1: the package key is nonempty. -/
set_option maxHeartbeats 1000000 in
theorem witness11FieldValidation_premise_key :
    witness11ViaRequest.key ≠ "" := by
  obtain ⟨witness, _coverageSource, _hw, _hc, hkey, _hdesc, hwit, _hfile, _hpath, _hdef,
    _hthm, _hmod, _hpkt, _hann, _hblue, _howner, _hcovthm, _hdeps, _himports,
    _hoptions⟩ :=
    HostMoleculeAnalysisRequest.witnessRequest?_allFields
      broadSurfaceMoleculeAnalysisRequest witness11OutputTarget
      witness11FieldValidation_selected
  have hsnap : witness = witness11WitnessSnapshot :=
    hwit.symm.trans witness11ViaRequest_witness
  rw [hkey, hsnap]
  decide

/- `validateMetadataShape` premise 2: the description is nonempty. -/
set_option maxHeartbeats 1000000 in
theorem witness11FieldValidation_premise_description :
    witness11ViaRequest.description ≠ "" := by
  obtain ⟨witness, _coverageSource, _hw, _hc, _hkey, hdesc, hwit, _hfile, _hpath, _hdef,
    _hthm, _hmod, _hpkt, _hann, _hblue, _howner, _hcovthm, _hdeps, _himports,
    _hoptions⟩ :=
    HostMoleculeAnalysisRequest.witnessRequest?_allFields
      broadSurfaceMoleculeAnalysisRequest witness11OutputTarget
      witness11FieldValidation_selected
  have hsnap : witness = witness11WitnessSnapshot :=
    hwit.symm.trans witness11ViaRequest_witness
  rw [hdesc, hsnap]
  decide

/- `validateMetadataShape` premise 3: the namespace path is valid. -/
set_option maxHeartbeats 1000000 in
theorem witness11FieldValidation_premise_namespacePath :
    validateNamespacePath "namespacePath" witness11ViaRequest.namespacePath = .ok () := by
  obtain ⟨_witness, _coverageSource, _hw, _hc, _hkey, _hdesc, _hwit, _hfile, hpath, _hdef,
    _hthm, _hmod, _hpkt, _hann, _hblue, _howner, _hcovthm, _hdeps, _himports,
    _hoptions⟩ :=
    HostMoleculeAnalysisRequest.witnessRequest?_allFields
      broadSurfaceMoleculeAnalysisRequest witness11OutputTarget
      witness11FieldValidation_selected
  rw [hpath]
  rfl

/- `validateMetadataShape` premise 5: the option lines are valid. -/
set_option maxHeartbeats 1000000 in
theorem witness11FieldValidation_premise_options :
    validateOptionLines "options" witness11ViaRequest.options = .ok () := by
  obtain ⟨_witness, _coverageSource, _hw, _hc, _hkey, _hdesc, _hwit, _hfile, _hpath, _hdef,
    _hthm, _hmod, _hpkt, _hann, _hblue, _howner, _hcovthm, _hdeps, _himports,
    hoptions⟩ :=
    HostMoleculeAnalysisRequest.witnessRequest?_allFields
      broadSurfaceMoleculeAnalysisRequest witness11OutputTarget
      witness11FieldValidation_selected
  rw [hoptions]
  rfl

/- `validateMetadataShape` premise 6: the generated file name is importable. -/
set_option maxHeartbeats 1000000 in
theorem witness11FieldValidation_premise_fileName :
    validateImportableLeanFileName "fileName" witness11ViaRequest.fileName = .ok () := by
  obtain ⟨witness, _coverageSource, _hw, _hc, _hkey, _hdesc, hwit, hfile, _hpath, _hdef,
    _hthm, _hmod, _hpkt, _hann, _hblue, _howner, _hcovthm, _hdeps, _himports,
    _hoptions⟩ :=
    HostMoleculeAnalysisRequest.witnessRequest?_allFields
      broadSurfaceMoleculeAnalysisRequest witness11OutputTarget
      witness11FieldValidation_selected
  have hsnap : witness = witness11WitnessSnapshot :=
    hwit.symm.trans witness11ViaRequest_witness
  rw [hfile, hsnap]
  rfl

/- `validateMetadataShape` premise 8: the coverage source module name is valid. -/
set_option maxHeartbeats 1000000 in
theorem witness11FieldValidation_premise_coverageSourceModule :
    validateModuleNames "coverageSourceModule"
      [witness11ViaRequest.coverageSourceModule] = .ok () := by
  obtain ⟨_witness, coverageSource, _hw, hc, _hkey, _hdesc, _hwit, _hfile, _hpath, _hdef,
    _hthm, hmod, _hpkt, _hann, _hblue, _howner, _hcovthm, _hdeps, _himports,
    _hoptions⟩ :=
    HostMoleculeAnalysisRequest.witnessRequest?_allFields
      broadSurfaceMoleculeAnalysisRequest witness11OutputTarget
      witness11FieldValidation_selected
  have hsource : coverageSource =
      broadSurfaceMoleculeAnalysisRequest.officialStereoRequest
        broadSurfaceOfficialCenterTarget :=
    Option.some_inj.mp (hc.symm.trans witness11FieldValidation_coverageSelected)
  rw [hmod, hsource]
  rfl

/- `validateMetadataShape` premise 9: the coverage packet name is valid. -/
set_option maxHeartbeats 1000000 in
theorem witness11FieldValidation_premise_coverageSourcePacketName :
    validateModuleNames "coverageSourcePacketName"
      [witness11ViaRequest.coverageSourcePacketName] = .ok () := by
  obtain ⟨_witness, coverageSource, _hw, hc, _hkey, _hdesc, _hwit, _hfile, _hpath, _hdef,
    _hthm, _hmod, hpkt, _hann, _hblue, _howner, _hcovthm, _hdeps, _himports,
    _hoptions⟩ :=
    HostMoleculeAnalysisRequest.witnessRequest?_allFields
      broadSurfaceMoleculeAnalysisRequest witness11OutputTarget
      witness11FieldValidation_selected
  have hsource : coverageSource =
      broadSurfaceMoleculeAnalysisRequest.officialStereoRequest
        broadSurfaceOfficialCenterTarget :=
    Option.some_inj.mp (hc.symm.trans witness11FieldValidation_coverageSelected)
  rw [hpkt, hsource]
  rfl

/- `validateMetadataShape` premise 10: the coverage annotations name is valid. -/
set_option maxHeartbeats 1000000 in
theorem witness11FieldValidation_premise_coverageSourceAnnotationsName :
    validateModuleNames "coverageSourceAnnotationsName"
      [witness11ViaRequest.coverageSourceAnnotationsName] = .ok () := by
  obtain ⟨_witness, coverageSource, _hw, hc, _hkey, _hdesc, _hwit, _hfile, _hpath, _hdef,
    _hthm, _hmod, _hpkt, hann, _hblue, _howner, _hcovthm, _hdeps, _himports,
    _hoptions⟩ :=
    HostMoleculeAnalysisRequest.witnessRequest?_allFields
      broadSurfaceMoleculeAnalysisRequest witness11OutputTarget
      witness11FieldValidation_selected
  have hsource : coverageSource =
      broadSurfaceMoleculeAnalysisRequest.officialStereoRequest
        broadSurfaceOfficialCenterTarget :=
    Option.some_inj.mp (hc.symm.trans witness11FieldValidation_coverageSelected)
  rw [hann, hsource]
  rfl

/- `validateMetadataShape` premise 11: the coverage blueprint name is valid. -/
set_option maxHeartbeats 1000000 in
theorem witness11FieldValidation_premise_coverageSourceBlueprintName :
    validateModuleNames "coverageSourceBlueprintName"
      [witness11ViaRequest.coverageSourceBlueprintName] = .ok () := by
  obtain ⟨_witness, coverageSource, _hw, hc, _hkey, _hdesc, _hwit, _hfile, _hpath, _hdef,
    _hthm, _hmod, _hpkt, _hann, hblue, _howner, _hcovthm, _hdeps, _himports,
    _hoptions⟩ :=
    HostMoleculeAnalysisRequest.witnessRequest?_allFields
      broadSurfaceMoleculeAnalysisRequest witness11OutputTarget
      witness11FieldValidation_selected
  have hsource : coverageSource =
      broadSurfaceMoleculeAnalysisRequest.officialStereoRequest
        broadSurfaceOfficialCenterTarget :=
    Option.some_inj.mp (hc.symm.trans witness11FieldValidation_coverageSelected)
  rw [hblue, hsource]
  rfl

/- `validateMetadataShape` premise 12: the coverage owner name is valid. -/
set_option maxHeartbeats 1000000 in
theorem witness11FieldValidation_premise_coverageSourceOwnerName :
    validateModuleNames "coverageSourceOwnerName"
      [witness11ViaRequest.coverageSourceOwnerName] = .ok () := by
  obtain ⟨_witness, coverageSource, _hw, hc, _hkey, _hdesc, _hwit, _hfile, _hpath, _hdef,
    _hthm, _hmod, _hpkt, _hann, _hblue, howner, _hcovthm, _hdeps, _himports,
    _hoptions⟩ :=
    HostMoleculeAnalysisRequest.witnessRequest?_allFields
      broadSurfaceMoleculeAnalysisRequest witness11OutputTarget
      witness11FieldValidation_selected
  have hsource : coverageSource =
      broadSurfaceMoleculeAnalysisRequest.officialStereoRequest
        broadSurfaceOfficialCenterTarget :=
    Option.some_inj.mp (hc.symm.trans witness11FieldValidation_coverageSelected)
  rw [howner, hsource]
  rfl

/-- **Field-projection validation of the index-eleven request metadata.**

The exact previous statement, proved by applying the field-decomposition theorem to the fourteen
separately compiled premises.  No request reduction and no assumed field success occur in this
final application. -/
theorem witness11ViaRequest_metadata_from_fields :
    witness11ViaRequest.validateMetadataShape = .ok () :=
  HostMoleculeTargetWitnessRequest.validateMetadataShape_eq_ok_of_fields
    witness11ViaRequest
    witness11FieldValidation_premise_key
    witness11FieldValidation_premise_description
    witness11FieldValidation_premise_namespacePath
    witness11ViaRequest_imports
    witness11FieldValidation_premise_options
    witness11FieldValidation_premise_fileName
    witness11ViaRequest_names
    witness11FieldValidation_premise_coverageSourceModule
    witness11FieldValidation_premise_coverageSourcePacketName
    witness11FieldValidation_premise_coverageSourceAnnotationsName
    witness11FieldValidation_premise_coverageSourceBlueprintName
    witness11FieldValidation_premise_coverageSourceOwnerName
    witness11ViaRequest_coverageOwner
    witness11ViaRequest_coverageNamesReady

assert_kernel_only witness11FieldValidation_selected_getD
assert_kernel_only witness11FieldValidation_eq_getD
assert_kernel_only witness11FieldValidation_selected
assert_kernel_only witness11FieldValidation_coverageSelected
assert_kernel_only witness11FieldValidation_premise_key
assert_kernel_only witness11FieldValidation_premise_description
assert_kernel_only witness11FieldValidation_premise_namespacePath
assert_kernel_only witness11FieldValidation_premise_options
assert_kernel_only witness11FieldValidation_premise_fileName
assert_kernel_only witness11FieldValidation_premise_coverageSourceModule
assert_kernel_only witness11FieldValidation_premise_coverageSourcePacketName
assert_kernel_only witness11FieldValidation_premise_coverageSourceAnnotationsName
assert_kernel_only witness11FieldValidation_premise_coverageSourceBlueprintName
assert_kernel_only witness11FieldValidation_premise_coverageSourceOwnerName
assert_kernel_only witness11ViaRequest_metadata_from_fields

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
