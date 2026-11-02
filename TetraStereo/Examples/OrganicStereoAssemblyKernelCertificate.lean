/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly
import TetraStereo.OneCenter.OrganicStereoSimultaneousCaseAssembly

set_option autoImplicit false



























namespace TetraStereo.Examples.OrganicStereoAssemblyKernelCertificate

/-! ## Molecular-evidence assembly (`TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly`)

All molecular declarations are referenced through the dedicated namespace that carries them. -/

section

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Exact left inverse: every independently supplied request, including its graph/conformation
compatibility fields, electronic unpaired-electron tie, and optional path/band presence data, is
recovered exactly by the decoder.  No hypothesis is left implicit. -/
example (request :
    TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.OrganicMolecularEvidence V) :
    TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.decode
        (TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.assemble request) =
      request :=
  TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.decode_assemble request

/-- Request injectivity: distinct requests have distinct constructed representations. -/
example : Function.Injective
    (TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.assemble :
      TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.OrganicMolecularEvidence V →
        TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.OrganicMolecularRepresentation
          V) :=
  TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.assemble_injective

/-- Arbitrary-set recovery: decoding the assembly image of any set of requests returns exactly
that set, preserving every correlation between the supplied channels. -/
example (requests : Set
    (TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.OrganicMolecularEvidence V)) :
    TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.decode ''
        (TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.assemble '' requests) =
      requests :=
  TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.decode_image_assemble_image
    requests

end

section

variable {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]

/-! ## Simultaneous case assembly (`TetraStereo.OneCenter`)

The empty-base-fields restriction and the explicit finite enumerations are hypotheses of the
theorems themselves, not of this certificate.  `CaseRequest` packs the base and the ordered bundle,
so the set equalities below correlate every channel; no product of marginals is used. -/

/-- Arbitrary correlated request-set recovery: for every set of whole requests whose bases have
empty case channels, the actual inverse applied to the assembly image returns exactly that set. -/
example (requests : Set (TetraStereo.OneCenter.CaseRequest V E B))
    (emptyBase : ∀ request ∈ requests,
      TetraStereo.OneCenter.CaseChannelsEmpty request.base) :
    TetraStereo.OneCenter.wholeRequestSet
        (TetraStereo.OneCenter.assembleSet requests) = requests :=
  TetraStereo.OneCenter.wholeRequestSet_assembleSet requests emptyBase

/-- Encoded arbitrary-set recovery through the real description encoding and request decoding:
for every set of empty-base requests and every explicit finite enumeration, encoding the assembled
descriptions, reading back the whole-request set, and decoding it returns exactly the original
correlated set. -/
example (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (requests : Set (TetraStereo.OneCenter.CaseRequest V E B))
    (emptyBase : ∀ request ∈ requests,
      TetraStereo.OneCenter.CaseChannelsEmpty request.base) :
    TetraStereo.OneCenter.decodeRequestSet eV eE eB
        (TetraStereo.OneCenter.wholeRequestSet
          (TetraStereo.OneCenter.encodeDescription eV eE eB ''
            TetraStereo.OneCenter.assembleSet requests)) = requests :=
  TetraStereo.OneCenter.decodeRequestSet_wholeRequestSet_encodeDescription_assembleSet
    eV eE eB requests emptyBase

end

/-! ## Selective kernel-authority assertions -/

/-! ### Molecular-evidence endpoints (dedicated namespace) -/

-- Exact left inverse of the molecular assembly on every independently supplied request.
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.decode_assemble

-- Injectivity of the molecular assembly.
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.assemble_injective

-- Recovery of the image of an arbitrary set of molecular requests.
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.decode_image_assemble_image

-- Exact recovery of both optional channel payloads and their presence tags.
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.assemble_paths?
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.assemble_bands?

-- Exact recovery of the supplied electronic evidence option.
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.assemble_electronic?

-- Band-source conformation compatibility, the source case used by the left inverse.
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.assemble_conformation_of_bands

/-! ### Simultaneous case-assembly endpoints (parent namespace) -/

-- Two-sided request inverse on every request with empty base case channels.
assert_kernel_only
  TetraStereo.OneCenter.wholeRequestOfState_assemble_of_emptyBase

-- Arbitrary correlated whole-request-set recovery.
assert_kernel_only
  TetraStereo.OneCenter.wholeRequestSet_assembleSet

-- Real request encoding/decoding round trip (not a `compatibleRequests` singleton).
assert_kernel_only
  TetraStereo.OneCenter.decodeRequest_encodeRequest

-- Assembly commutes with the actual description encoding.
assert_kernel_only
  TetraStereo.OneCenter.encodeDescription_assemble

-- Composite encoded arbitrary-set recovery: arbitrary empty-base correlated request set through
-- the real `encodeDescription`/`decodeDescription` route.
assert_kernel_only
  TetraStereo.OneCenter.decodeRequestSet_wholeRequestSet_encodeDescription_assembleSet
