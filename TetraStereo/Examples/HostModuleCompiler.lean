import TetraStereo.Engine.HostModuleCompiler

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace HostModuleCompiler

open OneCenter

noncomputable section

/-!
  Checked fixture for the host Lean module compiler.

  This file does not hand-author the host module.  It supplies structured host request data, then
  lets `HostOfficialStereoRequest.moduleSource` render the standalone Lean module that a host
  adapter would write.
-/

/-- Tetrahedral raw molecule used by the generated-host-module smoke test. -/
def compiledAutoBridgeRaw : RawMolecule where
  atoms :=
    [ AtomSpec.aliphatic Element.C
    , AtomSpec.aliphatic Element.F
    , AtomSpec.aliphatic Element.O
    , AtomSpec.aliphatic Element.N
    , AtomSpec.aliphatic Element.Cl
    ]
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.single }
    , { source := 0, target := 2, kind := ParsedBondKind.single }
    , { source := 0, target := 3, kind := ParsedBondKind.single }
    , { source := 0, target := 4, kind := ParsedBondKind.single }
    ]

/-- Six-carbon star molecule used to smoke-test typed non-center annotation serialization. -/
def compiledHelicalBridgeRaw : RawMolecule where
  atoms :=
    List.replicate 6 (AtomSpec.aliphatic Element.C)
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.single }
    , { source := 0, target := 2, kind := ParsedBondKind.single }
    , { source := 0, target := 3, kind := ParsedBondKind.single }
    , { source := 0, target := 4, kind := ParsedBondKind.single }
    ]

/-- A direct host request must reject duplicate unordered edges before emitting uncompilable Lean
source, independently of the external-packet intake check in that generated source. -/
def duplicateEdgeHostRaw : RawMolecule where
  atoms := [AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.F]
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.single }
    , { source := 1, target := 0, kind := ParsedBondKind.double }
    ]

/-- Typed detector annotations: branch atom `1` carries helical `M`, branch atom `2` carries `P`. -/
def compiledHelicalBridgeAnnotations : IndexedNoncenterStereoAnnotations where
  helices :=
    [ { helixPath := [1, 0, 5]
        frontReference := 1
        backReference := 5
        descriptor := HelicalDescriptor.M }
    , { helixPath := [2, 0, 5]
        frontReference := 2
        backReference := 5
        descriptor := HelicalDescriptor.P }
    ]

/-- Structured host request that the compiler renders into a standalone Lean module. -/
def compiledAutoBridgeHostRequest : Engine.HostOfficialStereoRequest where
  key := "compiled-auto-bridge-official-stereo-refusal"
  description := "compiled auto-built official-stereo refusal from host request"
  moduleFileName := "CompiledAutoBridgeHost.lean"
  namespacePath := ["TetraStereoGenerated", "Examples", "HostModules", "CompiledAutoBridge"]
  definitionPrefix := "compiledAutoBridge"
  packet := rawMoleculePacket compiledAutoBridgeRaw ChemistryImportTrust.proofCertifiedAdapter
  centerAtom := 0
  left := 0
  right := 1
  graphFuel := 0
  scheduleFuel := 0
  branchFuel := 0
  target := Engine.HostOfficialStereoCertificateTarget.refusal
    Engine.RefusalReason.unresolvedOfficialPriorities
  certificateFileName := "CompiledAutoBridgeOfficialStereoRefusal.lean"
  certificateTheoremName := "compiled_auto_bridge_official_stereo_query_checked"
  certificateNamespacePath := ["TetraStereoGenerated", "Examples", "Certificates"]

/-- Structured host request with typed helical annotations rendered by the compiler. -/
def compiledHelicalBridgeHostRequest : Engine.HostOfficialStereoRequest where
  key := "compiled-helical-bridge-official-stereo-comparison"
  description := "compiled official-stereo comparison from typed helical host annotations"
  moduleFileName := "CompiledHelicalBridgeHost.lean"
  namespacePath := ["TetraStereoGenerated", "Examples", "HostModules", "CompiledHelicalBridge"]
  definitionPrefix := "compiledHelicalBridge"
  packet := rawMoleculePacket compiledHelicalBridgeRaw ChemistryImportTrust.proofCertifiedAdapter
  annotations := compiledHelicalBridgeAnnotations
  centerAtom := 0
  left := 0
  right := 1
  graphFuel := 0
  scheduleFuel := 0
  branchFuel := 0
  target := Engine.HostOfficialStereoCertificateTarget.computedComparison
  certificateFileName := "CompiledHelicalBridgeOfficialStereoComparison.lean"
  certificateTheoremName := "compiled_helical_bridge_official_stereo_query_checked"
  certificateNamespacePath := ["TetraStereoGenerated", "Examples", "Certificates"]

/-- Deliberately inadmissible direct host request exercising the generated-module boundary. -/
def duplicateEdgeHostRequest : Engine.HostOfficialStereoRequest :=
  { compiledAutoBridgeHostRequest with
    key := "compiled-duplicate-edge-refusal"
    definitionPrefix := "compiledDuplicateEdge"
    packet := rawMoleculePacket duplicateEdgeHostRaw
    moduleFileName := "CompiledDuplicateEdgeHost.lean"
    namespacePath := ["TetraStereoGenerated", "Examples", "HostModules", "DuplicateEdge"]
    certificateFileName := "CompiledDuplicateEdgeCertificate.lean"
    certificateTheoremName := "compiled_duplicate_edge_checked" }

/-- Direct module generation refuses the duplicate before rendering a false proof by `rfl`. -/
theorem duplicateEdgeHostRequest_rejected :
    (match duplicateEdgeHostRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true := by
  decide

/-- Source-entry view of the generated host module. -/
def compiledAutoBridgeHostModuleEntry : Engine.CertificateSourceEntry :=
  compiledAutoBridgeHostRequest.moduleSourceEntry

/-- Source-entry view of the generated typed-annotation host module. -/
def compiledHelicalBridgeHostModuleEntry : Engine.CertificateSourceEntry :=
  compiledHelicalBridgeHostRequest.moduleSourceEntry

/-- The generated host-module entry uses a host-module key derived from the certificate key. -/
theorem compiledAutoBridgeHostModuleEntry_key :
    compiledAutoBridgeHostModuleEntry.key =
      "compiled-auto-bridge-official-stereo-refusal::host-module" :=
  rfl

/-- The compiler emits the expected standalone host module file name. -/
theorem compiledAutoBridgeHostModuleEntry_fileName :
    compiledAutoBridgeHostModuleEntry.fileName = "CompiledAutoBridgeHost.lean" :=
  rfl

/-- Shape validation cannot succeed when the generated host and certificate module names agree,
regardless of whether an earlier independent shape check has already rejected the request. -/
private theorem validateGeneratedShape_rejected_of_module_collision
    (request : Engine.HostOfficialStereoRequest)
    (hcollision : request.moduleName = request.certificateModuleName) :
    (match request.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true := by
  unfold Engine.HostOfficialStereoRequest.validateGeneratedShape
  cases h1 : Engine.requireHostRequestShape (request.key != "")
      "host official-stereo package key must not be empty"
  · rfl
  · cases h2 : Engine.requireHostRequestShape
        ((request.ownerRequestKey == "" && request.packageKeySuffix == "") ||
          (request.ownerRequestKey != "" &&
            Engine.hostPackageKeySegment? request.ownerRequestKey &&
            Engine.hostPackageKeySegment? request.packageKeySuffix &&
            request.key == Engine.hostScopedPackageKey request.ownerRequestKey request.packageKeySuffix))
        "host official-stereo package key owner/suffix metadata must exactly match the key"
    · rfl
    · cases h3 : Engine.validateNamespacePath "namespacePath" request.namespacePath
      · rfl
      · cases h4 : Engine.validateNamespacePath "certificateNamespacePath"
            request.certificateNamespacePath
        · rfl
        · cases h5 : Engine.validateModuleNames "moduleImports" request.moduleImports
          · rfl
          · cases h6 : Engine.validateOptionLines "options" request.options
            · rfl
            · cases h7 : Engine.validateGeneratedFileName "moduleFileName" request.moduleFileName
              · rfl
              · cases h8 : Engine.validateGeneratedFileName "certificateFileName"
                    request.certificateFileName
                · rfl
                · cases h9 : Engine.requireHostRequestShape request.packet.raw.admissible?
                      "host official-stereo raw molecule is not admissible"
                  · rfl
                  · simp [hcollision, Engine.requireHostRequestShape, Except.instMonad, Except.bind]

/-- Shape validation cannot succeed when the certificate theorem reuses a declaration in the host
namespace, independently of the outcomes of preceding shape checks. -/
private theorem validateGeneratedShape_rejected_of_declaration_collision
    (request : Engine.HostOfficialStereoRequest)
    (hnamespace : request.namespacePath = request.certificateNamespacePath)
    (hcontains : request.hostLocalDeclarationNames.contains request.certificateTheoremName = true) :
    (match request.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true := by
  have hmem : request.certificateTheoremName ∈ request.hostLocalDeclarationNames :=
    List.contains_iff_mem.mp hcontains
  unfold Engine.HostOfficialStereoRequest.validateGeneratedShape
  cases h1 : Engine.requireHostRequestShape (request.key != "")
      "host official-stereo package key must not be empty"
  · rfl
  · cases h2 : Engine.requireHostRequestShape
        ((request.ownerRequestKey == "" && request.packageKeySuffix == "") ||
          (request.ownerRequestKey != "" &&
            Engine.hostPackageKeySegment? request.ownerRequestKey &&
            Engine.hostPackageKeySegment? request.packageKeySuffix &&
            request.key == Engine.hostScopedPackageKey request.ownerRequestKey request.packageKeySuffix))
        "host official-stereo package key owner/suffix metadata must exactly match the key"
    · rfl
    · cases h3 : Engine.validateNamespacePath "namespacePath" request.namespacePath
      · rfl
      · cases h4 : Engine.validateNamespacePath "certificateNamespacePath"
            request.certificateNamespacePath
        · rfl
        · cases h5 : Engine.validateModuleNames "moduleImports" request.moduleImports
          · rfl
          · cases h6 : Engine.validateOptionLines "options" request.options
            · rfl
            · cases h7 : Engine.validateGeneratedFileName "moduleFileName" request.moduleFileName
              · rfl
              · cases h8 : Engine.validateGeneratedFileName "certificateFileName"
                    request.certificateFileName
                · rfl
                · cases h9 : Engine.requireHostRequestShape request.packet.raw.admissible?
                      "host official-stereo raw molecule is not admissible"
                  · rfl
                  · cases h10 : Engine.requireHostRequestShape
                        (decide (request.moduleName ≠ request.certificateModuleName))
                        "host official-stereo package has colliding host-module and certificate module paths"
                    · rfl
                    · simp [hnamespace, hmem, Engine.requireHostRequestShape,
                        Except.instMonad, Except.bind]

/-- Deliberately invalid request whose host module would collide with its certificate module. -/
def collidingHostCertificateRequest : Engine.HostOfficialStereoRequest :=
  { compiledAutoBridgeHostRequest with
    namespacePath :=
      ["TetraStereoGenerated", "Examples", "Certificates",
        "CompiledAutoBridgeOfficialStereoRefusal"] }

/-- Host/certificate module path collisions are rejected before writing generated files. -/
theorem collidingHostCertificateRequest_rejected :
    (match collidingHostCertificateRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    exact validateGeneratedShape_rejected_of_module_collision
      collidingHostCertificateRequest (by rfl)

/-- Deliberately invalid request whose certificate theorem would collide with a host declaration. -/
def collidingHostCertificateDeclarationRequest : Engine.HostOfficialStereoRequest :=
  { compiledAutoBridgeHostRequest with
    certificateNamespacePath := compiledAutoBridgeHostRequest.namespacePath
    certificateFileName := "AuditCertificate.lean"
    certificateTheoremName := compiledAutoBridgeHostRequest.rawName }

/-- Same-namespace host/certificate declaration collisions are rejected before generation. -/
theorem collidingHostCertificateDeclarationRequest_rejected :
    (match collidingHostCertificateDeclarationRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    have hnamespace : collidingHostCertificateDeclarationRequest.namespacePath =
        collidingHostCertificateDeclarationRequest.certificateNamespacePath := by
      rfl
    have hcontains :
        collidingHostCertificateDeclarationRequest.hostLocalDeclarationNames.contains
          collidingHostCertificateDeclarationRequest.certificateTheoremName = true := by
      rw [List.contains_iff_mem]
      simp [collidingHostCertificateDeclarationRequest,
        Engine.HostOfficialStereoRequest.hostLocalDeclarationNames,
        Engine.HostOfficialStereoRequest.rawName]
    exact validateGeneratedShape_rejected_of_declaration_collision
      collidingHostCertificateDeclarationRequest hnamespace hcontains

/-- The typed-annotation host-module entry uses a host-module key derived from the certificate key. -/
theorem compiledHelicalBridgeHostModuleEntry_key :
    compiledHelicalBridgeHostModuleEntry.key =
      "compiled-helical-bridge-official-stereo-comparison::host-module" :=
  rfl

/-- The compiler emits the expected typed-annotation host module file name. -/
theorem compiledHelicalBridgeHostModuleEntry_fileName :
    compiledHelicalBridgeHostModuleEntry.fileName = "CompiledHelicalBridgeHost.lean" :=
  rfl

/-! ### Emitted target-claim expressions after the Option migration

`HostOfficialStereoCertificateTarget.statement` is the only place that renders a generated
target-claim theorem body.  These focused checks pin the migrated forms: the compatibility
`computedComparison` target is the optional-outcome reflexivity, while literal `comparison` and
`refusal` targets keep their declared value and reason. -/

/-- `computedComparison` is compatibility reflexivity over the optional outcome, not an `Ordering`
claim. -/
theorem computedComparison_statement (requestExpr : String) :
    Engine.HostOfficialStereoCertificateTarget.computedComparison.statement requestExpr =
      "(" ++ requestExpr ++ ").outcome = (" ++ requestExpr ++ ").outcome" :=
  rfl

/-- A literal comparison target still names the declared `Ordering` in the emitted claim. -/
theorem comparison_statement (requestExpr : String) (expected : Ordering) :
    (Engine.HostOfficialStereoCertificateTarget.comparison expected).statement requestExpr =
      "TetraStereo.Engine.OfficialStereoTransactionClaim " ++ requestExpr ++ " " ++
        Engine.orderingExpr expected :=
  rfl

/-- A literal refusal target still names the declared reason in the emitted claim. -/
theorem refusal_statement (requestExpr : String) (reason : Engine.RefusalReason) :
    (Engine.HostOfficialStereoCertificateTarget.refusal reason).statement requestExpr =
      "TetraStereo.Engine.OfficialStereoRefusalClaim " ++ requestExpr ++ " " ++
        Engine.refusalReasonExpr reason :=
  rfl

/-- A `none` certificate can be declared only as an `implementationLimit` refusal; the emitted
statement keeps the substantive two-conjunct claim and the literal reason. -/
theorem implementationLimit_refusal_statement (requestExpr : String) :
    (Engine.HostOfficialStereoCertificateTarget.refusal
        Engine.RefusalReason.implementationLimit).statement requestExpr =
      "TetraStereo.Engine.OfficialStereoRefusalClaim " ++ requestExpr ++ " " ++
        "TetraStereo.Engine.RefusalReason.implementationLimit" :=
  rfl

/-- The compatibility target is discharged by `rfl`; nothing about a comparison is assumed. -/
theorem computedComparison_proofTerm :
    Engine.HostOfficialStereoCertificateTarget.computedComparison.proofTerm = "  rfl" :=
  rfl

/-- A literal comparison target remains a single kernel-checked equation. -/
theorem comparison_proofTerm (expected : Ordering) :
    (Engine.HostOfficialStereoCertificateTarget.comparison expected).proofTerm = "  rfl" :=
  rfl

/-- A literal refusal target remains a two-conjunct kernel check. -/
theorem refusal_proofTerm (reason : Engine.RefusalReason) :
    (Engine.HostOfficialStereoCertificateTarget.refusal reason).proofTerm = "  ⟨rfl, rfl⟩" :=
  rfl

end
end HostModuleCompiler
end Examples
end TetraStereo
