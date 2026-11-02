import TetraStereo.Engine.Result
import TetraStereo.OneCenter.OfficialCIPEngine
import TetraStereo.OneCenter.OfficialNoncenterDetectors
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter

noncomputable section
























/-- Render an `Ordering` as a Lean expression. -/
def orderingExpr : Ordering → String
  | Ordering.lt => "Ordering.lt"
  | Ordering.eq => "Ordering.eq"
  | Ordering.gt => "Ordering.gt"

/-- Render a public engine refusal reason as a Lean expression. -/
def refusalReasonExpr : RefusalReason → String
  | RefusalReason.unresolvedDescriptorPriorities =>
      "TetraStereo.Engine.RefusalReason.unresolvedDescriptorPriorities"
  | RefusalReason.unresolvedOfficialPriorities =>
      "TetraStereo.Engine.RefusalReason.unresolvedOfficialPriorities"
  | RefusalReason.unsupportedInput =>
      "TetraStereo.Engine.RefusalReason.unsupportedInput"
  | RefusalReason.unsupportedStereoElement =>
      "TetraStereo.Engine.RefusalReason.unsupportedStereoElement"
  | RefusalReason.implementationLimit =>
      "TetraStereo.Engine.RefusalReason.implementationLimit"


structure PublicOfficialStereoTheoremPlan where
  imports : List String := ["TetraStereo.Engine.OfficialStereoTransaction"]
  namespacePath : List String := ["TetraStereo", "Generated"]
  theoremName : String
  requestExpr : String
  proofTerm : String

namespace PublicOfficialStereoTheoremPlan

/-- Render a checked-success theorem for this public official-stereo transaction. -/
def successTheoremExport (plan : PublicOfficialStereoTheoremPlan)
    (expectedExpr : String) : LeanTheoremExport where
  imports := plan.imports
  namespacePath := plan.namespacePath
  theoremName := plan.theoremName
  statement :=
    "TetraStereo.Engine.OfficialStereoTransactionClaim " ++ plan.requestExpr ++ " " ++
      expectedExpr
  proofTerm := plan.proofTerm

/-- Render a checked-refusal theorem for this public official-stereo transaction. -/
def refusalTheoremExport (plan : PublicOfficialStereoTheoremPlan)
    (reason : RefusalReason) : LeanTheoremExport where
  imports := plan.imports
  namespacePath := plan.namespacePath
  theoremName := plan.theoremName
  statement :=
    "TetraStereo.Engine.OfficialStereoRefusalClaim " ++ plan.requestExpr ++ " " ++
      refusalReasonExpr reason
  proofTerm := plan.proofTerm

end PublicOfficialStereoTheoremPlan

/-- Which part of the official-CIP transaction actually resolved the comparison. -/
inductive OfficialCIPResolutionSource where
  | unresolved
  | hierarchicalDigraphGraphKey
  | detectorBranchContext
  deriving DecidableEq, Repr

/-- Comparator family used by the public official-CIP transaction. -/
inductive OfficialCIPComparatorKind where
  | hierarchicalDigraph
  deriving DecidableEq, Repr


structure OfficialCIPBranchAudit where
  descriptorSourceCount : ℕ
  contextHasOfficialValue : Bool
  complete : Bool
  atomSupportSources : Bool
  duplicateAtomSources : Bool
  phantomSources : Bool
  lonePairSources : Bool
  auxiliarySources : Bool
  deriving DecidableEq, Repr



structure OfficialCIPCompletenessAudit where
  resolutionSource : OfficialCIPResolutionSource
  graphResolved : Bool
  detectorComparisonResolved : Bool
  comparedBranchesComplete : Bool
  moleculeContextPopulationComplete : Bool
  exactVirtualPlacementPolicy : Bool
  policySuppliesVirtualNodes : Bool
  graphDuplicatePlacementSeen : Bool
  flattenedKeyFree : Bool
  certificateReady : Bool
  officialCompletenessReady : Bool
  deriving DecidableEq, Repr

/-- Public request for an official-CIP comparison backed by non-center detector output.

The normalized molecule fixes the atom universe.  A host/toolkit can supply indexed annotations for
axes, planes, helices, conformers, ensembles, auxiliary nodes, phantom nodes, and lone-pair nodes;
Lean converts valid indices into the proof-facing `Fin atomCount` universe before building the
official detector output and descriptor-source branch policy. -/
structure OfficialStereoRequest where
  normalized : ChemistryNormalizationResult
  annotations : IndexedNoncenterStereoAnnotations := {}
  molecule : MultiCenterMolecule (Fin normalized.parsed.atomCount)
  profile : DescriptorSourcePolicyProfile := DescriptorSourcePolicyProfile.exactDistance
  officialNodesAtDepth :
    molecule.Center → Fin 4 → ℕ → List (OfficialCIPNode (Fin normalized.parsed.atomCount)) :=
      fun _ _ _ => []
  graphFuel : ℕ := normalized.parsed.atomCount + 1
  scheduleFuel : ℕ := 0
  branchFuel : ℕ := 0
  center : molecule.Center
  localMolecule : OneCenterMolecule (Fin normalized.parsed.atomCount) :=
    molecule.toOneCenterMolecule center
  left : Fin 4
  right : Fin 4
  theoremPlan : PublicOfficialStereoTheoremPlan

namespace OfficialStereoRequest

/-- One-center view at the requested stereocenter. -/
def oneCenter (request : OfficialStereoRequest) :
    OneCenterMolecule (Fin request.normalized.parsed.atomCount) :=
  request.localMolecule

/-- Whether an official ligand context contains any detector-provided official-rule fact. -/
def contextHasAnyValue (context : CIPRuleEngine.OfficialLigandRuleContext) : Bool :=
  context.rule3Geometry?.isSome ||
    context.rule4aKind?.isSome ||
    context.rule4bPair?.isSome ||
    context.rule4cDescriptor?.isSome ||
    context.rule5Descriptor?.isSome

/-- Detector result built from normalized parser-visible units plus indexed external annotations. -/
def detection (request : OfficialStereoRequest) :
    OfficialUnitDetectionResult (Fin request.normalized.parsed.atomCount) :=
  request.normalized.officialUnitDetectionResultWith request.annotations

/-- Official detector output induced by the request's finite detector registry. -/
def output (request : OfficialStereoRequest) :
    OfficialDetectorOutput request.detection.Unit :=
  request.detection.toOfficialDetectorOutput

/-- Final descriptor environment after the request's finite detector schedule fuel. -/
def finalEnvironment (request : OfficialStereoRequest) :
    OfficialDescriptorEnvironment request.detection.Unit :=
  request.output.finalEnvironment request.scheduleFuel

/-- Descriptor-source branch policy induced by the request's detector registry and profile. -/
def policy (request : OfficialStereoRequest) :
    DescriptorSourceBranchPolicy request.molecule request.detection.Unit :=
  { request.detection.descriptorSourceBranchPolicyWith request.molecule request.profile with
    officialNodesAtDepth := request.officialNodesAtDepth }

/-- Detector-fed official context for a ligand branch. -/
def branchContextAt (request : OfficialStereoRequest)
    (center : request.molecule.Center) (branch : Fin 4) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  request.molecule.officialBranchContextFromDescriptorSourceDetectorWithin
    request.output request.policy request.scheduleFuel request.branchFuel center branch

/-- Descriptor-unit sources found on one requested branch after schedule and branch-walk fuel. -/
def branchDescriptorSourcesAt (request : OfficialStereoRequest)
    (center : request.molecule.Center) (branch : Fin 4) :
    List (BranchDescriptorUnitSource request.molecule request.detection.Unit) :=
  request.molecule.branchDescriptorUnitSourcesWithin
    request.finalEnvironment request.policy center branch request.branchFuel

/-- All distinguished centers in the request molecule. -/
def centers (request : OfficialStereoRequest) : List request.molecule.Center :=
  request.molecule.centers.attach.toList

/-- All center/branch pairs in the request molecule. -/
def centerBranches (request : OfficialStereoRequest) :
    List (request.molecule.Center × Fin 4) :=
  request.centers.flatMap fun center =>
    (List.finRange 4).map fun branch => (center, branch)

/-- Detector-fed official context for a ligand branch at the requested center. -/
def branchContext (request : OfficialStereoRequest) (branch : Fin 4) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  request.branchContextAt request.center branch

/-- Descriptor-unit sources found on one compared branch at the requested center. -/
def branchDescriptorSources (request : OfficialStereoRequest) (branch : Fin 4) :
    List (BranchDescriptorUnitSource request.molecule request.detection.Unit) :=
  request.branchDescriptorSourcesAt request.center branch

/-- Detector-fed official context family for the host molecule. -/
def context (request : OfficialStereoRequest) :
    request.molecule.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  fun center branch => request.branchContextAt center branch

/-- Descriptor-rich official-rule context supplied to the bounded rule-major comparison at the
requested stereocenter. -/
def compareContext (request : OfficialStereoRequest) :
    Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  fun branch => request.branchContext branch

/-- Left root of the official hierarchical-digraph graph-key comparison. -/
def digraphLeftRoot (request : OfficialStereoRequest) :
    OfficialCIPNode (Fin request.normalized.parsed.atomCount) :=
  OfficialCIPNode.rootFromEdge request.oneCenter.center
    (request.oneCenter.ligandAtom request.left)

/-- Right root of the official hierarchical-digraph graph-key comparison. -/
def digraphRightRoot (request : OfficialStereoRequest) :
    OfficialCIPNode (Fin request.normalized.parsed.atomCount) :=
  OfficialCIPNode.rootFromEdge request.oneCenter.center
    (request.oneCenter.ligandAtom request.right)

/-- Official hierarchical-digraph frontiers visited by the compared roots within graph fuel. -/
def digraphFrontiersWithinFuel (request : OfficialStereoRequest) :
    List (OfficialCIPNode (Fin request.normalized.parsed.atomCount)) :=
  (List.range (request.graphFuel + 1)).flatMap fun fuel =>
    request.oneCenter.mol.officialCIPFrontier fuel [request.digraphLeftRoot] ++
      request.oneCenter.mol.officialCIPFrontier fuel [request.digraphRightRoot]

/-- The actual bounded rule-major certificate computed at the supplied `graphFuel`.

This is the single source of truth for the transaction.  `none` means the bounded comparison did
not complete; in that case no context fallthrough can produce a certificate. -/
def certificate (request : OfficialStereoRequest) : Option CIPTraceCertificate :=
  request.oneCenter.cipOfficialCompareWithFuel
    request.compareContext request.graphFuel request.left request.right

/-- Trace of the same bounded rule-major certificate.  Its leading segment is the official
hierarchical-digraph trace; when the completed constitutional comparison ties, the existing
`compareDigraphThenOfficialCertificate` compiler appends the Rule 3/4/5 context trace. -/
def digraphTrace (request : OfficialStereoRequest) : Option (List CIPRuleDecision) :=
  request.certificate.map CIPTraceCertificate.trace

/-- Outcome of the same bounded rule-major certificate. -/
def outcome (request : OfficialStereoRequest) : Option Ordering :=
  request.certificate.map CIPTraceCertificate.outcome

/-- Trace-level outcome of the same bounded rule-major certificate. -/
def digraphOutcome (request : OfficialStereoRequest) : Option Ordering :=
  request.digraphTrace.map cipTraceOutcome

/-- Canonical total official engine certificate at the proved-stable default fuel.

`cipOfficialCompare` is total because the engine proved that `Fintype.card V + 1` is sufficient; it
is not a default-equality fallback. -/
def defaultEngineCertificate (request : OfficialStereoRequest) : CIPTraceCertificate :=
  request.oneCenter.cipOfficialCompare
    request.compareContext request.left request.right

@[simp] theorem digraphTrace_eq_certificate_map (request : OfficialStereoRequest) :
    request.digraphTrace =
      request.certificate.map CIPTraceCertificate.trace :=
  rfl

@[simp] theorem outcome_eq_certificate_map (request : OfficialStereoRequest) :
    request.outcome =
      request.certificate.map CIPTraceCertificate.outcome :=
  rfl

/-- Trace agreement: the transaction outcome is the lexicographic outcome of the trace of the very
same bounded certificate. -/
theorem outcome_eq_digraphTrace_map (request : OfficialStereoRequest) :
    request.outcome = request.digraphTrace.map cipTraceOutcome := by
  unfold outcome digraphTrace
  cases h : request.certificate with
  | none => rfl
  | some cert =>
      simp only [Option.map_some]
      rw [cert.sound]

/-- The trace-level outcome agrees with the certificate outcome. -/
theorem digraphOutcome_eq_outcome (request : OfficialStereoRequest) :
    request.digraphOutcome = request.outcome := by
  unfold digraphOutcome outcome digraphTrace
  cases h : request.certificate with
  | none => rfl
  | some cert =>
      simp only [Option.map_some]
      rw [cert.sound]

/-- A present certificate exposes its own outcome. -/
theorem outcome_eq_some_outcome_of_certificate_eq_some (request : OfficialStereoRequest)
    {cert : CIPTraceCertificate} (h : request.certificate = some cert) :
    request.outcome = some cert.outcome := by
  unfold outcome
  rw [h]
  rfl

/-- An observed optional outcome comes from an actual bounded certificate; the two are never
separately computed. -/
theorem certificate_eq_some_of_outcome_eq_some (request : OfficialStereoRequest)
    {expected : Ordering} (h : request.outcome = some expected) :
    ∃ cert, request.certificate = some cert ∧ cert.outcome = expected := by
  unfold outcome at h
  cases hc : request.certificate with
  | none =>
      rw [hc] at h
      cases h
  | some cert =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨cert, rfl, h⟩

/-! ### Readiness from the same computed certificate -/

/-- Whether the bounded rule-major computation returned a certificate. -/
def compiled (request : OfficialStereoRequest) : Bool :=
  request.certificate.isSome

/-- Whether the ordering is decisive (not a tie). -/
def orderingDecisive (o : Ordering) : Bool :=
  decide (o ≠ Ordering.eq)

/-- Whether the certificate outcome is present and decisive. -/
def outcomeDecisive (request : OfficialStereoRequest) : Bool :=
  match request.outcome with
  | none => false
  | some result => orderingDecisive result

/-- Comparison-level readiness: the bounded computation completed and produced a decisive outcome. -/
def certificateReady (request : OfficialStereoRequest) : Bool :=
  request.compiled && request.outcomeDecisive

/-- Readiness is exactly "some actual certificate with a decisive outcome". -/
theorem certificateReady_eq_true_iff (request : OfficialStereoRequest) :
    request.certificateReady = true ↔
      ∃ cert, request.certificate = some cert ∧ cert.outcome ≠ Ordering.eq := by
  unfold certificateReady compiled outcomeDecisive outcome
  cases h : request.certificate with
  | none => simp
  | some cert =>
      cases ho : cert.outcome <;> simp [ho, orderingDecisive]

/-- Non-readiness is exactly "no certificate, or a completed tie". -/
theorem certificateReady_eq_false_iff (request : OfficialStereoRequest) :
    request.certificateReady = false ↔
      request.certificate = none ∨
        ∃ cert, request.certificate = some cert ∧ cert.outcome = Ordering.eq := by
  constructor
  · intro h
    by_cases hc : request.certificate = none
    · exact Or.inl hc
    · right
      cases hcert : request.certificate with
      | none => exact absurd hcert hc
      | some cert =>
          refine ⟨cert, rfl, ?_⟩
          by_contra hne
          have htrue : request.certificateReady = true :=
            (certificateReady_eq_true_iff request).2 ⟨cert, hcert, hne⟩
          rw [htrue] at h
          cases h
  · intro h
    rcases h with hnone | ⟨cert, hcert, heq⟩
    · unfold certificateReady compiled outcomeDecisive
      simp [outcome, hnone]
    · unfold certificateReady compiled outcomeDecisive
      simp [outcome, hcert, heq, orderingDecisive]

/-! ### Classification of the deciding component

The transaction exposes which component decided without recomputing the comparison: it inspects the
rule families present in the trace of the same bounded certificate.  The official hierarchical
digraph emits only `atomicNumber`, `isotopeMass`, `duplicateAtom`, and `frontierExhaustion`
decisions; the Rule 3/4/5 context trace is appended only after the constitutional comparison ties,
so a decisive digraph-family decision means the graph decided. -/

/-- Rule families emitted by the official hierarchical-digraph comparator. -/
def isDigraphRule : CIPRuleFamily → Bool
  | CIPRuleFamily.atomicNumber => true
  | CIPRuleFamily.isotopeMass => true
  | CIPRuleFamily.duplicateAtom => true
  | CIPRuleFamily.frontierExhaustion => true
  | _ => false

/-- Whether a trace contains a decisive official-digraph decision. -/
def traceDecidedByDigraph (trace : List CIPRuleDecision) : Bool :=
  trace.any fun decision =>
    isDigraphRule decision.rule && orderingDecisive decision.outcome

/-- Whether the official hierarchical-digraph segment of the certificate decided. -/
def graphResolved (request : OfficialStereoRequest) : Bool :=
  match request.certificate with
  | none => false
  | some cert => orderingDecisive cert.outcome && traceDecidedByDigraph cert.trace

/-- Whether the completed comparison was decided by descriptor-rich context after a graph tie. -/
def detectorComparisonResolved (request : OfficialStereoRequest) : Bool :=
  match request.certificate with
  | none => false
  | some cert => orderingDecisive cert.outcome && !traceDecidedByDigraph cert.trace

/-- Which official-CIP component resolved this request, if any. -/
def resolutionSource (request : OfficialStereoRequest) : OfficialCIPResolutionSource :=
  if request.graphResolved then
    OfficialCIPResolutionSource.hierarchicalDigraphGraphKey
  else
    match request.certificate with
    | none => OfficialCIPResolutionSource.unresolved
    | some cert =>
        if cert.outcome = Ordering.eq then
          OfficialCIPResolutionSource.unresolved
        else
          OfficialCIPResolutionSource.detectorBranchContext

theorem resolutionSource_eq_hierarchicalDigraphGraphKey_of_graphResolved
    (request : OfficialStereoRequest) (h : request.graphResolved = true) :
    request.resolutionSource =
      OfficialCIPResolutionSource.hierarchicalDigraphGraphKey := by
  unfold resolutionSource
  rw [h]
  simp

theorem resolutionSource_eq_unresolved_of_certificate_eq_none
    (request : OfficialStereoRequest) (h : request.certificate = none) :
    request.resolutionSource = OfficialCIPResolutionSource.unresolved := by
  have hgraph : request.graphResolved = false := by
    simp [graphResolved, h]
  unfold resolutionSource
  rw [hgraph]
  simp [h]

theorem resolutionSource_eq_unresolved_of_outcome_eq
    (request : OfficialStereoRequest) {cert : CIPTraceCertificate}
    (hcert : request.certificate = some cert) (heq : cert.outcome = Ordering.eq) :
    request.resolutionSource = OfficialCIPResolutionSource.unresolved := by
  have hgraph : request.graphResolved = false := by
    simp [graphResolved, hcert, orderingDecisive, heq]
  unfold resolutionSource
  rw [hgraph]
  simp [hcert, heq]

/-- A decisive certificate whose trace contains no decisive digraph rule was decided by the
descriptor-rich context consulted after a completed constitutional tie. -/
theorem resolutionSource_eq_detectorBranchContext_of_not_graphResolved
    (request : OfficialStereoRequest) (hgraph : request.graphResolved = false)
    (hdec : request.outcomeDecisive = true) :
    request.resolutionSource = OfficialCIPResolutionSource.detectorBranchContext := by
  unfold resolutionSource
  rw [hgraph]
  cases hc : request.certificate with
  | none =>
      have hnone : request.outcomeDecisive = false := by
        simp [outcomeDecisive, outcome, hc]
      rw [hnone] at hdec
      cases hdec
  | some cert =>
      have hne : cert.outcome ≠ Ordering.eq := by
        intro he
        have hnone : request.outcomeDecisive = false := by
          simp [outcomeDecisive, outcome, hc, orderingDecisive, he]
        rw [hnone] at hdec
        cases hdec
      simp [hne]

/-- Whether a branch contains at least one relevant descriptor source. -/
def branchHasDescriptorSourceAt (request : OfficialStereoRequest)
    (center : request.molecule.Center) (branch : Fin 4) : Bool :=
  !(request.branchDescriptorSourcesAt center branch).isEmpty

/-- Whether a branch carries at least one official-rule fact in its branch context. -/
def branchHasOfficialContextAt (request : OfficialStereoRequest)
    (center : request.molecule.Center) (branch : Fin 4) : Bool :=
  contextHasAnyValue (request.branchContextAt center branch)

/-- Whether a branch has detector evidence that is both relevant and context-producing. -/
def branchCompleteAt (request : OfficialStereoRequest)
    (center : request.molecule.Center) (branch : Fin 4) : Bool :=
  request.branchHasDescriptorSourceAt center branch &&
    request.branchHasOfficialContextAt center branch

/-- Whether a compared branch contains at least one relevant descriptor source. -/
def branchHasDescriptorSource (request : OfficialStereoRequest) (branch : Fin 4) : Bool :=
  request.branchHasDescriptorSourceAt request.center branch

/-- Whether a compared branch carries at least one official-rule fact in its branch context. -/
def branchHasOfficialContext (request : OfficialStereoRequest) (branch : Fin 4) : Bool :=
  request.branchHasOfficialContextAt request.center branch

/-- Whether a compared branch has detector evidence that is both relevant and context-producing. -/
def branchComplete (request : OfficialStereoRequest) (branch : Fin 4) : Bool :=
  request.branchCompleteAt request.center branch

/-- Whether both compared branches have complete detector-backed branch evidence. -/
def detectorBranchesComplete (request : OfficialStereoRequest) : Bool :=
  request.branchComplete request.left && request.branchComplete request.right

/-- Whether the detector registry contains at least one immediately seeded descriptor fact. -/
def detectorReady (request : OfficialStereoRequest) : Bool :=
  request.detection.units.any OfficialDetectedUnit.hasInitialValue

/-- Whether the final detector environment contains at least one resolved descriptor fact. -/
def detectorHasResolvedValue (request : OfficialStereoRequest) : Bool :=
  (List.finRange request.detection.units.length).any fun unit =>
    request.finalEnvironment.hasAnyValue unit

/-- The public official-stereo transaction uses the hierarchical-digraph comparator, not the
legacy flattened key comparator. -/
def comparatorKind (_request : OfficialStereoRequest) : OfficialCIPComparatorKind :=
  OfficialCIPComparatorKind.hierarchicalDigraph


def flattenedKeyFree (request : OfficialStereoRequest) : Bool :=
  decide (request.comparatorKind = OfficialCIPComparatorKind.hierarchicalDigraph)

/-- Whether the request's virtual-node policy requires exact kind-and-distance placement. -/
def exactVirtualPlacementPolicy (request : OfficialStereoRequest) : Bool :=
  decide (request.profile.virtualNodeResolution = VirtualNodeResolutionPolicy.exactDistance)

/-- Policy-supplied official virtual nodes visible within branch-walk fuel. -/
def virtualNodesWithinBranchFuelAt (request : OfficialStereoRequest)
    (center : request.molecule.Center) (branch : Fin 4) :
    List (OfficialCIPNode (Fin request.normalized.parsed.atomCount)) :=
  (List.range (request.branchFuel + 1)).flatMap fun depth =>
    request.officialNodesAtDepth center branch depth

/-- Whether the request supplies any virtual official nodes through the branch policy. -/
def policySuppliesVirtualNodes (request : OfficialStereoRequest) : Bool :=
  request.centerBranches.any fun centerBranch =>
    !(request.virtualNodesWithinBranchFuelAt centerBranch.1 centerBranch.2).isEmpty

/-- Whether a source list contains a source of the requested kind. -/
def branchSourcesContainKind {request : OfficialStereoRequest}
    (sources : List (BranchDescriptorUnitSource request.molecule request.detection.Unit))
    (kind : BranchDescriptorSourceKind) : Bool :=
  sources.any fun source => source.sourceKind = kind


def branchAuditAt (request : OfficialStereoRequest)
    (center : request.molecule.Center) (branch : Fin 4) :
    OfficialCIPBranchAudit :=
  let sources := request.branchDescriptorSourcesAt center branch
  { descriptorSourceCount := sources.length
    contextHasOfficialValue := request.branchHasOfficialContextAt center branch
    complete := request.branchCompleteAt center branch
    atomSupportSources := branchSourcesContainKind sources BranchDescriptorSourceKind.atomSupport
    duplicateAtomSources := branchSourcesContainKind sources BranchDescriptorSourceKind.duplicateAtom
    phantomSources := branchSourcesContainKind sources BranchDescriptorSourceKind.phantom
    lonePairSources := branchSourcesContainKind sources BranchDescriptorSourceKind.lonePair
    auxiliarySources := branchSourcesContainKind sources BranchDescriptorSourceKind.auxiliary }


def branchAudit (request : OfficialStereoRequest) (branch : Fin 4) :
    OfficialCIPBranchAudit :=
  request.branchAuditAt request.center branch

/-- Whether every center/branch pair in the molecule has context-producing descriptor evidence. -/
def moleculeContextPopulationComplete (request : OfficialStereoRequest) : Bool :=
  request.centerBranches.all fun centerBranch =>
    request.branchCompleteAt centerBranch.1 centerBranch.2

/-- Whether graph-generated duplicate-node placement is visible in the compared digraph frontiers. -/
def graphDuplicatePlacementSeen (request : OfficialStereoRequest) : Bool :=
  request.digraphFrontiersWithinFuel.any fun node => node.isDuplicateLeaf



def officialCompletenessReady (request : OfficialStereoRequest) : Bool :=
  request.certificateReady &&
    request.moleculeContextPopulationComplete &&
      request.exactVirtualPlacementPolicy &&
        request.flattenedKeyFree


def completenessAudit (request : OfficialStereoRequest) : OfficialCIPCompletenessAudit where
  resolutionSource := request.resolutionSource
  graphResolved := request.graphResolved
  detectorComparisonResolved := request.detectorComparisonResolved
  comparedBranchesComplete := request.detectorBranchesComplete
  moleculeContextPopulationComplete := request.moleculeContextPopulationComplete
  exactVirtualPlacementPolicy := request.exactVirtualPlacementPolicy
  policySuppliesVirtualNodes := request.policySuppliesVirtualNodes
  graphDuplicatePlacementSeen := request.graphDuplicatePlacementSeen
  flattenedKeyFree := request.flattenedKeyFree
  certificateReady := request.certificateReady
  officialCompletenessReady := request.officialCompletenessReady

@[simp] theorem completenessAudit_certificateReady (request : OfficialStereoRequest) :
    request.completenessAudit.certificateReady = request.certificateReady :=
  rfl

@[simp] theorem completenessAudit_officialCompletenessReady
    (request : OfficialStereoRequest) :
    request.completenessAudit.officialCompletenessReady = request.officialCompletenessReady :=
  rfl

@[simp] theorem comparatorKind_eq_hierarchicalDigraph (request : OfficialStereoRequest) :
    request.comparatorKind = OfficialCIPComparatorKind.hierarchicalDigraph :=
  rfl

@[simp] theorem flattenedKeyFree_eq_true (request : OfficialStereoRequest) :
    request.flattenedKeyFree = true :=
  rfl

theorem officialCompletenessReady_eq_false_of_moleculeContextPopulationComplete_eq_false
    (request : OfficialStereoRequest)
    (h : request.moleculeContextPopulationComplete = false) :
    request.officialCompletenessReady = false := by
  simp [officialCompletenessReady, h]

/-! ### Refusal justification from the same computed certificate -/

/-- The refusal reason this request's own bounded computation justifies, if it refuses at all.

No certificate means the bounded constitutional comparison did not complete (implementation limit);
a completed tie means official priorities remain unresolved.  Deriving the reason from the computed
certificate rather than accepting it from the caller is what stops a refusal certificate from
advertising a cause the request does not exhibit. -/
def officialRefusalReason? (request : OfficialStereoRequest) : Option RefusalReason :=
  match request.certificate with
  | none => some RefusalReason.implementationLimit
  | some cert =>
      if cert.outcome = Ordering.eq then
        some RefusalReason.unresolvedOfficialPriorities
      else
        none

/-- A request justifies a refusal reason exactly when it is not certificate-ready. -/
theorem officialRefusalReason?_isSome_iff_not_certificateReady
    (request : OfficialStereoRequest) :
    request.officialRefusalReason?.isSome ↔ request.certificateReady = false := by
  unfold officialRefusalReason? certificateReady compiled outcomeDecisive outcome
  cases h : request.certificate with
  | none => simp
  | some cert =>
      by_cases ho : cert.outcome = Ordering.eq
      · simp [ho, orderingDecisive]
      · simp [ho, orderingDecisive]

/-- Exact characterization of the two refusal reasons this boundary can justify. -/
theorem officialRefusalReason?_eq_some_iff (request : OfficialStereoRequest)
    (reason : RefusalReason) :
    request.officialRefusalReason? = some reason ↔
      (request.certificate = none ∧ reason = RefusalReason.implementationLimit) ∨
        (∃ cert, request.certificate = some cert ∧ cert.outcome = Ordering.eq ∧
          reason = RefusalReason.unresolvedOfficialPriorities) := by
  unfold officialRefusalReason?
  cases h : request.certificate with
  | none =>
      constructor
      · intro hr
        refine Or.inl ⟨rfl, ?_⟩
        exact (Option.some.inj hr).symm
      · rintro (⟨-, hr⟩ | ⟨cert, hc, -⟩)
        · rw [hr]
        · cases hc
  | some cert =>
      by_cases ho : cert.outcome = Ordering.eq
      · simp only [if_pos ho]
        constructor
        · intro hr
          refine Or.inr ⟨cert, rfl, ho, ?_⟩
          exact (Option.some.inj hr).symm
        · rintro (⟨hc, -⟩ | ⟨cert', hc', ho', hr⟩)
          · cases hc
          · have hcert : cert = cert' := Option.some.inj hc'
            cases hcert
            rw [hr]
      · simp only [if_neg ho]
        constructor
        · intro hr
          cases hr
        · rintro (⟨hc, -⟩ | ⟨cert', hc', ho', -⟩)
          · cases hc
          · have hcert : cert = cert' := Option.some.inj hc'
            cases hcert
            exact absurd ho' ho

/-- A failed bounded rule-major computation justifies `implementationLimit`. -/
theorem officialRefusalReason_eq_some_implementationLimit_of_certificate_eq_none
    (request : OfficialStereoRequest) (h : request.certificate = none) :
    request.officialRefusalReason? = some RefusalReason.implementationLimit := by
  simp [officialRefusalReason?, h]

/-- A completed but unresolved equality justifies `unresolvedOfficialPriorities`. -/
theorem officialRefusalReason_eq_some_unresolvedOfficialPriorities_of_outcome_eq
    (request : OfficialStereoRequest) (h : request.outcome = some Ordering.eq) :
    request.officialRefusalReason? = some RefusalReason.unresolvedOfficialPriorities := by
  unfold outcome at h
  cases hc : request.certificate with
  | none =>
      rw [hc] at h
      cases h
  | some cert =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp [officialRefusalReason?, hc, h]

/-- A completed decisive certificate justifies no refusal. -/
theorem officialRefusalReason_eq_none_of_outcome_ne_eq (request : OfficialStereoRequest)
    {cert : CIPTraceCertificate} (hcert : request.certificate = some cert)
    (hne : cert.outcome ≠ Ordering.eq) :
    request.officialRefusalReason? = none := by
  simp [officialRefusalReason?, hcert, hne]

end OfficialStereoRequest

/-- Claim certified by a public official-stereo comparison transaction.

This is the `outcome = some expected` form: the expected literal is a concrete `Ordering`, and the
transaction must exhibit the optional outcome computed from the same bounded certificate. -/
def OfficialStereoTransactionClaim (request : OfficialStereoRequest) (expected : Ordering) : Prop :=
  request.outcome = some expected

/-- Refusal claim for a public official-stereo transaction.

The declared `reason` is pinned to the one the request's own computed certificate justifies, so a
certificate cannot name a cause the request does not exhibit. -/
def OfficialStereoRefusalClaim (request : OfficialStereoRequest) (reason : RefusalReason) : Prop :=
  request.certificateReady = false ∧ request.officialRefusalReason? = some reason

/-- Compile a detector-backed official-CIP comparison into a checked theorem artifact. -/
def compileOfficialStereoTransaction (request : OfficialStereoRequest) (expected : Ordering)
    (h : OfficialStereoTransactionClaim request expected) : LeanCertificateArtifact where
  kind := LeanCertificateKind.officialLigandComparison
  title := "Public engine detector-backed official CIP comparison: " ++ orderingExpr expected
  theoremExport := request.theoremPlan.successTheoremExport (orderingExpr expected)
  source? := some { format := ChemistryImportFormat.rawMolecule }
  claim := OfficialStereoTransactionClaim request expected
  proof := h

/-- Compile a detector-backed official-stereo refusal into a checked theorem artifact. -/
def compileOfficialStereoRefusal (request : OfficialStereoRequest) (reason : RefusalReason)
    (h : OfficialStereoRefusalClaim request reason) : LeanCertificateArtifact where
  kind := LeanCertificateKind.stereoClaimRefusal
  title := "Public engine detector-backed official CIP refusal: " ++ reason.label
  theoremExport := request.theoremPlan.refusalTheoremExport reason
  source? := some { format := ChemistryImportFormat.rawMolecule }
  claim := OfficialStereoRefusalClaim request reason
  proof := h

/-- A checked detector-backed official-CIP comparison. -/
structure CertifiedOfficialStereoComparison (request : OfficialStereoRequest) where
  expected : Ordering
  proof : OfficialStereoTransactionClaim request expected
  artifact : LeanCertificateArtifact
  artifact_eq : artifact = compileOfficialStereoTransaction request expected proof

namespace CertifiedOfficialStereoComparison

/-- The comparison artifact is checked by construction. -/
theorem artifact_checked {request : OfficialStereoRequest}
    (certificate : CertifiedOfficialStereoComparison request) :
    certificate.artifact.claim := by
  rw [certificate.artifact_eq]
  exact (compileOfficialStereoTransaction request certificate.expected certificate.proof).checked

end CertifiedOfficialStereoComparison

/-- A checked detector-backed official-stereo refusal. -/
structure CertifiedOfficialStereoRefusal (request : OfficialStereoRequest) where
  reason : RefusalReason
  proof : OfficialStereoRefusalClaim request reason
  artifact : LeanCertificateArtifact
  artifact_eq : artifact = compileOfficialStereoRefusal request reason proof

namespace CertifiedOfficialStereoRefusal

/-- The refusal artifact is checked by construction. -/
theorem artifact_checked {request : OfficialStereoRequest}
    (refusal : CertifiedOfficialStereoRefusal request) :
    refusal.artifact.claim := by
  rw [refusal.artifact_eq]
  exact (compileOfficialStereoRefusal request refusal.reason refusal.proof).checked

end CertifiedOfficialStereoRefusal

/-- Total public decision for a detector-backed official-stereo transaction. -/
inductive OfficialStereoDecision (request : OfficialStereoRequest) where
  | certified (certificate : CertifiedOfficialStereoComparison request)
  | refused (refusal : CertifiedOfficialStereoRefusal request)

namespace OfficialStereoDecision

/-- Optional ordering exposed by a total official-stereo decision. -/
def outcome? {request : OfficialStereoRequest} :
    OfficialStereoDecision request → Option Ordering
  | certified certificate => some certificate.expected
  | refused _ => none

/-- The checked proposition carried by this public official-stereo decision. -/
def artifactClaim {request : OfficialStereoRequest} :
    OfficialStereoDecision request → Prop
  | certified certificate => certificate.artifact.claim
  | refused refusal => refusal.artifact.claim

/-- Every public official-stereo decision carries a checked theorem artifact. -/
theorem artifact_checked {request : OfficialStereoRequest}
    (decision : OfficialStereoDecision request) : decision.artifactClaim := by
  cases decision with
  | certified certificate => exact certificate.artifact_checked
  | refused refusal => exact refusal.artifact_checked

end OfficialStereoDecision

/-- Run the detector-backed public official-stereo transaction.

The one bounded rule-major certificate determines the branch:
* `none` (constitutional comparison did not complete, e.g. insufficient supplied fuel) refuses with
  `implementationLimit`; a decisive descriptor context cannot be reached or certified;
* `some cert` with `cert.outcome = Ordering.eq` refuses with `unresolvedOfficialPriorities`;
* `some cert` with a decisive outcome certifies `outcome = some cert.outcome`. -/
def decideOfficialStereo (request : OfficialStereoRequest) : OfficialStereoDecision request :=
  if hsome : request.certificate.isSome = true then
    let cert : CIPTraceCertificate := request.certificate.get hsome
    have hcert : request.certificate = some cert :=
      Option.eq_some_of_isSome hsome
    if hout : cert.outcome = Ordering.eq then
      let reason : RefusalReason := RefusalReason.unresolvedOfficialPriorities
      have hreason : request.officialRefusalReason? = some reason := by
        simp [OfficialStereoRequest.officialRefusalReason?, hcert, hout]
        rfl
      have hready : request.certificateReady = false := by
        simp [OfficialStereoRequest.certificateReady, OfficialStereoRequest.compiled,
          OfficialStereoRequest.outcomeDecisive, OfficialStereoRequest.outcome, hcert, hout,
          OfficialStereoRequest.orderingDecisive]
      have hclaim : OfficialStereoRefusalClaim request reason := ⟨hready, hreason⟩
      OfficialStereoDecision.refused
        { reason := reason
          proof := hclaim
          artifact := compileOfficialStereoRefusal request reason hclaim
          artifact_eq := rfl }
    else
      have hproof : OfficialStereoTransactionClaim request cert.outcome := by
        unfold OfficialStereoTransactionClaim OfficialStereoRequest.outcome
        simp [hcert]
      OfficialStereoDecision.certified
        { expected := cert.outcome
          proof := hproof
          artifact := compileOfficialStereoTransaction request cert.outcome hproof
          artifact_eq := rfl }
  else
    have hnone : request.certificate = none := by
      cases hc : request.certificate with
      | none => rfl
      | some cert =>
          have hisSome : request.certificate.isSome = true := by simp [hc]
          exact absurd hisSome hsome
    let reason : RefusalReason := RefusalReason.implementationLimit
    have hreason : request.officialRefusalReason? = some reason := by
      simp [OfficialStereoRequest.officialRefusalReason?, hnone]
      rfl
    have hready : request.certificateReady = false := by
      simp [OfficialStereoRequest.certificateReady, OfficialStereoRequest.compiled, hnone]
    have hclaim : OfficialStereoRefusalClaim request reason := ⟨hready, hreason⟩
    OfficialStereoDecision.refused
      { reason := reason
        proof := hclaim
        artifact := compileOfficialStereoRefusal request reason hclaim
        artifact_eq := rfl }

namespace OfficialStereoRequest

/-- A failed bounded computation yields no optional outcome. -/
theorem outcome_eq_none_of_certificate_eq_none (request : OfficialStereoRequest)
    (h : request.certificate = none) :
    request.outcome = none := by
  unfold outcome
  rw [h]
  rfl

/-- The decision outcome of a failed bounded computation is `none`. -/
theorem decideOfficialStereo_outcome_eq_none_of_certificate_eq_none
    (request : OfficialStereoRequest) (h : request.certificate = none) :
    (decideOfficialStereo request).outcome? = none := by
  simp [decideOfficialStereo, h, OfficialStereoDecision.outcome?]

/-- A completed decisive certificate is certified with exactly its own outcome. -/
theorem decideOfficialStereo_outcome_eq_some_of_ne_eq (request : OfficialStereoRequest)
    {cert : CIPTraceCertificate} (h : request.certificate = some cert)
    (hne : cert.outcome ≠ Ordering.eq) :
    (decideOfficialStereo request).outcome? = some cert.outcome := by
  simp [decideOfficialStereo, h, hne, Option.get_some, OfficialStereoDecision.outcome?]

/-- A completed tie is refused and exposes no outcome. -/
theorem decideOfficialStereo_outcome_eq_none_of_eq (request : OfficialStereoRequest)
    {cert : CIPTraceCertificate} (h : request.certificate = some cert)
    (heq : cert.outcome = Ordering.eq) :
    (decideOfficialStereo request).outcome? = none := by
  simp [decideOfficialStereo, h, heq, Option.get_some, OfficialStereoDecision.outcome?]

/-- The decision exposes an outcome exactly when the same bounded certificate is decisive. -/
theorem decideOfficialStereo_outcome_eq_none_iff (request : OfficialStereoRequest) :
    (decideOfficialStereo request).outcome? = none ↔ request.certificateReady = false := by
  cases hc : request.certificate with
  | none =>
      rw [decideOfficialStereo_outcome_eq_none_of_certificate_eq_none request hc]
      unfold certificateReady compiled outcomeDecisive
      simp [outcome, hc]
  | some cert =>
      by_cases heq : cert.outcome = Ordering.eq
      · rw [decideOfficialStereo_outcome_eq_none_of_eq request hc heq]
        unfold certificateReady compiled outcomeDecisive
        simp [outcome, hc, heq, orderingDecisive]
      · rw [decideOfficialStereo_outcome_eq_some_of_ne_eq request hc heq]
        unfold certificateReady compiled outcomeDecisive
        simp [outcome, hc, heq, orderingDecisive]

/-- Insufficient-fuel failure is refused at the implementation limit even when the
descriptor-rich context would be decisive.

The transaction never applies context on its own: `certificate = none` already means the bounded
rule-major comparison (including its context fallthrough) did not complete, so no decisive context
is reachable and nothing is certified. -/
theorem refused_implementationLimit_of_certificate_eq_none
    (request : OfficialStereoRequest) (h : request.certificate = none) :
    request.outcome = none ∧
      request.officialRefusalReason? = some RefusalReason.implementationLimit ∧
        (decideOfficialStereo request).outcome? = none := by
  refine ⟨outcome_eq_none_of_certificate_eq_none request h,
    officialRefusalReason_eq_some_implementationLimit_of_certificate_eq_none request h, ?_⟩
  exact decideOfficialStereo_outcome_eq_none_of_certificate_eq_none request h

/-- A completed unresolved equality remains `unresolvedOfficialPriorities` and is refused. -/
theorem refused_unresolvedOfficialPriorities_of_outcome_eq
    (request : OfficialStereoRequest) (h : request.outcome = some Ordering.eq) :
    request.officialRefusalReason? = some RefusalReason.unresolvedOfficialPriorities ∧
      (decideOfficialStereo request).outcome? = none := by
  refine ⟨officialRefusalReason_eq_some_unresolvedOfficialPriorities_of_outcome_eq request h, ?_⟩
  obtain ⟨cert, hcert, heq⟩ := certificate_eq_some_of_outcome_eq_some request h
  exact decideOfficialStereo_outcome_eq_none_of_eq request hcert heq

/-! ### Agreement of the chosen engine with the default total engine

The bounded entry point is an `Option`, so agreement is stated exactly where the migrated engine
proves it: at the default fuel `Fintype.card V + 1`, and at every `default + extra`.  The
transaction consumes those lemmas; it never invents a default outcome for an arbitrary supplied
fuel. -/

/-- At the canonical default fuel, the transaction's bounded certificate is the default total
engine certificate.  This uses the migrated engine's proved-success lemma. -/
theorem certificate_eq_some_defaultEngineCertificate_of_graphFuel_eq_default
    (request : OfficialStereoRequest)
    (hfuel : request.graphFuel =
      Fintype.card (Fin request.normalized.parsed.atomCount) + 1) :
    request.certificate = some request.defaultEngineCertificate := by
  unfold certificate defaultEngineCertificate
  rw [hfuel]
  exact OneCenterMolecule.cipOfficialCompareWithFuel_default_eq_some
    request.oneCenter request.compareContext request.left request.right

/-- Every fuel at or above the proved default bound yields the same default certificate. -/
theorem certificate_eq_some_defaultEngineCertificate_of_graphFuel_eq_stable
    (request : OfficialStereoRequest) (extra : ℕ)
    (hfuel : request.graphFuel =
      (Fintype.card (Fin request.normalized.parsed.atomCount) + 1) + extra) :
    request.certificate = some request.defaultEngineCertificate := by
  unfold certificate defaultEngineCertificate
  rw [hfuel]
  exact OneCenterMolecule.cipOfficialCompareWithFuel_stable_default
    request.oneCenter request.compareContext request.left request.right extra

/-- Trace agreement with the default engine at the default fuel. -/
theorem digraphTrace_eq_some_defaultEngineCertificate_trace_of_graphFuel_eq_default
    (request : OfficialStereoRequest)
    (hfuel : request.graphFuel =
      Fintype.card (Fin request.normalized.parsed.atomCount) + 1) :
    request.digraphTrace = some request.defaultEngineCertificate.trace := by
  unfold digraphTrace
  rw [certificate_eq_some_defaultEngineCertificate_of_graphFuel_eq_default request hfuel]
  rfl

/-- Trace agreement with the default engine at every fuel at or above the default bound. -/
theorem digraphTrace_eq_some_defaultEngineCertificate_trace_of_graphFuel_eq_stable
    (request : OfficialStereoRequest) (extra : ℕ)
    (hfuel : request.graphFuel =
      (Fintype.card (Fin request.normalized.parsed.atomCount) + 1) + extra) :
    request.digraphTrace = some request.defaultEngineCertificate.trace := by
  unfold digraphTrace certificate defaultEngineCertificate
  rw [hfuel]
  exact OneCenterMolecule.cipOfficialCompareWithFuel_trace_stable_default
    request.oneCenter request.compareContext request.left request.right extra

/-- Outcome agreement with the default engine at the default fuel. -/
theorem outcome_eq_some_defaultEngineCertificate_outcome_of_graphFuel_eq_default
    (request : OfficialStereoRequest)
    (hfuel : request.graphFuel =
      Fintype.card (Fin request.normalized.parsed.atomCount) + 1) :
    request.outcome = some request.defaultEngineCertificate.outcome := by
  unfold outcome
  rw [certificate_eq_some_defaultEngineCertificate_of_graphFuel_eq_default request hfuel]
  rfl

/-- Outcome agreement with the default engine at every fuel at or above the default bound. -/
theorem outcome_eq_some_defaultEngineCertificate_outcome_of_graphFuel_eq_stable
    (request : OfficialStereoRequest) (extra : ℕ)
    (hfuel : request.graphFuel =
      (Fintype.card (Fin request.normalized.parsed.atomCount) + 1) + extra) :
    request.outcome = some request.defaultEngineCertificate.outcome := by
  unfold outcome certificate defaultEngineCertificate
  rw [hfuel]
  exact OneCenterMolecule.cipOfficialCompareWithFuel_outcome_stable_default
    request.oneCenter request.compareContext request.left request.right extra

end OfficialStereoRequest

/-! ### Kernel-authority guards -/

assert_kernel_only TetraStereo.Engine.OfficialStereoRequest.outcome_eq_digraphTrace_map
assert_kernel_only TetraStereo.Engine.OfficialStereoRequest.digraphOutcome_eq_outcome
assert_kernel_only TetraStereo.Engine.OfficialStereoRequest.certificateReady_eq_true_iff
assert_kernel_only TetraStereo.Engine.OfficialStereoRequest.certificateReady_eq_false_iff
assert_kernel_only
  TetraStereo.Engine.OfficialStereoRequest.officialRefusalReason?_isSome_iff_not_certificateReady
assert_kernel_only TetraStereo.Engine.OfficialStereoRequest.officialRefusalReason?_eq_some_iff
assert_kernel_only
  TetraStereo.Engine.OfficialStereoRequest.decideOfficialStereo_outcome_eq_none_iff
assert_kernel_only
  TetraStereo.Engine.OfficialStereoRequest.refused_implementationLimit_of_certificate_eq_none
assert_kernel_only
  TetraStereo.Engine.OfficialStereoRequest.refused_unresolvedOfficialPriorities_of_outcome_eq
assert_kernel_only
  TetraStereo.Engine.OfficialStereoRequest.certificate_eq_some_defaultEngineCertificate_of_graphFuel_eq_default
assert_kernel_only
  TetraStereo.Engine.OfficialStereoRequest.certificate_eq_some_defaultEngineCertificate_of_graphFuel_eq_stable
assert_kernel_only
  TetraStereo.Engine.OfficialStereoRequest.digraphTrace_eq_some_defaultEngineCertificate_trace_of_graphFuel_eq_stable
assert_kernel_only
  TetraStereo.Engine.OfficialStereoRequest.outcome_eq_some_defaultEngineCertificate_outcome_of_graphFuel_eq_stable
assert_kernel_only TetraStereo.Engine.CertifiedOfficialStereoComparison.artifact_checked
assert_kernel_only TetraStereo.Engine.OfficialStereoDecision.artifact_checked

end
end Engine
end TetraStereo
