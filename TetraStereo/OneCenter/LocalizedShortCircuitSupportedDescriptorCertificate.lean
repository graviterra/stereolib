import TetraStereo.OneCenter.LocalizedDependencyPrefix
import TetraStereo.OneCenter.LocalizedShortCircuitBoundedPipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedShortCircuit
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- A molecular target's computed local evidence, justified by a separately checked predecessor
prefix. The target is absent from that prefix; all permitted auxiliary reads are explicitly covered. -/
structure SupportedDescriptorCertificate (input : Input) (target : Occurrence input)
    (descriptor : LocalizedAuxiliaryLabel) where
  cache : Cached.RuntimeCache input
  support : DependencySupport input target
  localEvidence : Bounded.DescriptorCertificate input.certified
    (input.certified.localizedRerootChildrenFromCarrier? cache.carrier) target
    (input.certified.localizedDependencyView (lookup support.facts) target) descriptor

theorem SupportedDescriptorCertificate.local_production
    {input : Input} {target : Occurrence input} {descriptor : LocalizedAuxiliaryLabel}
    (certificate : SupportedDescriptorCertificate input target descriptor) :
    evaluator input (carrierFuel input) target
      (input.certified.localizedDependencyView (lookup certificate.support.facts) target) =
        some descriptor := by
  apply certificate.localEvidence.production
  intro cursor
  rw [certificate.cache.exact]
  exact input.certified.localizedRerootChildrenFromCarrier?_eq_executable cursor

/-- Checked auxiliary support transports the bounded target construction to the global solution.
This includes Rule45-dependent and pseudoasymmetric results; no all-view invariance is assumed. -/
theorem SupportedDescriptorCertificate.reference_assignment
    {input : Input} {target : Occurrence input} {descriptor : LocalizedAuxiliaryLabel}
    (certificate : SupportedDescriptorCertificate input target descriptor) :
    referenceState input target = some descriptor :=
  certificate.support.evaluator_eq_reference.symm.trans certificate.local_production

theorem SupportedDescriptorCertificate.evaluation_assignment
    {input : Input} {target : Occurrence input} {descriptor : LocalizedAuxiliaryLabel}
    (certificate : SupportedDescriptorCertificate input target descriptor)
    (result : Evaluation input) : lookup result.facts target = some descriptor := by
  rw [evaluation_eq_reference input result]
  exact certificate.reference_assignment

theorem SupportedDescriptorCertificate.positive_sound
    {input : Input} {target : Occurrence input} {descriptor : LocalizedAuxiliaryLabel}
    (certificate : SupportedDescriptorCertificate input target descriptor) :
    input.certified.DeclarativeLocalizedOccurrenceShortCircuitRule3Through5Descriptor
      target (input.certified.localizedDependencyView (referenceState input) target) descriptor :=
  reference_positive_sound input target descriptor certificate.reference_assignment

/-- Compile the target from established support using the proved smaller budget. -/
def certifyWithSupport? (input : Input) (cache : Cached.RuntimeCache input)
    (ready : input.certified.LocalizedRule3CallbackFreeCarrierCertificate (carrierFuel input))
    (target : Occurrence input) (support : DependencySupport input target) :
    Option (Sigma fun descriptor => SupportedDescriptorCertificate input target descriptor) := do
  let localEvidence ← Bounded.descriptorCertificate? input.certified
    (input.certified.localizedRerootChildrenFromCarrier? cache.carrier) ready target
    (input.certified.localizedDependencyView (lookup support.facts) target)
  pure ⟨localEvidence.1, { cache, support, localEvidence := localEvidence.2 }⟩

/-- Replay externally proposed predecessor nodes before using any of their optional labels. -/
def certifyWithProposedSupport? (input : Input) (cache : Cached.RuntimeCache input)
    (target : Occurrence input) (nodes : Nodes input) :
    Option (Sigma fun descriptor => SupportedDescriptorCertificate input target descriptor) := do
  let ready ← input.certified.localizedRule3CallbackFreeCarrierCertificate? (carrierFuel input)
  let support ← checkDependencySupport? input cache target nodes
  certifyWithSupport? input cache ready target support

/-- From molecular input, construct the cache, readiness evidence, checked dependency prefix,
full bounded comparison evidence, geometry and descriptor. No target answer is an argument. -/
def certifySupported? (input : Input) (target : Occurrence input) :
    Option (Sigma fun descriptor => SupportedDescriptorCertificate input target descriptor) := do
  let ready ← input.certified.localizedRule3CallbackFreeCarrierCertificate? (carrierFuel input)
  let cache := Cached.buildRuntimeCache input
  let support := Linear.produceDependencySupport input cache ready target
  certifyWithSupport? input cache ready target support

/-- Export the target's proposed value in the EXISTING data-only node format. The export stores
the proved label directly; it does not recompute the target evaluator to choose that label. -/
def SupportedDescriptorCertificate.targetNode
    {input : Input} {target : Occurrence input} {descriptor : LocalizedAuxiliaryLabel}
    (certificate : SupportedDescriptorCertificate input target descriptor) :
    Node (Occurrence input) LocalizedAuxiliaryLabel :=
  { target, outcome := some descriptor
    references := producerReferences (dependencies input) certificate.support.facts target }

theorem SupportedDescriptorCertificate.targetNode_valid
    {input : Input} {target : Occurrence input} {descriptor : LocalizedAuxiliaryLabel}
    (certificate : SupportedDescriptorCertificate input target descriptor) :
    ValidNode (runtimeSystem input) (dependencies input) certificate.support.facts certificate.targetNode := by
  have valid := producerNode_valid (runtimeSystem input) (dependencies input)
    certificate.support.facts target
    (input.certified.localizedDependencyList_nodup (carrierFuel input) target) certificate.support.covers
  refine ⟨valid.1, valid.2.1, valid.2.2.1, ?_⟩
  have equation : (runtimeSystem input).executableStep
      (lookup (referenced certificate.support.facts certificate.targetNode.references)) target =
        referenceState input target := by
    apply Eq.trans _ (reference_equation input target)
    apply input.certified.localizedCertificateSystem_evaluatorLocal (carrierFuel input)
      (runtimeSemantics input (carrierFuel input))
    intro source depends
    apply checked_referenced_lookup_eq_of_fixed (runtimeSystem input) (dependencies input)
      (referenceState input)
      (input.certified.localizedCertificateSystem_evaluatorLocal (carrierFuel input)
        (runtimeSemantics input (carrierFuel input)))
      (reference_equation input) certificate.support.nodes certificate.support.facts
      certificate.support.accepted
    change source ∈ (referenced certificate.support.facts
      (producerNode (runtimeSystem input) (dependencies input) certificate.support.facts target).references).map Prod.fst
    rw [valid.2.2.1]
    exact depends
  exact certificate.reference_assignment.symm.trans equation.symm

/-- A standalone replayable dependency certificate for the target, without later global nodes. -/
def SupportedDescriptorCertificate.nodes
    {input : Input} {target : Occurrence input} {descriptor : LocalizedAuxiliaryLabel}
    (certificate : SupportedDescriptorCertificate input target descriptor) : Nodes input :=
  certificate.support.nodes ++ [certificate.targetNode]

/-- The ordinary checker accepts the exported certificate, including its final target value. -/
theorem SupportedDescriptorCertificate.nodes_accepted
    {input : Input} {target : Occurrence input} {descriptor : LocalizedAuxiliaryLabel}
    (certificate : SupportedDescriptorCertificate input target descriptor) :
    check (runtimeSystem input) (dependencies input) certificate.nodes =
      some (certificate.support.facts ++ [(target, some descriptor)]) :=
  check_append_node (runtimeSystem input) (dependencies input) certificate.support.nodes
    certificate.support.facts certificate.targetNode certificate.support.accepted certificate.targetNode_valid

/-- User-facing target selection uses an atom index and the automatically perceived candidates. -/
structure CertifiedTarget (input : Input) where
  target : Occurrence input
  descriptor : LocalizedAuxiliaryLabel
  certificate : SupportedDescriptorCertificate input target descriptor

def certifyCenter? (input : Input) (atomIndex : Nat) : Option (CertifiedTarget input) := do
  let center ← input.certified.canonicalTetrahedralCenters.find? (fun center => center.val.val == atomIndex)
  let target := input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center
  let result ← certifySupported? input target
  pure { target, descriptor := result.1, certificate := result.2 }

def certifySourceCenter? (source : AuthoritativeChemicalInput) (atomIndex : Nat) :
    Option ((input : Input) × CertifiedTarget input) := do
  let input ← admitSource? source
  let result ← certifyCenter? input atomIndex
  pure ⟨input, result⟩

def certifySmilesCenter? (text : String) (spatial : SpatialConfiguration) (atomIndex : Nat)
    (cycles : List AromaticCycle := []) : Except ParserError (Option ((input : Input) × CertifiedTarget input)) :=
  (admitSmilesSpatial? text spatial cycles).map fun admitted => do
    let input ← admitted
    let result ← certifyCenter? input atomIndex
    pure ⟨input, result⟩

end TetraStereo.OneCenter.LocalizedShortCircuit
