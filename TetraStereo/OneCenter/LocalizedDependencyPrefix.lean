import TetraStereo.Certificate.DependencyPrefix
import TetraStereo.OneCenter.LocalizedShortCircuitCachedPipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedShortCircuit
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- A checked partial certificate covers every permitted target read and excludes the target.
Verified `none` facts remain listed; an unlisted fact cannot satisfy coverage. -/
structure DependencySupport (input : Input) (target : Occurrence input) where
  nodes : Nodes input
  facts : Facts input
  accepted : check (runtimeSystem input) (dependencies input) nodes = some facts
  covers : ∀ source ∈ dependencies input target, source ∈ facts.map Prod.fst
  targetAbsent : target ∉ facts.map Prod.fst

/-- Check arbitrary proposed support independently of a complete global certificate. -/
def checkDependencySupport? (input : Input) (cache : Cached.RuntimeCache input)
    (target : Occurrence input) (nodes : Nodes input) : Option (DependencySupport input target) :=
  match accepted : check (Cached.systemUsingCache input cache)
      (Cached.dependenciesUsingCache input cache) nodes with
  | none => none
  | some facts =>
      if covered : (dependencies input target).all
          (fun source => decide (source ∈ facts.map Prod.fst)) = true then
        if absent : target ∉ facts.map Prod.fst then
          some
            { nodes, facts
              accepted := by
                rwa [Cached.systemUsingCache_eq, Cached.dependenciesUsingCache_eq] at accepted
              covers := fun source present =>
                of_decide_eq_true ((List.all_eq_true.mp covered) source present)
              targetAbsent := absent }
        else none
      else none

/-- The exact predecessor portion of the automatically constructed dependency schedule. -/
def dependencyPrefixOrder (input : Input) (target : Occurrence input) : List (Occurrence input) :=
  prefixBeforeTarget (input.certified.localizedCertificateOrder (carrierFuel input)) target

theorem dependencyPrefixOrder_ready (input : Input) (target : Occurrence input) :
    PrefixReady (dependencies input) [] (dependencyPrefixOrder input target) :=
  PrefixReady.take _ _ _ _ (input.certified.prefixReady_localizedCertificateOrder (carrierFuel input))

theorem dependencyPrefixOrder_support (input : Input) (target : Occurrence input) :
    (∀ source ∈ dependencies input target, source ∈ dependencyPrefixOrder input target) ∧
      target ∉ dependencyPrefixOrder input target :=
  prefix_before_target _ _ _
    (input.certified.prefixReady_localizedCertificateOrder (carrierFuel input))
    (input.certified.localizedCertificateOrder_nodup (carrierFuel input))
    (input.certified.localizedCertificateOrder_complete (carrierFuel input) target)

/-- Generate the prefix with materialized carrier/dependency tables. The producer's generic
proof supplies acceptance and coverage for every molecular target; no state is supplied. -/
def produceDependencySupport (input : Input) (cache : Cached.RuntimeCache input)
    (target : Occurrence input) : DependencySupport input target :=
  let nodes := produce (Cached.systemUsingCache input cache)
    (Cached.dependenciesUsingCache input cache) (dependencyPrefixOrder input target)
  let facts := nodes.map (fun node => (node.target, node.outcome))
  have targets : facts.map Prod.fst = dependencyPrefixOrder input target :=
    produce_result_targets _ _ _
  { nodes, facts
    accepted := by
      dsimp only [nodes, facts]
      rw [Cached.systemUsingCache_eq, Cached.dependenciesUsingCache_eq]
      exact produce_check _ _ _ (dependencyPrefixOrder_ready input target)
        (fun source _ => input.certified.localizedDependencyList_nodup (carrierFuel input) source)
    covers := by
      rw [targets]
      exact (dependencyPrefixOrder_support input target).1
    targetAbsent := by
      rw [targets]
      exact (dependencyPrefixOrder_support input target).2 }

/-- Partial checked facts agree with the generated solution at every LISTED occurrence. -/
theorem DependencySupport.lookup_eq_reference
    {input : Input} {target : Occurrence input} (support : DependencySupport input target)
    (source : Occurrence input) (present : source ∈ support.facts.map Prod.fst) :
    lookup support.facts source = referenceState input source :=
  checked_lookup_eq_of_fixed (runtimeSystem input) (dependencies input) (referenceState input)
    (input.certified.localizedCertificateSystem_evaluatorLocal (carrierFuel input)
      (runtimeSemantics input (carrierFuel input)))
    (reference_equation input) support.nodes support.facts support.accepted source present

/-- All legal auxiliary reads agree. No claim is made about unlisted or nondependency values. -/
theorem DependencySupport.view_eq_reference
    {input : Input} {target : Occurrence input} (support : DependencySupport input target) :
    input.certified.localizedDependencyView (lookup support.facts) target =
      input.certified.localizedDependencyView (referenceState input) target := by
  funext source deeper
  exact support.lookup_eq_reference source (support.covers source
    ((input.certified.mem_localizedDependencyList_iff (carrierFuel input) target source).mpr deeper))

/-- The target evaluator using only its verified support is the generated global outcome. -/
theorem DependencySupport.evaluator_eq_reference
    {input : Input} {target : Occurrence input} (support : DependencySupport input target) :
    evaluator input (carrierFuel input) target
      (input.certified.localizedDependencyView (lookup support.facts) target) =
        referenceState input target := by
  rw [support.view_eq_reference]
  exact reference_equation input target

end TetraStereo.OneCenter.LocalizedShortCircuit
