import TetraStereo.OneCenter.LocalizedOccurrenceFiniteCarrier
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.Certificate.FiniteRankedOrder
import TetraStereo.Certificate.DependencyCheckedModel
import TetraStereo.Certificate.DependencyProducer

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open DeclarativeCIP
open TetraStereo.Certificate
open Dependency

/-- Every dependency precedes its target in a list satisfying this split property. -/
private theorem ready_of_splits {O : Type} (deps : O → List O) (whole : List O)
    (earlier : ∀ pre target tail, whole = pre ++ target :: tail →
      ∀ inner ∈ deps target, inner ∈ pre)
    (pre rest : List O) (split : whole = pre ++ rest) : PrefixReady deps pre rest := by
  induction rest generalizing pre with
  | nil => trivial
  | cons target tail ih =>
      refine ⟨earlier pre target tail split, ?_⟩
      apply ih (pre ++ [target])
      simpa using split

def localizedCertificateRank (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence fuel) : Nat := occurrence.1.remaining

def localizedCertificateOrder (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    List (input.LocalizedCIPOccurrence fuel) :=
  FiniteRankedOrder.rankedOrder (input.localizedCertificateRank fuel)
    (input.localizedOccurrenceCarrier fuel)

def localizedCertificateDependencies (input : CertifiedLocalizedCIPInput) (fuel : Nat) :=
  input.localizedDependencyList fuel

def localizedCertificateSystem (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    OccurrenceSystem input.TetrahedralCenter (input.LocalizedCIPOccurrence fuel)
      LocalizedAuxiliaryLabel :=
  input.localizedAuxiliaryOccurrenceSystemExecutableRoot semantics

def localizedCertificateNodes (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :=
  produce (input.localizedCertificateSystem fuel semantics)
    (input.localizedCertificateDependencies fuel) (input.localizedCertificateOrder fuel)

def localizedCertificateFacts (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :=
  (input.localizedCertificateNodes fuel semantics).map fun node => (node.target, node.outcome)

theorem localizedCertificateOrder_nodup (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedCertificateOrder fuel).Nodup :=
  FiniteRankedOrder.nodup_rankedOrder _ _ (input.localizedOccurrenceCarrier_nodup fuel)

theorem localizedCertificateOrder_complete (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence ∈ input.localizedCertificateOrder fuel :=
  (FiniteRankedOrder.mem_rankedOrder _ _).mpr
    (input.localizedOccurrenceCarrier_complete fuel occurrence)

theorem prefixReady_localizedCertificateOrder (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    PrefixReady (input.localizedCertificateDependencies fuel) []
      (input.localizedCertificateOrder fuel) := by
  apply ready_of_splits _ (input.localizedCertificateOrder fuel)
  · intro pre target tail split inner member
    exact FiniteRankedOrder.mem_prefix_of_rank_lt
      (input.localizedCertificateRank fuel) split
      (input.localizedOccurrenceCarrier_complete fuel inner)
      (input.localizedDepthDependency_remaining_lt
        ((input.mem_localizedDependencyList_iff fuel target inner).mp member))
  · rfl

theorem localizedCertificate_check (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    check (input.localizedCertificateSystem fuel semantics)
      (input.localizedCertificateDependencies fuel) (input.localizedCertificateNodes fuel semantics) =
      some (input.localizedCertificateFacts fuel semantics) :=
  produce_check _ _ _ (input.prefixReady_localizedCertificateOrder fuel)
    (fun target _ => input.localizedDependencyList_nodup fuel target)

theorem localizedCertificateFacts_targets (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    (input.localizedCertificateFacts fuel semantics).map Prod.fst =
      input.localizedCertificateOrder fuel := produce_result_targets _ _ _

theorem localizedCertificateSystem_derivationStepCorrespondence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    (input.localizedCertificateSystem fuel semantics).DerivationStepCorrespondence :=
  input.localizedAuxiliaryOccurrenceSystemExecutableRoot_derivationStepCorrespondence semantics

theorem localizedCertificateSystem_evaluatorLocal (input : CertifiedLocalizedCIPInput)
    (fuel : Nat) (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    (input.localizedCertificateSystem fuel semantics).EvaluatorLocalFor
      (relation (input.localizedCertificateDependencies fuel)) := by
  intro left right target agree
  exact input.localizedExecutableStep_eq_of_depthAgree semantics.executableRule left right target
    (fun source deeper => agree source
      ((input.mem_localizedDependencyList_iff fuel target source).mpr deeper))

/-- The certificate is generated from the input; no proposed solution is an assumption. -/
theorem localizedCertificateFacts_cipModel (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    (input.localizedCertificateSystem fuel semantics).CIPModel
      (lookup (input.localizedCertificateFacts fuel semantics)) := by
  apply DependencyCheckedModel.checked_lookup_cipModel _ _
    (input.localizedCertificateNodes fuel semantics) _ (input.localizedCertificate_check fuel semantics)
  · rw [input.localizedCertificateFacts_targets fuel semantics]
    exact input.localizedCertificateOrder_nodup fuel
  · intro occurrence
    rw [input.localizedCertificateFacts_targets fuel semantics]
    exact input.localizedCertificateOrder_complete fuel occurrence
  · exact input.localizedCertificateSystem_evaluatorLocal fuel semantics
  · exact input.localizedCertificateSystem_derivationStepCorrespondence fuel semantics

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
