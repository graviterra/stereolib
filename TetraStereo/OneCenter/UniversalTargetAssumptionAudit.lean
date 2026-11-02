import TetraStereo.OneCenter.LocalizedRawUniversalReferenceClosure
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.KernelOnly

set_option autoImplicit false



























































namespace TetraStereo.OneCenter

namespace LocalizedUniversalTargetAudit

open CertifiedLocalizedCIPInput TetraStereo.Certificate.Dependency

/-! ## The runtime occurrence of a legitimate graph-level occurrence -/

/-- The actual runtime occurrence assigned to a legitimate graph-level occurrence.

The address of a legitimate occurrence has length at most `atomCount`, so it is covered by the
shared occurrence enumeration at the pipeline carrier fuel `atomCount + 1`.  The membership proof
is the existing coverage theorem `legitimateOccurrence_mem_localizedOccurrences_of_fuel`; no
carrier-membership premise is assumed. -/
def legitimateOccurrenceRuntime
    (input : LocalizedReference.Input)
    {root : input.certified.Atom}
    {node : OfficialCIPNode input.certified.Atom}
    {address : List Nat}
    (occ : CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified root node address) :
    LocalizedUniversalReference.Occurrence input :=
  ⟨{ root := root
     address := address
     node := node
     remaining := LocalizedUniversalReference.carrierFuel input + 1 - address.length },
   CertifiedLocalizedCIPInput.legitimateOccurrence_mem_localizedOccurrences_of_fuel
     input.certified occ (fuel := LocalizedUniversalReference.carrierFuel input) (by
       have bound :=
         CertifiedLocalizedCIPInput.legitimateOccurrence_address_length_le_atomCount
           input.certified occ
       have fuelEq : LocalizedUniversalReference.carrierFuel input =
           input.certified.certified.input.molecule.atomCount + 1 := rfl
       omega)⟩

@[simp] theorem legitimateOccurrenceRuntime_root
    (input : LocalizedReference.Input)
    {root : input.certified.Atom}
    {node : OfficialCIPNode input.certified.Atom}
    {address : List Nat}
    (occ : CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified root node address) :
    (legitimateOccurrenceRuntime input occ).1.root = root := rfl

@[simp] theorem legitimateOccurrenceRuntime_address
    (input : LocalizedReference.Input)
    {root : input.certified.Atom}
    {node : OfficialCIPNode input.certified.Atom}
    {address : List Nat}
    (occ : CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified root node address) :
    (legitimateOccurrenceRuntime input occ).1.address = address := rfl

@[simp] theorem legitimateOccurrenceRuntime_node
    (input : LocalizedReference.Input)
    {root : input.certified.Atom}
    {node : OfficialCIPNode input.certified.Atom}
    {address : List Nat}
    (occ : CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified root node address) :
    (legitimateOccurrenceRuntime input occ).1.node = node := rfl

@[simp] theorem legitimateOccurrenceRuntime_remaining
    (input : LocalizedReference.Input)
    {root : input.certified.Atom}
    {node : OfficialCIPNode input.certified.Atom}
    {address : List Nat}
    (occ : CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified root node address) :
    (legitimateOccurrenceRuntime input occ).1.remaining =
      LocalizedUniversalReference.carrierFuel input + 1 - address.length := rfl

/-- The runtime occurrence of a legitimate occurrence retains a strictly positive fuel reserve. -/
theorem legitimateOccurrenceRuntime_remaining_pos
    (input : LocalizedReference.Input)
    {root : input.certified.Atom}
    {node : OfficialCIPNode input.certified.Atom}
    {address : List Nat}
    (occ : CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified root node address) :
    0 < (legitimateOccurrenceRuntime input occ).1.remaining := by
  have bound :=
    CertifiedLocalizedCIPInput.legitimateOccurrence_address_length_le_atomCount
      input.certified occ
  have fuelEq : LocalizedUniversalReference.carrierFuel input =
      input.certified.certified.input.molecule.atomCount + 1 := rfl
  rw [legitimateOccurrenceRuntime_remaining input occ]
  omega

/-- The runtime occurrence of a legitimate occurrence belongs to the executable carrier. -/
theorem legitimateOccurrenceRuntime_mem_carrier
    (input : LocalizedReference.Input)
    {root : input.certified.Atom}
    {node : OfficialCIPNode input.certified.Atom}
    {address : List Nat}
    (occ : CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified root node address) :
    legitimateOccurrenceRuntime input occ ∈
      input.certified.localizedOccurrenceCarrier
        (LocalizedUniversalReference.carrierFuel input) :=
  input.certified.localizedOccurrenceCarrier_complete
    (LocalizedUniversalReference.carrierFuel input)
    (legitimateOccurrenceRuntime input occ)

/-- The runtime occurrence of a legitimate occurrence is a target of the generated reference
facts, through the complete ranked certificate order. -/
theorem legitimateOccurrenceRuntime_mem_referenceFacts
    (input : LocalizedReference.Input)
    {root : input.certified.Atom}
    {node : OfficialCIPNode input.certified.Atom}
    {address : List Nat}
    (occ : CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified root node address) :
    legitimateOccurrenceRuntime input occ ∈
      (LocalizedUniversalReference.referenceFacts input).map Prod.fst := by
  rw [LocalizedUniversalReference.reference_targets input]
  exact input.certified.localizedCertificateOrder_complete
    (LocalizedUniversalReference.carrierFuel input)
    (legitimateOccurrenceRuntime input occ)

/-! ## Exact-label semantics at a legitimate occurrence -/

/-- **Positive exact-label semantics at a legitimate occurrence.**  The generated reference state
assigns a label exactly when some declarative universal descriptor exists at the state's own
dependency view. -/
theorem legitimateOccurrenceRuntime_referenceState_some_iff
    (input : LocalizedReference.Input)
    {root : input.certified.Atom}
    {node : OfficialCIPNode input.certified.Atom}
    {address : List Nat}
    (occ : CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified root node address)
    (descriptor : LocalizedAuxiliaryLabel) :
    LocalizedUniversalReference.referenceState input
        (legitimateOccurrenceRuntime input occ) = some descriptor ↔
      ∃ evaluationBudget : Nat,
        input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor
          (legitimateOccurrenceRuntime input occ)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (legitimateOccurrenceRuntime input occ))
          evaluationBudget descriptor :=
  LocalizedUniversalReference.referenceState_eq_some_iff_exists_declarativeUniversalDescriptor_unconditional
    input (legitimateOccurrenceRuntime input occ) descriptor

/-- **Exact refusal semantics at a legitimate occurrence.**  The generated reference state refuses
a legitimately generated occurrence exactly when no declarative universal descriptor exists at any
Rule-3 budget at the state's own dependency view.  This is an exact logical equivalence: it is not a
claim of chemical nonexistence, only the operational refusal boundary. -/
theorem legitimateOccurrenceRuntime_referenceState_none_iff
    (input : LocalizedReference.Input)
    {root : input.certified.Atom}
    {node : OfficialCIPNode input.certified.Atom}
    {address : List Nat}
    (occ : CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified root node address) :
    LocalizedUniversalReference.referenceState input
        (legitimateOccurrenceRuntime input occ) = none ↔
      ∀ (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel),
        ¬ input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor
          (legitimateOccurrenceRuntime input occ)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (legitimateOccurrenceRuntime input occ))
          evaluationBudget descriptor :=
  LocalizedUniversalReference.referenceState_eq_none_iff_forall_not_declarativeUniversalDescriptor_unconditional
    input (legitimateOccurrenceRuntime input occ)

/-! ## The coverage bundle -/

/-- Runtime coverage of one legitimate graph-level occurrence: the actual runtime occurrence with
the requested root, address and node, exact remaining depth, positive reserve, executable-carrier
membership, reference-fact target membership, and both directions of the unconditional exact-label
semantics at the generated reference state.

The predicate is stated in terms of the *existing* generated state and the *existing* declarative
relation.  It assumes nothing about any descriptor's presence or absence. -/
def LegitimateOccurrenceRuntimeCoverage
    (input : LocalizedReference.Input)
    (root : input.certified.Atom)
    (node : OfficialCIPNode input.certified.Atom)
    (address : List Nat) : Prop :=
  ∃ occurrence : LocalizedUniversalReference.Occurrence input,
    occurrence.1.root = root ∧
      occurrence.1.address = address ∧
        occurrence.1.node = node ∧
          occurrence.1.remaining =
            LocalizedUniversalReference.carrierFuel input + 1 - address.length ∧
            0 < occurrence.1.remaining ∧
              occurrence ∈ input.certified.localizedOccurrenceCarrier
                (LocalizedUniversalReference.carrierFuel input) ∧
                occurrence ∈
                  (LocalizedUniversalReference.referenceFacts input).map Prod.fst ∧
                  (∀ descriptor : LocalizedAuxiliaryLabel,
                    LocalizedUniversalReference.referenceState input occurrence = some descriptor ↔
                      ∃ evaluationBudget : Nat,
                        input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor
                          occurrence
                          (input.certified.localizedDependencyView
                            (LocalizedUniversalReference.referenceState input) occurrence)
                          evaluationBudget descriptor) ∧
                    (LocalizedUniversalReference.referenceState input occurrence = none ↔
                      ∀ (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel),
                        ¬ input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor
                          occurrence
                          (input.certified.localizedDependencyView
                            (LocalizedUniversalReference.referenceState input) occurrence)
                          evaluationBudget descriptor)

/-- **Breakthrough composition: every legitimate graph-level occurrence is a covered runtime
target with exact-label semantics.**

This is the missing join between the graph-level carrier coverage and the runtime universal
reference closure.  Its proof constructs the runtime occurrence by the coverage theorem at the
pipeline fuel `atomCount + 1`, places it in the executable carrier and in the generated fact
targets, and transports the unconditional exact-label semantics.  No descriptor, evidence,
ranking or model hypothesis is used. -/
theorem legitimateOccurrence_runtimeCoverage
    (input : LocalizedReference.Input)
    {root : input.certified.Atom}
    {node : OfficialCIPNode input.certified.Atom}
    {address : List Nat}
    (occ : CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified root node address) :
    LegitimateOccurrenceRuntimeCoverage input root node address := by
  refine ⟨legitimateOccurrenceRuntime input occ, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact legitimateOccurrenceRuntime_remaining input occ
  · exact legitimateOccurrenceRuntime_remaining_pos input occ
  · exact legitimateOccurrenceRuntime_mem_carrier input occ
  · exact legitimateOccurrenceRuntime_mem_referenceFacts input occ
  · exact fun descriptor =>
      legitimateOccurrenceRuntime_referenceState_some_iff input occ descriptor
  · exact legitimateOccurrenceRuntime_referenceState_none_iff input occ

/-! ## Coverage by an arbitrary accepted evaluation result -/

/-- Every accepted `Evaluation` result — not only the generated fallback — covers the runtime
occurrence as a fact target.  The proof uses the checked-replay coverage invariant
(`checkProposals?_exact`), not a property of the fallback production. -/
theorem legitimateOccurrence_mem_evaluationFacts
    (input : LocalizedReference.Input)
    (result : LocalizedUniversalReference.Evaluation input)
    {root : input.certified.Atom}
    {node : OfficialCIPNode input.certified.Atom}
    {address : List Nat}
    (occ : CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified root node address) :
    ∃ occurrence : LocalizedUniversalReference.Occurrence input,
      occurrence.1.root = root ∧
        occurrence.1.address = address ∧
          occurrence.1.node = node ∧
            occurrence ∈ result.facts.map Prod.fst := by
  obtain ⟨_checked, _nodup, coverage⟩ :=
    (LocalizedUniversalReference.checkProposals?_exact input result.nodes result.facts).mp
      result.accepted
  refine ⟨legitimateOccurrenceRuntime input occ, rfl, rfl, rfl, ?_⟩
  unfold LocalizedUniversalReference.covered at coverage
  have member :=
    input.certified.localizedOccurrenceCarrier_complete
      (LocalizedUniversalReference.carrierFuel input)
      (legitimateOccurrenceRuntime input occ)
  exact of_decide_eq_true
    ((List.all_eq_true.mp coverage) (legitimateOccurrenceRuntime input occ) member)

/-! ## Raw-source endpoint -/

/-- **Raw-source universal endpoint with legitimate-occurrence coverage.**

Starting only from the executable raw gate and one coordinate per stored atom, the actual
`LocalizedReference.admitRawSpatial?` succeeds on the exact converted molecule; the admitted input
carries the unique independent semantic reference model realized by the generated `referenceState`;
every legitimate graph-level occurrence of the admitted certified graph is a covered runtime target
with exact-label semantics; and every runnable `evaluate` lookup is pointwise equivalent to the
independent declarative universal-descriptor relation at its own dependency view.

The legitimate-occurrence conjunct is the new content.  The conversion, admission, uniqueness,
realization and evaluator equivalence are the already kernel-guarded results of
`LocalizedRawUniversalReferenceClosure`; they are reused verbatim. -/
theorem rawSource_legitimateOccurrence_universalEndpoint
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (rawReady : LocalizedRawGraphReadiness.RawLocalizedGraphSourceReady molecule)
    (spatialLength : spatial.positions.length = molecule.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      molecule.toSemanticMolecule? = some semantic ∧
        LocalizedReference.admitRawSpatial? molecule spatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            molecule.AuthoritativeStructureAgreement input.certified.certified.input ∧
              input.certified.certified.input.spatial? = some spatial ∧
                (∃! state : input.certified.LocalizedAuxiliaryState
                    (LocalizedUniversalReference.carrierFuel input),
                  LocalizedUniversalReference.IndependentSemanticReferenceModel input state) ∧
                  LocalizedUniversalReference.IndependentSemanticReferenceModel input
                    (LocalizedUniversalReference.referenceState input) ∧
                    (∀ (root : input.certified.Atom)
                        (node : OfficialCIPNode input.certified.Atom) (address : List Nat),
                      CertifiedLocalizedCIPInput.LegitimateOccurrence input.certified
                          root node address →
                        LegitimateOccurrenceRuntimeCoverage input root node address) ∧
                      (∀ (nodes : LocalizedUniversalReference.Nodes input)
                          (target : LocalizedUniversalReference.Occurrence input)
                          (descriptor : LocalizedAuxiliaryLabel),
                        lookup
                            (LocalizedUniversalReference.evaluate input nodes).facts target =
                          some descriptor ↔
                          ∃ evaluationBudget : Nat,
                            input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
                              (input.certified.localizedDependencyView
                                (lookup
                                  (LocalizedUniversalReference.evaluate input nodes).facts) target)
                              evaluationBudget descriptor) := by
  obtain ⟨semantic, input, converted, admitted, moleculeEq, agreement, spatialEq⟩ :=
    LocalizedRawGraphReadiness.admitRawSpatial?_of_raw molecule spatial rawReady spatialLength
  obtain ⟨uniqueModel, realized, evaluatorEquivalence⟩ :=
    LocalizedRawUniversalReferenceClosure.universalReferenceClosure_of_input input
  exact ⟨semantic, input, converted, admitted, moleculeEq, agreement, spatialEq,
    uniqueModel, realized,
    fun root node address occ => legitimateOccurrence_runtimeCoverage input occ,
    evaluatorEquivalence⟩

end LocalizedUniversalTargetAudit

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.LocalizedUniversalTargetAudit.legitimateOccurrenceRuntime_root
assert_kernel_only
  TetraStereo.OneCenter.LocalizedUniversalTargetAudit.legitimateOccurrenceRuntime_address
assert_kernel_only
  TetraStereo.OneCenter.LocalizedUniversalTargetAudit.legitimateOccurrenceRuntime_node
assert_kernel_only
  TetraStereo.OneCenter.LocalizedUniversalTargetAudit.legitimateOccurrenceRuntime_remaining
assert_kernel_only
  TetraStereo.OneCenter.LocalizedUniversalTargetAudit.legitimateOccurrenceRuntime_remaining_pos
assert_kernel_only
  TetraStereo.OneCenter.LocalizedUniversalTargetAudit.legitimateOccurrenceRuntime_mem_carrier
assert_kernel_only
  TetraStereo.OneCenter.LocalizedUniversalTargetAudit.legitimateOccurrenceRuntime_mem_referenceFacts
assert_kernel_only
  TetraStereo.OneCenter.LocalizedUniversalTargetAudit.legitimateOccurrenceRuntime_referenceState_some_iff
assert_kernel_only
  TetraStereo.OneCenter.LocalizedUniversalTargetAudit.legitimateOccurrenceRuntime_referenceState_none_iff
assert_kernel_only
  TetraStereo.OneCenter.LocalizedUniversalTargetAudit.legitimateOccurrence_runtimeCoverage
assert_kernel_only
  TetraStereo.OneCenter.LocalizedUniversalTargetAudit.legitimateOccurrence_mem_evaluationFacts
assert_kernel_only
  TetraStereo.OneCenter.LocalizedUniversalTargetAudit.rawSource_legitimateOccurrence_universalEndpoint
