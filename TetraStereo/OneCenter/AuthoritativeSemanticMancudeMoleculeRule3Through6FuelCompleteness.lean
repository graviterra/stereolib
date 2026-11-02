import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3FuelCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6Totality

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Finite-fuel completeness of the source-canonical tetrahedral endpoint

This theorem removes recursive-builder success assumptions from the molecule endpoint.  At the
proved finite reroot bound, the retained premises are chemical/evidential: a represented
four-ligand spatial frame with nonzero parity, resolved Rule-3 observations, unambiguous coupled
Rule-3 topology, and applicability of the appropriate Rules-3--6 branch to the unique canonical
initial partition.
-/

/-- Chemically meaningful sufficient evidence for the complete source-canonical Rules-1a--6
endpoint at its proved uniform finite recursion bound. -/
def AromaticCanonicalScheduledRule3Through6ChemicallyReadyAtBound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  let view := source.aromaticCanonicalDependencyView state target
  let ruleFuel := 2 * (carrierFuel + 1)
  ∃ roots parity,
    source.aromaticCanonicalOccurrenceLigandFrame? target = some roots ∧
      source.aromaticCanonicalRerootFrameParity? roots = some parity ∧
      source.AromaticCanonicalRule3GeometryResolved carrierFuel ∧
      (∀ rawKeys,
        roots.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
          ruleFuel) = some rawKeys →
        source.DeclarativeAromaticCanonicalRule3TopologyUnambiguous rawKeys) ∧
      ∃ rootsLength : roots.length = 4,
        ∀ partition,
          source.buildAromaticCanonicalRule3Through5InitialPartition?
              target view ruleFuel roots = some partition →
            source.AromaticCanonicalRule6TopologyAdmissible
                center.1 roots rootsLength partition ∧
              ∃ descriptor,
                source.AromaticCanonicalRule3Through6BranchDescriptorJudgment
                  target view ruleFuel roots partition parity descriptor

/-- Every chemically ready perceived center reaches a final descriptor at the explicit uniform
finite recursion bound. -/
theorem exists_aromaticCanonicalScheduledRule3Through6Descriptor?_at_bound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalScheduledRule3Through6ChemicallyReadyAtBound
      semantics center) :
    ∃ descriptor,
      source.aromaticCanonicalScheduledRule3Through6Descriptor?
        semantics (2 * (carrierFuel + 1)) center = some descriptor := by
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  let view := source.aromaticCanonicalDependencyView state target
  let ruleFuel := 2 * (carrierFuel + 1)
  change ∃ descriptor,
    source.aromaticCanonicalScheduledRule3Through6Descriptor?
      semantics ruleFuel center = some descriptor
  change ∃ roots parity,
      source.aromaticCanonicalOccurrenceLigandFrame? target = some roots ∧
        source.aromaticCanonicalRerootFrameParity? roots = some parity ∧
        source.AromaticCanonicalRule3GeometryResolved carrierFuel ∧
        (∀ rawKeys,
          roots.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
            ruleFuel) = some rawKeys →
          source.DeclarativeAromaticCanonicalRule3TopologyUnambiguous rawKeys) ∧
        ∃ rootsLength : roots.length = 4,
          ∀ partition,
            source.buildAromaticCanonicalRule3Through5InitialPartition?
                target view ruleFuel roots = some partition →
              source.AromaticCanonicalRule6TopologyAdmissible
                  center.1 roots rootsLength partition ∧
                ∃ descriptor,
                  source.AromaticCanonicalRule3Through6BranchDescriptorJudgment
                    target view ruleFuel roots partition parity descriptor at ready
  rcases ready with
    ⟨roots, parity, rootsComputed, parityComputed, geometryResolved,
      declarativeTopology,
      rootsLength, everyPartition⟩
  have valid : ∀ cursor ∈ roots,
      source.AromaticCanonicalRerootCursorValid cursor :=
    source.aromaticCanonicalOccurrenceLigandFrame_cursor_valid
      target roots rootsComputed
  have resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel :=
    (source.aromaticCanonicalRule3GeometryResolved_iff_spatiallyResolved
      carrierFuel).mp geometryResolved
  have topology : ∀ rawKeys,
      roots.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
        ruleFuel) = some rawKeys →
      source.AromaticCanonicalRule3TopologyUnambiguous rawKeys := by
    intro rawKeys computed
    exact (source.aromaticCanonicalRule3TopologyUnambiguous_iff_declarative
      rawKeys).mpr (declarativeTopology rawKeys computed)
  have inputsResolved :
      source.AromaticCanonicalRule3Through5RootInputsResolved
        target view ruleFuel roots := by
    exact source.aromaticCanonicalRule3Through5RootInputsResolved_at_twice
      target view roots rootsLength valid resolved topology
  have chemicallyReady : source.AromaticCanonicalRule3Through6ChemicallyReady
      center.1 target view ruleFuel roots parity :=
    ⟨rootsLength, inputsResolved, everyPartition⟩
  have schedulerReady : source.AromaticCanonicalRule3Through6Ready
      center.1 target view ruleFuel roots parity :=
    (source.aromaticCanonicalRule3Through6ChemicallyReady_iff_ready
      center.1 target view ruleFuel roots parity).mp chemicallyReady
  rcases schedulerReady with ⟨descriptor, finalJudgment⟩
  refine ⟨descriptor,
    (source.aromaticCanonicalScheduledRule3Through6Descriptor?_eq_some_iff_executableJudgment
      semantics ruleFuel center descriptor).mpr ?_⟩
  exact ⟨roots, parity, rootsComputed, parityComputed, finalJudgment⟩

/-- End-to-end completeness and correctness together: readiness produces an emitted descriptor
and an independent complete molecule-level derivation of that same descriptor. -/
theorem exists_aromaticCanonicalScheduledRule3Through6Descriptor_and_judgment_at_bound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalScheduledRule3Through6ChemicallyReadyAtBound
      semantics center) :
    ∃ descriptor,
      source.aromaticCanonicalScheduledRule3Through6Descriptor?
          semantics (2 * (carrierFuel + 1)) center = some descriptor ∧
        source.AromaticCanonicalScheduledRule3Through6DescriptorJudgment
          semantics (2 * (carrierFuel + 1)) center descriptor := by
  obtain ⟨descriptor, computed⟩ :=
    source.exists_aromaticCanonicalScheduledRule3Through6Descriptor?_at_bound
      semantics center ready
  have executable :=
    (source.aromaticCanonicalScheduledRule3Through6Descriptor?_eq_some_iff_executableJudgment
      semantics (2 * (carrierFuel + 1)) center descriptor).mp computed
  exact ⟨descriptor, computed, executable.complete⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
