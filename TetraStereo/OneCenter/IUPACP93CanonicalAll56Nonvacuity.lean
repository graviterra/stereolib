import TetraStereo.OneCenter.IUPACP93CanonicalObservationCompiler
import TetraStereo.OneCenter.IUPACP93CanonicalSourceProgram
import TetraStereo.OneCenter.IUPACRemaining56P93ReviewedNonvacuity

set_option autoImplicit false

/-!
# Canonical all-56 P-93 nonvacuity

This module is the final source-program transport.  It inverts the exhaustive descriptor-kernel
row into the exact closed-production clause, selects that clause's admitted source entry, and
casts the independently compiled production judgment into the assembled global reviewed table.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open IUPACNormativeProvision

namespace P93CanonicalSourceProgram

/-- Exact inverse routing from the exhaustive 56-row descriptor kernel to the closed clause
whose canonical payload compiler owns that row. -/
def toClosedProduction : Remaining71P93DescriptorKernelRow → P93Clause
  | .general row => .general row
  | .noncarbon row => .noncarbon row
  | .acyclic row => .acyclic row
  | .cyclic .cyclicConfigurations => .monocyclic .cyclicConfigurations
  | .cyclic .monocyclicAbsoluteCenters => .monocyclic .monocyclicAbsoluteCenters
  | .cyclic .monocyclicAchiralCenters => .monocyclic .monocyclicAchiralCenters
  | .cyclic .monocyclicCisTrans => .monocyclic .monocyclicCisTrans
  | .cyclic .monocyclicRCT => .monocyclic .monocyclicRCT
  | .cyclic .unsaturatedMonocycles => .monocyclic .unsaturatedMonocycles
  | .cyclic .cyclicDoubleBonds => .monocyclic .cyclicDoubleBonds
  | .cyclic .exocyclicDoubleBondEZ => .monocyclic .exocyclicDoubleBondEZ
  | .cyclic .exocyclicDoubleBondOther => .monocyclic .exocyclicDoubleBondOther
  | .cyclic .vonBaeyerCIPCenters => .vonBaeyer .vonBaeyerCIPCenters
  | .cyclic .vonBaeyerEndoExoSynAnti => .vonBaeyer .vonBaeyerEndoExoSynAnti
  | .cyclic .vonBaeyerCisTrans => .vonBaeyer .vonBaeyerCisTrans
  | .cyclic .vonBaeyerDoubleBonds => .vonBaeyer .vonBaeyerDoubleBonds
  | .cyclic .spiroXabcd => .spiro .spiroXabcd
  | .cyclic .spiroXabab => .spiro .spiroXabab
  | .cyclic .spiroDoubleBonds => .spiro .spiroDoubleBonds
  | .cyclic .spiroNontetrahedralCenters => .spiroNontetrahedral
  | .cyclic .spiroAxialChirality => .spiro .spiroAxialChirality
  | .cyclic .fusedBridgedCIP => .fusedCyclophane .fusedBridgedCIP
  | .cyclic .cisoidTransoid => .fusedCyclophane .cisoidTransoid
  | .cyclic .cyclophanePlanes => .fusedCyclophane .cyclophanePlanes
  | .cyclic .cyclophaneCenters => .fusedCyclophane .cyclophaneCenters
  | .cyclic .cyclophaneDoubleBonds => .fusedCyclophane .cyclophaneDoubleBonds
  | .cyclic .fullereneGeneralMethodology => .fullerene .generalMethodology
  | .cyclic .fullereneInherentParentChirality => .fullerene .inherentParentChirality
  | .cyclic .fullereneInherentSubstitutionChirality =>
      .fullerene .inherentSubstitutionChirality
  | .cyclic .fullereneNoninherentSubstitutionChirality =>
      .fullerene .noninherentSubstitutionChirality
  | .cyclic .fullereneChiralSubstituents => .fullerene .chiralSubstituents
  | .cyclic .fullereneSuperimposedStereogenicElements =>
      .fullerene .superimposedStereogenicElements
  | .cyclic .ringAssemblyAxes => .ringAssembly .axes
  | .cyclic .ringAssemblyCenters => .ringAssembly .centers
  | .cyclic .ringAssemblyDoubleBonds => .ringAssembly .doubleBonds
  | .cyclic .coupledRingChainConfigurations => .coupledRingChain .configurations

@[simp] theorem ofClosedProduction_toClosedProduction
    (row : Remaining71P93DescriptorKernelRow) :
    Remaining71P93DescriptorKernelRow.ofClosedProduction (toClosedProduction row) = row := by
  cases row with
  | general child | noncarbon child | acyclic child => rfl
  | cyclic child => cases child <;> rfl

theorem toClosedProduction_mem_all
    (row : Remaining71P93DescriptorKernelRow) : toClosedProduction row ∈ P93Clause.all := by
  cases row with
  | general child =>
      cases child <;> simp [toClosedProduction, P93Clause.all,
        Remaining71P93ClosedProductionRow.all,
        Remaining71P93ClosedProductionRow.generalRows, Remaining71P93GeneralAuthorityRow.all]
  | noncarbon child =>
      cases child <;> simp [toClosedProduction, P93Clause.all,
        Remaining71P93ClosedProductionRow.all,
        Remaining71P93ClosedProductionRow.noncarbonRows,
        Remaining71P93NoncarbonAuthorityRow.all]
  | acyclic child =>
      cases child <;> simp [toClosedProduction, P93Clause.all,
        Remaining71P93ClosedProductionRow.all,
        Remaining71P93ClosedProductionRow.acyclicRows, Remaining71P93AcyclicAuthorityRow.all]
  | cyclic child =>
      cases child <;> simp [toClosedProduction, P93Clause.all,
        Remaining71P93ClosedProductionRow.all,
        Remaining71P93ClosedProductionRow.fullereneRows,
        Remaining71P93ClosedProductionRow.monocyclicRows,
        Remaining71P93ClosedProductionRow.vonBaeyerRows,
        Remaining71P93ClosedProductionRow.ringAssemblyRows,
        Remaining71P93ClosedProductionRow.spiroRows,
        Remaining71P93ClosedProductionRow.fusedCyclophaneRows,
        Remaining71P93ClosedProductionRow.coupledRingChainRows,
        Remaining71P93FullereneAuthorityRow.all, Remaining71P93MonocyclicAuthorityRow.all,
        Remaining71P93VonBaeyerAuthorityRow.all, Remaining71P93RingAssemblyAuthorityRow.all,
        Remaining71P93SpiroReadyAuthorityRow.all,
        Remaining71P93FusedCyclophaneAuthorityRow.all,
        Remaining71P93CoupledRingChainAuthorityRow.all]

/-- Forget the ergonomic family match and expose the exact aggregate closed-row carrier. -/
theorem entryProductionWitness_exact
    (program : P93CanonicalSourceProgram) (entry : P93CanonicalClauseObservationEntry)
    (witness : program.EntryProductionWitness entry) :
    let policies := program.compiledPolicies.toRemaining71WithP94Schema
    ∃ observation : (entry.clause.reference policies).Observation,
      entry.clause.ProductionJudges policies entry.source observation := by
  dsimp only
  generalize clauseEq : entry.clause = clause
  cases clause with
  | fullerene row | noncarbon row | general row | monocyclic row | vonBaeyer row
  | ringAssembly row | acyclic row | spiro row | fusedCyclophane row
  | coupledRingChain row =>
      simpa [EntryProductionWitness, clauseEq, P93CanonicalSourceProgram.compiledPolicies,
        Remaining56P93ReviewedPolicies.toRemaining71WithP94Schema] using witness
  | spiroNontetrahedral =>
      simpa [EntryProductionWitness, clauseEq, P93CanonicalSourceProgram.compiledPolicies,
        Remaining56P93ReviewedPolicies.toRemaining71WithP94Schema] using witness

/-- Select an admitted canonical entry and expose its reviewed reference judgment and
applicability at the exact aggregate closed row. -/
theorem closedProduction_reference_nonvacuous
    (program : P93CanonicalSourceProgram) (row : P93Clause)
    (rowMem : row ∈ P93Clause.all) :
    let policies := program.compiledPolicies.toRemaining71WithP94Schema
    ∃ input, ∃ observation : (row.reference policies).Observation,
      input.StructurallyWellFormed ∧ (row.reference policies).Applicable input ∧
        (row.reference policies).Judges input observation := by
  dsimp only
  rcases program.all56_entry_productionJudges row rowMem with
    ⟨entry, entryMem, clauseEq, entryWitness⟩
  have exactWitness := program.entryProductionWitness_exact entry entryWitness
  rw [clauseEq] at exactWitness
  rcases exactWitness with ⟨observation, productionJudged⟩
  have judged := (row.production_eq_reference
    program.compiledPolicies.toRemaining71WithP94Schema entry.source observation).1
      productionJudged
  have applicable := row.reference_applicable_of_judged
    program.compiledPolicies.toRemaining71WithP94Schema entry.source observation judged
  exact ⟨entry.source, observation, entry.sourceAdmitted, applicable, judged⟩

/-- A complete canonical P-93 source program supplies the exact 56-row witness family required by
the assembled global reviewed semantics.  No policy, observation, or row witness is supplied by
the caller beyond the program itself. -/
theorem remaining56P93ReviewedNonvacuity
    (program : P93CanonicalSourceProgram)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ParameterizedRemaining56P93ReviewedNonvacuity program.compiledPolicies negative := by
  dsimp only [ParameterizedRemaining56P93ReviewedNonvacuity]
  intro row
  let closed := toClosedProduction row
  let reviewedPolicies := program.compiledPolicies.toRemaining71WithP94Schema
  rcases program.closedProduction_reference_nonvacuous closed
      (toClosedProduction_mem_all row) with
    ⟨input, observation, admitted, applicable, judged⟩
  have inverse : Remaining71P93DescriptorKernelRow.ofClosedProduction closed = row := by
    exact ofClosedProduction_toClosedProduction row
  have descriptorReferenceEq :
      row.reference reviewedPolicies = closed.reference reviewedPolicies := by
    rw [← Remaining71P93DescriptorKernelRow.ofClosedProduction_reference
      reviewedPolicies closed, inverse]
  let globalPolicies := program.compiledPolicies.toDescriptorBearingWithP94Schema
  let global := assembleGlobalReviewedSemantics globalPolicies negative
  have globalReferenceEq :
      (global.reviewed.row row.provision).reference = row.reference reviewedPolicies := by
    simpa [global, globalPolicies, reviewedPolicies,
      Remaining56P93ReviewedPolicies.toDescriptorBearingWithP94Schema,
      Remaining56P93ReviewedPolicies.toRemaining71WithP94Schema] using
        congrArg ReviewedProvisionSemantics.reference
          (globalReviewedSemantics_remaining71P93_exact global row)
  have referenceEq :
      (global.reviewed.row row.provision).reference = closed.reference reviewedPolicies :=
    globalReferenceEq.trans descriptorReferenceEq
  have globalAdmitted : global.reviewed.ChemicallyAdmitted input := by
    simpa [global, assembleGlobalReviewedSemantics, assembledGlobalReviewedTable] using admitted
  let globalObservation := cast
    (congrArg ProvisionReference.Observation referenceEq.symm) observation
  refine ⟨input, globalObservation, globalAdmitted,
    (ProvisionReference.applicable_congr referenceEq _).mpr applicable, ?_⟩
  apply (ProvisionReference.judges_cast_congr
    referenceEq input globalObservation).mpr
  simpa [globalObservation] using judged

/-- The frozen canonical P-93 program discharges the entire 56-row positive frontier without a
caller-supplied program, policy, source entry, observation, or row witness. -/
theorem iupacP93CanonicalRemaining56ReviewedNonvacuity
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ParameterizedRemaining56P93ReviewedNonvacuity
      iupacP93CanonicalSourceProgram.compiledPolicies negative :=
  iupacP93CanonicalSourceProgram.remaining56P93ReviewedNonvacuity negative

end P93CanonicalSourceProgram
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalSourceProgram.iupacP93CanonicalRemaining56ReviewedNonvacuity
