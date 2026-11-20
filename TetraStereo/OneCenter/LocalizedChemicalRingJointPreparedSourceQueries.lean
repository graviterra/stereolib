import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceProfileMap
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The molecular query domain consumed by the independent candidate reader.
Queries are exactly reached real occurrences at detected molecular centers. Every supported
candidate read belongs to this domain, and each query has the actual source/target frame data
needed by the execution theorem. No frame, reader match, or descriptor is supplied by the user.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueries

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedReachableConfigurations (Reached reached_child reached_root)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant descendant_reached)
open LocalizedMarkedUncappedOperations (generated_of_reachedFrom)
open LocalizedMarkedRetainedStateReader (rawOccurrenceKey)
open LocalizedGenericMarkedRecalculation (WellFormedBonds structuralDepth)
open LocalizedChemicalRingJointPreparedSourceStateReadback
open LocalizedChemicalRingJointPreparedStructuralProfile
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData occurrenceData_exists)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- A molecular real detected query, independent of auxiliary labels and compilation. -/
def QueryEligible (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) (node : Node) : Prop :=
  Reached mol node ∧ node.provenance = .realAtom ∧
    ∃ center : input.detectedMultiCenterMolecule.Center, node.atom = center.1.val

abbrev SourceQuery (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) :=
  {node : Node // QueryEligible input mol node}

/-- The current atom is already determined by the complete molecular occurrence key. -/
theorem rawOccurrenceKey_head {n : Nat} (unit : OccurrenceUnit (Fin n)) :
    (rawOccurrenceKey unit).history.head? = some unit.atom.val := by
  simp only [rawOccurrenceKey, List.head?_map, List.head?_reverse, List.getLast?_cons,
    Option.map_some, OccurrenceUnit.atom]

/-- Every reader-supported query is a reached real detected query. In particular restricting
the candidate profile to this molecular domain loses none of the actual reads. -/
theorem supported_query_eligible (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    {depth : Nat} {source query : Node} (reached : Reached mol source)
    (unit : DetectedOccurrence input.moleculeGraph)
    (supported : SupportedNode mol depth source unit.1 query) :
    QueryEligible input mol query := by
  obtain ⟨child, edge, rest⟩ := supported.2.1
  have queryReached := descendant_reached (reached_child mol source child reached edge) rest
  obtain ⟨root, _valid, path⟩ := queryReached
  have head := (generated_of_reachedFrom mol root query path).history_head
  have identity : query.atom = unit.1.atom.val := by
    apply Option.some.inj
    rw [← head]
    change (canonicalOccurrenceKey query).history.head? = _
    rw [supported.1]
    exact rawOccurrenceKey_head unit.1
  let center : input.detectedMultiCenterMolecule.Center := ⟨unit.1.atom, by
    exact (input.moleculeGraph.mem_tetrahedralCenterSet _).mpr
      ((input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mpr unit.2)⟩
  exact ⟨⟨root, _valid, path⟩, supported.provenance, center, identity⟩

/-- Every actual detected center's final occurrence is in the source query domain. -/
theorem final_query_eligible (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (center : input.detectedMultiCenterMolecule.Center) :
    QueryEligible input mol (canonicalCenterRoot center.1.val) :=
  ⟨reached_root mol center.1.val
      (LocalizedMarkedCertifiedTerminalRefusal.raw_atom_bound mol input agreement center.1),
    rfl, center, rfl⟩

/-- Source query eligibility derives all execution-frame correspondence data. The domain
contains molecular predicates, not an assumed frame, key comparison or chosen descriptor. -/
theorem sourceQuery_data_exists (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded) (query : SourceQuery input mol) :
    ∃ center : input.detectedMultiCenterMolecule.Center,
      query.1.atom = center.1.val ∧ Nonempty (OccurrenceData input mol center query.1) := by
  obtain ⟨center, current⟩ := query.2.2.2
  exact ⟨center, current, occurrenceData_exists input mol agreement admissible supported single
    center query.1 query.2.1 query.2.2.1 current⟩

/-- The true candidate-query dependency is well-founded even with unrestricted context data. -/
theorem sourceQueryDependency_wellFounded {Context : Type*}
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) (wellFormed : WellFormedBonds mol) :
    WellFounded (fun (query source : Context × SourceQuery input mol) =>
      StrictDescendant mol source.2.1 query.2.1) :=
  Subrelation.wf
    (fun {_query source : Context × SourceQuery input mol} path =>
      structuralDepth_lt mol wellFormed source.2.2.1 path)
    (measure (fun query : Context × SourceQuery input mol => structuralDepth mol query.2.1)).wf

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueries

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueries.rawOccurrenceKey_head
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueries.supported_query_eligible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueries.final_query_eligible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueries.sourceQuery_data_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueries.sourceQueryDependency_wellFounded

assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueries.QueryEligible
  [TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile.stableProfile,
   TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.generated,
   TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedDescriptor?,
   TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames]
