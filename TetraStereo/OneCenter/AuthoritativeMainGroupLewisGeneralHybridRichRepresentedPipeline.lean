import TetraStereo.OneCenter.AuthoritativeSemanticMancudeRichTetrahedralWholeMoleculeAnalysis
import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralHybridRepresentedPipeline

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Complete represented source pipeline with case-preserving tetrahedral descriptors

This is the five-family inventory-aware pipeline with its tetrahedral branch upgraded from bare
`R/S` to `R/S/r/s`.  The other four branches retain their existing exact electronic-inventory,
open-cumulene, and fully-cyclic authority judgments.
-/

/-- Public represented source result whose tetrahedral constructor retains uppercase/lowercase
descriptor case. -/
inductive AromaticCanonicalHybridRichRepresentedResult
    (source : AuthoritativeChemicalInput) where
  | tetrahedral (assignment : source.AromaticCanonicalRule3Through6RSPseudoAssignment)
  | ordinaryDoubleBond
      (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
  | oddOpenCumulene
      (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment)
  | evenOpenCumulene
      (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment)
  | fullyCyclicCumuleneParent
      (component : source.AromaticCanonicalCyclicCumuleneComponent)
  deriving DecidableEq

/-- Complete five-family result after checked generalized-Lewis electronic certification. -/
noncomputable def analyzeAromaticCanonicalHybridRichRepresentedOfReady
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalHybridRichRepresentedResult :=
  (source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
      carrierFuel ruleFuel).map .tetrahedral ++
    ((source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
        supplied ready).analyzeOrdinaryDoubleBonds carrierFuel
          (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)).map
      .ordinaryDoubleBond ++
    (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial carrierFuel ruleFuel).map
      .oddOpenCumulene ++
    (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial carrierFuel ruleFuel).map
      .evenOpenCumulene ++
    source.aromaticCanonicalCyclicCumuleneComponents.map .fullyCyclicCumuleneParent

/-- Exact executable family meaning of one case-preserving represented result. -/
def AromaticCanonicalHybridRichRepresentedExecutableMember
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalHybridRichRepresentedResult) : Prop :=
  match result with
  | .tetrahedral assignment =>
      source.AromaticCanonicalConcreteRule3Through6RSPseudoExecutableJudgment
        carrierFuel ruleFuel assignment.center assignment.descriptor
  | .ordinaryDoubleBond assignment =>
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel
          (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
            supplied ready).inventorySource
          bond
          (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.left)
          (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.right)
          assignment
  | .oddOpenCumulene assignment =>
      ∃ unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits,
        source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
          carrierFuel ruleFuel unit = some assignment
  | .evenOpenCumulene assignment =>
      ∃ unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits,
        source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
          carrierFuel ruleFuel unit = some assignment
  | .fullyCyclicCumuleneParent component =>
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component

/-- Independent declarative meaning of every case-preserving represented result. -/
def DeclarativeAromaticCanonicalHybridRichRepresentedMember
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalHybridRichRepresentedResult) : Prop :=
  match result with
  | .tetrahedral assignment =>
      source.AromaticCanonicalConcreteRule3Through6RSPseudoExecutableJudgment
        carrierFuel ruleFuel assignment.center assignment.descriptor
  | .ordinaryDoubleBond assignment =>
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel
          (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
            supplied ready).inventorySource
          bond
          (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.left)
          (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.right)
          assignment
  | .oddOpenCumulene assignment =>
      source.DeclarativeAromaticCanonicalOddOpenCumuleneSpatialAssignment
        carrierFuel ruleFuel assignment
  | .evenOpenCumulene assignment =>
      source.DeclarativeAromaticCanonicalEvenOpenCumuleneAxialAssignment
        carrierFuel ruleFuel assignment
  | .fullyCyclicCumuleneParent component =>
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component ∧
        BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
        ¬BlueBookP93.Cyclic.OpenTerminalCumuleneSchemaApplies .fullyCyclicCumulene

/-- Exact membership of the case-preserving five-family result. -/
theorem mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalHybridRichRepresentedResult) :
    result ∈ source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
        supplied ready carrierFuel ruleFuel ↔
      source.AromaticCanonicalHybridRichRepresentedExecutableMember
        supplied ready carrierFuel ruleFuel result := by
  cases result with
  | tetrahedral assignment =>
      simp [analyzeAromaticCanonicalHybridRichRepresentedOfReady,
        AromaticCanonicalHybridRichRepresentedExecutableMember,
        source.mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff]
  | ordinaryDoubleBond assignment =>
      simp [analyzeAromaticCanonicalHybridRichRepresentedOfReady,
        AromaticCanonicalHybridRichRepresentedExecutableMember,
        source.mem_certifiedMainGroupLewisGeneralHybridAnalyzeOrdinaryDoubleBonds_iff_canonical
          supplied ready carrierFuel
            (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)
            assignment]
  | oddOpenCumulene assignment =>
      simp [analyzeAromaticCanonicalHybridRichRepresentedOfReady,
        AromaticCanonicalHybridRichRepresentedExecutableMember,
        source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff]
  | evenOpenCumulene assignment =>
      simp [analyzeAromaticCanonicalHybridRichRepresentedOfReady,
        AromaticCanonicalHybridRichRepresentedExecutableMember,
        source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff]
  | fullyCyclicCumuleneParent component =>
      simp [analyzeAromaticCanonicalHybridRichRepresentedOfReady,
        AromaticCanonicalHybridRichRepresentedExecutableMember,
        source.mem_aromaticCanonicalCyclicCumuleneComponents_iff]

/-- Every emitted case-preserving descriptor has its independent family judgment. -/
theorem analyzeAromaticCanonicalHybridRichRepresentedOfReady_member_sound
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalHybridRichRepresentedResult)
    (present : result ∈ source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
      supplied ready carrierFuel ruleFuel) :
    source.DeclarativeAromaticCanonicalHybridRichRepresentedMember
      supplied ready carrierFuel ruleFuel result := by
  have executable :=
    (source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
      supplied ready carrierFuel ruleFuel result).mp present
  cases result with
  | tetrahedral assignment => exact executable
  | ordinaryDoubleBond assignment => exact executable
  | oddOpenCumulene assignment =>
      exact source.analyzeAromaticCanonicalOddOpenCumuleneSpatial_member_sound
        carrierFuel ruleFuel assignment
        ((source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
          carrierFuel ruleFuel assignment).mpr executable)
  | evenOpenCumulene assignment =>
      exact source.analyzeAromaticCanonicalEvenOpenCumuleneAxial_member_sound
        carrierFuel ruleFuel assignment
        ((source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
          carrierFuel ruleFuel assignment).mpr executable)
  | fullyCyclicCumuleneParent component =>
      exact ⟨executable, executable.authority_topology.1,
        executable.authority_topology.2⟩

/-- Constructor disjointness and family-local physical identity make the rich result duplicate
free for arbitrary fuel. -/
theorem analyzeAromaticCanonicalHybridRichRepresentedOfReady_nodup
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat) :
    (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
      supplied ready carrierFuel ruleFuel).Nodup := by
  have tetrahedralNodup :=
    (source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_nodup
      carrierFuel ruleFuel).map (by
        intro left right equal
        cases equal
        rfl : Function.Injective
          (AromaticCanonicalHybridRichRepresentedResult.tetrahedral (source := source)))
  have ordinaryNodup :=
    ((source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
      supplied ready).analyzeOrdinaryDoubleBonds_nodup carrierFuel
        (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)).map (by
          intro left right equal
          cases equal
          rfl : Function.Injective
            (AromaticCanonicalHybridRichRepresentedResult.ordinaryDoubleBond
              (source := source)))
  have oddNodup :=
    (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial_nodup
      carrierFuel ruleFuel).map (by
        intro left right equal
        cases equal
        rfl : Function.Injective
          (AromaticCanonicalHybridRichRepresentedResult.oddOpenCumulene (source := source)))
  have evenNodup :=
    (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial_nodup
      carrierFuel ruleFuel).map (by
        intro left right equal
        cases equal
        rfl : Function.Injective
          (AromaticCanonicalHybridRichRepresentedResult.evenOpenCumulene (source := source)))
  have cyclicNodup :=
    source.aromaticCanonicalCyclicCumuleneComponents_nodup.map (by
      intro left right equal
      cases equal
      rfl : Function.Injective
        (AromaticCanonicalHybridRichRepresentedResult.fullyCyclicCumuleneParent
          (source := source)))
  rw [analyzeAromaticCanonicalHybridRichRepresentedOfReady]
  simpa only [List.append_assoc] using tetrahedralNodup.append
    (ordinaryNodup.append
      (oddNodup.append (evenNodup.append cyclicNodup (by
        simp [List.disjoint_left])) (by simp [List.disjoint_left]))
      (by simp [List.disjoint_left])) (by simp [List.disjoint_left])

theorem count_tetrahedral_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalRule3Through6RSPseudoAssignment) :
    (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
      supplied ready carrierFuel ruleFuel).count (.tetrahedral assignment) =
      (source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
        carrierFuel ruleFuel).count assignment := by
  rw [(source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_nodup
    supplied ready carrierFuel ruleFuel).count,
    (source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_nodup
      carrierFuel ruleFuel).count]
  simp [analyzeAromaticCanonicalHybridRichRepresentedOfReady]

theorem count_ordinaryDoubleBond_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
      supplied ready carrierFuel ruleFuel).count (.ordinaryDoubleBond assignment) =
      ((source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
        supplied ready).analyzeOrdinaryDoubleBonds carrierFuel
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel)).count assignment := by
  rw [(source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_nodup
    supplied ready carrierFuel ruleFuel).count,
    ((source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
      supplied ready).analyzeOrdinaryDoubleBonds_nodup carrierFuel
        (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)).count]
  simp [analyzeAromaticCanonicalHybridRichRepresentedOfReady]

theorem count_oddOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) :
    (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
      supplied ready carrierFuel ruleFuel).count (.oddOpenCumulene assignment) =
      (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
        carrierFuel ruleFuel).count assignment := by
  rw [(source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_nodup
    supplied ready carrierFuel ruleFuel).count,
    (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial_nodup
      carrierFuel ruleFuel).count]
  simp [analyzeAromaticCanonicalHybridRichRepresentedOfReady]

theorem count_evenOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) :
    (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
      supplied ready carrierFuel ruleFuel).count (.evenOpenCumulene assignment) =
      (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
        carrierFuel ruleFuel).count assignment := by
  rw [(source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_nodup
    supplied ready carrierFuel ruleFuel).count,
    (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial_nodup
      carrierFuel ruleFuel).count]
  simp [analyzeAromaticCanonicalHybridRichRepresentedOfReady]

/-- Independent readiness of every descriptor-bearing branch in the rich five-family result. -/
structure AromaticCanonicalHybridRichRepresentedPipelineReadyAtBound
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel : Nat) : Prop where
  electronic : source.MainGroupLewisGeneralHybridCertificationReady supplied
  tetrahedral : ∀ center,
    source.AromaticCanonicalConcreteRule3Through6RSPseudoReady
      carrierFuel (2 * (carrierFuel + 1)) center
  ordinaryDoubleBond :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
        carrierFuel
        (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
          supplied electronic).inventorySource
        bond
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel (2 * (carrierFuel + 1)) bond.left)
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel (2 * (carrierFuel + 1)) bond.right)
  oddOpenCumulene :
    ∀ unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits,
      ∃ terminals,
        source.AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence
          carrierFuel (2 * (carrierFuel + 1)) unit terminals
  evenOpenCumulene :
    ∀ unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits,
      ∃ terminals,
        source.AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence
          carrierFuel (2 * (carrierFuel + 1)) unit terminals

/-- Soundness, duplicate freedom, and literal exact-once coverage for the rich represented result. -/
structure AromaticCanonicalHybridRichRepresentedPipelineCompleteAtBound
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel : Nat)
    (ready : source.AromaticCanonicalHybridRichRepresentedPipelineReadyAtBound
      supplied carrierFuel) : Prop where
  emittedSound : ∀ result,
    result ∈ source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
        supplied ready.electronic carrierFuel (2 * (carrierFuel + 1)) →
      source.DeclarativeAromaticCanonicalHybridRichRepresentedMember
        supplied ready.electronic carrierFuel (2 * (carrierFuel + 1)) result
  outputNodup :
    (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
      supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).Nodup
  tetrahedralExact : ∀ center,
    ∃ assignment,
      assignment.center = center ∧
        (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
          supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).count
            (.tetrahedral assignment) = 1
  ordinaryDoubleBondExact :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      ∃ assignment,
        assignment.bond = bond ∧
          (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).count
              (.ordinaryDoubleBond assignment) = 1
  oddOpenCumuleneExact :
    ∀ unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits,
      ∃ assignment,
        assignment.unit = unit ∧
          (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).count
              (.oddOpenCumulene assignment) = 1
  evenOpenCumuleneExact :
    ∀ unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits,
      ∃ assignment,
        assignment.unit = unit ∧
          (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).count
              (.evenOpenCumulene assignment) = 1
  fullyCyclicCumuleneExact :
    ∀ component ∈ source.aromaticCanonicalCyclicCumuleneComponents,
      (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
        supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).count
          (.fullyCyclicCumuleneParent component) = 1

/-- The complete five-family source theorem now retains `R/S/r/s` at every tetrahedral center. -/
theorem analyzeAromaticCanonicalHybridRichRepresented_complete_at_bound
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel : Nat)
    (ready : source.AromaticCanonicalHybridRichRepresentedPipelineReadyAtBound
      supplied carrierFuel) :
    source.AromaticCanonicalHybridRichRepresentedPipelineCompleteAtBound
      supplied carrierFuel ready := by
  constructor
  · intro result present
    exact source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_member_sound
      supplied ready.electronic carrierFuel (2 * (carrierFuel + 1)) result present
  · exact source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_nodup
      supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))
  · intro center
    obtain ⟨assignment, centerIdentity, familyCount⟩ :=
      (source.exists_count_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_eq_one_iff_ready
        carrierFuel (2 * (carrierFuel + 1)) center).mpr (ready.tetrahedral center)
    exact ⟨assignment, centerIdentity, by
      rw [source.count_tetrahedral_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
      exact familyCount⟩
  · intro bond owner
    obtain ⟨assignment, bondIdentity, familyCount⟩ :=
      (source.exists_count_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_eq_one_iff_readiness
        carrierFuel
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel (2 * (carrierFuel + 1)))
        (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
          supplied ready.electronic).inventorySource bond).mpr
            (ready.ordinaryDoubleBond bond owner)
    refine ⟨assignment, bondIdentity, ?_⟩
    rw [source.count_ordinaryDoubleBond_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
    simpa [CertifiedAuthoritativeChemicalInputWithAtomElectronicStates.analyzeOrdinaryDoubleBonds]
      using familyCount
  · intro unit owner
    obtain ⟨terminals, evidence⟩ := ready.oddOpenCumulene unit owner
    obtain ⟨assignment, unitIdentity, familyCount⟩ :=
      source.exists_count_analyzeAromaticCanonicalOddOpenCumuleneSpatial_eq_one_of_dependencies
        carrierFuel (2 * (carrierFuel + 1)) unit terminals evidence
    exact ⟨assignment, unitIdentity, by
      rw [source.count_oddOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
      exact familyCount⟩
  · intro unit owner
    obtain ⟨terminals, evidence⟩ := ready.evenOpenCumulene unit owner
    obtain ⟨assignment, unitIdentity, familyCount⟩ :=
      source.exists_count_analyzeAromaticCanonicalEvenOpenCumuleneAxial_eq_one_of_dependencies
        carrierFuel (2 * (carrierFuel + 1)) unit terminals evidence
    exact ⟨assignment, unitIdentity, by
      rw [source.count_evenOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
      exact familyCount⟩
  · intro component owner
    rw [(source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_nodup
      supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).count]
    simp [analyzeAromaticCanonicalHybridRichRepresentedOfReady, owner]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
