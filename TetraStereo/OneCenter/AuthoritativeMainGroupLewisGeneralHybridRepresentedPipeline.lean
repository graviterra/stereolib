import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralHybridEvidence
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteRepresentedPipelineCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Hybrid electronic-state evidence in the complete represented source pipeline

The generalized-Lewis hybrid certifier previously ended at the ordinary-double-bond family.
This module makes that certified, inventory-aware analyzer the ordinary-double-bond branch of the
same five-family result that already carries tetrahedral, odd/even open-cumulene, and fully cyclic
P-31 outcomes.  The total optional entry point refuses exactly at the checked atom-state boundary;
when it succeeds, every branch has exact membership and the combined list is duplicate-free.
-/

/-- Five-family represented output whose ordinary-double-bond branch is driven by the certified
hybrid electronic-state inventory rather than the older connectivity-only endpoint defaults. -/
noncomputable def analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes :=
  (source.analyzeAromaticCanonicalConcreteRule3Through6 carrierFuel ruleFuel).map
      source.embedTetrahedralInConcreteStereochemicalResult ++
    ((source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
        supplied ready).analyzeOrdinaryDoubleBonds carrierFuel
          (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)).map
      source.embedOrdinaryDoubleBondInConcreteStereochemicalResult ++
    (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial carrierFuel ruleFuel).map
      source.embedOddOpenCumuleneInConcreteStereochemicalResult ++
    (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial carrierFuel ruleFuel).map
      source.embedEvenOpenCumuleneInConcreteStereochemicalResult ++
    source.aromaticCanonicalCyclicCumuleneComponents.map
      AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.fullyCyclicCumuleneParent

/-- Total checked entry point.  Electronic-state certification is performed before any represented
descriptor branch is exposed. -/
noncomputable def analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventory?
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel ruleFuel : Nat) :
    Option (List source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes) := by
  classical
  exact if ready : source.MainGroupLewisGeneralHybridCertificationReady supplied then
    some (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
      supplied ready carrierFuel ruleFuel)
  else none

/-- Exact executable membership for the certified five-family result. -/
def AromaticCanonicalHybridElectronicInventoryRepresentedExecutableMember
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes) : Prop :=
  match result with
  | .prior (.prior (.prior (.tetrahedral assignment))) =>
      source.AromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment
        carrierFuel ruleFuel assignment.center assignment.descriptor
  | .prior (.prior (.prior (.ordinaryDoubleBond assignment))) =>
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel
          (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
            supplied ready).inventorySource
          bond
          (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.left)
          (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.right)
          assignment
  | .prior (.prior (.oddOpenCumulene assignment)) =>
      ∃ unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits,
        source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
          carrierFuel ruleFuel unit = some assignment
  | .prior (.evenOpenCumulene assignment) =>
      ∃ unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits,
        source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
          carrierFuel ruleFuel unit = some assignment
  | .fullyCyclicCumuleneParent component =>
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component

/-- Independent meaning of every result in the certified five-family output. -/
def DeclarativeAromaticCanonicalHybridElectronicInventoryRepresentedMember
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes) : Prop :=
  match result with
  | .prior (.prior (.prior (.tetrahedral assignment))) =>
      source.AromaticCanonicalScheduledRule3Through6GeometricDescriptorJudgment
        (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel ruleFuel) ruleFuel assignment.center assignment.descriptor
  | .prior (.prior (.prior (.ordinaryDoubleBond assignment))) =>
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel
          (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
            supplied ready).inventorySource
          bond
          (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.left)
          (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.right)
          assignment
  | .prior (.prior (.oddOpenCumulene assignment)) =>
      source.DeclarativeAromaticCanonicalOddOpenCumuleneSpatialAssignment
        carrierFuel ruleFuel assignment
  | .prior (.evenOpenCumulene assignment) =>
      source.DeclarativeAromaticCanonicalEvenOpenCumuleneAxialAssignment
        carrierFuel ruleFuel assignment
  | .fullyCyclicCumuleneParent component =>
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component ∧
        BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
        ¬BlueBookP93.Cyclic.OpenTerminalCumuleneSchemaApplies .fullyCyclicCumulene

/-- Exact family membership of the certified five-family list. -/
theorem mem_analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_iff
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes) :
    result ∈
        source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
          supplied ready carrierFuel ruleFuel ↔
      source.AromaticCanonicalHybridElectronicInventoryRepresentedExecutableMember
        supplied ready carrierFuel ruleFuel result := by
  rcases result with prior | component
  · rcases prior with prior | even
    · rcases prior with prior | odd
      · rcases prior with tetrahedral | ordinaryDoubleBond
        · simp [analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady,
            AromaticCanonicalHybridElectronicInventoryRepresentedExecutableMember,
            embedTetrahedralInConcreteStereochemicalResult,
            embedOrdinaryDoubleBondInConcreteStereochemicalResult,
            embedOddOpenCumuleneInConcreteStereochemicalResult,
            embedEvenOpenCumuleneInConcreteStereochemicalResult,
            source.mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_executableJudgment]
        · simp [analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady,
            AromaticCanonicalHybridElectronicInventoryRepresentedExecutableMember,
            embedTetrahedralInConcreteStereochemicalResult,
            embedOrdinaryDoubleBondInConcreteStereochemicalResult,
            embedOddOpenCumuleneInConcreteStereochemicalResult,
            embedEvenOpenCumuleneInConcreteStereochemicalResult,
            source.mem_certifiedMainGroupLewisGeneralHybridAnalyzeOrdinaryDoubleBonds_iff_canonical
              supplied ready carrierFuel
                (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)
                ordinaryDoubleBond]
      · simp [analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady,
          AromaticCanonicalHybridElectronicInventoryRepresentedExecutableMember,
          embedTetrahedralInConcreteStereochemicalResult,
          embedOrdinaryDoubleBondInConcreteStereochemicalResult,
          embedOddOpenCumuleneInConcreteStereochemicalResult,
          embedEvenOpenCumuleneInConcreteStereochemicalResult,
          source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff]
    · simp [analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady,
        AromaticCanonicalHybridElectronicInventoryRepresentedExecutableMember,
        embedTetrahedralInConcreteStereochemicalResult,
        embedOrdinaryDoubleBondInConcreteStereochemicalResult,
        embedOddOpenCumuleneInConcreteStereochemicalResult,
        embedEvenOpenCumuleneInConcreteStereochemicalResult,
        source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff]
  · simp [analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady,
      AromaticCanonicalHybridElectronicInventoryRepresentedExecutableMember,
      embedTetrahedralInConcreteStereochemicalResult,
      embedOrdinaryDoubleBondInConcreteStereochemicalResult,
      embedOddOpenCumuleneInConcreteStereochemicalResult,
      embedEvenOpenCumuleneInConcreteStereochemicalResult,
      source.mem_aromaticCanonicalCyclicCumuleneComponents_iff]

/-- Every emitted descriptor has the corresponding independent complete-rule and exact-geometry
judgment; the non-descriptor cyclic branch has its P-31 applicability and P-93 exclusion. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_member_sound
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes)
    (present : result ∈
      source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
        supplied ready carrierFuel ruleFuel) :
    source.DeclarativeAromaticCanonicalHybridElectronicInventoryRepresentedMember
      supplied ready carrierFuel ruleFuel result := by
  have executable :=
    (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_iff
      supplied ready carrierFuel ruleFuel result).mp present
  rcases result with prior | component
  · rcases prior with prior | even
    · rcases prior with prior | odd
      · rcases prior with tetrahedral | ordinaryDoubleBond
        · exact source.aromaticCanonicalConcreteRule3Through6Descriptor?_geometry_sound
            carrierFuel ruleFuel tetrahedral.center tetrahedral.descriptor
            ((source.aromaticCanonicalConcreteRule3Through6Descriptor?_eq_some_iff_executableJudgment
              carrierFuel ruleFuel tetrahedral.center tetrahedral.descriptor).mpr executable)
        · exact executable
      · exact source.analyzeAromaticCanonicalOddOpenCumuleneSpatial_member_sound
          carrierFuel ruleFuel odd
          ((source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
            carrierFuel ruleFuel odd).mpr executable)
    · exact source.analyzeAromaticCanonicalEvenOpenCumuleneAxial_member_sound
        carrierFuel ruleFuel even
        ((source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
          carrierFuel ruleFuel even).mpr executable)
  · exact ⟨executable, executable.authority_topology.1, executable.authority_topology.2⟩

/-- Constructor disjointness and family-local physical-unit uniqueness make the complete
inventory-aware output duplicate-free. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_nodup
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
      supplied ready carrierFuel ruleFuel).Nodup := by
  have tetrahedralNodup :=
    (source.analyzeAromaticCanonicalConcreteRule3Through6_nodup
      carrierFuel ruleFuel).map (by
        intro left right equal
        cases equal
        rfl : Function.Injective source.embedTetrahedralInConcreteStereochemicalResult)
  have ordinaryDoubleBondNodup :=
    ((source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
      supplied ready).analyzeOrdinaryDoubleBonds_nodup carrierFuel
        (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)).map (by
          intro left right equal
          cases equal
          rfl : Function.Injective source.embedOrdinaryDoubleBondInConcreteStereochemicalResult)
  have oddNodup :=
    (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial_nodup
      carrierFuel ruleFuel).map (by
        intro left right equal
        cases equal
        rfl : Function.Injective source.embedOddOpenCumuleneInConcreteStereochemicalResult)
  have evenNodup :=
    (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial_nodup
      carrierFuel ruleFuel).map (by
        intro left right equal
        cases equal
        rfl : Function.Injective source.embedEvenOpenCumuleneInConcreteStereochemicalResult)
  have cyclicNodup :=
    source.aromaticCanonicalCyclicCumuleneComponents_nodup.map (by
      intro left right equal
      cases equal
      rfl : Function.Injective
        AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.fullyCyclicCumuleneParent)
  rw [analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady]
  simpa only [List.append_assoc] using tetrahedralNodup.append
    (ordinaryDoubleBondNodup.append
      (oddNodup.append (evenNodup.append cyclicNodup (by
        simp [List.disjoint_left, embedEvenOpenCumuleneInConcreteStereochemicalResult])) (by
          simp [List.disjoint_left, embedOddOpenCumuleneInConcreteStereochemicalResult,
            embedEvenOpenCumuleneInConcreteStereochemicalResult])) (by
        simp [List.disjoint_left, embedOrdinaryDoubleBondInConcreteStereochemicalResult,
          embedOddOpenCumuleneInConcreteStereochemicalResult,
          embedEvenOpenCumuleneInConcreteStereochemicalResult])) (by
      simp [List.disjoint_left, embedTetrahedralInConcreteStereochemicalResult,
        embedOrdinaryDoubleBondInConcreteStereochemicalResult,
        embedOddOpenCumuleneInConcreteStereochemicalResult,
        embedEvenOpenCumuleneInConcreteStereochemicalResult])

/-- Tetrahedral membership is unchanged by replacing only the ordinary-double-bond branch. -/
theorem mem_embedTetrahedralInHybridElectronicInventoryRepresented_iff
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment) :
    source.embedTetrahedralInConcreteStereochemicalResult assignment ∈
        source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
          supplied ready carrierFuel ruleFuel ↔
      assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6
        carrierFuel ruleFuel := by
  rw [source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_iff]
  exact (source.mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_executableJudgment
    carrierFuel ruleFuel assignment).symm

/-- The ordinary-double-bond members of the combined result are exactly those of the certified
inventory-aware family analyzer. -/
theorem mem_embedOrdinaryDoubleBondInHybridElectronicInventoryRepresented_iff
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    source.embedOrdinaryDoubleBondInConcreteStereochemicalResult assignment ∈
        source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
          supplied ready carrierFuel ruleFuel ↔
      assignment ∈
        (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
          supplied ready).analyzeOrdinaryDoubleBonds carrierFuel
            (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel) := by
  rw [source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_iff]
  exact (source.mem_certifiedMainGroupLewisGeneralHybridAnalyzeOrdinaryDoubleBonds_iff_canonical
    supplied ready carrierFuel
      (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel) assignment).symm

/-- Odd-open-cumulene membership is preserved literally. -/
theorem mem_embedOddOpenCumuleneInHybridElectronicInventoryRepresented_iff
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) :
    source.embedOddOpenCumuleneInConcreteStereochemicalResult assignment ∈
        source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
          supplied ready carrierFuel ruleFuel ↔
      assignment ∈ source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
        carrierFuel ruleFuel := by
  rw [source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_iff]
  exact (source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
    carrierFuel ruleFuel assignment).symm

/-- Even-open-cumulene membership is preserved literally. -/
theorem mem_embedEvenOpenCumuleneInHybridElectronicInventoryRepresented_iff
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) :
    source.embedEvenOpenCumuleneInConcreteStereochemicalResult assignment ∈
        source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
          supplied ready carrierFuel ruleFuel ↔
      assignment ∈ source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
        carrierFuel ruleFuel := by
  rw [source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_iff]
  exact (source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
    carrierFuel ruleFuel assignment).symm

/-- Fully cyclic P-31 component membership is preserved literally. -/
theorem mem_fullyCyclicCumuleneParentInHybridElectronicInventoryRepresented_iff
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) :
    .fullyCyclicCumuleneParent component ∈
        source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
          supplied ready carrierFuel ruleFuel ↔
      component ∈ source.aromaticCanonicalCyclicCumuleneComponents := by
  rw [source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_iff]
  exact (source.mem_aromaticCanonicalCyclicCumuleneComponents_iff component).symm

/-- Literal tetrahedral counts are unchanged in the inventory-aware combined result. -/
theorem count_embedTetrahedralInHybridElectronicInventoryRepresented
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
      supplied ready carrierFuel ruleFuel).count
        (source.embedTetrahedralInConcreteStereochemicalResult assignment) =
      (source.analyzeAromaticCanonicalConcreteRule3Through6
        carrierFuel ruleFuel).count assignment := by
  rw [(source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_nodup
    supplied ready carrierFuel ruleFuel).count,
    (source.analyzeAromaticCanonicalConcreteRule3Through6_nodup
      carrierFuel ruleFuel).count]
  simp [source.mem_embedTetrahedralInHybridElectronicInventoryRepresented_iff]

/-- Literal inventory-aware ordinary-double-bond counts are preserved by the combined result. -/
theorem count_embedOrdinaryDoubleBondInHybridElectronicInventoryRepresented
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
      supplied ready carrierFuel ruleFuel).count
        (source.embedOrdinaryDoubleBondInConcreteStereochemicalResult assignment) =
      ((source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
        supplied ready).analyzeOrdinaryDoubleBonds carrierFuel
          (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)).count
        assignment := by
  rw [(source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_nodup
    supplied ready carrierFuel ruleFuel).count,
    ((source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
      supplied ready).analyzeOrdinaryDoubleBonds_nodup carrierFuel
        (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)).count]
  simp [source.mem_embedOrdinaryDoubleBondInHybridElectronicInventoryRepresented_iff]

/-- Literal odd-open-cumulene counts are unchanged. -/
theorem count_embedOddOpenCumuleneInHybridElectronicInventoryRepresented
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
      supplied ready carrierFuel ruleFuel).count
        (source.embedOddOpenCumuleneInConcreteStereochemicalResult assignment) =
      (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
        carrierFuel ruleFuel).count assignment := by
  rw [(source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_nodup
    supplied ready carrierFuel ruleFuel).count,
    (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial_nodup
      carrierFuel ruleFuel).count]
  simp [source.mem_embedOddOpenCumuleneInHybridElectronicInventoryRepresented_iff]

/-- Literal even-open-cumulene counts are unchanged. -/
theorem count_embedEvenOpenCumuleneInHybridElectronicInventoryRepresented
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
      supplied ready carrierFuel ruleFuel).count
        (source.embedEvenOpenCumuleneInConcreteStereochemicalResult assignment) =
      (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
        carrierFuel ruleFuel).count assignment := by
  rw [(source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_nodup
    supplied ready carrierFuel ruleFuel).count,
    (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial_nodup
      carrierFuel ruleFuel).count]
  simp [source.mem_embedEvenOpenCumuleneInHybridElectronicInventoryRepresented_iff]

/-- Literal fully cyclic component counts are unchanged. -/
theorem count_fullyCyclicCumuleneParentInHybridElectronicInventoryRepresented
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
      supplied ready carrierFuel ruleFuel).count (.fullyCyclicCumuleneParent component) =
      source.aromaticCanonicalCyclicCumuleneComponents.count component := by
  rw [(source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_nodup
    supplied ready carrierFuel ruleFuel).count,
    source.aromaticCanonicalCyclicCumuleneComponents_nodup.count]
  simp [source.mem_fullyCyclicCumuleneParentInHybridElectronicInventoryRepresented_iff]

/-- Independent readiness for all descriptor-bearing families after checked hybrid atom-state
certification.  The ordinary-double-bond premise is explicitly the inventory-aware judgment. -/
structure AromaticCanonicalHybridElectronicInventoryRepresentedPipelineReadyAtBound
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel : Nat) : Prop where
  electronic : source.MainGroupLewisGeneralHybridCertificationReady supplied
  tetrahedral : ∀ center,
    source.AromaticCanonicalConcreteRule3Through6ChemicallyReadyAtBound carrierFuel center
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

/-- Exact-once and emitted-result correctness of the complete represented output with checked
hybrid atom-state evidence. -/
structure AromaticCanonicalHybridElectronicInventoryRepresentedPipelineCompleteAtBound
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel : Nat)
    (ready : source.AromaticCanonicalHybridElectronicInventoryRepresentedPipelineReadyAtBound
      supplied carrierFuel) : Prop where
  emittedSound : ∀ result,
    result ∈
        source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
          supplied ready.electronic carrierFuel (2 * (carrierFuel + 1)) →
      source.DeclarativeAromaticCanonicalHybridElectronicInventoryRepresentedMember
        supplied ready.electronic carrierFuel (2 * (carrierFuel + 1)) result
  outputNodup :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
      supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).Nodup
  tetrahedralExact : ∀ center,
    ∃ assignment,
      assignment.center = center ∧
        (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
          supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).count
            (source.embedTetrahedralInConcreteStereochemicalResult assignment) = 1
  ordinaryDoubleBondExact :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      ∃ assignment,
        assignment.bond = bond ∧
          (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
            supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).count
              (source.embedOrdinaryDoubleBondInConcreteStereochemicalResult assignment) = 1
  oddOpenCumuleneExact :
    ∀ unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits,
      ∃ assignment,
        assignment.unit = unit ∧
          (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
            supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).count
              (source.embedOddOpenCumuleneInConcreteStereochemicalResult assignment) = 1
  evenOpenCumuleneExact :
    ∀ unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits,
      ∃ assignment,
        assignment.unit = unit ∧
          (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
            supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).count
              (source.embedEvenOpenCumuleneInConcreteStereochemicalResult assignment) = 1
  fullyCyclicCumuleneExact :
    ∀ component ∈ source.aromaticCanonicalCyclicCumuleneComponents,
      (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
        supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))).count
          (.fullyCyclicCumuleneParent component) = 1

/-- Every independently ready represented unit is emitted exactly once by the inventory-aware
five-family analyzer, and every emitted descriptor has its independent judgment. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventory_complete_at_bound
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel : Nat)
    (ready : source.AromaticCanonicalHybridElectronicInventoryRepresentedPipelineReadyAtBound
      supplied carrierFuel) :
    source.AromaticCanonicalHybridElectronicInventoryRepresentedPipelineCompleteAtBound
      supplied carrierFuel ready := by
  constructor
  · intro result present
    exact source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_member_sound
      supplied ready.electronic carrierFuel (2 * (carrierFuel + 1)) result present
  · exact source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_nodup
      supplied ready.electronic carrierFuel (2 * (carrierFuel + 1))
  · intro center
    obtain ⟨assignment, centerIdentity, familyCount⟩ :=
      source.exists_count_analyzeAromaticCanonicalConcreteRule3Through6_eq_one_at_bound
        carrierFuel center (ready.tetrahedral center)
    exact ⟨assignment, centerIdentity, by
      rw [source.count_embedTetrahedralInHybridElectronicInventoryRepresented]
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
    rw [source.count_embedOrdinaryDoubleBondInHybridElectronicInventoryRepresented]
    simpa [CertifiedAuthoritativeChemicalInputWithAtomElectronicStates.analyzeOrdinaryDoubleBonds]
      using familyCount
  · intro unit owner
    obtain ⟨terminals, evidence⟩ := ready.oddOpenCumulene unit owner
    obtain ⟨assignment, unitIdentity, familyCount⟩ :=
      source.exists_count_analyzeAromaticCanonicalOddOpenCumuleneSpatial_eq_one_of_dependencies
        carrierFuel (2 * (carrierFuel + 1)) unit terminals evidence
    exact ⟨assignment, unitIdentity, by
      rw [source.count_embedOddOpenCumuleneInHybridElectronicInventoryRepresented]
      exact familyCount⟩
  · intro unit owner
    obtain ⟨terminals, evidence⟩ := ready.evenOpenCumulene unit owner
    obtain ⟨assignment, unitIdentity, familyCount⟩ :=
      source.exists_count_analyzeAromaticCanonicalEvenOpenCumuleneAxial_eq_one_of_dependencies
        carrierFuel (2 * (carrierFuel + 1)) unit terminals evidence
    exact ⟨assignment, unitIdentity, by
      rw [source.count_embedEvenOpenCumuleneInHybridElectronicInventoryRepresented]
      exact familyCount⟩
  · intro component owner
    rw [source.count_fullyCyclicCumuleneParentInHybridElectronicInventoryRepresented,
      source.aromaticCanonicalCyclicCumuleneComponents_nodup.count]
    simp [owner]

/-- Every successful total analysis returns a duplicate-free five-family result. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventory?_some_nodup
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel ruleFuel : Nat)
    (results : List source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes)
    (computed : source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventory?
      supplied carrierFuel ruleFuel = some results) : results.Nodup := by
  classical
  unfold analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventory? at computed
  split at computed
  next ready =>
    simp only [Option.some.injEq] at computed
    subst results
    exact source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady_nodup
      supplied ready carrierFuel ruleFuel
  next notReady => contradiction

/-- The total entry point refuses exactly when its generalized hybrid electronic-state evidence
fails the exhaustive source certification boundary. -/
@[simp] theorem analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventory?_eq_none_iff_refusal
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (carrierFuel ruleFuel : Nat) :
    source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventory?
        supplied carrierFuel ruleFuel = none ↔
      source.MainGroupLewisGeneralHybridCertificationRefusal supplied := by
  classical
  rw [← source.not_mainGroupLewisGeneralHybridCertificationReady_iff_refusal]
  simp [analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventory?]

/-- On certified input, the total entry point returns the literal certified five-family list. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventory?_eq_some_of_ready
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (ready : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat) :
    source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventory?
        supplied carrierFuel ruleFuel =
      some
        (source.analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventoryOfReady
          supplied ready carrierFuel ruleFuel) := by
  classical
  simp [analyzeAromaticCanonicalConcreteStereochemistryWithHybridElectronicInventory?, ready]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
