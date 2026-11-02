import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralHybridRichRepresentedPipeline
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeCanonicalReadinessCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6RSPseudoConservativeExtension
import TetraStereo.OneCenter.AuthoritativeSemanticOpenCumuleneExactReadiness
import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondElectronicInventoryExactReadiness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Unconditional canonical completeness of the rich five-family source pipeline

The earlier aggregate completeness theorem assumed that every connectivity candidate was ready.
That is a useful sufficient theorem, but it is stronger than the chemically exact statement:
connectivity candidates which are not stereogenic must be refused rather than assigned.

This module removes that global assumption.  For each physical candidate independently, literal
count-one occurrence in the final `R/S/r/s`-preserving five-family result is equivalent to the
corresponding independent canonical chemical/spatial readiness relation.  Thus the same theorem
classifies both successful emission and conservative exclusion.
-/

/-- Retaining tetrahedral descriptor case has exactly the old canonical chemical success domain. -/
theorem aromaticCanonicalConcreteRule3Through6RSPseudoReady_iff_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalConcreteRule3Through6RSPseudoReady
        carrierFuel ruleFuel center ↔
      source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
        carrierFuel ruleFuel center := by
  exact
    (source.aromaticCanonicalScheduledRule3Through6Ready_iff_rspseudoReady
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel) ruleFuel center).symm.trans
      (source.aromaticCanonicalConcreteRule3Through6Ready_iff_canonicalChemicalReadiness
        carrierFuel ruleFuel center)

/-- A tetrahedral candidate occurs exactly once in the final rich result iff its independent
canonical Rules 1a--6 chemical readiness holds. -/
theorem exists_count_tetrahedral_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff_canonicalReadiness
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (electronic : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (∃ assignment,
        assignment.center = center ∧
          (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            supplied electronic carrierFuel ruleFuel).count
              (.tetrahedral assignment) = 1) ↔
      source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
        carrierFuel ruleFuel center := by
  constructor
  · rintro ⟨assignment, centerIdentity, combinedCount⟩
    have familyCount :
        (source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
          carrierFuel ruleFuel).count assignment = 1 := by
      rw [← source.count_tetrahedral_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady
        supplied electronic carrierFuel ruleFuel assignment]
      exact combinedCount
    have richReady :=
      (source.exists_count_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_eq_one_iff_ready
        carrierFuel ruleFuel center).mp ⟨assignment, centerIdentity, familyCount⟩
    exact
      (source.aromaticCanonicalConcreteRule3Through6RSPseudoReady_iff_canonicalChemicalReadiness
        carrierFuel ruleFuel center).mp richReady
  · intro canonicalReady
    have richReady :=
      (source.aromaticCanonicalConcreteRule3Through6RSPseudoReady_iff_canonicalChemicalReadiness
        carrierFuel ruleFuel center).mpr canonicalReady
    obtain ⟨assignment, centerIdentity, familyCount⟩ :=
      (source.exists_count_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_eq_one_iff_ready
        carrierFuel ruleFuel center).mpr richReady
    refine ⟨assignment, centerIdentity, ?_⟩
    rw [source.count_tetrahedral_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
    exact familyCount

/-- An ordinary-double-bond candidate occurs exactly once in the final rich result iff the
independent inventory-aware endpoint and geometry judgment is ready. -/
theorem exists_count_ordinaryDoubleBond_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff_canonicalReadiness
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (electronic : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    (∃ assignment,
        assignment.bond = bond ∧
          (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            supplied electronic carrierFuel ruleFuel).count
              (.ordinaryDoubleBond assignment) = 1) ↔
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
        carrierFuel
        (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
          supplied electronic).inventorySource
        bond
        (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.left)
        (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.right) := by
  let certified :=
    source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady supplied electronic
  let viewAt := source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel
  constructor
  · rintro ⟨assignment, bondIdentity, combinedCount⟩
    have certifiedCount :
        (certified.analyzeOrdinaryDoubleBonds carrierFuel viewAt).count assignment = 1 := by
      rw [← source.count_ordinaryDoubleBond_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady
        supplied electronic carrierFuel ruleFuel assignment]
      exact combinedCount
    apply
      (source.exists_count_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_eq_one_iff_readiness
        carrierFuel viewAt certified.inventorySource bond).mp
    refine ⟨assignment, bondIdentity, ?_⟩
    simpa [CertifiedAuthoritativeChemicalInputWithAtomElectronicStates.analyzeOrdinaryDoubleBonds]
      using certifiedCount
  · intro canonicalReady
    obtain ⟨assignment, bondIdentity, familyCount⟩ :=
      (source.exists_count_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_eq_one_iff_readiness
        carrierFuel viewAt certified.inventorySource bond).mpr canonicalReady
    refine ⟨assignment, bondIdentity, ?_⟩
    rw [source.count_ordinaryDoubleBond_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
    simpa [certified, viewAt,
      CertifiedAuthoritativeChemicalInputWithAtomElectronicStates.analyzeOrdinaryDoubleBonds]
      using familyCount

/-- An odd open cumulene occurs exactly once in the final rich result iff its independent
canonical planar judgment is ready. -/
theorem exists_count_oddOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff_canonicalReadiness
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (electronic : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) :
    (∃ assignment,
        assignment.unit = unit ∧
          (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            supplied electronic carrierFuel ruleFuel).count
              (.oddOpenCumulene assignment) = 1) ↔
      source.AromaticCanonicalOddOpenCumuleneCanonicalReadiness
        carrierFuel ruleFuel unit := by
  constructor
  · rintro ⟨assignment, unitIdentity, combinedCount⟩
    apply
      (source.exists_count_analyzeAromaticCanonicalOddOpenCumuleneSpatial_eq_one_iff_canonicalReadiness
        carrierFuel ruleFuel unit).mp
    refine ⟨assignment, unitIdentity, ?_⟩
    rw [← source.count_oddOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady
      supplied electronic carrierFuel ruleFuel assignment]
    exact combinedCount
  · intro canonicalReady
    obtain ⟨assignment, unitIdentity, familyCount⟩ :=
      (source.exists_count_analyzeAromaticCanonicalOddOpenCumuleneSpatial_eq_one_iff_canonicalReadiness
        carrierFuel ruleFuel unit).mpr canonicalReady
    refine ⟨assignment, unitIdentity, ?_⟩
    rw [source.count_oddOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
    exact familyCount

/-- An even open cumulene occurs exactly once in the final rich result iff its independent
canonical axial judgment is ready. -/
theorem exists_count_evenOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff_canonicalReadiness
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (electronic : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) :
    (∃ assignment,
        assignment.unit = unit ∧
          (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            supplied electronic carrierFuel ruleFuel).count
              (.evenOpenCumulene assignment) = 1) ↔
      source.AromaticCanonicalEvenOpenCumuleneCanonicalReadiness
        carrierFuel ruleFuel unit := by
  constructor
  · rintro ⟨assignment, unitIdentity, combinedCount⟩
    apply
      (source.exists_count_analyzeAromaticCanonicalEvenOpenCumuleneAxial_eq_one_iff_canonicalReadiness
        carrierFuel ruleFuel unit).mp
    refine ⟨assignment, unitIdentity, ?_⟩
    rw [← source.count_evenOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady
      supplied electronic carrierFuel ruleFuel assignment]
    exact combinedCount
  · intro canonicalReady
    obtain ⟨assignment, unitIdentity, familyCount⟩ :=
      (source.exists_count_analyzeAromaticCanonicalEvenOpenCumuleneAxial_eq_one_iff_canonicalReadiness
        carrierFuel ruleFuel unit).mpr canonicalReady
    refine ⟨assignment, unitIdentity, ?_⟩
    rw [source.count_evenOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
    exact familyCount

/-- A fully cyclic cumulene parent occurs exactly once in the final rich result iff it belongs to
the independently characterized canonical component list. -/
theorem count_fullyCyclicCumuleneParent_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady_eq_one_iff
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (electronic : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) :
    (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
      supplied electronic carrierFuel ruleFuel).count
        (.fullyCyclicCumuleneParent component) = 1 ↔
      component ∈ source.aromaticCanonicalCyclicCumuleneComponents := by
  rw [(source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_nodup
    supplied electronic carrierFuel ruleFuel).count]
  simp [analyzeAromaticCanonicalHybridRichRepresentedOfReady]

/-- Unconditional exact positive/negative classification for every currently represented rich
source family.  Only generalized-Lewis certification is global; stereogenicity/readiness is
classified independently per candidate and is not assumed. -/
structure AromaticCanonicalHybridRichRepresentedCanonicalCompleteness
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (electronic : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat) : Prop where
  emittedSound : ∀ result,
    result ∈ source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
        supplied electronic carrierFuel ruleFuel →
      source.DeclarativeAromaticCanonicalHybridRichRepresentedMember
        supplied electronic carrierFuel ruleFuel result
  outputNodup :
    (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
      supplied electronic carrierFuel ruleFuel).Nodup
  tetrahedralExact : ∀ center,
    (∃ assignment,
        assignment.center = center ∧
          (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            supplied electronic carrierFuel ruleFuel).count
              (.tetrahedral assignment) = 1) ↔
      source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
        carrierFuel ruleFuel center
  ordinaryDoubleBondExact : ∀ bond,
    (∃ assignment,
        assignment.bond = bond ∧
          (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            supplied electronic carrierFuel ruleFuel).count
              (.ordinaryDoubleBond assignment) = 1) ↔
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
        carrierFuel
        (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
          supplied electronic).inventorySource
        bond
        (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.left)
        (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.right)
  oddOpenCumuleneExact : ∀ unit,
    (∃ assignment,
        assignment.unit = unit ∧
          (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            supplied electronic carrierFuel ruleFuel).count
              (.oddOpenCumulene assignment) = 1) ↔
      source.AromaticCanonicalOddOpenCumuleneCanonicalReadiness
        carrierFuel ruleFuel unit
  evenOpenCumuleneExact : ∀ unit,
    (∃ assignment,
        assignment.unit = unit ∧
          (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            supplied electronic carrierFuel ruleFuel).count
              (.evenOpenCumulene assignment) = 1) ↔
      source.AromaticCanonicalEvenOpenCumuleneCanonicalReadiness
        carrierFuel ruleFuel unit
  fullyCyclicCumuleneExact : ∀ component,
    (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
      supplied electronic carrierFuel ruleFuel).count
        (.fullyCyclicCumuleneParent component) = 1 ↔
      component ∈ source.aromaticCanonicalCyclicCumuleneComponents

/-- The final rich represented source analyzer satisfies unconditional per-candidate canonical
completeness at arbitrary carrier and rule fuel. -/
theorem analyzeAromaticCanonicalHybridRichRepresented_canonical_complete
    (source : AuthoritativeChemicalInput)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (electronic : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalHybridRichRepresentedCanonicalCompleteness
      supplied electronic carrierFuel ruleFuel := by
  constructor
  · exact source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_member_sound
      supplied electronic carrierFuel ruleFuel
  · exact source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_nodup
      supplied electronic carrierFuel ruleFuel
  · exact source.exists_count_tetrahedral_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff_canonicalReadiness
      supplied electronic carrierFuel ruleFuel
  · exact source.exists_count_ordinaryDoubleBond_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff_canonicalReadiness
      supplied electronic carrierFuel ruleFuel
  · exact source.exists_count_oddOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff_canonicalReadiness
      supplied electronic carrierFuel ruleFuel
  · exact source.exists_count_evenOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff_canonicalReadiness
      supplied electronic carrierFuel ruleFuel
  · exact source.count_fullyCyclicCumuleneParent_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady_eq_one_iff
      supplied electronic carrierFuel ruleFuel

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
