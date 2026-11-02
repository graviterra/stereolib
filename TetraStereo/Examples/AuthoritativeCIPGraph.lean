import TetraStereo.OneCenter.AuthoritativeCIPGraph

set_option autoImplicit false

namespace TetraStereo.Examples.AuthoritativeCIPGraph

open OneCenter

private def element (atomicNumber : ℕ) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement :=
  { atomicNumber := atomicNumber, positive := positive, atMost118 := bounded }

private def oneAtomMolecule (atomicNumber : ℕ) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : SemanticMolecule :=
  { atoms := [{ element := element atomicNumber positive bounded }]
    interactions := [] }

/-- Every presently named element reaches the proof-facing graph without passing through the
parser's small `Element` enumeration. -/
theorem every_current_element_reaches_the_constitutional_graph
    (atomicNumber : ℕ) (positive : 0 < atomicNumber) (bounded : atomicNumber ≤ 118) :
    let molecule := oneAtomMolecule atomicNumber positive bounded
    molecule.LocalizedCIPGraphReady ∧
      molecule.toLocalizedMoleculeGraph.atomZ
        ⟨0, by simp [molecule, oneAtomMolecule, SemanticMolecule.atomCount]⟩ =
        atomicNumber := by
  have membership : atomicNumber ∈ CIPRule2MassData.currentAtomicNumbers := by
    rw [CIPRule2MassData.currentAtomicNumbers_exact]
    simp
    omega
  obtain ⟨mass, observed⟩ :=
    CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value
      atomicNumber membership
  simp [oneAtomMolecule, SemanticMolecule.LocalizedCIPGraphReady,
    SemanticMolecule.StructurallyWellFormed,
    SemanticMolecule.ExplicitLocalizedClosedShellAtoms,
    SemanticMolecule.AllRule2MassesKnown, SemanticAtom.Rule2MassKnown,
    SemanticAtom.rule2MassPico?, observed,
    SemanticMolecule.LocalizedCovalentPairsOnly,
    SemanticMolecule.LocalizedCovalentRecordsUnique,
    SemanticMolecule.localizedCovalentKeys, SemanticMolecule.localizedCovalentRecords,
    SemanticAtom.ExplicitLocalizedClosedShell,
    SemanticMolecule.toLocalizedMoleculeGraph, SemanticMolecule.atomCount, element]

private def uranium := element 92 (by decide) (by decide)
private def oxygen := element 8 (by decide) (by decide)
private def carbon := element 6 (by decide) (by decide)
private def hydrogen := element 1 (by decide) (by decide)

private def uraniumDioxideFragment : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms :=
          [{ element := uranium, isotopeMassNumber? := some 238, formalCharge := 2 },
           { element := oxygen, isotopeMassNumber? := some 18, formalCharge := -2 }]
        interactions := [{ participants := [0, 1], kind := .covalent 2 }] } }

private def certifiedUraniumDioxideFragment : CertifiedAuthoritativeChemicalInput :=
  (uraniumDioxideFragment.certify?).get (by decide)

private def localizedUraniumDioxideFragment : CertifiedLocalizedCIPInput :=
  (certifiedUraniumDioxideFragment.certifyLocalizedCIP?).get (by decide)

theorem all_element_bridge_preserves_atomic_number_isotope_charge_and_order :
    localizedUraniumDioxideFragment.moleculeGraph.atomZ ⟨0, by decide⟩ = 92 ∧
      localizedUraniumDioxideFragment.moleculeGraph.atomMass ⟨0, by decide⟩ =
        238050786936000 ∧
      localizedUraniumDioxideFragment.moleculeGraph.formalCharge ⟨0, by decide⟩ = 2 ∧
      localizedUraniumDioxideFragment.moleculeGraph.atomZ ⟨1, by decide⟩ = 8 ∧
      localizedUraniumDioxideFragment.moleculeGraph.atomMass ⟨1, by decide⟩ =
        17999159612140 ∧
      localizedUraniumDioxideFragment.moleculeGraph.formalCharge ⟨1, by decide⟩ = -2 ∧
      localizedUraniumDioxideFragment.moleculeGraph.bond
        ⟨0, by decide⟩ ⟨1, by decide⟩ = 2 := by
  decide

private def mixedNaturalAndExplicitIsotopeInput : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms :=
          [{ element := carbon }, { element := carbon, isotopeMassNumber? := some 13 }]
        interactions := [] } }

private def certifiedMixedNaturalAndExplicitIsotopeInput : CertifiedAuthoritativeChemicalInput :=
  (mixedNaturalAndExplicitIsotopeInput.certify?).get (by decide)

private def localizedMixedNaturalAndExplicitIsotopeInput : CertifiedLocalizedCIPInput :=
  (certifiedMixedNaturalAndExplicitIsotopeInput.certifyLocalizedCIP?).get (by decide)

/-- The former natural/explicit refusal boundary is gone: ordinary carbon and carbon-13 coexist,
and their exact source values give the chemically required Rule-2 order. -/
theorem mixed_natural_and_explicit_isotope_uses_exact_mass_data :
    localizedMixedNaturalAndExplicitIsotopeInput.moleculeGraph.atomMass ⟨0, by decide⟩ =
        12011000000000 ∧
      localizedMixedNaturalAndExplicitIsotopeInput.moleculeGraph.atomMass ⟨1, by decide⟩ =
        13003354835340 ∧
      localizedMixedNaturalAndExplicitIsotopeInput.moleculeGraph.atomMass ⟨0, by decide⟩ <
        localizedMixedNaturalAndExplicitIsotopeInput.moleculeGraph.atomMass ⟨1, by decide⟩ := by
  decide

private def hydrogenConventionInput : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms :=
          [{ element := hydrogen },
           { element := hydrogen, isotopeMassNumber? := some 1 },
           { element := hydrogen, isotopeMassNumber? := some 2 }]
        interactions := [] } }

private def certifiedHydrogenConventionInput : CertifiedAuthoritativeChemicalInput :=
  (hydrogenConventionInput.certify?).get (by decide)

private def localizedHydrogenConventionInput : CertifiedLocalizedCIPInput :=
  (certifiedHydrogenConventionInput.certifyLocalizedCIP?).get (by decide)

/-- The universal bridge shares P-92.3's `H = ¹H < ²H` convention with the parser path. -/
theorem ordinary_hydrogen_ties_protium_and_deuterium_outranks_both :
    localizedHydrogenConventionInput.moleculeGraph.atomMass ⟨0, by decide⟩ =
        1007825031898 ∧
      localizedHydrogenConventionInput.moleculeGraph.atomMass ⟨1, by decide⟩ =
        1007825031898 ∧
      localizedHydrogenConventionInput.moleculeGraph.atomMass ⟨2, by decide⟩ =
        2014101777844 := by
  decide

private def unknownNuclideInput : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [{ element := carbon, isotopeMassNumber? := some 999 }]
        interactions := [] } }

private def certifiedUnknownNuclideInput : CertifiedAuthoritativeChemicalInput :=
  (unknownNuclideInput.certify?).get (by decide)

/-- Structurally legal syntax cannot invent a physical isotope datum: an absent nuclide fails the
source-backed graph-admission gate. -/
theorem unknown_nuclide_is_rejected_before_cip_comparison :
    certifiedUnknownNuclideInput.certifyLocalizedCIP? = none := by
  decide

private def radicalInput : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [{ element := oxygen, unpairedElectrons := 1 }]
        interactions := [] } }

private def certifiedRadicalInput : CertifiedAuthoritativeChemicalInput :=
  (radicalInput.certify?).get (by decide)

theorem radical_information_cannot_be_silently_projected :
    certifiedRadicalInput.certifyLocalizedCIP? = none := by
  decide

private def aromaticInput : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [{ element := oxygen, aromaticInput := true }]
        interactions := [] } }

private def certifiedAromaticInput : CertifiedAuthoritativeChemicalInput :=
  (aromaticInput.certify?).get (by decide)

theorem aromatic_input_cannot_be_silently_localized :
    certifiedAromaticInput.certifyLocalizedCIP? = none := by
  decide

private def multicenterInput : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [{ element := uranium }, { element := oxygen }, { element := oxygen }]
        interactions := [{ participants := [0, 1, 2], kind := .multicenter 2 }] } }

private def certifiedMulticenterInput : CertifiedAuthoritativeChemicalInput :=
  (multicenterInput.certify?).get (by decide)

theorem multicenter_interaction_requires_normative_normalization :
    certifiedMulticenterInput.certifyLocalizedCIP? = none := by
  decide

private def duplicatePairInput : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [{ element := uranium }, { element := oxygen }]
        interactions :=
          [{ participants := [0, 1], kind := .covalent 1 },
           { participants := [1, 0], kind := .covalent 2 }] } }

private def certifiedDuplicatePairInput : CertifiedAuthoritativeChemicalInput :=
  (duplicatePairInput.certify?).get (by decide)

theorem contradictory_pair_records_are_rejected_orientation_independently :
    certifiedDuplicatePairInput.certifyLocalizedCIP? = none := by
  decide

end TetraStereo.Examples.AuthoritativeCIPGraph
