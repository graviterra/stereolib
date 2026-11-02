import TetraStereo.OneCenter.ChemistrySemantics

set_option autoImplicit false

namespace TetraStereo.Examples.CertifiedChemistryNormalization

open OneCenter

private def atom (element : Element) (charge : Int := 0) : AtomSpec :=
  { element := element, charge := charge, explicitHydrogens? := some 0 }

private def tetraBoron (charge : Int) : RawMolecule where
  atoms := [atom .B charge, atom .F, atom .Cl, atom .Br, atom .I]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 0, target := 4, kind := .single } ]

theorem ordinary_input_reaches_certified_normalization :
    (parseAndNormalizeOpenSMILESCertified "C").isOk = true := by
  decide

theorem neutral_four_coordinate_boron_fails_valence_admission :
    normalizeRawMoleculeCertified? (tetraBoron 0) = none := by
  decide

theorem anionic_four_coordinate_boron_is_admitted :
    (normalizeRawMoleculeCertified? (tetraBoron (-1))).isSome = true := by
  decide

private def duplicateEdge : RawMolecule where
  atoms := [atom .C, atom .C]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 1, target := 0, kind := .single } ]

theorem duplicate_edge_fails_structural_admission :
    normalizeRawMoleculeCertified? duplicateEdge = none := by
  decide

private def nonexistentNuclide : RawMolecule where
  atoms :=
    [{ element := .C, isotope? := some 999, explicitHydrogens? := some 0 }]
  bonds := []

/-- Structural and valence validity cannot certify an isotope label that has no frozen physical
nuclide datum. -/
theorem nonexistent_nuclide_fails_rule2_mass_admission :
    normalizeRawMoleculeCertified? nonexistentNuclide = none := by
  decide

end TetraStereo.Examples.CertifiedChemistryNormalization
