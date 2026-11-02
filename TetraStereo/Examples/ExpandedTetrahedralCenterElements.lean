import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.Examples.ExpandedTetrahedralCenterElements

open OneCenter

private def center (element : Element) : AtomSpec :=
  { element := element, explicitHydrogens? := some 0,
    tetrahedral? := some .clockwise }

private def ligand (element : Element) : AtomSpec :=
  { element := element, explicitHydrogens? := some 0 }

private def fourCoordinate (element : Element) : RawMolecule where
  atoms := [center element, ligand .F, ligand .Cl, ligand .Br, ligand .I]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 0, target := 4, kind := .single } ]

private def threeCoordinateOxygen : RawMolecule where
  atoms := [{ (center .O) with charge := 1 }, ligand .F, ligand .Cl, ligand .Br]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single } ]

theorem boron_is_a_supported_four_coordinate_tetrahedral_center :
    (fourCoordinate .B).tetrahedralOutcome 12 0 = StereoOutcome.tetrahedral .R := by
  decide

theorem germanium_is_a_supported_four_coordinate_tetrahedral_center :
    (fourCoordinate .Ge).tetrahedralOutcome 12 0 = StereoOutcome.tetrahedral .R := by
  decide

theorem three_coordinate_oxygen_uses_a_lowest_priority_lone_pair :
    threeCoordinateOxygen.ligandsWithLonePair 0 = [4, 1, 2, 3] ∧
      threeCoordinateOxygen.tetrahedralOutcome 12 0 = StereoOutcome.tetrahedral .R := by
  decide

end TetraStereo.Examples.ExpandedTetrahedralCenterElements
