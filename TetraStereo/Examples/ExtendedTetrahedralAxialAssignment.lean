import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.Examples.ExtendedTetrahedralAxialAssignment

open OneCenter

/-! The constitution from the OpenSMILES specification's extended-tetrahedral allene example,
evaluated through native endpoint CIP rankings and the collapsed-tetrahedron parity carrier. -/

private def atomWithoutHydrogens (element : Element) : AtomSpec :=
  { element := element, explicitHydrogens? := some 0 }

private def allene : RawMolecule where
  atoms :=
    [ atomWithoutHydrogens .N,
      atomWithoutHydrogens .C,
      atomWithoutHydrogens .Br,
      atomWithoutHydrogens .C,
      atomWithoutHydrogens .C,
      atomWithoutHydrogens .O,
      atomWithoutHydrogens .C ]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 1, target := 2, kind := .single },
      { source := 1, target := 3, kind := .double },
      { source := 3, target := 4, kind := .double },
      { source := 4, target := 5, kind := .single },
      { source := 4, target := 6, kind := .single } ]
  neighborOrder := [[1], [0, 2, 3], [1], [1, 4], [3, 5, 6], [4], [4]]

private def carrier (parity : TetrahedralInputParity) : ExtendedTetrahedralParityCarrier :=
  { left := 1, leftPartner := 3, parityCarrier := 3, rightPartner := 3, right := 4
    path := [1, 3, 4], parity := parity }

theorem clockwise_carrier_assigns_Sa :
    extendedTetrahedralAxialOutcome (normalizeRawMolecule allene) allene [] 16
      (carrier .clockwise) = StereoOutcome.axial AxialDescriptor.Sa := by
  decide

theorem anticlockwise_carrier_assigns_Ra :
    extendedTetrahedralAxialOutcome (normalizeRawMolecule allene) allene [] 16
      (carrier .anticlockwise) = StereoOutcome.axial AxialDescriptor.Ra := by
  decide

theorem one_parity_inversion_swaps_axial_descriptor :
    ( extendedTetrahedralAxialOutcome (normalizeRawMolecule allene) allene [] 16
        (carrier .clockwise),
      extendedTetrahedralAxialOutcome (normalizeRawMolecule allene) allene [] 16
        (carrier .anticlockwise)) =
      (StereoOutcome.axial AxialDescriptor.Sa,
        StereoOutcome.axial AxialDescriptor.Ra) := by
  decide

end TetraStereo.Examples.ExtendedTetrahedralAxialAssignment
