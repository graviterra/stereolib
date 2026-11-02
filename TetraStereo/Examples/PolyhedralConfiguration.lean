import TetraStereo.OneCenter.PolyhedralConfiguration

set_option autoImplicit false

namespace TetraStereo.Examples.PolyhedralConfiguration

open OneCenter

private def p (number : ℕ) (primes : ℕ := 0) : PolyhedralPriorityNumber :=
  { number := number, primes := primes }

theorem t_shape_example_TS_3_2 :
    tShapeConfigurationIndex (p 2) = [p 2] := by
  decide

theorem square_planar_example_SP_4_3 :
    squarePlanarConfigurationIndex (p 3) = [p 3] := by
  decide

theorem four_coordinate_square_pyramid_example_SPY_4_2 :
    squarePyramid4ConfigurationIndex (p 2) = [p 2] := by
  decide

theorem see_saw_example_SS_4_12 :
    seeSawConfigurationIndex (p 2) (p 1) = [p 1, p 2] := by
  decide

theorem trigonal_bipyramid_example_TBPY_5_35 :
    trigonalBipyramidConfigurationIndex (p 5) (p 3) = [p 3, p 5] := by
  decide

theorem square_pyramid_example_SPY_5_14 :
    squarePyramidConfigurationIndex (p 1) (p 4) = [p 1, p 4] := by
  decide

theorem octahedron_example_OC_6_25 :
    octahedronConfigurationIndex (p 2) (p 5) = [p 2, p 5] := by
  decide

theorem unprimed_precedes_primed_when_priority_numbers_tie :
    comparePolyhedralPriority (p 1) (p 1 1) = Ordering.gt := by
  decide

theorem clockwise_is_C_and_counterclockwise_is_A :
    (PolyhedralChiralitySymbol.ofRotation .clockwise,
      PolyhedralChiralitySymbol.ofRotation .counterclockwise) = (.C, .A) := by
  decide

theorem rendered_octahedral_descriptor :
    ({ geometry := .octahedron
       configurationIndex := [[p 2, p 5]]
       absolute? := some (.ac .C) } : PolyhedralDescriptor).label = "OC-6-25-C" := by
  decide

theorem pentagonal_bipyramid_IR_9_3_3_6_example :
    bipyramidalConfigurationIndex (p 3) (p 4) [p 1, p 2, p 3, p 4, p 2] =
      [[p 3, p 4], [p 1, p 2, p 3, p 4, p 2]] := by
  decide

theorem pentagonal_bipyramid_cycle_is_start_and_direction_independent :
    canonicalPolyhedralCycle [p 3, p 4, p 2, p 1, p 2] =
        [p 1, p 2, p 3, p 4, p 2] ∧
      canonicalPolyhedralCycle [p 2, p 4, p 3, p 2, p 1] =
        [p 1, p 2, p 3, p 4, p 2] := by
  decide

theorem rendered_pentagonal_bipyramidal_descriptor :
    ({ geometry := .pentagonalBipyramid
       configurationIndex := [[p 3, p 4], [p 1, p 2, p 3, p 4, p 2]] } :
      PolyhedralDescriptor).label = "PBPY-7-34-12342" := by
  decide

theorem red_book_table_IR_9_2_symbols_are_exhaustive :
    PolyhedralGeometry.all.map PolyhedralGeometry.symbol =
      [ "L-2", "A-2", "TP-3", "TPY-3", "TS-3", "T-4", "SP-4", "SPY-4",
        "SS-4", "TBPY-5", "SPY-5", "OC-6", "TPR-6", "PBPY-7", "OCF-7",
        "TPRS-7", "CU-8", "SAPR-8", "DD-8", "HBPY-8", "OCT-8", "TPRT-8",
        "TPRS-8", "TPRS-9", "HBPY-9" ] := by
  decide

end TetraStereo.Examples.PolyhedralConfiguration
