import TetraStereo.OneCenter.RSSymmetryChiralityClass
import TetraStereo.Examples.Symmetry

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter

/-!
  A small quotient-level sanity check for `R/S` on the symmetry-aware affine quotient.

  For the toy CHBrClF graph example, `StereogenicByCIP` lets us define `rsAffine`, and the
  canonical right/left realizations land in distinct affine stereochemical classes distinguished
  by their `R/S` value.
-/

namespace CHBrClF

abbrev rightClass : oneCenter.AffineStereoQ :=
  Quotient.mk (oneCenter.stereoRealizationSetoid) bromochlorofluoromethaneRightRealization

abbrev leftClass : oneCenter.AffineStereoQ :=
  Quotient.mk (oneCenter.stereoRealizationSetoid) bromochlorofluoromethaneLeftRealization

example : oneCenter.rsAffine stereogenicByCIP rightClass =
    oneCenter.rs bromochlorofluoromethaneRightRealization := by
  simp [rightClass]

example : oneCenter.rsAffine stereogenicByCIP leftClass =
    oneCenter.rs bromochlorofluoromethaneLeftRealization := by
  simp [leftClass]

example :
    oneCenter.rsAffine stereogenicByCIP leftClass =
      RS.swap (oneCenter.rsAffine stereogenicByCIP rightClass) := by
  simp [leftClass, rightClass, rs_left_eq_swap_rs_right]

theorem rightClass_ne_leftClass : rightClass ≠ leftClass := by
  intro hEq
  have h := congrArg (oneCenter.rsAffine stereogenicByCIP) hEq
  -- Reduce to the previously established inequality on concrete realizations.
  have :
      oneCenter.rs bromochlorofluoromethaneRightRealization =
        oneCenter.rs bromochlorofluoromethaneLeftRealization := by
    simpa [rightClass, leftClass] using h
  exact rs_right_ne_rs_left this

end CHBrClF

end Examples
end TetraStereo
