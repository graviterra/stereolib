import TetraStereo.OneCenter.CIPSymmetryChiralityClass
import TetraStereo.Examples.Symmetry

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter

/-!
  Symmetry-aware affine quotient sanity checks:

  - Methane (`CH₄`) becomes a singleton quotient (odd symmetry collapses handedness).
  - Bromochlorofluoromethane (`CHBrClF`) has exactly two classes (CIP-stereogenic ⇒ chiral-by-symmetry).
-/

namespace Methane

example : Subsingleton (oneCenter.AffineStereoQ) :=
  oneCenter.subsingleton_affineStereoQ_of_achiralBySymmetry achiralBySymmetry

end Methane

namespace CHBrClF

example : ∃ a b : oneCenter.AffineStereoQ, a ≠ b ∧ ∀ q : oneCenter.AffineStereoQ, q = a ∨ q = b :=
  oneCenter.affineStereoQ_exactly_two_classes_of_stereogenicByCIP stereogenicByCIP

end CHBrClF

end Examples
end TetraStereo
