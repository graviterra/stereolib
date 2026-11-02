import TetraStereo.OneCenter.CIPSymmetry
import TetraStereo.OneCenter.SymmetryChiralityClass

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A CIP-stereogenic one-center molecule has exactly two symmetry-aware affine stereochemical
classes. -/
theorem affineStereoQ_exactly_two_classes_of_stereogenicByCIP (m : OneCenterMolecule V)
    (h : m.StereogenicByCIP) :
    ∃ a b : m.AffineStereoQ, a ≠ b ∧ ∀ q : m.AffineStereoQ, q = a ∨ q = b := by
  exact
    m.affineStereoQ_exactly_two_classes_of_chiralBySymmetry (m.chiralBySymmetry_of_stereogenicByCIP h)

end OneCenterMolecule

end
end OneCenter
end TetraStereo
