import TetraStereo.OneCenter.Rule6HandednessCore
import TetraStereo.OneCenter.Basic
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingPairingParity

/-- The matching containing edge {a,b} is named by the partner of native ligand zero.
For an edge away from zero, that partner is the one remaining nonzero ligand. -/
def matching (a b : Fin 4) : Nat :=
  if a = 0 then b.val else if b = 0 then a.val else 6 - a.val - b.val

/-- The three opposite-edge pairs, ordered by the rank of the partner of the senior ligand. -/
def matchingOrder (p : Equiv.Perm (Fin 4)) : List Nat :=
  [matching (p 0) (p 1), matching (p 0) (p 2), matching (p 0) (p 3)]

theorem matchingOrder_perm (p : Equiv.Perm (Fin 4)) :
    (matchingOrder p).Perm [1, 2, 3] := by
  fin_cases p <;> decide

def matchingEven (p : Equiv.Perm (Fin 4)) : Bool :=
  RawMolecule.permutationIsEven (matchingOrder p)

theorem matchingEven_eq_sign (p : Equiv.Perm (Fin 4)) :
    matchingEven p = (Equiv.Perm.sign p == 1) := by
  fin_cases p <;> decide

theorem handedness_eq_matching (p : Equiv.Perm (Fin 4)) :
    permHandedness p = if matchingEven p then 1 else -1 := by
  rw [matchingEven_eq_sign]
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simp [permHandedness, h]

end TetraStereo.OneCenter.LocalizedChemicalRingPairingParity

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPairingParity.matchingOrder_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPairingParity.matchingEven_eq_sign
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPairingParity.handedness_eq_matching
