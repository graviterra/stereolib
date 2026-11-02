import TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
import TetraStereo.OneCenter.OpenSMILESSyntaxContinuation

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter

def prefixState (parity : TetrahedralInputParity) : ParseState :=
  { atoms := prefixAtoms parity
    bonds := prefixBonds
    current? := some 4
    order := [[1, 2, 4], [0], [0, 3], [2], [0, 5], [4]]
    introductionPredecessors := [none, some 0, some 0, some 2, some 0, some 4] }

/-- Intermediate actual atom-allocation trace. The claimed independent final graph remains
`raw parity n`; no successful public parse is hidden in its definition. -/
def tailState : Nat → ParseState → ParseState
  | 0, state => state.addAtom (bracket .C 3)
  | n + 1, state => tailState n (state.addAtom (bracket .C 2))

def finalState (parity : TetrahedralInputParity) (n : Nat) : ParseState :=
  tailState n (prefixState parity)

theorem prefix_chars_length (parity : TetrahedralInputParity) :
    (prefixChars parity).length = if parity = .clockwise then 31 else 30 := by
  cases parity <;> rfl

theorem tail_chars_length (n : Nat) : (tailChars n).length = 5 * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [tailChars, List.length_append, ih]
      change 5 + 5 * (n + 1) = 5 * (n + 1 + 1)
      omega

theorem tail_chars_eq_methylene_chain (n : Nat) :
    tailChars n = syntaxMethyleneChain n ++ "[CH3]".toList := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [tailChars, syntaxMethyleneChain, ih]
      rfl

/-- Six bracket atoms, one triple-bond token and six branch delimiters consume 13 tokens. -/
theorem parse_prefix (parity : TetrahedralInputParity) (fuel : Nat) (rest : List Char) :
    parseCharsFuel (fuel + 13) (prefixChars parity ++ rest) {} =
      parseCharsFuel fuel rest (prefixState parity) := by
  cases parity <;> rfl

theorem parse_tail (n fuel : Nat) (state : ParseState) :
    parseCharsFuel (fuel + n + 2) (tailChars n) state = .ok (tailState n state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      change parseCharsFuel ((fuel + n + 2) + 1)
        ('[' :: 'C' :: 'H' :: '2' :: ']' :: tailChars n) state = _
      change parseCharsFuel (fuel + n + 2) (tailChars n)
        (state.addAtom (bracket .C 2)) = _
      exact ih _

theorem actual_parse_trace (parity : TetrahedralInputParity) (n : Nat) :
    parseChars (smiles parity n).toList {} = .ok (finalState parity n) := by
  have enough : n + 15 ≤ (prefixChars parity ++ tailChars n).length + 1 := by
    rw [List.length_append, prefix_chars_length, tail_chars_length]
    split <;> omega
  let extra := (prefixChars parity ++ tailChars n).length + 1 - (n + 15)
  have fuelEq : (prefixChars parity ++ tailChars n).length + 1 =
      (extra + n + 2) + 13 := by dsimp [extra]; omega
  unfold parseChars smiles
  simp only [String.toList_ofList]
  rw [fuelEq, parse_prefix, parse_tail]
  rfl

def syntaxPrefixState : OpenSMILESSyntaxState :=
  { currentPresent := true, pendingBond := false, atomsSeen := 6, branchStarts := [] }

theorem syntax_prefix (parity : TetrahedralInputParity) (fuel : Nat) (rest : List Char) :
    openSMILESSyntaxValidFuel (fuel + 13) (prefixChars parity ++ rest) {} =
      openSMILESSyntaxValidFuel fuel rest syntaxPrefixState := by
  cases parity <;> rfl

theorem syntax_tail (n fuel : Nat) :
    openSMILESSyntaxValidFuel (n + (fuel + 2)) (tailChars n) syntaxPrefixState = true := by
  rw [tail_chars_eq_methylene_chain,
    openSMILESSyntaxValidFuel_methylene_chain n (fuel + 2)]
  cases n with
  | zero => rfl
  | succ n =>
      rw [OpenSMILESSyntaxState.afterAtoms_succ]
      rfl

/-- The actual admission scanner accepts both parities for every natural chain length. -/
theorem actual_syntax_valid (parity : TetrahedralInputParity) (n : Nat) :
    openSMILESSyntaxValid (smiles parity n) = true := by
  have enough : n + 15 ≤ (prefixChars parity ++ tailChars n).length + 1 := by
    rw [List.length_append, prefix_chars_length, tail_chars_length]
    split <;> omega
  let extra := (prefixChars parity ++ tailChars n).length + 1 - (n + 15)
  have fuelEq : (prefixChars parity ++ tailChars n).length + 1 =
      (n + (extra + 2)) + 13 := by dsimp [extra]; omega
  unfold openSMILESSyntaxValid smiles
  simp only [String.toList_ofList]
  rw [fuelEq, syntax_prefix, syntax_tail]

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
