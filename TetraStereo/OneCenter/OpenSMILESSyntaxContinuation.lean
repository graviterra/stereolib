import TetraStereo.OneCenter.ChemistrySemantics
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-- Grammar-state effect of a fully consumed atom token. -/
def OpenSMILESSyntaxState.afterAtom (state : OpenSMILESSyntaxState) : OpenSMILESSyntaxState :=
  { state with currentPresent := true, pendingBond := false, atomsSeen := state.atomsSeen + 1 }

/-- Grammar-state effect of a run of atom tokens, preserving the open-branch stack. -/
def OpenSMILESSyntaxState.afterAtoms : Nat → OpenSMILESSyntaxState → OpenSMILESSyntaxState
  | 0, state => state
  | count + 1, state => OpenSMILESSyntaxState.afterAtoms count state.afterAtom

/-- Character spelling used by arbitrary-length saturated-chain families. -/
def syntaxMethyleneChain : Nat → List Char
  | 0 => []
  | count + 1 => ['[', 'C', 'H', '2', ']'] ++ syntaxMethyleneChain count

/-- A bracket atom is consumed as one token. Its charge, parity and hydrogen punctuation cannot
be mistaken for structural branch/bond syntax by the admission pass. -/
theorem openSMILESSyntaxValidFuel_bracket_atom (fuel : Nat) (chars rest : List Char)
    (state : OpenSMILESSyntaxState) (atom : AtomSpec)
    (parsed : parseAtomToken? ('[' :: chars) = some (atom, rest)) :
    openSMILESSyntaxValidFuel (fuel + 1) ('[' :: chars) state =
      openSMILESSyntaxValidFuel fuel rest state.afterAtom := by
  change (match parseAtomToken? ('[' :: chars) with
    | some (_, remaining) => openSMILESSyntaxValidFuel fuel remaining state.afterAtom
    | none => _) = _
  rw [parsed]

/-- Exact one-token continuation for a bracket methylene. -/
theorem openSMILESSyntaxValidFuel_methylene (fuel : Nat) (rest : List Char)
    (state : OpenSMILESSyntaxState) :
    openSMILESSyntaxValidFuel (fuel + 1) ('[' :: 'C' :: 'H' :: '2' :: ']' :: rest) state =
      openSMILESSyntaxValidFuel fuel rest state.afterAtom := by rfl

/-- An arbitrary number of bracket methylenes consumes exactly that many units of parser fuel and
changes only the atom count and last-token flags. No finite sampling is used in this bridge. -/
theorem openSMILESSyntaxValidFuel_methylene_chain (count fuel : Nat) (rest : List Char)
    (state : OpenSMILESSyntaxState) :
    openSMILESSyntaxValidFuel (count + fuel) (syntaxMethyleneChain count ++ rest) state =
      openSMILESSyntaxValidFuel fuel rest (state.afterAtoms count) := by
  induction count generalizing state with
  | zero => simp only [Nat.zero_add, syntaxMethyleneChain, List.nil_append,
      OpenSMILESSyntaxState.afterAtoms]
  | succ count inductionHypothesis =>
      simpa only [Nat.succ_add, syntaxMethyleneChain, List.append_assoc, List.cons_append,
        List.nil_append, openSMILESSyntaxValidFuel_methylene,
        OpenSMILESSyntaxState.afterAtoms] using inductionHypothesis state.afterAtom

/-- Positive runs finish with an atom and preserve all enclosing branch-opening counters. -/
theorem OpenSMILESSyntaxState.afterAtoms_succ (count : Nat) (state : OpenSMILESSyntaxState) :
    state.afterAtoms (count + 1) =
      { state with
        currentPresent := true
        pendingBond := false
        atomsSeen := state.atomsSeen + (count + 1) } := by
  induction count generalizing state with
  | zero => rfl
  | succ count inductionHypothesis =>
      change state.afterAtom.afterAtoms (count + 1) = _
      rw [inductionHypothesis]
      simp only [afterAtom]
      congr 1
      omega

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.openSMILESSyntaxValidFuel_bracket_atom
assert_kernel_only TetraStereo.OneCenter.openSMILESSyntaxValidFuel_methylene_chain
assert_kernel_only TetraStereo.OneCenter.OpenSMILESSyntaxState.afterAtoms_succ
