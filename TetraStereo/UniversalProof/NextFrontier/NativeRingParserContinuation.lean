import TetraStereo.UniversalProof.NextFrontier.NativeRingDomain

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingParserContinuation

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain

/-- Character-level CH2 repetition. The recursion is on the molecular family parameter. -/
def chainChars : Nat → List Char
  | 0 => []
  | n + 1 => ['[', 'C', 'H', '2', ']'] ++ chainChars n

theorem chainSyntax_toList (n : Nat) : (chainSyntax n).toList = chainChars n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [chainSyntax, String.toList_append, chainChars, ih]; rfl

/-- The actual finite token prefix, before the arbitrary CH2 chain. -/
def headChars (parity : TetrahedralInputParity) : List Char :=
  (tagToken parity ++ "([F])([CH]([Cl])").toList

/-- This operational intermediate is deliberately not the independent physical ring record.
The theorem below checks how the parser reaches it; a separate join must identify its closed
molecule with `ringRaw`. -/
def headState (parity : TetrahedralInputParity) : ParseState :=
  let root := ({} : ParseState).addAtom (taggedCarbon parity)
  let fluorine := ({ root with branches := [0] } : ParseState).addAtom
    { AtomSpec.aliphatic .F with explicitHydrogens? := some 0 }
  let restored : ParseState := { fluorine with current? := some 0, branches := [0] }
  let carbon := restored.addAtom (NativeRingDomain.carbon 1)
  let chlorine := ({ carbon with branches := [2, 0] } : ParseState).addAtom
    { AtomSpec.aliphatic .Cl with explicitHydrogens? := some 0 }
  { chlorine with current? := some 2, branches := [0] }

/-- Independently named operational CH2 continuation; no parse-success hypothesis is present. -/
def appendChain : Nat → ParseState → ParseState
  | 0, state => state
  | n + 1, state => appendChain n (state.addAtom (carbon 2))

theorem parse_head (parity : TetrahedralInputParity) (fuel : Nat) (tail : List Char) :
    parseCharsFuel (fuel + 9) (headChars parity ++ tail) {} =
      parseCharsFuel fuel tail (headState parity) := by
  cases parity <;> rfl

theorem parse_chain_atom (fuel : Nat) (tail : List Char) (state : ParseState) :
    parseCharsFuel (fuel + 1) (['[', 'C', 'H', '2', ']'] ++ tail) state =
      parseCharsFuel fuel tail (state.addAtom (carbon 2)) := rfl

/-- Every chain length is interpreted by the actual recursive parser, with arbitrary surrounding
state and continuation. This is a structural induction, not a list of bounded examples. -/
theorem parse_chain (n fuel : Nat) (tail : List Char) (state : ParseState) :
    parseCharsFuel (fuel + n) (chainChars n ++ tail) state =
      parseCharsFuel fuel tail (appendChain n state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      rw [show fuel + (n + 1) = (fuel + n) + 1 by omega]
      simp only [chainChars, List.append_assoc]
      rw [parse_chain_atom, ih]
      rfl

/-- Reassociate the structural chain recursion so physical invariants can be proved by
adding the final atom. -/
theorem appendChain_succ_right (n : Nat) (state : ParseState) :
    appendChain (n + 1) state = (appendChain n state).addAtom (carbon 2) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => exact ih (state.addAtom (carbon 2))

@[simp] theorem addAtom_atoms (state : ParseState) (atom : AtomSpec) :
    (state.addAtom atom).atoms = state.atoms ++ [atom] := by
  unfold ParseState.addAtom
  cases state.current? <;> rfl

@[simp] theorem addAtom_current (state : ParseState) (atom : AtomSpec) :
    (state.addAtom atom).current? = some state.atoms.length := by
  unfold ParseState.addAtom
  cases state.current? <;> rfl

@[simp] theorem addAtom_pending (state : ParseState) (atom : AtomSpec) :
    (state.addAtom atom).pendingBond? = none := by
  unfold ParseState.addAtom
  cases state.current? <;> rfl

@[simp] theorem addAtom_branches (state : ParseState) (atom : AtomSpec) :
    (state.addAtom atom).branches = state.branches := by
  unfold ParseState.addAtom
  cases state.current? <;> rfl

@[simp] theorem addAtom_rings (state : ParseState) (atom : AtomSpec) :
    (state.addAtom atom).rings = state.rings := by
  unfold ParseState.addAtom
  cases state.current? <;> rfl

theorem appendChain_atoms (n : Nat) (state : ParseState) :
    (appendChain n state).atoms = state.atoms ++ List.replicate n (carbon 2) := by
  induction n with
  | zero => simp [appendChain]
  | succ n ih =>
      rw [appendChain_succ_right, addAtom_atoms, ih]
      simp only [List.replicate_add, List.replicate_one, List.append_assoc]

theorem appendChain_branches (n : Nat) (state : ParseState) :
    (appendChain n state).branches = state.branches := by
  induction n with
  | zero => rfl
  | succ n ih => rw [appendChain_succ_right, addAtom_branches, ih]

theorem appendChain_rings (n : Nat) (state : ParseState) :
    (appendChain n state).rings = state.rings := by
  induction n with
  | zero => rfl
  | succ n ih => rw [appendChain_succ_right, addAtom_rings, ih]

theorem appendChain_current (n : Nat) (state : ParseState) :
    (appendChain (n + 1) state).current? = some (state.atoms.length + n) := by
  rw [appendChain_succ_right, addAtom_current, appendChain_atoms]
  simp only [List.length_append, List.length_replicate]

theorem appendChain_pending (n : Nat) (state : ParseState) :
    (appendChain (n + 1) state).pendingBond? = none := by
  rw [appendChain_succ_right, addAtom_pending]

/-- The actual operational chain has the independent family's complete atom inventory. -/
theorem ring_chain_atoms (n : Nat) (parity : TetrahedralInputParity) :
    (appendChain (n + 1) (headState parity)).atoms = (ringRaw n parity).atoms := by
  rw [appendChain_atoms]
  rfl

theorem ring_chain_current (n : Nat) (parity : TetrahedralInputParity) :
    (appendChain (n + 1) (headState parity)).current? = some (n + 4) := by
  rw [appendChain_current]
  change some (4 + n) = some (n + 4)
  rw [Nat.add_comm]

theorem ring_chain_shape (n : Nat) (parity : TetrahedralInputParity) :
    (appendChain (n + 1) (headState parity)).branches = [0] ∧
    (appendChain (n + 1) (headState parity)).rings = [] ∧
    (appendChain (n + 1) (headState parity)).pendingBond? = none := by
  rw [appendChain_branches, appendChain_rings, appendChain_pending]
  exact ⟨rfl, rfl, rfl⟩

/-- Token-level interpretation of the ring-opening digit, branch restoration, and closing digit.
The errors remain explicit until the physical-state join proves that these operations succeed. -/
def closeChain (state : ParseState) : Except ParserError ParseState := do
  let opened ← state.handleRingDigit 1
  let restored ← opened.popBranch
  restored.handleRingDigit 1

theorem parse_closure (fuel : Nat) (tail : List Char) (state : ParseState) :
    parseCharsFuel (fuel + 3) (['1', ')', '1'] ++ tail) state = (do
      let closed ← closeChain state
      parseCharsFuel fuel tail closed) := by
  change (state.handleRingDigit 1).bind (fun opened =>
      opened.popBranch.bind (fun restored =>
        (restored.handleRingDigit 1).bind (fun closed => parseCharsFuel fuel tail closed))) =
    ((state.handleRingDigit 1).bind (fun opened =>
      opened.popBranch.bind (fun restored => restored.handleRingDigit 1))).bind
        (fun closed => parseCharsFuel fuel tail closed)
  cases state.handleRingDigit 1 with
  | error error => rfl
  | ok opened =>
      change opened.popBranch.bind (fun restored =>
          (restored.handleRingDigit 1).bind (fun closed => parseCharsFuel fuel tail closed)) =
        (opened.popBranch.bind (fun restored => restored.handleRingDigit 1)).bind
          (fun closed => parseCharsFuel fuel tail closed)
      cases opened.popBranch <;> rfl

theorem ringSyntax_toList (n : Nat) (parity : TetrahedralInputParity) :
    (ringSyntax n parity).toList =
      headChars parity ++ chainChars (n + 1) ++ ['1', ')', '1'] := by
  simp only [ringSyntax, headChars, String.toList_append, chainSyntax_toList,
    List.append_assoc]
  rfl

/-- The actual public core parser reaches a fully explicit operational construction for every
ring size and both parities. The remaining physical join is not asserted by this theorem. -/
theorem parse_ring_core (n fuel : Nat) (parity : TetrahedralInputParity) :
    parseCharsFuel (fuel + n + 13) (ringSyntax n parity).toList {} = (do
      let closed ← closeChain (appendChain (n + 1) (headState parity))
      parseCharsFuel fuel [] closed) := by
  rw [ringSyntax_toList]
  rw [show fuel + n + 13 = ((fuel + 3) + (n + 1)) + 9 by omega]
  rw [List.append_assoc, parse_head]
  rw [parse_chain]
  exact parse_closure fuel [] (appendChain (n + 1) (headState parity))

end TetraStereo.UniversalProof.NativeRingParserContinuation
