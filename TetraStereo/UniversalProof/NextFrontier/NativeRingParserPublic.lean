import TetraStereo.UniversalProof.NextFrontier.NativeRingParserPhysicalJoin
import TetraStereo.UniversalProof.GeneralRingPhysicalAdmissionProofs.GeneralRingPhysicalAdmission
import TetraStereo.OneCenter.OpenSMILESSyntaxContinuation

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingParserPublic

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.NativeRingParserContinuation
open TetraStereo.UniversalProof.NativeRingParserPhysicalJoin
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission

def parityExtra : TetrahedralInputParity → Nat
  | .anticlockwise => 0
  | .clockwise => 1

theorem chainChars_length (n : Nat) : (chainChars n).length = 5 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chainChars, ih]; omega

theorem ringSyntax_length (n : Nat) (parity : TetrahedralInputParity) :
    (ringSyntax n parity).toList.length = 5 * n + 29 + parityExtra parity := by
  rw [ringSyntax_toList]
  simp only [List.length_append, chainChars_length]
  have headLength : (headChars parity).length = 21 + parityExtra parity := by
    cases parity <;> decide
  rw [headLength]
  simp only [List.length_cons, List.length_nil]
  omega

/-- The public parser's character-derived fuel dominates the exact token count uniformly. -/
theorem parse_ring_chars (n : Nat) (parity : TetrahedralInputParity) :
    parseChars (ringSyntax n parity).toList {} = .ok (closedState n parity) := by
  unfold parseChars
  rw [ringSyntax_length]
  rw [show 5 * n + 29 + parityExtra parity + 1 =
    ((4 * n + 16 + parityExtra parity) + 1) + n + 13 by omega]
  exact parse_ring_state n (4 * n + 16 + parityExtra parity) parity

def grammarHeadState : OpenSMILESSyntaxState where
  currentPresent := true
  pendingBond := false
  atomsSeen := 4
  branchStarts := [2]

theorem grammar_head (parity : TetrahedralInputParity) (fuel : Nat) (tail : List Char) :
    openSMILESSyntaxValidFuel (fuel + 9) (headChars parity ++ tail) {} =
      openSMILESSyntaxValidFuel fuel tail grammarHeadState := by
  cases parity <;> rfl

theorem chainChars_syntaxMethylene (n : Nat) : chainChars n = syntaxMethyleneChain n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [chainChars, syntaxMethyleneChain, ih]

theorem grammar_closure (n fuel : Nat) :
    openSMILESSyntaxValidFuel (fuel + 4) ['1', ')', '1']
      (grammarHeadState.afterAtoms (n + 1)) = true := by
  rw [OpenSMILESSyntaxState.afterAtoms_succ]
  change (!(some 2 == some (4 + (n + 1))) &&
    (decide (2 < 4 + (n + 1)) && true)) = true
  have unequal : (2 : Nat) ≠ 4 + (n + 1) := by omega
  have grew : 2 < 4 + (n + 1) := by omega
  simp [unequal, grew]

theorem grammar_ring (n fuel : Nat) (parity : TetrahedralInputParity) :
    openSMILESSyntaxValidFuel ((fuel + 1) + n + 13) (ringSyntax n parity).toList {} = true := by
  rw [ringSyntax_toList]
  rw [show (fuel + 1) + n + 13 = ((n + 1) + (fuel + 4)) + 9 by omega]
  rw [List.append_assoc, grammar_head, chainChars_syntaxMethylene,
    openSMILESSyntaxValidFuel_methylene_chain]
  exact grammar_closure n fuel

theorem ring_syntax_admitted (n : Nat) (parity : TetrahedralInputParity) :
    openSMILESSyntaxValid (ringSyntax n parity) = true := by
  unfold openSMILESSyntaxValid
  rw [ringSyntax_length]
  rw [show 5 * n + 29 + parityExtra parity + 1 =
    ((4 * n + 16 + parityExtra parity) + 1) + n + 13 by omega]
  exact grammar_ring n (4 * n + 16 + parityExtra parity) parity

theorem finalize_ring_state (n : Nat) (parity : TetrahedralInputParity) :
    finalizeParseState (closedState n parity) = .ok (ringRaw n parity) := by
  have admitted : (ringRaw n parity).admissible? = true :=
    (RawMolecule.admissible?_eq_true_iff _).mpr (ringRaw_admissible n parity)
  unfold finalizeParseState
  change (if ([] : List Nat) = [] then
    if ([] : List RingOpening) = [] then
      if (none : Option ParsedBondKind) = none then
        if (ringRaw n parity).normalizeUnspecifiedBonds.admissible? then
          Except.ok (ringRaw n parity).normalizeUnspecifiedBonds
        else Except.error _
      else Except.error _
    else Except.error _
  else Except.error _) = _
  rw [ringRaw_normalizeUnspecifiedBonds]
  simp only [admitted, ↓reduceIte]

/-- Every family string, at every natural ring extension and either parity, reaches the exact
independent physical record through the public grammar, parser, finalizer and provenance checks. -/
theorem parse_ring (n : Nat) (parity : TetrahedralInputParity) :
    parseOpenSMILES (ringSyntax n parity) = .ok (ringRaw n parity) :=
  parseOpenSMILES_eq_ok_of _ _ _ (ring_syntax_admitted n parity) (parse_ring_chars n parity)
    (finalize_ring_state n parity) (ringRaw_parser_introduction_valid n parity)

theorem certified_ring (n : Nat) (parity : TetrahedralInputParity) :
    parseAndNormalizeOpenSMILESCertified (ringSyntax n parity) =
      .ok (ringRawCertified n parity) := by
  unfold parseAndNormalizeOpenSMILESCertified parseAndNormalizeOpenSMILES
  rw [parse_ring]
  change (match normalizeRawMoleculeCertified? (ringRaw n parity) with
    | some certified => Except.ok certified
    | none => Except.error _) = _
  rw [ringRaw_actual_certified_intake]

end TetraStereo.UniversalProof.NativeRingParserPublic
