import TetraStereo.OneCenter.ChemistrySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

set_option maxHeartbeats 1000000 in
theorem parseElement?_rest_length_lt
    {chars : List Char} {element : Element} {aromatic : Bool} {rest : List Char}
    (parsed : parseElement? chars = some (element, aromatic, rest)) :
    rest.length < chars.length := by
  cases chars with
  | nil => simp [parseElement?] at parsed
  | cons first chars =>
      cases chars with
      | nil =>
          simp only [parseElement?] at parsed
          repeat' split at parsed <;> simp_all
      | cons second tail =>
          simp only [parseElement?] at parsed
          repeat' split at parsed <;> simp_all

theorem takeBracketBody?_tail_length_lt
    {chars body tail : List Char}
    (parsed : takeBracketBody? chars = some (body, tail)) :
    tail.length < chars.length := by
  induction chars generalizing body tail with
  | nil => simp [takeBracketBody?] at parsed
  | cons first chars inductionHypothesis =>
      by_cases closing : first = ']'
      · subst first
        simp [takeBracketBody?] at parsed
        simp_all
      · cases recursiveComputed : takeBracketBody? chars with
        | none => simp [takeBracketBody?, recursiveComputed] at parsed
        | some bodyAndTail =>
            rcases bodyAndTail with ⟨recursiveBody, recursiveTail⟩
            simp [takeBracketBody?, recursiveComputed] at parsed
            rcases parsed with ⟨_, rfl⟩
            have tailShorter := inductionHypothesis recursiveComputed
            simp only [List.length_cons]
            omega

theorem parseAtomToken?_rest_length_lt
    {chars : List Char} {atom : AtomSpec} {rest : List Char}
    (parsed : parseAtomToken? chars = some (atom, rest)) :
    rest.length < chars.length := by
  cases chars with
  | nil => simp [parseAtomToken?, parseElement?] at parsed
  | cons first chars =>
      by_cases bracket : first = '['
      · subst first
        cases bodyComputed : takeBracketBody? chars with
        | none => simp [parseAtomToken?, bodyComputed] at parsed
        | some bodyAndTail =>
            rcases bodyAndTail with ⟨body, tail⟩
            cases atomComputed : parseBracketAtomBody? body with
            | none => simp [parseAtomToken?, bodyComputed, atomComputed] at parsed
            | some parsedAtom =>
                simp [parseAtomToken?, bodyComputed, atomComputed] at parsed
                rcases parsed with ⟨_, rfl⟩
                have tailShorter := takeBracketBody?_tail_length_lt bodyComputed
                simp only [List.length_cons]
                omega
      · cases elementComputed : parseElement? (first :: chars) with
        | none => simp [parseAtomToken?, bracket, elementComputed] at parsed
        | some parsedElement =>
            rcases parsedElement with ⟨element, aromatic, outputRest⟩
            simp [parseAtomToken?, bracket, elementComputed] at parsed
            rcases parsed with ⟨_, rfl⟩
            exact parseElement?_rest_length_lt elementComputed

set_option maxHeartbeats 1000000 in
theorem parseRingToken?_rest_length_lt
    {chars : List Char} {digit : Nat} {rest : List Char}
    (parsed : parseRingToken? chars = some (digit, rest)) :
    rest.length < chars.length := by
  cases chars with
  | nil => simp [parseRingToken?] at parsed
  | cons first chars =>
      cases chars with
      | nil =>
          simp only [parseRingToken?] at parsed
          repeat' split at parsed <;> simp_all
      | cons second chars =>
          cases chars with
          | nil =>
              simp only [parseRingToken?] at parsed
              repeat' split at parsed <;> simp_all
          | cons third tail =>
              by_cases percent : first = '%'
              · subst first
                cases tensComputed : digit? second with
                | none => simp [parseRingToken?, tensComputed] at parsed
                | some tens =>
                    cases onesComputed : digit? third with
                    | none => simp [parseRingToken?, tensComputed, onesComputed] at parsed
                    | some ones =>
                        simp [parseRingToken?, tensComputed, onesComputed] at parsed
                        rcases parsed with ⟨_, rfl⟩
                        simp
                        omega
              · cases digitComputed : digit? first with
                | none => simp [parseRingToken?, percent, digitComputed] at parsed
                | some firstDigit =>
                    cases firstDigit with
                    | zero => simp [parseRingToken?, percent, digitComputed] at parsed
                    | succ positiveDigit =>
                        simp [parseRingToken?, percent, digitComputed] at parsed
                        rcases parsed with ⟨_, rfl⟩
                        simp

theorem ParseState.pushBranch_ne_parserFuelExhausted (state : ParseState) :
    state.pushBranch ≠ Except.error "parser fuel exhausted" := by
  cases currentComputed : state.current? <;>
    simp [ParseState.pushBranch, currentComputed]

theorem ParseState.popBranch_ne_parserFuelExhausted (state : ParseState) :
    state.popBranch ≠ Except.error "parser fuel exhausted" := by
  cases branchesComputed : state.branches <;>
    simp [ParseState.popBranch, branchesComputed]

theorem ParseState.resolveRingBondKind_ne_parserFuelExhausted
    (state : ParseState) (opening : RingOpening) (current : Nat) :
    state.resolveRingBondKind opening current ≠
      Except.error "parser fuel exhausted" := by
  unfold ParseState.resolveRingBondKind
  split
  · split <;> simp_all
  · simp
  · simp
  · split <;> simp_all

theorem ParseState.handleRingDigit_ne_parserFuelExhausted
    (state : ParseState) (digit : Nat) :
    state.handleRingDigit digit ≠ Except.error "parser fuel exhausted" := by
  unfold ParseState.handleRingDigit
  split
  · simp
  · rename_i current currentComputed
    split
    · simp
    · rename_i opening openingComputed
      cases resolved : state.resolveRingBondKind opening current with
      | error message =>
          have notFuel := state.resolveRingBondKind_ne_parserFuelExhausted opening current
          simp [resolved] at notFuel
          change Except.error message ≠ Except.error "parser fuel exhausted"
          simpa using notFuel
      | ok kind =>
          change Except.ok _ ≠ Except.error "parser fuel exhausted"
          simp

theorem parseCharsFuel_ne_parserFuelExhausted_of_length_lt
    (fuel : Nat) (chars : List Char) (state : ParseState)
    (enough : chars.length < fuel) :
    parseCharsFuel fuel chars state ≠ Except.error "parser fuel exhausted" := by
  induction fuel generalizing chars state with
  | zero => omega
  | succ fuel inductionHypothesis =>
      cases chars with
      | nil => simp [parseCharsFuel]
      | cons first rest =>
          have restEnough : rest.length < fuel := by
            simp only [List.length_cons] at enough
            omega
          by_cases dot : first = '.'
          · subst first
            simpa [parseCharsFuel] using
              inductionHypothesis rest
                { state with current? := none, pendingBond? := none } restEnough
          · by_cases opening : first = '('
            · subst first
              cases pushed : state.pushBranch with
              | error message =>
                  have notFuel := state.pushBranch_ne_parserFuelExhausted
                  simp [pushed] at notFuel
                  intro computation
                  simp [parseCharsFuel, pushed] at computation
                  change Except.error message =
                    Except.error "parser fuel exhausted" at computation
                  exact notFuel (by simpa using computation)
              | ok nextState =>
                  simpa [parseCharsFuel, pushed] using
                    inductionHypothesis rest nextState restEnough
            · by_cases closing : first = ')'
              · subst first
                cases popped : state.popBranch with
                | error message =>
                    have notFuel := state.popBranch_ne_parserFuelExhausted
                    simp [popped] at notFuel
                    intro computation
                    simp [parseCharsFuel, popped] at computation
                    change Except.error message =
                      Except.error "parser fuel exhausted" at computation
                    exact notFuel (by simpa using computation)
                | ok nextState =>
                    simpa [parseCharsFuel, popped] using
                      inductionHypothesis rest nextState restEnough
              · cases atomParsed : parseAtomToken? (first :: rest) with
                | none =>
                    cases bondParsed : parseBondToken? first with
                    | some bond =>
                        simpa [parseCharsFuel, dot, opening, closing, atomParsed,
                          bondParsed] using
                          inductionHypothesis rest
                            { state with pendingBond? := some bond } restEnough
                    | none =>
                        cases ringParsed : parseRingToken? (first :: rest) with
                        | none =>
                            simp [parseCharsFuel, dot, opening, closing, atomParsed,
                              bondParsed, ringParsed]
                        | some ringAndRest =>
                            rcases ringAndRest with ⟨digit, outputRest⟩
                            have outputShort := parseRingToken?_rest_length_lt ringParsed
                            have outputEnough : outputRest.length < fuel := by
                              omega
                            cases handled : state.handleRingDigit digit with
                            | error message =>
                                have notFuel :=
                                  state.handleRingDigit_ne_parserFuelExhausted digit
                                simp [handled] at notFuel
                                intro computation
                                simp [parseCharsFuel, dot, opening, closing, atomParsed,
                                  bondParsed, ringParsed, handled] at computation
                                change Except.error message =
                                  Except.error "parser fuel exhausted" at computation
                                exact notFuel (by simpa using computation)
                            | ok nextState =>
                                simpa [parseCharsFuel, dot, opening, closing, atomParsed,
                                  bondParsed, ringParsed, handled] using
                                  inductionHypothesis outputRest nextState outputEnough
                | some atomAndRest =>
                    rcases atomAndRest with ⟨atom, outputRest⟩
                    have outputShort := parseAtomToken?_rest_length_lt atomParsed
                    have outputEnough : outputRest.length < fuel := by
                      omega
                    simpa [parseCharsFuel, dot, opening, closing, atomParsed] using
                      inductionHypothesis outputRest (state.addAtom atom) outputEnough

theorem parseChars_ne_parserFuelExhausted (chars : List Char) (state : ParseState) :
    parseChars chars state ≠ Except.error "parser fuel exhausted" := by
  apply parseCharsFuel_ne_parserFuelExhausted_of_length_lt
  simp

theorem finalizeParseState_ne_parserFuelExhausted (state : ParseState) :
    finalizeParseState state ≠ Except.error "parser fuel exhausted" := by
  unfold finalizeParseState
  split
  · split
    · split
      · simp only
        split <;> simp
      · simp
    · simp
  · simp

theorem parseOpenSMILES_ne_parserFuelExhausted (input : String) :
    parseOpenSMILES input ≠ Except.error "parser fuel exhausted" := by
  unfold parseOpenSMILES
  split
  · cases parsed : parseChars input.toList {} with
    | error message =>
        have notFuel := parseChars_ne_parserFuelExhausted input.toList {}
        have different : message ≠ "parser fuel exhausted" := by
          simpa [parsed] using notFuel
        simp [different]
    | ok state =>
        simp only
        cases finalized : finalizeParseState state with
        | error message =>
            have notFuel := finalizeParseState_ne_parserFuelExhausted state
            simpa [finalized] using notFuel
        | ok molecule =>
            simp only
            split <;> simp
  · simp

end TetraStereo.OneCenter
