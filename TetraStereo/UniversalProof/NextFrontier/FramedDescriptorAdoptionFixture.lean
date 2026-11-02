import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false





































namespace TetraStereo.UniversalProof.FramedDescriptorAdoptionFixtureProofs.FramedDescriptorAdoptionFixture

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule

/-! ## Fixture: same actual parser string, no fabricated molecule/state literal -/

/-- The 11-atom fixture string.  Central carbon index 1 carries H, Br and two constitutionally
identical `CH(F)Cl` arms at indices 2 and 7, written with opposite parities. -/
def nativeFixtureString : String :=
  "[H]-[C@](-[C@](-[H])(-[F])-[Cl])(-[Br])-[C@@](-[H])(-[F])-[Cl]"

/-- Parsed fixture.  `none` is the fail-closed fallback; `nativeFixture_parse_success` proves it is
not taken.  No molecule or auxiliary-state literal is invented, so no parser/runtime convention is
assumed by a hand-written value. -/
def nativeFixtureMol? : Option RawMolecule :=
  match parseOpenSMILES nativeFixtureString with
  | .ok mol => some mol
  | .error _ => none

/-! ## Kernel-checkable structural facts (no fabricated literal)

The four `Option`-targeted facts use `nativeFixtureMol?.map … = some …` rather than
`(parseOpenSMILES …).map … = .ok …`: the parser error type has no `DecidableEq`, so `Except`
equality is not decidable.  Mapping through `nativeFixtureMol?` moves the comparison into
`Option` of a decidable payload.  Same actual parser string; the corrections are retained. -/

/-- The fixture is accepted by the actual parser. -/
theorem nativeFixture_parse_success :
    (parseOpenSMILES nativeFixtureString).isOk = true := by
  decide +kernel

/-- The fixture has 11 atoms. -/
theorem nativeFixture_atomCount :
    nativeFixtureMol?.map (fun mol => mol.atomCount) = some 11 := by
  decide +kernel

/-- Central carbon index 1 has exactly four ligands (H, arm, Br, arm). -/
theorem nativeFixture_central_ligand_count :
    nativeFixtureMol?.map (fun mol => (mol.ligandsWithLonePair 1).length) = some 4 := by
  decide +kernel

/-- The actual central ligand indices are `[0, 2, 6, 7]` (H, arm, Br, arm). -/
theorem nativeFixture_central_ligands :
    nativeFixtureMol?.map (fun mol => mol.ligandsWithLonePair 1) = some [0, 2, 6, 7] := by
  decide +kernel

/-- First arm (index 2) is a four-ligand carbon. -/
theorem nativeFixture_arm2_ligand_count :
    nativeFixtureMol?.map (fun mol => (mol.ligandsWithLonePair 2).length) = some 4 := by
  decide +kernel

/-- Second arm (index 7) is a four-ligand carbon. -/
theorem nativeFixture_arm7_ligand_count :
    nativeFixtureMol?.map (fun mol => (mol.ligandsWithLonePair 7).length) = some 4 := by
  decide +kernel

/-- The central atom carries a tetrahedral annotation. -/
theorem nativeFixture_central_tagged :
    nativeFixtureMol?.map
      (fun mol => (mol.atomAt? 1).any (fun spec => spec.tetrahedral?.isSome)) = some true := by
  decide +kernel

/-- A genuine canonical profile exists at the central root of the parsed fixture. -/
theorem nativeFixture_central_profile_exists :
    nativeFixtureMol?.map
      (fun mol => (FrameRuntime.profile? mol (canonicalCenterRoot 1)).isSome) = some true := by
  decide +kernel

/-! ## Preserved historical gap: `historicalRestrictedDecision?` refuses a nonempty auxiliary constitutional tie -/

/-- The historical restricted outer decision is *exact* on an empty auxiliary tie. -/
theorem decision?_exact_of_empty_constitutional_tie
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor)
    (constitutional :
      FrameRuntime.compareBranch? mol profile authoritative fuel .rule2
        (.actual left) (.actual right) = some Ordering.eq)
    (empty : state = []) :
    FrameRuntime.historicalRestrictedDecision? mol profile authoritative state fuel left right =
      some { ordering := Ordering.eq } := by
  unfold FrameRuntime.historicalRestrictedDecision?
  rw [constitutional, empty]
  rfl




theorem decision?_refuses_nonempty_constitutional_tie
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor)
    (constitutional :
      FrameRuntime.compareBranch? mol profile authoritative fuel .rule2
        (.actual left) (.actual right) = some Ordering.eq)
    (nonempty : state ≠ []) :
    FrameRuntime.historicalRestrictedDecision? mol profile authoritative state fuel left right = none := by
  unfold FrameRuntime.historicalRestrictedDecision?
  rw [constitutional]
  cases state with
  | nil => exact absurd rfl nonempty
  | cons fact facts => rfl




theorem decision?_decided_tie_is_empty_exact
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor)
    (constitutional :
      FrameRuntime.compareBranch? mol profile authoritative fuel .rule2
        (.actual left) (.actual right) = some Ordering.eq)
    (decided : FrameRuntime.historicalRestrictedDecision? mol profile authoritative state fuel left right ≠ none) :
    state = [] ∧
      FrameRuntime.historicalRestrictedDecision? mol profile authoritative state fuel left right =
        some { ordering := Ordering.eq } := by
  by_cases empty : state = []
  · exact ⟨empty, decision?_exact_of_empty_constitutional_tie mol profile authoritative state fuel
      left right constitutional empty⟩
  · exact absurd (decision?_refuses_nonempty_constitutional_tie mol profile authoritative state fuel
      left right constitutional empty) decided








/-- Ordering code: `0 = lt, 1 = eq, 2 = gt`. -/
def orderingCode : Ordering → Nat
  | .lt => 0
  | .eq => 1
  | .gt => 2

/-- Ordering code with `3 = none` (refused / unbuilt). -/
def optionOrderingCode : Option Ordering → Nat
  | none => 3
  | some ordering => orderingCode ordering

/-- Complete occurrence key (history + provenance), atom, descriptor R/S, uppercase and
priorityPositions — every `OccurrenceAuxFact` field, in an unambiguous product. -/
def auxFactSummary (fact : OccurrenceAuxFact) :
    CanonicalOccurrenceKey × Nat × RS × Bool × List Nat :=
  (fact.key, fact.atom, fact.descriptor, fact.uppercase, fact.priorityPositions)

/-- Full auxiliary state summary, preserving occurrence key/history/provenance. -/
def auxStateSummary (state : OccurrenceAuxState) :
    List (CanonicalOccurrenceKey × Nat × RS × Bool × List Nat) :=
  state.map auxFactSummary

/-- Ligand indices (with lone pair) at every atom of the fixture. -/
def fixtureLigandDiagnostic (mol : RawMolecule) : List (Nat × List Nat) :=
  (List.range mol.atomCount).map (fun i => (i, mol.ligandsWithLonePair i))

/-- Tetrahedral-annotation presence per atom. -/
def fixtureAtomDiagnostic (mol : RawMolecule) : List (Nat × Bool) :=
  (List.range mol.atomCount).map (fun i =>
    (i, (mol.atomAt? i).any (fun spec => spec.tetrahedral?.isSome)))

/-- The shared-profile strict RULE-2 comparison at the arm pair, in fast (`authoritative := false`)
and authoritative (`authoritative := true`) modes.  The code is `0=lt 1=eq 2=gt`; `lt`/`gt` report a
strict RULE-2 decision and are NOT a Rule-4 indication (see retraction). -/
def fixtureSharedConstitutional (mol : RawMolecule) : Option (Nat × Nat) := do
  let profile ← FrameRuntime.profile? mol (canonicalCenterRoot 1)
  let roots ← occurrenceLigandFrame? mol (canonicalCenterRoot 1)
  let left ← roots.find? (fun cursor => cursor.node.atom == 2)
  let right ← roots.find? (fun cursor => cursor.node.atom == 7)
  let fuel := analysisFuel mol
  let fast ← FrameRuntime.compareBranch? mol profile false fuel .rule2
    (.actual left) (.actual right)
  let authoritative ← FrameRuntime.compareBranch? mol profile true fuel .rule2
    (.actual left) (.actual right)
  pure (orderingCode fast, orderingCode authoritative)

/-- The HISTORICAL restricted outer `decision?` refusal at the arm pair in fast and authoritative modes, using the
fast (`buildOccurrenceAuxState?`) and fully authoritative
(`buildOccurrenceAuxStateFullyAuthoritative?`) auxiliary environments respectively.  Code
`0=lt 1=eq 2=gt 3=none(refused)`. -/
def fixtureFrameDecision (mol : RawMolecule) : Option (Nat × Nat) := do
  let profile ← FrameRuntime.profile? mol (canonicalCenterRoot 1)
  let fastState ← buildOccurrenceAuxState? mol (analysisFuel mol) 1
  let authoritativeState ← buildOccurrenceAuxStateFullyAuthoritative? mol (analysisFuel mol) 1
  let roots ← occurrenceLigandFrame? mol (canonicalCenterRoot 1)
  let left ← roots.find? (fun cursor => cursor.node.atom == 2)
  let right ← roots.find? (fun cursor => cursor.node.atom == 7)
  let fuel := analysisFuel mol
  let fast :=
    match FrameRuntime.historicalRestrictedDecision? mol profile false fastState fuel left right with
    | none => 3
    | some decision => orderingCode decision.ordering
  let authoritative :=
    match FrameRuntime.historicalRestrictedDecision? mol profile true authoritativeState fuel left right with
    | none => 3
    | some decision => orderingCode decision.ordering
  pure (fast, authoritative)

/-- EXPLORATORY LEGACY old-algorithm projection for the arm pair.  Every field is produced by a
legacy occurrence function, in both the fast (`…?`) and unrestricted authoritative
(`…Authoritative?`) variants; none of these certifies a repaired stage and none is reachable from
`decision?`.  `lowercaseGuard` is the Rule-4c legacy state guard `state.any (·.uppercase = false)`.
R/R and S/S are reported separately. -/
structure LegacyRuleProjection where
  rule4aFast : Nat
  rule4aAuthoritative : Nat
  rule4bRRFast : Nat
  rule4bRRAuthoritative : Nat
  rule4bSSFast : Nat
  rule4bSSAuthoritative : Nat
  lowercaseGuard : Bool
  rule4cFast : Nat
  rule4cAuthoritative : Nat
  rule5RRFast : Nat
  rule5RRAuthoritative : Nat
  rule5SSFast : Nat
  rule5SSAuthoritative : Nat
  rule5CompleteFast : Option (Ordering × Bool)
  rule5CompleteAuthoritative : Option (Ordering × Bool)
  deriving Repr, DecidableEq

/-- Legacy occurrence Rule-4a/4b/4c and Rule-5 R/R, S/S projection at the arm pair.  The Rule-5
`R/R` vs `S/S` split and the `pseudo` flag are what reveal whether this concrete fixture is
enantiomorphic; that is read off, never assumed from the written `@`/`@@`. -/
def fixtureLegacyRuleProjection (mol : RawMolecule) : Option LegacyRuleProjection := do
  let state ← buildOccurrenceAuxState? mol (analysisFuel mol) 1
  let roots ← occurrenceLigandFrame? mol (canonicalCenterRoot 1)
  let left ← roots.find? (fun cursor => cursor.node.atom == 2)
  let right ← roots.find? (fun cursor => cursor.node.atom == 7)
  let fuel := analysisFuel mol
  let fast : RawDescriptorRuleStage → Nat := fun stage =>
    optionOrderingCode (compareOccurrenceDescriptorAtTiedRoot? mol state fuel stage left right)
  let authoritative : RawDescriptorRuleStage → Nat := fun stage =>
    optionOrderingCode
      (compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel stage left right)
  let rule5Fast : Option (Ordering × Bool) := do
    let comparison ← compareOccurrenceRule5? mol state fuel left right
    pure (comparison.ordering, comparison.pseudo)
  let rule5Authoritative : Option (Ordering × Bool) := do
    let comparison ← compareOccurrenceRule5Authoritative? mol state fuel left right
    pure (comparison.ordering, comparison.pseudo)
  pure
    { rule4aFast := fast .rule4a
      rule4aAuthoritative := authoritative .rule4a
      rule4bRRFast := fast (.rule4b RS.R RS.R)
      rule4bRRAuthoritative := authoritative (.rule4b RS.R RS.R)
      rule4bSSFast := fast (.rule4b RS.S RS.S)
      rule4bSSAuthoritative := authoritative (.rule4b RS.S RS.S)
      lowercaseGuard := state.any (fun fact => !fact.uppercase)
      rule4cFast := fast .rule4c
      rule4cAuthoritative := authoritative .rule4c
      rule5RRFast := fast (.rule5 RS.R RS.R)
      rule5RRAuthoritative := authoritative (.rule5 RS.R RS.R)
      rule5SSFast := fast (.rule5 RS.S RS.S)
      rule5SSAuthoritative := authoritative (.rule5 RS.S RS.S)
      rule5CompleteFast := rule5Fast
      rule5CompleteAuthoritative := rule5Authoritative }

/-- EXPLORATORY LEGACY complete comparison at the arm pair: the fast proved occurrence comparison
versus the unrestricted authoritative variant.  `OccurrenceComparison` is preserved whole via its
`Repr`, so the `pseudo` and `rule4cCarrier?` fields remain unambiguous. -/
def fixtureCompleteComparison (mol : RawMolecule) :
    Option (Option OccurrenceComparison × Option OccurrenceComparison) := do
  let state ← buildOccurrenceAuxState? mol (analysisFuel mol) 1
  let roots ← occurrenceLigandFrame? mol (canonicalCenterRoot 1)
  let left ← roots.find? (fun cursor => cursor.node.atom == 2)
  let right ← roots.find? (fun cursor => cursor.node.atom == 7)
  let fuel := analysisFuel mol
  pure (compareOccurrenceBranches? mol state fuel left right,
        compareOccurrenceBranchesUnrestrictedAuthoritative? mol state fuel left right)





#eval (parseOpenSMILES nativeFixtureString).isOk
#eval nativeFixtureMol?.map (fun mol => mol.atomCount)
#eval nativeFixtureMol?.map fixtureLigandDiagnostic
#eval nativeFixtureMol?.map fixtureAtomDiagnostic
#eval nativeFixtureMol?.map (fun mol =>
  (buildOccurrenceAuxState? mol (analysisFuel mol) 1).map auxStateSummary)
#eval nativeFixtureMol?.map (fun mol =>
  (buildOccurrenceAuxStateFullyAuthoritative? mol (analysisFuel mol) 1).map auxStateSummary)
#eval nativeFixtureMol?.map (fun mol =>
  (occurrenceLigandFrame? mol (canonicalCenterRoot 1)).map
    (fun roots => roots.map (fun cursor => cursor.node.atom)))
#eval nativeFixtureMol?.map (fun mol =>
  ((FrameRuntime.profile? mol (canonicalCenterRoot 2)).isSome,
   (FrameRuntime.profile? mol (canonicalCenterRoot 7)).isSome))
#eval nativeFixtureMol?.map fixtureSharedConstitutional
#eval nativeFixtureMol?.map fixtureFrameDecision
#eval nativeFixtureMol?.map fixtureLegacyRuleProjection
#eval nativeFixtureMol?.map fixtureCompleteComparison

end TetraStereo.UniversalProof.FramedDescriptorAdoptionFixtureProofs.FramedDescriptorAdoptionFixture
