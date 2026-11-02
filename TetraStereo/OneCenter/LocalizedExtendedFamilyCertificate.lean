import TetraStereo.OneCenter.LocalizedExtendedFamilyReferencePipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedExtendedShortCircuit.FamilyCertificate
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- Plain identifiers and optional labels for every perceived candidate. `none` records a
refused evaluation, not a theorem of chemical nonexistence. -/
structure Report where
  tetrahedral : LocalizedExtendedShortCircuit.Report
  even : List (List Nat × Option AxialDescriptor)
  odd : List (List Nat × Option DoubleBondStereo)
  monocyclic : List ((Nat × Nat) × Option DoubleBondStereo)
  ordinaryAcyclic : List ((Nat × Nat) × Option StereoOutcome)
  cyclicBoundaries : List Nat
  deriving DecidableEq, Repr

/-- Preserve the two E/Z values; the total projection has an explicit unspecified value
outside that range rather than fabricating an E or Z assignment. -/
def ezValue : BlueBookP93.Acyclic.Descriptor → DoubleBondStereo
  | .E => .E
  | .Z => .Z
  | _ => .unspecified

def evenId {input : Input} (axis : input.certified.LocalizedEvenAxialChain) : List Nat :=
  axis.val.path.map Fin.val

def oddId {input : Input} (axis : input.certified.LocalizedOddCumuleneChain) : List Nat :=
  axis.val.path.map Fin.val

def bondId {input : Input} (bond : input.certified.LocalizedCanonicalDoubleBond) : Nat × Nat :=
  (bond.val.1.val, bond.val.2.val)

def boundaryId {input : Input}
    (boundary : input.certified.LocalizedFullyCyclicCumuleneAuthorityBoundary) : Nat :=
  boundary.component.representative.val

def attemptRows {C R I V : Type} {Meaning : R → Prop}
    (identify : C → I) (value : R → V) (attempts : List (Families.Attempt C R Meaning)) :
    List (I × Option V) :=
  attempts.map fun attempt => (identify attempt.candidate, attempt.outcome.map value)

def encode {input : Input} (result : Families.Result input) : Report :=
  { tetrahedral := report input result.auxiliary.facts
    even := attemptRows evenId (fun a => a.result.assignment.descriptor) result.even
    odd := attemptRows oddId (fun a => ezValue a.result.descriptor) result.odd
    monocyclic := attemptRows bondId (fun a => ezValue a.result.descriptor) result.monocyclic
    ordinaryAcyclic := result.ordinaryAcyclic.map fun attempt =>
      (bondId attempt.candidate, attempt.outcome.map fun assignment => assignment.outcome)
    cyclicBoundaries := result.boundaries.map boundaryId }

/-- Submitted family data has no proof-bearing family assignment or result. Auxiliary nodes
use the existing stable occurrence-indexed certificate format. -/
structure Payload (input : Input) where
  auxiliaryNodes : Nodes input
  report : Report

def exportPayload {input : Input} (result : Families.Result input) : Payload input :=
  { auxiliaryNodes := result.auxiliary.nodes, report := encode result }

/-- Proof-bearing evidence exists only after checking and recomputing the submitted report. -/
structure Checked (input : Input) (payload : Payload input) where
  result : Families.Result input
  nodesExact : result.auxiliary.nodes = payload.auxiliaryNodes
  reportExact : encode result = payload.report

/-- Validate the complete auxiliary certificate, recompute every family and boundary, and
compare the entire ordered report, including missing outcomes and candidate multiplicities. -/
def check? (input : Input) (payload : Payload input) : Option (Checked input payload) :=
  match accepted : Cached.checkProposals? input payload.auxiliaryNodes with
  | none => none
  | some facts =>
      let auxiliary : Evaluation input :=
        { nodes := payload.auxiliaryNodes, facts
          accepted := (Cached.checkProposals?_eq input payload.auxiliaryNodes).symm.trans accepted }
      let result := Families.ofEvaluation input auxiliary
      if same : encode result = payload.report then
        some { result, nodesExact := rfl, reportExact := same }
      else none

/-- Export depends on the checked facts and exact family lists, not on proof fields. -/
theorem encode_ofEvaluation {input : Input} (result : Families.Result input) :
    encode (Families.ofEvaluation input result.auxiliary) = encode result := by
  simp only [encode, Families.ofEvaluation, result.evenExact, result.oddExact,
    result.monocyclicExact, result.ordinaryAcyclicExact, result.boundariesExact]

/-- Every internally produced complete report replays through the external checker. -/
theorem check_export_isSome {input : Input} (result : Families.Result input) :
    (check? input (exportPayload result)).isSome = true := by
  have accepted : Cached.checkProposals? input result.auxiliary.nodes = some result.auxiliary.facts := by
    rw [Cached.checkProposals?_eq]
    exact result.auxiliary.accepted
  have encoded : ∀ proof : LocalizedExtendedShortCircuit.checkProposals? input result.auxiliary.nodes =
      some result.auxiliary.facts,
      encode (Families.ofEvaluation input ⟨result.auxiliary.nodes, result.auxiliary.facts, proof⟩) =
        encode result := by
    intro proof
    exact encode_ofEvaluation result
  simp only [check?, exportPayload]
  split
  next absent => simp_all
  next facts found =>
    have factsEq : result.auxiliary.facts = facts := Option.some.inj (accepted.symm.trans found)
    subst facts
    split
    next same => rfl
    next different => exact False.elim (different (encoded _))

theorem Checked.auxiliary_eq_reference {input : Input} {payload : Payload input}
    (checked : Checked input payload) :
    lookup checked.result.auxiliary.facts = referenceState input :=
  evaluation_eq_reference input checked.result.auxiliary

theorem Checked.tetrahedral_exact {input : Input} {payload : Payload input}
    (checked : Checked input payload) : payload.report.tetrahedral = analyze input := by
  rw [← checked.reportExact]
  exact evaluation_report_eq_reference input checked.result.auxiliary


theorem Checked.candidates_exact {input : Input} {payload : Payload input}
    (checked : Checked input payload) :
    payload.report.even.map Prod.fst = input.certified.localizedEvenAxialChains.attach.map evenId ∧
    payload.report.odd.map Prod.fst = input.certified.localizedOddCumuleneChains.attach.map oddId ∧
    payload.report.monocyclic.map Prod.fst = (Families.canonicalDoubleBonds input).map bondId ∧
    payload.report.ordinaryAcyclic.map Prod.fst = (Families.canonicalDoubleBonds input).map bondId ∧
    payload.report.cyclicBoundaries = (Families.cyclicBoundaries input).map boundaryId := by
  rw [← checked.reportExact]
  simp [encode, attemptRows, checked.result.evenExact, checked.result.oddExact,
    checked.result.monocyclicExact, checked.result.ordinaryAcyclicExact, checked.result.boundariesExact,
    Families.evenAttempts, Families.oddAttempts, Families.ringAttempts, Families.ordinaryAttempts,
    Function.comp_def]

private theorem positive_attempt {C R I V : Type} {Meaning : R → Prop}
    (identify : C → I) (value : R → V) (attempts : List (Families.Attempt C R Meaning))
    (identifier : I) (label : V)
    (present : (identifier, some label) ∈ attemptRows identify value attempts) :
    ∃ attempt ∈ attempts, ∃ assignment,
      identify attempt.candidate = identifier ∧ attempt.outcome = some assignment ∧
      value assignment = label ∧ Meaning assignment := by
  obtain ⟨attempt, member, shape⟩ := List.mem_map.mp present
  cases outcome : attempt.outcome with
  | none => simp [outcome] at shape
  | some assignment =>
      simp only [outcome, Option.map_some, Prod.mk.injEq, Option.some.injEq] at shape
      exact ⟨attempt, member, assignment, shape.1, outcome, shape.2, attempt.sound assignment outcome⟩

theorem Checked.even_positive {input : Input} {payload : Payload input}
    (checked : Checked input payload) (identifier : List Nat) (label : AxialDescriptor)
    (present : (identifier, some label) ∈ payload.report.even) :
    ∃ attempt ∈ checked.result.even, ∃ assignment,
      evenId attempt.candidate = identifier ∧ attempt.outcome = some assignment ∧
      (fun a => a.result.assignment.descriptor) assignment = label ∧
      input.certified.DeclarativeLocalizedEvenAxialSpatialAssignmentWithState
        (carrierFuel input) (referenceState input) assignment := by
  have row : (identifier, some label) ∈
      attemptRows evenId (fun a => a.result.assignment.descriptor) checked.result.even := by
    simpa only [← checked.reportExact, encode] using present
  obtain ⟨attempt, member, assignment, identified, computed, labeled, sound⟩ :=
    positive_attempt _ _ _ identifier label row
  refine ⟨attempt, member, assignment, identified, computed, labeled, ?_⟩
  simpa only [evaluation_eq_reference input checked.result.auxiliary] using sound

theorem Checked.odd_positive {input : Input} {payload : Payload input}
    (checked : Checked input payload) (identifier : List Nat) (label : DoubleBondStereo)
    (present : (identifier, some label) ∈ payload.report.odd) :
    ∃ attempt ∈ checked.result.odd, ∃ assignment,
      oddId attempt.candidate = identifier ∧ attempt.outcome = some assignment ∧
      (fun a => ezValue a.result.descriptor) assignment = label ∧
      input.certified.DeclarativeLocalizedOddCumuleneEZSpatialAssignmentWithState
        (carrierFuel input) (referenceState input) assignment := by
  have row : (identifier, some label) ∈
      attemptRows oddId (fun a => ezValue a.result.descriptor) checked.result.odd := by
    simpa only [← checked.reportExact, encode] using present
  obtain ⟨attempt, member, assignment, identified, computed, labeled, sound⟩ :=
    positive_attempt _ _ _ identifier label row
  refine ⟨attempt, member, assignment, identified, computed, labeled, ?_⟩
  simpa only [evaluation_eq_reference input checked.result.auxiliary] using sound

theorem Checked.monocyclic_positive {input : Input} {payload : Payload input}
    (checked : Checked input payload) (identifier : Nat × Nat) (label : DoubleBondStereo)
    (present : (identifier, some label) ∈ payload.report.monocyclic) :
    ∃ attempt ∈ checked.result.monocyclic, ∃ assignment,
      bondId attempt.candidate = identifier ∧ attempt.outcome = some assignment ∧
      (fun a => ezValue a.result.descriptor) assignment = label ∧
      input.certified.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignmentWithState
        (carrierFuel input) (referenceState input) assignment := by
  have row : (identifier, some label) ∈
      attemptRows bondId (fun a => ezValue a.result.descriptor) checked.result.monocyclic := by
    simpa only [← checked.reportExact, encode] using present
  obtain ⟨attempt, member, assignment, identified, computed, labeled, sound⟩ :=
    positive_attempt _ _ _ identifier label row
  refine ⟨attempt, member, assignment, identified, computed, labeled, ?_⟩
  simpa only [evaluation_eq_reference input checked.result.auxiliary] using sound

/-- Ordinary output retains the independent assignment certificate at the reference state,
including its endpoint Rule5 flags and its E/Z or sequence-cis/trans outcome judgment. -/
theorem Checked.ordinary_positive {input : Input} {payload : Payload input}
    (checked : Checked input payload) (identifier : Nat × Nat) (label : StereoOutcome)
    (present : (identifier, some label) ∈ payload.report.ordinaryAcyclic) :
    ∃ bond : input.certified.LocalizedCanonicalDoubleBond,
      bondId bond = identifier ∧
      ∃ assignment : OrdinaryPlanar.Assignment input.certified (carrierFuel input)
        (referenceState input) bond, assignment.outcome = label := by
  rw [← evaluation_eq_reference input checked.result.auxiliary]
  have row : (identifier, some label) ∈ checked.result.ordinaryAcyclic.map
      (fun attempt => (bondId attempt.candidate, attempt.outcome.map fun a => a.outcome)) := by
    simpa only [← checked.reportExact, encode] using present
  obtain ⟨attempt, member, shape⟩ := List.mem_map.mp row
  cases outcome : attempt.outcome with
  | none => simp [outcome] at shape
  | some assignment =>
      simp only [outcome, Option.map_some, Prod.mk.injEq, Option.some.injEq] at shape
      exact ⟨attempt.candidate, shape.1, assignment, shape.2⟩

theorem Checked.boundary_sound {input : Input} {payload : Payload input}
    (checked : Checked input payload) (identifier : Nat)
    (present : identifier ∈ payload.report.cyclicBoundaries) :
    ∃ boundary, boundaryId boundary = identifier ∧
      input.certified.DeclarativeLocalizedFullyCyclicCumuleneAuthorityBoundary boundary := by
  have row : identifier ∈ checked.result.boundaries.map boundaryId := by
    simpa only [← checked.reportExact, encode] using present
  obtain ⟨boundary, member, identified⟩ := List.mem_map.mp row
  refine ⟨boundary, identified, (Families.cyclicBoundaries_exact input boundary).mp ?_⟩
  rwa [checked.result.boundariesExact] at member

end TetraStereo.OneCenter.LocalizedExtendedShortCircuit.FamilyCertificate
