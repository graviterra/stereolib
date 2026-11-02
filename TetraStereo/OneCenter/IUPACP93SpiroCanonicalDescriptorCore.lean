import TetraStereo.OneCenter.LocalizedSpiroAuthoritativeXaabbAxialDescriptor
import TetraStereo.OneCenter.IUPACP93SpiroAuthorityCarrier
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through5FixedPoint

set_option autoImplicit false

/-!
# Scheduled-analyzer descriptor witness core for localized P-93 spiro centers

This module is a one-way bridge from the localized scheduled spiro analyzers.  It covers the
tetrahedral `Xabcd` and `Xabab` center descriptors and the paired center/axial description of
`Xaabb`.  The witness core retains the actual localized spiro carrier,
connectivity-only topology proof, matrix-pattern judgment, scheduled `R/S/r/s` judgment, and,
for `Xabab`, an occurrence-bearing traversal produced from the promoted-key matrix.

The generic bridge remains parameterized by `AromaticCanonicalRuleSemantics`, so its generic
judgment must not be mistaken for an independent reviewed provision reference.  The final section
also specializes the bridge to the fixed source-derived
`aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics`.  That specialization removes the
caller-selected semantics callback and retains the constructor's independently stated canonical
occurrence outcome relation.  It remains conditional on matrix readiness and successful analyzer
computation, and it does not close an authority provision row.

It deliberately does not construct `P93AuthoritySpiroSystem`: the localized analyzer represents
rings as `Finset input.Atom`, whereas the authority carrier requires two ordered internal ring
paths together with source-path proofs.  Nor does an atom index manufacture a nomenclature
citation.  Consequently this file states no authority-policy agreement and no reference
completeness theorem.  The spiro double-bond row is also excluded: there is presently no
localized authoritative polycyclic double-bond analyzer to project.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Acyclic
open BlueBookP93.Cyclic

/-! ## Exact P-91 to P-93 spelling conversion -/

/-- Partial conversion from the literal P-91 tokens emitted by the localized spiro analyzers to
the independent P-93 descriptor vocabulary.  It is intentionally undefined outside the six
center/axis spellings used by the covered spiro rows. -/
def p93SpiroDescriptorOfP91? : BlueBookP91.Descriptor → Option Descriptor
  | .capitalR => some .R
  | .capitalS => some .S
  | .lowercaseR => some .r
  | .lowercaseS => some .s
  | .capitalM => some .M
  | .capitalP => some .P
  | _ => none

/-- Exact graph of the partial P-91 to P-93 conversion. -/
theorem p93SpiroDescriptorOfP91?_eq_some_iff
    (token : BlueBookP91.Descriptor) (descriptor : Descriptor) :
    p93SpiroDescriptorOfP91? token = some descriptor ↔
      (token = .capitalR ∧ descriptor = .R) ∨
      (token = .capitalS ∧ descriptor = .S) ∨
      (token = .lowercaseR ∧ descriptor = .r) ∨
      (token = .lowercaseS ∧ descriptor = .s) ∨
      (token = .capitalM ∧ descriptor = .M) ∨
      (token = .capitalP ∧ descriptor = .P) := by
  cases token <;> cases descriptor <;> simp [p93SpiroDescriptorOfP91?]

/-- Conversion preserves the exact descriptor family selected by the localized analyzer. -/
theorem p93SpiroDescriptorOfP91?_matches_family
    (mode : SpiroConfigurationMode)
    (token : BlueBookP91.Descriptor) (descriptor : Descriptor)
    (applies : SpiroLocalDescriptorApplies mode token)
    (converted : p93SpiroDescriptorOfP91? token = some descriptor) :
    P93SpiroCenterDescriptorMatchesFamily mode.family descriptor := by
  cases mode <;> cases token <;> cases descriptor <;>
    simp_all [SpiroLocalDescriptorApplies, p93SpiroDescriptorOfP91?,
      SpiroConfigurationMode.family, P93SpiroCenterDescriptorMatchesFamily]

/-- The `Xaabb` analyzer's center and axial projections convert exactly to the independent
P-93 `R`/`M`, `S`/`P` correspondence. -/
theorem p93SpiroDescriptorOfP91?_xaabb_correspondence (ranked : RS) :
    ∃ centerDescriptor axialDescriptor,
      p93SpiroDescriptorOfP91?
          (spiroCenterP91DescriptorOfRSPseudo (.chiral ranked)) =
        some centerDescriptor ∧
      p93SpiroDescriptorOfP91? (spiroXaabbAxialP91DescriptorOfRS ranked) =
        some axialDescriptor ∧
      P93SpiroCenterDescriptorMatchesFamily .centerRS centerDescriptor ∧
      P93SpiroCenterDescriptorMatchesFamily .axialMP axialDescriptor ∧
      P93SpiroCenterAxialCorrespondence centerDescriptor axialDescriptor := by
  cases ranked
  · exact ⟨.R, .M, rfl, rfl, Or.inl rfl, Or.inl rfl, trivial⟩
  · exact ⟨.S, .P, rfl, rfl, Or.inr rfl, Or.inr rfl, trivial⟩

/-! ## Source-bound observations and scheduled-analyzer witness judgments -/

/-- The three policy-free analyzer projections currently supported. -/
inductive P93SpiroCanonicalDescriptorCoreRow where
  | xabcd
  | xabab
  | xaabbAxial
  deriving DecidableEq, Repr

/-- A localized center together with the connectivity-only topology used by every analyzer in
this file.  Keeping the proof in the frame prevents a detached descriptor from being presented
as analyzer output. -/
structure P93SpiroCanonicalDescriptorSourceFrame
    (input : CertifiedLocalizedCIPInput) where
  center : input.Atom
  carrier : input.LocalizedSpiroCenter center
  topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier

namespace P93SpiroCanonicalDescriptorSourceFrame

noncomputable def tetraCenter
    {input : CertifiedLocalizedCIPInput}
    (frame : P93SpiroCanonicalDescriptorSourceFrame input) :
    input.certified.input.AromaticCanonicalTetrahedralCenter :=
  input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro
    frame.center frame.carrier frame.topology

noncomputable def dependencyView
    {input : CertifiedLocalizedCIPInput}
    (frame : P93SpiroCanonicalDescriptorSourceFrame input)
    (carrierFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel) :
    input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel frame.tetraCenter) :=
  let source := input.certified.input
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel frame.tetraCenter
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  source.aromaticCanonicalDependencyView state target

end P93SpiroCanonicalDescriptorSourceFrame

structure P93SpiroXabcdCanonicalDescriptorObservation
    (input : CertifiedLocalizedCIPInput) where
  frame : P93SpiroCanonicalDescriptorSourceFrame input
  descriptor : Descriptor

structure P93SpiroXababCanonicalDescriptorObservation
    (input : CertifiedLocalizedCIPInput) where
  frame : P93SpiroCanonicalDescriptorSourceFrame input
  family : SpiroDescriptorFamily
  occurrenceOrder : XababOccurrenceOrder
  descriptor : Descriptor

structure P93SpiroXaabbAxialCanonicalDescriptorObservation
    (input : CertifiedLocalizedCIPInput) where
  frame : P93SpiroCanonicalDescriptorSourceFrame input
  centerDescriptor : Descriptor
  axialDescriptor : Descriptor

/-- Row-dependent observation carrier. -/
def P93SpiroCanonicalDescriptorCoreObservation
    (row : P93SpiroCanonicalDescriptorCoreRow)
    (input : CertifiedLocalizedCIPInput) : Type :=
  match row with
  | .xabcd => P93SpiroXabcdCanonicalDescriptorObservation input
  | .xabab => P93SpiroXababCanonicalDescriptorObservation input
  | .xaabbAxial => P93SpiroXaabbAxialCanonicalDescriptorObservation input

/-- Actual occurrence evidence retained by the `Xabab` core.  This is an existential over the
full traversal object, not three caller-provided booleans. -/
def P93SpiroXababActualOccurrenceEvidence
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (frame : P93SpiroCanonicalDescriptorSourceFrame input)
    (order : XababOccurrenceOrder) : Prop :=
  ∃ traversal : input.AuthoritativeSpiroMatrixRowXababTraversal carrierFuel ruleFuel
      frame.center frame.carrier frame.topology (frame.dependencyView carrierFuel semantics)
      (0 : Fin 4),
    order = traversal.toLegacyEvidence.toOccurrenceOrder

/-- Conditional meaning of an analyzer-witness observation for the supplied scheduled semantics.
It mentions no P-93 authority policy, `ValidFor`, citation, or provision reference judgment, but
it is not independent of the executable rule semantics supplied by the caller. -/
def P93SpiroCanonicalDescriptorCoreJudgment
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel) :
    (row : P93SpiroCanonicalDescriptorCoreRow) →
      P93SpiroCanonicalDescriptorCoreObservation row input → Prop
  | .xabcd, observation =>
      ∃ rankedDescriptor : LocalizedTetrahedralRSPseudoDescriptor,
        input.DeclarativeAuthoritativeSpiroReferenceCoherentLigandPattern
            carrierFuel ruleFuel observation.frame.center observation.frame.carrier
            observation.frame.topology
            (observation.frame.dependencyView carrierFuel semantics) .Xabcd ∧
          input.certified.input.AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
            semantics ruleFuel observation.frame.tetraCenter rankedDescriptor ∧
          SpiroCenterRSPseudoApplicable .Xabcd rankedDescriptor ∧
          p93SpiroDescriptorOfP91?
              (spiroCenterP91DescriptorOfRSPseudo rankedDescriptor) =
            some observation.descriptor ∧
          P93SpiroCenterDescriptorMatchesFamily .centerRS observation.descriptor
  | .xabab, observation =>
      ∃ rankedDescriptor : LocalizedTetrahedralRSPseudoDescriptor,
        input.DeclarativeAuthoritativeSpiroReferenceCoherentLigandPattern
            carrierFuel ruleFuel observation.frame.center observation.frame.carrier
            observation.frame.topology
            (observation.frame.dependencyView carrierFuel semantics) .Xabab ∧
          input.certified.input.AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
            semantics ruleFuel observation.frame.tetraCenter rankedDescriptor ∧
          SpiroCenterRSPseudoApplicable .Xabab rankedDescriptor ∧
          observation.family = (spiroCenterModeOfRSPseudo rankedDescriptor).family ∧
          p93SpiroDescriptorOfP91?
              (spiroCenterP91DescriptorOfRSPseudo rankedDescriptor) =
            some observation.descriptor ∧
          P93SpiroXababActualOccurrenceEvidence input carrierFuel ruleFuel semantics
            observation.frame observation.occurrenceOrder ∧
          ValidXababOccurrenceOrder observation.occurrenceOrder ∧
          P93SpiroCenterDescriptorMatchesFamily observation.family observation.descriptor
  | .xaabbAxial, observation =>
      ∃ rankedDescriptor : RS,
        input.DeclarativeAuthoritativeSpiroReferenceCoherentLigandPattern
            carrierFuel ruleFuel observation.frame.center observation.frame.carrier
            observation.frame.topology
            (observation.frame.dependencyView carrierFuel semantics) .Xaabb ∧
          input.certified.input.AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
            semantics ruleFuel observation.frame.tetraCenter (.chiral rankedDescriptor) ∧
          p93SpiroDescriptorOfP91?
              (spiroCenterP91DescriptorOfRSPseudo (.chiral rankedDescriptor)) =
            some observation.centerDescriptor ∧
          p93SpiroDescriptorOfP91? (spiroXaabbAxialP91DescriptorOfRS rankedDescriptor) =
            some observation.axialDescriptor ∧
          P93SpiroCenterDescriptorMatchesFamily .centerRS observation.centerDescriptor ∧
          P93SpiroCenterDescriptorMatchesFamily .axialMP observation.axialDescriptor ∧
          P93SpiroCenterAxialCorrespondence
            observation.centerDescriptor observation.axialDescriptor

namespace CertifiedLocalizedCIPInput

/-- A center analyzer judgment in the `Xabcd` branch projects to a policy-free source core. -/
theorem p93SpiroXabcdCanonicalDescriptorCore_of_judgment
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment)
    (derived : input.AuthoritativeSpiroCenterDescriptorJudgment carrierFuel ruleFuel semantics
      center carrier topology assignment)
    (patternEq : assignment.pattern = .Xabcd) :
    ∃ observation : P93SpiroCanonicalDescriptorCoreObservation .xabcd input,
      observation.frame.center = center ∧
        P93SpiroCanonicalDescriptorCoreJudgment input carrierFuel ruleFuel semantics
          .xabcd observation := by
  rcases derived with ⟨pattern, rankedDescriptor, patternJudged, rankedJudged,
    applicable, _occurrence, rfl⟩
  simp only [makeAuthoritativeSpiroCenterDescriptorAssignment] at patternEq
  subst pattern
  cases rankedDescriptor with
  | chiral ranked =>
      cases ranked with
      | R =>
          exact ⟨{ frame := { center, carrier, topology }, descriptor := .R }, rfl,
            ⟨.chiral .R, patternJudged, rankedJudged, applicable, rfl, Or.inl rfl⟩⟩
      | S =>
          exact ⟨{ frame := { center, carrier, topology }, descriptor := .S }, rfl,
            ⟨.chiral .S, patternJudged, rankedJudged, applicable, rfl, Or.inr rfl⟩⟩
  | pseudoasymmetric ranked =>
      cases ranked <;> simp [SpiroCenterRSPseudoApplicable] at applicable

/-- Exact analyzer computation supplies the `Xabcd` core once matrix readiness identifies the
independent center judgment. -/
theorem p93SpiroXabcdCanonicalDescriptorCore_of_computation
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment)
    (ready :
      let frame : P93SpiroCanonicalDescriptorSourceFrame input := { center, carrier, topology }
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel ruleFuel
        frame.tetraCenter (frame.dependencyView carrierFuel semantics))
    (computed : input.authoritativeSpiroCenterDescriptor? carrierFuel ruleFuel semantics
      center carrier topology = some assignment)
    (patternEq : assignment.pattern = .Xabcd) :
    ∃ observation : P93SpiroCanonicalDescriptorCoreObservation .xabcd input,
      observation.frame.center = center ∧
        P93SpiroCanonicalDescriptorCoreJudgment input carrierFuel ruleFuel semantics
          .xabcd observation := by
  apply input.p93SpiroXabcdCanonicalDescriptorCore_of_judgment carrierFuel ruleFuel semantics
    center carrier topology assignment
  · exact (input.authoritativeSpiroCenterDescriptor?_eq_some_iff carrierFuel ruleFuel semantics
      center carrier topology assignment ready).mp computed
  · exact patternEq

/-- An `Xabab` center judgment projects both its P-93 descriptor and an actual occurrence-bearing
matrix traversal. -/
theorem p93SpiroXababCanonicalDescriptorCore_of_judgment
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment)
    (derived : input.AuthoritativeSpiroCenterDescriptorJudgment carrierFuel ruleFuel semantics
      center carrier topology assignment)
    (patternEq : assignment.pattern = .Xabab) :
    ∃ observation : P93SpiroCanonicalDescriptorCoreObservation .xabab input,
      observation.frame.center = center ∧
        P93SpiroCanonicalDescriptorCoreJudgment input carrierFuel ruleFuel semantics
          .xabab observation := by
  rcases derived with ⟨pattern, rankedDescriptor, patternJudged, rankedJudged,
    applicable, occurrence, rfl⟩
  simp only [makeAuthoritativeSpiroCenterDescriptorAssignment] at patternEq
  subst pattern
  change Nonempty (input.AuthoritativeSpiroMatrixRowXababTraversal carrierFuel ruleFuel
    center carrier topology
    (({ center, carrier, topology } : P93SpiroCanonicalDescriptorSourceFrame input).dependencyView
      carrierFuel semantics) (0 : Fin 4)) at occurrence
  rcases occurrence with ⟨traversal⟩
  let descriptor : Descriptor := match rankedDescriptor with
    | .chiral .R => .R | .chiral .S => .S
    | .pseudoasymmetric .r => .r | .pseudoasymmetric .s => .s
  have converted : p93SpiroDescriptorOfP91?
      (spiroCenterP91DescriptorOfRSPseudo rankedDescriptor) = some descriptor := by
    cases rankedDescriptor with
    | chiral ranked => cases ranked <;> rfl
    | pseudoasymmetric ranked => cases ranked <;> rfl
  let order := traversal.toLegacyEvidence.toOccurrenceOrder
  refine ⟨
    { frame := { center, carrier, topology }
      family := (spiroCenterModeOfRSPseudo rankedDescriptor).family
      occurrenceOrder := order
      descriptor }, rfl, ?_⟩
  refine ⟨rankedDescriptor, patternJudged, rankedJudged, applicable, rfl, converted,
    ⟨traversal, rfl⟩, ?_, ?_⟩
  · exact (valid_toOccurrenceOrder_iff traversal.toLegacyEvidence).2
      traversal.toLegacyEvidence_valid
  · exact p93SpiroDescriptorOfP91?_matches_family
      (spiroCenterModeOfRSPseudo rankedDescriptor)
      (spiroCenterP91DescriptorOfRSPseudo rankedDescriptor) descriptor
      (spiroCenterP91DescriptorOfRSPseudo_applies rankedDescriptor) converted

/-- Exact analyzer computation supplies the `Xabab` core under matrix readiness. -/
theorem p93SpiroXababCanonicalDescriptorCore_of_computation
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment)
    (ready :
      let frame : P93SpiroCanonicalDescriptorSourceFrame input := { center, carrier, topology }
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel ruleFuel
        frame.tetraCenter (frame.dependencyView carrierFuel semantics))
    (computed : input.authoritativeSpiroCenterDescriptor? carrierFuel ruleFuel semantics
      center carrier topology = some assignment)
    (patternEq : assignment.pattern = .Xabab) :
    ∃ observation : P93SpiroCanonicalDescriptorCoreObservation .xabab input,
      observation.frame.center = center ∧
        P93SpiroCanonicalDescriptorCoreJudgment input carrierFuel ruleFuel semantics
          .xabab observation := by
  apply input.p93SpiroXababCanonicalDescriptorCore_of_judgment carrierFuel ruleFuel semantics
    center carrier topology assignment
  · exact (input.authoritativeSpiroCenterDescriptor?_eq_some_iff carrierFuel ruleFuel semantics
      center carrier topology assignment ready).mp computed
  · exact patternEq

/-- The localized `Xaabb` axial analyzer projects its center/axis pair to the exact finite P-93
correspondence, while retaining the matrix pattern and scheduled center judgment. -/
theorem p93SpiroXaabbAxialCanonicalDescriptorCore_of_judgment
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroXaabbAxialDescriptorAssignment)
    (derived : input.AuthoritativeSpiroXaabbAxialDescriptorJudgment carrierFuel ruleFuel semantics
      center carrier topology assignment) :
    ∃ observation : P93SpiroCanonicalDescriptorCoreObservation .xaabbAxial input,
      observation.frame.center = center ∧
        P93SpiroCanonicalDescriptorCoreJudgment input carrierFuel ruleFuel semantics
          .xaabbAxial observation := by
  rcases derived with ⟨centerAssignment, ranked, centerDerived, patternEq, rankedEq, rfl⟩
  rcases centerDerived with ⟨pattern, rankedDescriptor, patternJudged, rankedJudged,
    applicable, _occurrence, centerAssignmentEq⟩
  subst centerAssignment
  simp only [makeAuthoritativeSpiroCenterDescriptorAssignment] at patternEq rankedEq
  subst pattern
  cases rankedEq
  rcases p93SpiroDescriptorOfP91?_xaabb_correspondence ranked with
    ⟨centerDescriptor, axialDescriptor, centerConverted, axialConverted,
      centerMatches, axialMatches, correspondence⟩
  refine ⟨{ frame := { center, carrier, topology }, centerDescriptor, axialDescriptor }, rfl, ?_⟩
  exact ⟨ranked, patternJudged, rankedJudged, centerConverted, axialConverted,
    centerMatches, axialMatches, correspondence⟩

/-- Exact axial analyzer computation supplies the `Xaabb` policy-free core under matrix
readiness. -/
theorem p93SpiroXaabbAxialCanonicalDescriptorCore_of_computation
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroXaabbAxialDescriptorAssignment)
    (ready :
      let frame : P93SpiroCanonicalDescriptorSourceFrame input := { center, carrier, topology }
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel ruleFuel
        frame.tetraCenter (frame.dependencyView carrierFuel semantics))
    (computed : input.authoritativeSpiroXaabbAxialDescriptor? carrierFuel ruleFuel semantics
      center carrier topology = some assignment) :
    ∃ observation : P93SpiroCanonicalDescriptorCoreObservation .xaabbAxial input,
      observation.frame.center = center ∧
        P93SpiroCanonicalDescriptorCoreJudgment input carrierFuel ruleFuel semantics
          .xaabbAxial observation := by
  apply input.p93SpiroXaabbAxialCanonicalDescriptorCore_of_judgment
    carrierFuel ruleFuel semantics center carrier topology assignment
  exact (input.authoritativeSpiroXaabbAxialDescriptor?_eq_some_iff
    carrierFuel ruleFuel semantics center carrier topology assignment ready).mp computed

/-! ## Fixed source-canonical semantics specialization

The following wrappers eliminate the caller's choice of `AromaticCanonicalRuleSemantics`.  They
select the concrete occurrence Rule-3--5 semantics whose derivation relation is the independently
stated canonical occurrence outcome relation.  Matrix readiness and endpoint success remain
explicit: this is a deterministic scheduled-analyzer soundness layer, not authority completeness.
-/

/-- The one fixed source-derived semantics used by every canonical spiro wrapper below. -/
noncomputable def p93SpiroCanonicalRuleSemantics
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat) :
    input.certified.input.AromaticCanonicalRuleSemantics carrierFuel :=
  input.certified.input.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
    carrierFuel ruleFuel

/-- Parameter-free center analyzer obtained by fixing the source-canonical occurrence semantics. -/
noncomputable def authoritativeCanonicalSpiroCenterDescriptor?
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    Option AuthoritativeSpiroCenterDescriptorAssignment :=
  input.authoritativeSpiroCenterDescriptor? carrierFuel ruleFuel
    (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)
    center carrier topology

/-- Parameter-free `Xaabb` axial analyzer using the same fixed source-canonical semantics. -/
noncomputable def authoritativeCanonicalSpiroXaabbAxialDescriptor?
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    Option AuthoritativeSpiroXaabbAxialDescriptorAssignment :=
  input.authoritativeSpiroXaabbAxialDescriptor? carrierFuel ruleFuel
    (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)
    center carrier topology

/-- Canonical-semantics specialization of the dependent core judgment. -/
def P93SpiroCanonicalDescriptorCoreCanonicalJudgment
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat) :
    (row : P93SpiroCanonicalDescriptorCoreRow) →
      P93SpiroCanonicalDescriptorCoreObservation row input → Prop :=
  P93SpiroCanonicalDescriptorCoreJudgment input carrierFuel ruleFuel
    (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)

/-- Exact meaning of the parameter-free center analyzer under canonical matrix readiness. -/
theorem authoritativeCanonicalSpiroCenterDescriptor?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment)
    (ready :
      let frame : P93SpiroCanonicalDescriptorSourceFrame input := { center, carrier, topology }
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel ruleFuel
        frame.tetraCenter
          (frame.dependencyView carrierFuel
            (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel))) :
    input.authoritativeCanonicalSpiroCenterDescriptor? carrierFuel ruleFuel
        center carrier topology = some assignment ↔
      input.AuthoritativeSpiroCenterDescriptorJudgment carrierFuel ruleFuel
        (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)
        center carrier topology assignment := by
  exact input.authoritativeSpiroCenterDescriptor?_eq_some_iff carrierFuel ruleFuel
    (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)
    center carrier topology assignment ready

/-- Exact meaning of the parameter-free `Xaabb` axial analyzer under canonical readiness. -/
theorem authoritativeCanonicalSpiroXaabbAxialDescriptor?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroXaabbAxialDescriptorAssignment)
    (ready :
      let frame : P93SpiroCanonicalDescriptorSourceFrame input := { center, carrier, topology }
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel ruleFuel
        frame.tetraCenter
          (frame.dependencyView carrierFuel
            (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel))) :
    input.authoritativeCanonicalSpiroXaabbAxialDescriptor? carrierFuel ruleFuel
        center carrier topology = some assignment ↔
      input.AuthoritativeSpiroXaabbAxialDescriptorJudgment carrierFuel ruleFuel
        (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)
        center carrier topology assignment := by
  exact input.authoritativeSpiroXaabbAxialDescriptor?_eq_some_iff carrierFuel ruleFuel
    (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)
    center carrier topology assignment ready

/-- Canonical `Xabcd` computation yields the source-bound core with no semantics argument. -/
theorem p93SpiroXabcdCanonicalDescriptorCore_of_canonical_computation
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment)
    (ready :
      let frame : P93SpiroCanonicalDescriptorSourceFrame input := { center, carrier, topology }
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel ruleFuel
        frame.tetraCenter
          (frame.dependencyView carrierFuel
            (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)))
    (computed : input.authoritativeCanonicalSpiroCenterDescriptor? carrierFuel ruleFuel
      center carrier topology = some assignment)
    (patternEq : assignment.pattern = .Xabcd) :
    ∃ observation : P93SpiroCanonicalDescriptorCoreObservation .xabcd input,
      observation.frame.center = center ∧
        P93SpiroCanonicalDescriptorCoreCanonicalJudgment input carrierFuel ruleFuel
          .xabcd observation := by
  exact input.p93SpiroXabcdCanonicalDescriptorCore_of_computation carrierFuel ruleFuel
    (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)
    center carrier topology assignment ready computed patternEq

/-- Canonical `Xabab` computation yields a core retaining an actual traversal certificate. -/
theorem p93SpiroXababCanonicalDescriptorCore_of_canonical_computation
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment)
    (ready :
      let frame : P93SpiroCanonicalDescriptorSourceFrame input := { center, carrier, topology }
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel ruleFuel
        frame.tetraCenter
          (frame.dependencyView carrierFuel
            (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)))
    (computed : input.authoritativeCanonicalSpiroCenterDescriptor? carrierFuel ruleFuel
      center carrier topology = some assignment)
    (patternEq : assignment.pattern = .Xabab) :
    ∃ observation : P93SpiroCanonicalDescriptorCoreObservation .xabab input,
      observation.frame.center = center ∧
        P93SpiroCanonicalDescriptorCoreCanonicalJudgment input carrierFuel ruleFuel
          .xabab observation := by
  exact input.p93SpiroXababCanonicalDescriptorCore_of_computation carrierFuel ruleFuel
    (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)
    center carrier topology assignment ready computed patternEq

/-- Canonical `Xaabb` axial computation yields the exact source-bound center/axis core. -/
theorem p93SpiroXaabbAxialCanonicalDescriptorCore_of_canonical_computation
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroXaabbAxialDescriptorAssignment)
    (ready :
      let frame : P93SpiroCanonicalDescriptorSourceFrame input := { center, carrier, topology }
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel ruleFuel
        frame.tetraCenter
          (frame.dependencyView carrierFuel
            (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)))
    (computed : input.authoritativeCanonicalSpiroXaabbAxialDescriptor? carrierFuel ruleFuel
      center carrier topology = some assignment) :
    ∃ observation : P93SpiroCanonicalDescriptorCoreObservation .xaabbAxial input,
      observation.frame.center = center ∧
        P93SpiroCanonicalDescriptorCoreCanonicalJudgment input carrierFuel ruleFuel
          .xaabbAxial observation := by
  exact input.p93SpiroXaabbAxialCanonicalDescriptorCore_of_computation carrierFuel ruleFuel
    (input.p93SpiroCanonicalRuleSemantics carrierFuel ruleFuel)
    center carrier topology assignment ready computed

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.p93SpiroDescriptorOfP91?_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.p93SpiroDescriptorOfP91?_matches_family
assert_kernel_only TetraStereo.OneCenter.p93SpiroDescriptorOfP91?_xaabb_correspondence
assert_kernel_only TetraStereo.OneCenter.P93SpiroCanonicalDescriptorCoreJudgment
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.p93SpiroXabcdCanonicalDescriptorCore_of_computation
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.p93SpiroXababCanonicalDescriptorCore_of_computation
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.p93SpiroXaabbAxialCanonicalDescriptorCore_of_computation
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.authoritativeCanonicalSpiroCenterDescriptor?_eq_some_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.authoritativeCanonicalSpiroXaabbAxialDescriptor?_eq_some_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.p93SpiroXabcdCanonicalDescriptorCore_of_canonical_computation
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.p93SpiroXababCanonicalDescriptorCore_of_canonical_computation
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.p93SpiroXaabbAxialCanonicalDescriptorCore_of_canonical_computation
