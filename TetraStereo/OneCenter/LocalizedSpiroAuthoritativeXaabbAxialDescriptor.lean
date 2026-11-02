import TetraStereo.OneCenter.LocalizedSpiroAuthoritativeCenterDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-!
# The P-93.5.3.5 axial description of an `Xaabb` spiro center

P-92.1.2.2.3 fixes the axis correspondence `R` = `M` and `S` = `P`.  P-93.5.3.5
permits that axial description for an `Xaabb` spiro system while retaining the center `R/S`
description for preferred IUPAC names.  The definitions below state both facts independently of
the molecule analyzer.
-/

/-- P-92 helicity corresponding to an ordinary `R/S` result when the same configuration is read
as a chirality axis. -/
def spiroXaabbAxialHelicityOfRS : RS → BlueBookP92.Helicity
  | .R => .M
  | .S => .P

/-- Literal P-91 axial token corresponding to the preferred center token. -/
def spiroXaabbAxialP91DescriptorOfRS : RS → BlueBookP91.Descriptor
  | .R => .capitalM
  | .S => .capitalP

/-- Embed the production `RS` type into the independent P-92 `RSDescriptor` type. -/
def spiroXaabbP92RSDescriptorOfRS : RS → BlueBookP92.RSDescriptor
  | .R => .R
  | .S => .S

/-- The executable conversion is exactly the P-92.1.2.2.3 axis correspondence. -/
theorem correspondingRS_spiroXaabbAxialHelicityOfRS (descriptor : RS) :
    BlueBookP92.correspondingRS .axis (spiroXaabbAxialHelicityOfRS descriptor) =
      spiroXaabbP92RSDescriptorOfRS descriptor := by
  cases descriptor <;> rfl

/-- Independent token-level correspondence between the preferred center spelling and the
permitted axial spelling. -/
def SpiroXaabbCenterAxialTokenCorrespondence :
    BlueBookP91.Descriptor → BlueBookP91.Descriptor → Prop
  | .capitalR, .capitalM
  | .capitalS, .capitalP => True
  | _, _ => False

instance (center axial : BlueBookP91.Descriptor) :
    Decidable (SpiroXaabbCenterAxialTokenCorrespondence center axial) := by
  cases center <;> cases axial <;>
    simp [SpiroXaabbCenterAxialTokenCorrespondence] <;> exact inferInstance

/-- The two executable token projections satisfy the independent token relation. -/
theorem spiroXaabb_center_axial_token_correspondence (descriptor : RS) :
    SpiroXaabbCenterAxialTokenCorrespondence
      (spiroCenterP91DescriptorOfRSPseudo (.chiral descriptor))
      (spiroXaabbAxialP91DescriptorOfRS descriptor) := by
  cases descriptor <;> trivial

/-- P-93.5.3.5 naming status on the `Xaabb` tetrahedral domain.  Both modes describe the
configuration, but the center `R/S` mode is the preferred-IUPAC-name spelling. -/
def SpiroXaabbModePreferredForPIN : SpiroConfigurationMode → Prop
  | .centerRS => True
  | _ => False

instance (mode : SpiroConfigurationMode) :
    Decidable (SpiroXaabbModePreferredForPIN mode) := by
  cases mode <;> simp [SpiroXaabbModePreferredForPIN] <;> exact inferInstance

/-- Exact P-93 boundary: center `R/S` and axial `M/P` are both applicable, but only center
`R/S` is preferred for the PIN. -/
theorem xaabb_center_preferred_axial_permitted :
    SpiroConfigurationModeApplicable .Xaabb .tetrahedral .centerRS ∧
      SpiroConfigurationModeApplicable .Xaabb .tetrahedral .axialMP ∧
      SpiroXaabbModePreferredForPIN .centerRS ∧
      ¬SpiroXaabbModePreferredForPIN .axialMP := by
  exact ⟨trivial, trivial, trivial, by simp [SpiroXaabbModePreferredForPIN]⟩

/-- Every converted axial token is in the P-91 axial/helicity family. -/
theorem spiroXaabbAxialP91DescriptorOfRS_applies (descriptor : RS) :
    SpiroLocalDescriptorApplies .axialMP
      (spiroXaabbAxialP91DescriptorOfRS descriptor) := by
  cases descriptor <;> trivial

end BlueBookP93.Cyclic

namespace CertifiedLocalizedCIPInput

open BlueBookP93.Cyclic

/-- Final permitted axial alternative paired with the preferred center descriptor from the same
authoritative `Xaabb` computation. -/
structure AuthoritativeSpiroXaabbAxialDescriptorAssignment where
  center : Nat
  rankedDescriptor : RS
  preferredCenterDescriptor : BlueBookP91.Descriptor
  mode : SpiroConfigurationMode
  descriptor : BlueBookP91.Descriptor
  deriving DecidableEq, Repr

def makeAuthoritativeSpiroXaabbAxialDescriptorAssignment
    (center : Nat) (rankedDescriptor : RS) :
    AuthoritativeSpiroXaabbAxialDescriptorAssignment :=
  { center
    rankedDescriptor
    preferredCenterDescriptor :=
      spiroCenterP91DescriptorOfRSPseudo (.chiral rankedDescriptor)
    mode := .axialMP
    descriptor := spiroXaabbAxialP91DescriptorOfRS rankedDescriptor }

/-- Project the completed center analyzer to the permitted `Xaabb` axial spelling.  No axial
token is accepted from the caller. -/
noncomputable def authoritativeSpiroXaabbAxialDescriptor?
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    Option AuthoritativeSpiroXaabbAxialDescriptorAssignment := do
  let centerAssignment ← input.authoritativeSpiroCenterDescriptor?
    carrierFuel ruleFuel semantics center carrier judged
  match centerAssignment.pattern, centerAssignment.rankedDescriptor with
  | .Xaabb, .chiral descriptor =>
      some (makeAuthoritativeSpiroXaabbAxialDescriptorAssignment
        center.val descriptor)
  | _, _ => none

/-- Independent exact meaning of an emitted `Xaabb` axial alternative. -/
def AuthoritativeSpiroXaabbAxialDescriptorJudgment
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroXaabbAxialDescriptorAssignment) : Prop :=
  ∃ centerAssignment descriptor,
    input.AuthoritativeSpiroCenterDescriptorJudgment carrierFuel ruleFuel semantics
        center carrier judged centerAssignment ∧
      centerAssignment.pattern = .Xaabb ∧
      centerAssignment.rankedDescriptor = .chiral descriptor ∧
      assignment = makeAuthoritativeSpiroXaabbAxialDescriptorAssignment
        center.val descriptor

/-- The axial projection is exact against the independent `Xaabb` center judgment. -/
theorem authoritativeSpiroXaabbAxialDescriptor?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroXaabbAxialDescriptorAssignment)
    (ready :
      let tetraCenter :=
        input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
      let source := input.certified.input
      let target := source.aromaticCanonicalFinalOccurrence carrierFuel tetraCenter
      let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
      let view := source.aromaticCanonicalDependencyView state target
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady
        carrierFuel ruleFuel tetraCenter view) :
    input.authoritativeSpiroXaabbAxialDescriptor? carrierFuel ruleFuel semantics
        center carrier judged = some assignment ↔
      input.AuthoritativeSpiroXaabbAxialDescriptorJudgment carrierFuel ruleFuel semantics
        center carrier judged assignment := by
  unfold authoritativeSpiroXaabbAxialDescriptor?
  cases computed : input.authoritativeSpiroCenterDescriptor?
      carrierFuel ruleFuel semantics center carrier judged with
  | none =>
      constructor
      · simp
      · rintro ⟨centerAssignment, descriptor, centerJudged, _pattern, _ranked,
          _assignment⟩
        have centerComputed :=
          (input.authoritativeSpiroCenterDescriptor?_eq_some_iff
            carrierFuel ruleFuel semantics center carrier judged centerAssignment ready).mpr
            centerJudged
        rw [computed] at centerComputed
        contradiction
  | some centerAssignment =>
      have centerJudged :=
        (input.authoritativeSpiroCenterDescriptor?_eq_some_iff
          carrierFuel ruleFuel semantics center carrier judged centerAssignment ready).mp computed
      constructor
      · intro axialComputed
        cases patternEq : centerAssignment.pattern with
        | Xabcd => simp [patternEq] at axialComputed
        | Xabab => simp [patternEq] at axialComputed
        | Xaabb =>
            cases rankedEq : centerAssignment.rankedDescriptor with
            | chiral descriptor =>
                have assignmentEq : assignment =
                    makeAuthoritativeSpiroXaabbAxialDescriptorAssignment
                      center.val descriptor := by
                  simpa [computed, patternEq, rankedEq] using axialComputed.symm
                exact ⟨centerAssignment, descriptor, centerJudged,
                  patternEq, rankedEq, assignmentEq⟩
            | pseudoasymmetric descriptor =>
                simp [patternEq, rankedEq] at axialComputed
      · rintro ⟨candidate, descriptor, candidateJudged, patternEq, rankedEq, rfl⟩
        have candidateComputed :=
          (input.authoritativeSpiroCenterDescriptor?_eq_some_iff
            carrierFuel ruleFuel semantics center carrier judged candidate ready).mpr
            candidateJudged
        rw [computed] at candidateComputed
        have candidateEq : candidate = centerAssignment :=
          (Option.some.inj candidateComputed).symm
        subst candidate
        simp [patternEq, rankedEq]

/-- A successful center judgment whose pattern is `Xaabb` is necessarily an ordinary uppercase
`R/S` result.  This is a consequence of the P-93 mode table, not an additional premise. -/
theorem AuthoritativeSpiroCenterDescriptorJudgment.xaabb_chiral_form
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment)
    (derived : input.AuthoritativeSpiroCenterDescriptorJudgment
      carrierFuel ruleFuel semantics center carrier judged assignment)
    (xaabb : assignment.pattern = .Xaabb) :
    ∃ descriptor,
      assignment = makeAuthoritativeSpiroCenterDescriptorAssignment
        center.val .Xaabb (.chiral descriptor) := by
  rcases derived with ⟨pattern, rankedDescriptor, _patternJudged, _rankedJudged,
    applicable, _occurrence, rfl⟩
  cases pattern <;> cases rankedDescriptor <;>
    simp [makeAuthoritativeSpiroCenterDescriptorAssignment,
      SpiroCenterRSPseudoApplicable] at xaabb applicable ⊢

/-- Every emitted axial alternative obeys the P-92 axis correspondence and the P-91/P-93
applicability tables, while retaining its preferred center token. -/
theorem AuthoritativeSpiroXaabbAxialDescriptorJudgment.conforms
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroXaabbAxialDescriptorAssignment)
    (derived : input.AuthoritativeSpiroXaabbAxialDescriptorJudgment
      carrierFuel ruleFuel semantics center carrier judged assignment) :
    SpiroConfigurationModeApplicable .Xaabb .tetrahedral assignment.mode ∧
      SpiroLocalDescriptorApplies assignment.mode assignment.descriptor ∧
      SpiroXaabbModePreferredForPIN .centerRS ∧
      (¬SpiroXaabbModePreferredForPIN assignment.mode) ∧
      SpiroXaabbCenterAxialTokenCorrespondence
        assignment.preferredCenterDescriptor assignment.descriptor ∧
      BlueBookP92.correspondingRS .axis
          (spiroXaabbAxialHelicityOfRS assignment.rankedDescriptor) =
        spiroXaabbP92RSDescriptorOfRS assignment.rankedDescriptor := by
  rcases derived with ⟨centerAssignment, descriptor, _centerJudged,
    _pattern, _ranked, rfl⟩
  exact ⟨trivial,
    spiroXaabbAxialP91DescriptorOfRS_applies descriptor,
    trivial,
    by simp [makeAuthoritativeSpiroXaabbAxialDescriptorAssignment,
      SpiroXaabbModePreferredForPIN],
    spiroXaabb_center_axial_token_correspondence descriptor,
    correspondingRS_spiroXaabbAxialHelicityOfRS descriptor⟩

/-- Readiness of the derived `Xaabb` axial endpoint. -/
def AuthoritativeSpiroXaabbAxialDescriptorReady
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    Prop :=
  ∃ assignment,
    input.AuthoritativeSpiroXaabbAxialDescriptorJudgment carrierFuel ruleFuel semantics
      center carrier judged assignment

theorem authoritativeSpiroXaabbAxialDescriptor?_isSome_iff_ready
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (ready :
      let tetraCenter :=
        input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
      let source := input.certified.input
      let target := source.aromaticCanonicalFinalOccurrence carrierFuel tetraCenter
      let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
      let view := source.aromaticCanonicalDependencyView state target
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady
        carrierFuel ruleFuel tetraCenter view) :
    (input.authoritativeSpiroXaabbAxialDescriptor? carrierFuel ruleFuel semantics
      center carrier judged).isSome = true ↔
      input.AuthoritativeSpiroXaabbAxialDescriptorReady carrierFuel ruleFuel semantics
        center carrier judged := by
  rw [Option.isSome_iff_exists]
  unfold AuthoritativeSpiroXaabbAxialDescriptorReady
  exact exists_congr fun assignment =>
    input.authoritativeSpiroXaabbAxialDescriptor?_eq_some_iff
      carrierFuel ruleFuel semantics center carrier judged assignment ready

/-- Exhaustive refusal: either the complete preferred-center pipeline refuses, or it succeeds on
a non-`Xaabb` pattern.  A successful `Xaabb` center judgment is necessarily uppercase and hence
always has the axial alternative. -/
def AuthoritativeSpiroXaabbAxialDescriptorRefusal
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    Prop :=
  input.AuthoritativeSpiroCenterDescriptorRefusal carrierFuel ruleFuel semantics
      center carrier judged ∨
    ∃ centerAssignment,
      input.AuthoritativeSpiroCenterDescriptorJudgment carrierFuel ruleFuel semantics
          center carrier judged centerAssignment ∧
        centerAssignment.pattern ≠ .Xaabb

/-- The derived axial endpoint refuses exactly for the two semantic causes above. -/
theorem authoritativeSpiroXaabbAxialDescriptor?_eq_none_iff_refusal
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (ready :
      let tetraCenter :=
        input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
      let source := input.certified.input
      let target := source.aromaticCanonicalFinalOccurrence carrierFuel tetraCenter
      let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
      let view := source.aromaticCanonicalDependencyView state target
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady
        carrierFuel ruleFuel tetraCenter view) :
    input.authoritativeSpiroXaabbAxialDescriptor? carrierFuel ruleFuel semantics
        center carrier judged = none ↔
      input.AuthoritativeSpiroXaabbAxialDescriptorRefusal carrierFuel ruleFuel semantics
        center carrier judged := by
  constructor
  · intro axialNone
    cases centerComputed : input.authoritativeSpiroCenterDescriptor?
        carrierFuel ruleFuel semantics center carrier judged with
    | none =>
        exact Or.inl
          ((input.authoritativeSpiroCenterDescriptor?_eq_none_iff_refusal
            carrierFuel ruleFuel semantics center carrier judged ready).mp centerComputed)
    | some centerAssignment =>
        have centerJudged :=
          (input.authoritativeSpiroCenterDescriptor?_eq_some_iff
            carrierFuel ruleFuel semantics center carrier judged centerAssignment ready).mp
            centerComputed
        right
        refine ⟨centerAssignment, centerJudged, ?_⟩
        intro patternEq
        obtain ⟨descriptor, assignmentEq⟩ :=
          centerJudged.xaabb_chiral_form input carrierFuel ruleFuel semantics center carrier
            judged centerAssignment patternEq
        subst centerAssignment
        simp [authoritativeSpiroXaabbAxialDescriptor?, centerComputed,
          makeAuthoritativeSpiroCenterDescriptorAssignment] at axialNone
  · intro refusal
    rcases refusal with centerRefusal | notXaabb
    · have centerNone :=
        (input.authoritativeSpiroCenterDescriptor?_eq_none_iff_refusal
          carrierFuel ruleFuel semantics center carrier judged ready).mpr centerRefusal
      simp [authoritativeSpiroXaabbAxialDescriptor?, centerNone]
    · rcases notXaabb with ⟨centerAssignment, centerJudged, patternNe⟩
      have centerComputed :=
        (input.authoritativeSpiroCenterDescriptor?_eq_some_iff
          carrierFuel ruleFuel semantics center carrier judged centerAssignment ready).mpr
          centerJudged
      cases patternEq : centerAssignment.pattern with
      | Xabcd => simp [authoritativeSpiroXaabbAxialDescriptor?, centerComputed, patternEq]
      | Xabab => simp [authoritativeSpiroXaabbAxialDescriptor?, centerComputed, patternEq]
      | Xaabb => exact False.elim (patternNe patternEq)

theorem authoritativeSpiroXaabbAxialDescriptorReady_iff_not_refusal
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (ready :
      let tetraCenter :=
        input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
      let source := input.certified.input
      let target := source.aromaticCanonicalFinalOccurrence carrierFuel tetraCenter
      let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
      let view := source.aromaticCanonicalDependencyView state target
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady
        carrierFuel ruleFuel tetraCenter view) :
    input.AuthoritativeSpiroXaabbAxialDescriptorReady carrierFuel ruleFuel semantics
        center carrier judged ↔
      ¬input.AuthoritativeSpiroXaabbAxialDescriptorRefusal carrierFuel ruleFuel semantics
        center carrier judged := by
  rw [← input.authoritativeSpiroXaabbAxialDescriptor?_isSome_iff_ready
      carrierFuel ruleFuel semantics center carrier judged ready,
    ← input.authoritativeSpiroXaabbAxialDescriptor?_eq_none_iff_refusal
      carrierFuel ruleFuel semantics center carrier judged ready]
  cases input.authoritativeSpiroXaabbAxialDescriptor? carrierFuel ruleFuel semantics
      center carrier judged <;> simp

/-- Public zero-or-one list for the permitted axial alternative. -/
noncomputable def authoritativeSpiroXaabbAxialAssignments
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    List AuthoritativeSpiroXaabbAxialDescriptorAssignment :=
  (input.authoritativeSpiroXaabbAxialDescriptor? carrierFuel ruleFuel semantics
    center carrier judged).toList

theorem mem_authoritativeSpiroXaabbAxialAssignments_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroXaabbAxialDescriptorAssignment)
    (ready :
      let tetraCenter :=
        input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
      let source := input.certified.input
      let target := source.aromaticCanonicalFinalOccurrence carrierFuel tetraCenter
      let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
      let view := source.aromaticCanonicalDependencyView state target
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady
        carrierFuel ruleFuel tetraCenter view) :
    assignment ∈ input.authoritativeSpiroXaabbAxialAssignments
        carrierFuel ruleFuel semantics center carrier judged ↔
      input.AuthoritativeSpiroXaabbAxialDescriptorJudgment carrierFuel ruleFuel semantics
        center carrier judged assignment := by
  rw [authoritativeSpiroXaabbAxialAssignments, Option.mem_toList,
    input.authoritativeSpiroXaabbAxialDescriptor?_eq_some_iff
      carrierFuel ruleFuel semantics center carrier judged assignment ready]

theorem authoritativeSpiroXaabbAxialAssignments_nodup
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    (input.authoritativeSpiroXaabbAxialAssignments carrierFuel ruleFuel semantics
      center carrier judged).Nodup := by
  unfold authoritativeSpiroXaabbAxialAssignments
  cases input.authoritativeSpiroXaabbAxialDescriptor? carrierFuel ruleFuel semantics
      center carrier judged <;> simp

theorem authoritativeSpiroXaabbAxialAssignments_count_eq_one_of_success
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroXaabbAxialDescriptorAssignment)
    (computed : input.authoritativeSpiroXaabbAxialDescriptor? carrierFuel ruleFuel semantics
      center carrier judged = some assignment) :
    (input.authoritativeSpiroXaabbAxialAssignments carrierFuel ruleFuel semantics
      center carrier judged).count assignment = 1 := by
  simp [authoritativeSpiroXaabbAxialAssignments, computed]

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
