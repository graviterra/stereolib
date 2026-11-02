import TetraStereo.OneCenter.LocalizedSpiroAuthoritativeXababTraversal
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6RSPseudoTotality

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-!
# Final tetrahedral spiro center descriptors from the authoritative source pipeline

This layer converts the source scheduler's proof-relevant `R/S/r/s` result into the literal P-91
token required by the applicable P-93 spiro-center row.  `Xabab` occurrence traversal is obtained
from the actual four-row promoted-key matrix; it is not accepted as three caller booleans.
-/

/-- P-93 center mode determined by the P-92 uppercase/lowercase classification. -/
def spiroCenterModeOfRSPseudo :
    LocalizedTetrahedralRSPseudoDescriptor → SpiroConfigurationMode
  | .chiral _ => .centerRS
  | .pseudoasymmetric _ => .centerPseudoRS

/-- Literal P-91 token corresponding to the authoritative `R/S/r/s` result. -/
def spiroCenterP91DescriptorOfRSPseudo :
    LocalizedTetrahedralRSPseudoDescriptor → BlueBookP91.Descriptor
  | .chiral .R => .capitalR
  | .chiral .S => .capitalS
  | .pseudoasymmetric .r => .lowercaseR
  | .pseudoasymmetric .s => .lowercaseS

/-- The P-93 ligand-pattern rows that permit the selected center descriptor case. -/
def SpiroCenterRSPseudoApplicable
    (pattern : SpiroLigandPattern)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) : Prop :=
  match pattern, descriptor with
  | .Xabcd, .chiral _
  | .Xabab, _
  | .Xaabb, .chiral _ => True
  | _, _ => False

instance (pattern : SpiroLigandPattern)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    Decidable (SpiroCenterRSPseudoApplicable pattern descriptor) := by
  cases pattern <;> cases descriptor <;>
    simp [SpiroCenterRSPseudoApplicable] <;> exact inferInstance

/-- The selected P-91 token is always in the selected center descriptor family. -/
theorem spiroCenterP91DescriptorOfRSPseudo_applies
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    SpiroLocalDescriptorApplies
      (spiroCenterModeOfRSPseudo descriptor)
      (spiroCenterP91DescriptorOfRSPseudo descriptor) := by
  cases descriptor with
  | chiral rs => cases rs <;> trivial
  | pseudoasymmetric rs => cases rs <;> trivial

/-- The new applicability predicate is exactly the already transcribed P-93 mode table. -/
theorem spiroCenterRSPseudoApplicable_iff_modeApplicable
    (pattern : SpiroLigandPattern)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    SpiroCenterRSPseudoApplicable pattern descriptor ↔
      SpiroConfigurationModeApplicable pattern .tetrahedral
        (spiroCenterModeOfRSPseudo descriptor) := by
  cases pattern <;> cases descriptor <;>
    simp [SpiroCenterRSPseudoApplicable, spiroCenterModeOfRSPseudo,
      SpiroConfigurationModeApplicable]

end BlueBookP93.Cyclic

namespace CertifiedLocalizedCIPInput

open BlueBookP93.Cyclic

/-- Public final assignment for one tetrahedral spiro center. -/
structure AuthoritativeSpiroCenterDescriptorAssignment where
  center : Nat
  pattern : SpiroLigandPattern
  rankedDescriptor : LocalizedTetrahedralRSPseudoDescriptor
  mode : SpiroConfigurationMode
  descriptor : BlueBookP91.Descriptor
  deriving DecidableEq, Repr

def makeAuthoritativeSpiroCenterDescriptorAssignment
    (center : Nat) (pattern : SpiroLigandPattern)
    (rankedDescriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    AuthoritativeSpiroCenterDescriptorAssignment :=
  { center
    pattern
    rankedDescriptor
    mode := spiroCenterModeOfRSPseudo rankedDescriptor
    descriptor := spiroCenterP91DescriptorOfRSPseudo rankedDescriptor }

/-- Proof-relevant occurrence readiness for the final center token.  Only `Xabab` needs the
senior-first cross-ring traversal. -/
def AuthoritativeSpiroCenterOccurrenceReady
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (pattern : SpiroLigandPattern) : Prop :=
  match pattern with
  | .Xabab =>
      Nonempty (input.AuthoritativeSpiroMatrixRowXababTraversal carrierFuel ruleFuel
        center carrier judged view (0 : Fin 4))
  | _ => True

/-- Boolean occurrence gate used by the final executable analyzer. -/
noncomputable def authoritativeSpiroCenterOccurrenceReadyBool
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (pattern : SpiroLigandPattern) : Bool :=
  match pattern with
  | .Xabab =>
      (input.authoritativeSpiroMatrixRowXababTraversal? carrierFuel ruleFuel
        center carrier judged view (0 : Fin 4)).isSome
  | _ => true

theorem authoritativeSpiroCenterOccurrenceReadyBool_eq_true_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (pattern : SpiroLigandPattern) :
    input.authoritativeSpiroCenterOccurrenceReadyBool carrierFuel ruleFuel
        center carrier judged view pattern = true ↔
      input.AuthoritativeSpiroCenterOccurrenceReady carrierFuel ruleFuel
        center carrier judged view pattern := by
  cases pattern <;>
    simp [authoritativeSpiroCenterOccurrenceReadyBool,
      AuthoritativeSpiroCenterOccurrenceReady,
      authoritativeSpiroMatrixRowXababTraversal?_isSome_iff]

/-- Final molecule-to-P-93/P-91 tetrahedral spiro center analyzer. -/
noncomputable def authoritativeSpiroCenterDescriptor?
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    Option AuthoritativeSpiroCenterDescriptorAssignment := do
  let tetraCenter :=
    input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
  let source := input.certified.input
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel tetraCenter
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  let view := source.aromaticCanonicalDependencyView state target
  let pattern ← input.localizedSpiroLigandPatternFromAuthoritativeMatrix?
    carrierFuel ruleFuel center carrier judged view
  let rankedDescriptor ←
    source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
      semantics ruleFuel tetraCenter
  if _applicable : SpiroCenterRSPseudoApplicable pattern rankedDescriptor then
    if input.authoritativeSpiroCenterOccurrenceReadyBool carrierFuel ruleFuel
        center carrier judged view pattern then
      some (makeAuthoritativeSpiroCenterDescriptorAssignment
        center.val pattern rankedDescriptor)
    else none
  else none

/-- Independent exact meaning of one final emitted center token. -/
def AuthoritativeSpiroCenterDescriptorJudgment
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment) : Prop :=
  let tetraCenter :=
    input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
  let source := input.certified.input
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel tetraCenter
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  let view := source.aromaticCanonicalDependencyView state target
  ∃ pattern rankedDescriptor,
    input.DeclarativeAuthoritativeSpiroReferenceCoherentLigandPattern
        carrierFuel ruleFuel center carrier judged view pattern ∧
      source.AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
        semantics ruleFuel tetraCenter rankedDescriptor ∧
      SpiroCenterRSPseudoApplicable pattern rankedDescriptor ∧
      input.AuthoritativeSpiroCenterOccurrenceReady carrierFuel ruleFuel
        center carrier judged view pattern ∧
      assignment = makeAuthoritativeSpiroCenterDescriptorAssignment
        center.val pattern rankedDescriptor

/-- Under exact 4×4 key-matrix readiness, the final analyzer emits exactly the independently
stated P-93 pattern, P-92 ranked descriptor, occurrence traversal, and P-91 token judgment. -/
theorem authoritativeSpiroCenterDescriptor?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment)
    (ready :
      let tetraCenter :=
        input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
      let source := input.certified.input
      let target := source.aromaticCanonicalFinalOccurrence carrierFuel tetraCenter
      let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
      let view := source.aromaticCanonicalDependencyView state target
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady
        carrierFuel ruleFuel tetraCenter view) :
    input.authoritativeSpiroCenterDescriptor? carrierFuel ruleFuel semantics
        center carrier judged = some assignment ↔
      input.AuthoritativeSpiroCenterDescriptorJudgment carrierFuel ruleFuel semantics
        center carrier judged assignment := by
  let tetraCenter :=
    input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
  let source := input.certified.input
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel tetraCenter
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  let view := source.aromaticCanonicalDependencyView state target
  change input.AuthoritativeSpiroRule3Through6KeyMatrixReady
    carrierFuel ruleFuel tetraCenter view at ready
  unfold authoritativeSpiroCenterDescriptor? AuthoritativeSpiroCenterDescriptorJudgment
  dsimp only
  constructor
  · intro computed
    cases patternComputed : input.localizedSpiroLigandPatternFromAuthoritativeMatrix?
        carrierFuel ruleFuel center carrier judged view with
    | none => simp [tetraCenter, source, target, state, view, patternComputed] at computed
    | some pattern =>
        cases rankedComputed :
            source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
              semantics ruleFuel tetraCenter with
        | none =>
            simp [tetraCenter, source, target, state, view, patternComputed,
              rankedComputed] at computed
        | some rankedDescriptor =>
            by_cases applicable : SpiroCenterRSPseudoApplicable pattern rankedDescriptor
            · by_cases occurrence :
                  input.authoritativeSpiroCenterOccurrenceReadyBool carrierFuel ruleFuel
                    center carrier judged view pattern = true
              · have assignmentEq : assignment =
                    makeAuthoritativeSpiroCenterDescriptorAssignment
                      center.val pattern rankedDescriptor := by
                  simpa [tetraCenter, source, target, state, view, patternComputed,
                    rankedComputed, applicable, occurrence] using computed.symm
                exact ⟨pattern, rankedDescriptor,
                  (input.localizedSpiroLigandPatternFromAuthoritativeMatrix?_eq_some_iff
                    carrierFuel ruleFuel center carrier judged view ready pattern).mp
                      patternComputed,
                  (source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_some_iff
                    semantics ruleFuel tetraCenter rankedDescriptor).mp rankedComputed,
                  applicable,
                  (input.authoritativeSpiroCenterOccurrenceReadyBool_eq_true_iff
                    carrierFuel ruleFuel center carrier judged view pattern).mp occurrence,
                  assignmentEq⟩
              · simp [tetraCenter, source, target, state, view, patternComputed,
                  rankedComputed, applicable, occurrence] at computed
            · simp [tetraCenter, source, target, state, view, patternComputed,
                rankedComputed, applicable] at computed
  · rintro ⟨pattern, rankedDescriptor, patternJudged, rankedJudged,
      applicable, occurrence, rfl⟩
    have patternComputed :=
      (input.localizedSpiroLigandPatternFromAuthoritativeMatrix?_eq_some_iff
        carrierFuel ruleFuel center carrier judged view ready pattern).mpr patternJudged
    have rankedComputed :=
      (source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_some_iff
        semantics ruleFuel tetraCenter rankedDescriptor).mpr rankedJudged
    have occurrenceComputed :=
      (input.authoritativeSpiroCenterOccurrenceReadyBool_eq_true_iff
        carrierFuel ruleFuel center carrier judged view pattern).mpr occurrence
    simp [tetraCenter, source, target, state, view, patternComputed, rankedComputed,
      applicable, occurrenceComputed]

/-- Every emitted final token is in the P-91 family required by its emitted mode. -/
theorem AuthoritativeSpiroCenterDescriptorJudgment.p91_applies
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment)
    (derived : input.AuthoritativeSpiroCenterDescriptorJudgment carrierFuel ruleFuel semantics
      center carrier judged assignment) :
    SpiroLocalDescriptorApplies assignment.mode assignment.descriptor := by
  rcases derived with ⟨pattern, rankedDescriptor, _pattern, _ranked, _applicable,
    _occurrence, rfl⟩
  exact spiroCenterP91DescriptorOfRSPseudo_applies rankedDescriptor

/-- A coherent `Xabab` row under matrix readiness supplies the occurrence traversal automatically;
the other two patterns need no traversal. -/
theorem DeclarativeAuthoritativeSpiroReferenceCoherentLigandPattern.occurrenceReady
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel ruleFuel
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged) view)
    (pattern : SpiroLigandPattern)
    (coherent : input.DeclarativeAuthoritativeSpiroReferenceCoherentLigandPattern
      carrierFuel ruleFuel center carrier judged view pattern) :
    input.AuthoritativeSpiroCenterOccurrenceReady carrierFuel ruleFuel
      center carrier judged view pattern := by
  cases pattern with
  | Xabcd => trivial
  | Xaabb => trivial
  | Xabab =>
      exact ready.exists_matrixRow_xababTraversal input carrierFuel ruleFuel center carrier
        judged view (0 : Fin 4) (coherent 0)

/-- Readiness of the final tetrahedral spiro center endpoint. -/
def AuthoritativeSpiroCenterDescriptorReady
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    Prop :=
  ∃ assignment,
    input.AuthoritativeSpiroCenterDescriptorJudgment carrierFuel ruleFuel semantics
      center carrier judged assignment

theorem authoritativeSpiroCenterDescriptor?_isSome_iff_ready
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
    (input.authoritativeSpiroCenterDescriptor? carrierFuel ruleFuel semantics
        center carrier judged).isSome = true ↔
      input.AuthoritativeSpiroCenterDescriptorReady carrierFuel ruleFuel semantics
        center carrier judged := by
  rw [Option.isSome_iff_exists]
  unfold AuthoritativeSpiroCenterDescriptorReady
  exact exists_congr fun assignment =>
    input.authoritativeSpiroCenterDescriptor?_eq_some_iff carrierFuel ruleFuel semantics
      center carrier judged assignment ready

/-- Exhaustive semantic refusal of the final spiro center endpoint.  The occurrence-traversal
case does not appear: matrix readiness and a coherent `Xabab` judgment prove it automatically. -/
def AuthoritativeSpiroCenterDescriptorRefusal
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    Prop :=
  let tetraCenter :=
    input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
  let source := input.certified.input
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel tetraCenter
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  let view := source.aromaticCanonicalDependencyView state target
  (∀ pattern,
      ¬ input.DeclarativeAuthoritativeSpiroReferenceCoherentLigandPattern
        carrierFuel ruleFuel center carrier judged view pattern) ∨
    (¬ source.AromaticCanonicalScheduledRule3Through6RSPseudoReady
      semantics ruleFuel tetraCenter) ∨
    ∃ pattern rankedDescriptor,
      input.DeclarativeAuthoritativeSpiroReferenceCoherentLigandPattern
          carrierFuel ruleFuel center carrier judged view pattern ∧
        source.AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
          semantics ruleFuel tetraCenter rankedDescriptor ∧
        ¬SpiroCenterRSPseudoApplicable pattern rankedDescriptor

/-- `none` has exactly three causes: no coherent P-93 pattern, no complete P-92 `R/S/r/s`
result, or a real pattern/result pair outside the P-93 center-mode table. -/
theorem authoritativeSpiroCenterDescriptor?_eq_none_iff_refusal
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
    input.authoritativeSpiroCenterDescriptor? carrierFuel ruleFuel semantics
        center carrier judged = none ↔
      input.AuthoritativeSpiroCenterDescriptorRefusal carrierFuel ruleFuel semantics
        center carrier judged := by
  let tetraCenter :=
    input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
  let source := input.certified.input
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel tetraCenter
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  let view := source.aromaticCanonicalDependencyView state target
  change input.AuthoritativeSpiroRule3Through6KeyMatrixReady
    carrierFuel ruleFuel tetraCenter view at ready
  unfold AuthoritativeSpiroCenterDescriptorRefusal
  dsimp only
  constructor
  · intro refused
    cases patternComputed : input.localizedSpiroLigandPatternFromAuthoritativeMatrix?
        carrierFuel ruleFuel center carrier judged view with
    | none =>
        exact Or.inl
          ((input.localizedSpiroLigandPatternFromAuthoritativeMatrix?_eq_none_iff
            carrierFuel ruleFuel center carrier judged view ready).mp patternComputed)
    | some pattern =>
        have patternJudged :=
          (input.localizedSpiroLigandPatternFromAuthoritativeMatrix?_eq_some_iff
            carrierFuel ruleFuel center carrier judged view ready pattern).mp patternComputed
        cases rankedComputed :
            source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
              semantics ruleFuel tetraCenter with
        | none =>
            exact Or.inr (Or.inl
              ((source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_none_iff_not_ready
                semantics ruleFuel tetraCenter).mp rankedComputed))
        | some rankedDescriptor =>
            have rankedJudged :=
              (source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_some_iff
                semantics ruleFuel tetraCenter rankedDescriptor).mp rankedComputed
            by_cases applicable : SpiroCenterRSPseudoApplicable pattern rankedDescriptor
            · have occurrenceReady := patternJudged.occurrenceReady input carrierFuel ruleFuel
                center carrier judged view ready pattern
              have occurrenceComputed :=
                (input.authoritativeSpiroCenterOccurrenceReadyBool_eq_true_iff
                  carrierFuel ruleFuel center carrier judged view pattern).mpr occurrenceReady
              simp [authoritativeSpiroCenterDescriptor?, tetraCenter, source, target, state, view,
                patternComputed, rankedComputed, applicable, occurrenceComputed] at refused
            · exact Or.inr (Or.inr
                ⟨pattern, rankedDescriptor, patternJudged, rankedJudged, applicable⟩)
  · intro refusal
    rcases refusal with noPattern | noRanked | mismatch
    · have patternNone :=
        (input.localizedSpiroLigandPatternFromAuthoritativeMatrix?_eq_none_iff
          carrierFuel ruleFuel center carrier judged view ready).mpr noPattern
      simp [authoritativeSpiroCenterDescriptor?, tetraCenter, source, target, state, view,
        patternNone]
    · have rankedNone :=
        (source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_none_iff_not_ready
          semantics ruleFuel tetraCenter).mpr noRanked
      unfold authoritativeSpiroCenterDescriptor?
      simp [tetraCenter, source, rankedNone]
    · rcases mismatch with
        ⟨pattern, rankedDescriptor, patternJudged, rankedJudged, notApplicable⟩
      have patternComputed :=
        (input.localizedSpiroLigandPatternFromAuthoritativeMatrix?_eq_some_iff
          carrierFuel ruleFuel center carrier judged view ready pattern).mpr patternJudged
      have rankedComputed :=
        (source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_some_iff
          semantics ruleFuel tetraCenter rankedDescriptor).mpr rankedJudged
      simp [authoritativeSpiroCenterDescriptor?, tetraCenter, source, target, state, view,
        patternComputed, rankedComputed, notApplicable]

theorem authoritativeSpiroCenterDescriptorReady_iff_not_refusal
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
    input.AuthoritativeSpiroCenterDescriptorReady carrierFuel ruleFuel semantics
        center carrier judged ↔
      ¬ input.AuthoritativeSpiroCenterDescriptorRefusal carrierFuel ruleFuel semantics
        center carrier judged := by
  rw [← input.authoritativeSpiroCenterDescriptor?_isSome_iff_ready
      carrierFuel ruleFuel semantics center carrier judged ready,
    ← input.authoritativeSpiroCenterDescriptor?_eq_none_iff_refusal
      carrierFuel ruleFuel semantics center carrier judged ready]
  cases input.authoritativeSpiroCenterDescriptor? carrierFuel ruleFuel semantics
      center carrier judged <;> simp

/-- Public zero-or-one family list for the recognized tetrahedral spiro center. -/
noncomputable def authoritativeSpiroCenterAssignments
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    List AuthoritativeSpiroCenterDescriptorAssignment :=
  (input.authoritativeSpiroCenterDescriptor? carrierFuel ruleFuel semantics
    center carrier judged).toList

theorem mem_authoritativeSpiroCenterAssignments_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment)
    (ready :
      let tetraCenter :=
        input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
      let source := input.certified.input
      let target := source.aromaticCanonicalFinalOccurrence carrierFuel tetraCenter
      let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
      let view := source.aromaticCanonicalDependencyView state target
      input.AuthoritativeSpiroRule3Through6KeyMatrixReady
        carrierFuel ruleFuel tetraCenter view) :
    assignment ∈ input.authoritativeSpiroCenterAssignments carrierFuel ruleFuel semantics
        center carrier judged ↔
      input.AuthoritativeSpiroCenterDescriptorJudgment carrierFuel ruleFuel semantics
        center carrier judged assignment := by
  rw [authoritativeSpiroCenterAssignments, Option.mem_toList,
    input.authoritativeSpiroCenterDescriptor?_eq_some_iff
      carrierFuel ruleFuel semantics center carrier judged assignment ready]

theorem authoritativeSpiroCenterAssignments_nodup
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    (input.authoritativeSpiroCenterAssignments carrierFuel ruleFuel semantics
      center carrier judged).Nodup := by
  unfold authoritativeSpiroCenterAssignments
  cases input.authoritativeSpiroCenterDescriptor? carrierFuel ruleFuel semantics
      center carrier judged <;> simp

/-- Every successfully emitted final spiro-center assignment occurs literally once. -/
theorem authoritativeSpiroCenterAssignments_count_eq_one_of_success
    (input : CertifiedLocalizedCIPInput) (carrierFuel ruleFuel : Nat)
    (semantics : input.certified.input.AromaticCanonicalRuleSemantics carrierFuel)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (assignment : AuthoritativeSpiroCenterDescriptorAssignment)
    (computed : input.authoritativeSpiroCenterDescriptor? carrierFuel ruleFuel semantics
      center carrier judged = some assignment) :
    (input.authoritativeSpiroCenterAssignments carrierFuel ruleFuel semantics
      center carrier judged).count assignment = 1 := by
  simp [authoritativeSpiroCenterAssignments, computed]

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
