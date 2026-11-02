import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondEndpointRule3Through5
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through5

set_option autoImplicit false

/-!
# A safe Rule-3 constitutional-reference boundary diagnostic

The predecessor round tried to repair the Rule-3 geometry-readiness gap by re-reading a
missing constitutional reference as the structural nonunit `some none` at the node compiler
(`aromaticCanonicalRule3SpatialNodeClassified?`).  That repair was rejected, and correctly so:
`aromaticCanonicalRule3ConstitutionalSeniorReference? = none` can record failure to compile the represented frame or absence of a strict senior
after successful compilation. Neither case establishes chemical non-stereogenicity.
IUPAC Rules 4a--5 may still separate such constitutionally tied ligands -- this is exactly
pseudoasymmetry -- so "no constitutional senior reference" must **never** be read as "the endpoint
is chemically non-stereogenic".  The separate theorem for the authoritative through-Rule-5 endpoint comparator
shows coexistence of compiled Rule-3 spatial-key ties and later-rule distinctions
(`compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5_pseudo_decides_later`, reusing the
existing `..._pseudo_implies_rule3_eq`).

This module therefore does **not** change the executable and does **not** re-classify anything.  It
adds a *tri-state* diagnostic that refines the existing total option selector without collapsing the
chemically incompatible cases:

* `available reference` -- a unique strict Rules-1a--2 senior reference exists;
* `absent` -- the represented Rules-1a--2 frame compiled exhaustively, but no represented
  neighbour strictly outranks all distinct others (absence of a strict represented constitutional senior; the frame may be empty);
* `unresolved` -- some represented neighbour's complete Rules-1a--2 branch key was refused
  (genuine missing evidence).

The refinement is total and failure-preserving: `boundary?.toOption` is definitionally the legacy
`aromaticCanonicalRule3ConstitutionalSeniorReference?`, so the diagnostic never invents a positive
result and never consumes the old refusal.  `absent` and `unresolved` are distinct, and `absent`
certifies that the represented frame is *complete* -- a downstream consumer can retain this distinction while seeking separately valid later-rule keys.
This diagnostic does not supply Rule-3 geometry readiness or those keys.  Nothing here claims a
full Rule-3 resolution or a stereogenicity classification.
-/

namespace TetraStereo.UniversalProof.Rule3ConstitutionalReferenceBoundaryProofs

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open CertifiedLocalizedCIPInput

/-- Safe three-way boundary at one ordinary-double-bond endpoint, refining the total option
`aromaticCanonicalRule3ConstitutionalSeniorReference?`.

`absent` is an *epistemic* statement about the represented Rules-1a--2 frame only.  It carries no
hydrogen-count and no stereogenicity information: it is produced both by an empty represented
neighbour list and by a non-empty constitutionally tied frame, and Rules 4a--5 may still resolve a
later-rule (possibly pseudoasymmetric) distinction. -/
inductive AromaticCanonicalRule3ConstitutionalReferenceBoundary
    (source : AuthoritativeChemicalInput) : Type where
  /-- A unique strict constitutional (Rules 1a--2) senior reference among the represented
  non-partner neighbours. -/
  | available (reference : source.AromaticCanonicalAtom)
  /-- The represented frame compiled exhaustively, but no represented neighbour strictly outranks
  every distinct represented competitor.  This is absence of a strict represented senior, **not** a
  non-stereogenicity claim; the represented frame can be empty. -/
  | absent
  /-- Some represented neighbour's complete Rules-1a--2 branch key was refused: genuine missing
  evidence. -/
  | unresolved

namespace AromaticCanonicalRule3ConstitutionalReferenceBoundary

/-- Forget the two refusal reasons, recovering exactly the observable result of the legacy option
selector.  This is the refinement projection onto the existing API. -/
def toOption {source : AuthoritativeChemicalInput} :
    AromaticCanonicalRule3ConstitutionalReferenceBoundary source →
      Option source.AromaticCanonicalAtom
  | .available reference => some reference
  | .absent => none
  | .unresolved => none

@[simp] theorem toOption_available {source : AuthoritativeChemicalInput}
    (reference : source.AromaticCanonicalAtom) :
    (available reference).toOption = some reference := rfl

@[simp] theorem toOption_absent {source : AuthoritativeChemicalInput} :
    (absent (source := source)).toOption = none := rfl

@[simp] theorem toOption_unresolved {source : AuthoritativeChemicalInput} :
    (unresolved (source := source)).toOption = none := rfl

/-- `toOption` hits `some reference` exactly at the `available` value: the diagnostic cannot emit a
positive result the underlying selector would not have emitted. -/
theorem toOption_eq_some_iff {source : AuthoritativeChemicalInput}
    (boundary : AromaticCanonicalRule3ConstitutionalReferenceBoundary source)
    (reference : source.AromaticCanonicalAtom) :
    boundary.toOption = some reference ↔ boundary = .available reference := by
  cases boundary with
  | available represented =>
      simp only [toOption_available]
      constructor <;> intro equality <;> injection equality with injected <;> rw [injected]
  | absent => simp [toOption_absent]
  | unresolved => simp [toOption_unresolved]

/-- The diagnostic refuses (`toOption = none`) exactly in the two refusal values, never at
`available`. -/
theorem toOption_eq_none_iff {source : AuthoritativeChemicalInput}
    (boundary : AromaticCanonicalRule3ConstitutionalReferenceBoundary source) :
    boundary.toOption = none ↔ boundary = .absent ∨ boundary = .unresolved := by
  cases boundary with
  | available reference => simp [toOption_available]
  | absent => simp [toOption_absent]
  | unresolved => simp [toOption_unresolved]

end AromaticCanonicalRule3ConstitutionalReferenceBoundary

/-- Three-way semantic diagnostic (noncomputable, like the legacy selector).  It mirrors `aromaticCanonicalRule3ConstitutionalSeniorReference?`
step for step -- the same represented substituent list, the same per-branch key compilation, and
the same strict-maximum search -- but reports a compiled frame without a strict represented senior (`absent`) separately from a
refused comparison (`unresolved`). -/
noncomputable def aromaticCanonicalRule3ConstitutionalReferenceBoundary?
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    AromaticCanonicalRule3ConstitutionalReferenceBoundary source :=
  match (source.aromaticCanonicalRule3Substituents endpoint partner).mapM
      (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) with
  | none => .unresolved
  | some ranked =>
      match ranked.find? (fun candidate =>
          source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked) with
      | some senior => .available senior.atom
      | none => .absent

/-- **Refinement and failure preservation.**  Collapsing the diagnostic back to an option is
observationally equal to the legacy selector: the diagnostic adds information without changing the
observable success/failure boundary. -/
theorem aromaticCanonicalRule3ConstitutionalReferenceBoundary?_toOption
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    (aromaticCanonicalRule3ConstitutionalReferenceBoundary? source endpoint partner).toOption =
      source.aromaticCanonicalRule3ConstitutionalSeniorReference? endpoint partner := by
  classical
  unfold aromaticCanonicalRule3ConstitutionalReferenceBoundary?
    aromaticCanonicalRule3ConstitutionalSeniorReference?
  let candidates := source.aromaticCanonicalRule3Substituents endpoint partner
  cases rankedComputed : candidates.mapM
      (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) with
  | none =>
      simp [candidates, rankedComputed,
        AromaticCanonicalRule3ConstitutionalReferenceBoundary.toOption]
  | some ranked =>
      cases seniorComputed : ranked.find? (fun candidate =>
          source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked) with
      | none =>
          simp [candidates, rankedComputed, seniorComputed,
            AromaticCanonicalRule3ConstitutionalReferenceBoundary.toOption]
      | some senior =>
          simp [candidates, rankedComputed, seniorComputed,
            AromaticCanonicalRule3ConstitutionalReferenceBoundary.toOption]

/-- The boundary is `available reference` exactly when the legacy selector emits `some reference`. -/
theorem aromaticCanonicalRule3ConstitutionalReferenceBoundary?_eq_available_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (reference : source.AromaticCanonicalAtom) :
    aromaticCanonicalRule3ConstitutionalReferenceBoundary? source endpoint partner =
        .available reference ↔
      source.aromaticCanonicalRule3ConstitutionalSeniorReference? endpoint partner =
        some reference := by
  rw [← aromaticCanonicalRule3ConstitutionalReferenceBoundary?_toOption source endpoint partner]
  exact (AromaticCanonicalRule3ConstitutionalReferenceBoundary.toOption_eq_some_iff
    (aromaticCanonicalRule3ConstitutionalReferenceBoundary? source endpoint partner) reference).symm

/-- `unresolved` is exactly a refused represented branch comparison: genuine missing evidence. -/
theorem aromaticCanonicalRule3ConstitutionalReferenceBoundary?_eq_unresolved_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    aromaticCanonicalRule3ConstitutionalReferenceBoundary? source endpoint partner =
        .unresolved ↔
      (source.aromaticCanonicalRule3Substituents endpoint partner).mapM
        (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) = none := by
  classical
  unfold aromaticCanonicalRule3ConstitutionalReferenceBoundary?
  cases (source.aromaticCanonicalRule3Substituents endpoint partner).mapM
      (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) with
  | none => simp
  | some ranked =>
      cases seniorComputed : ranked.find? (fun candidate =>
          source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked) with
      | none => simp [seniorComputed]
      | some senior => simp [seniorComputed]

/-- `absent` is exactly a fully compiled represented frame with no strict maximum: absence of a strict represented senior after successful compilation, not a refusal. -/
theorem aromaticCanonicalRule3ConstitutionalReferenceBoundary?_eq_absent_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    aromaticCanonicalRule3ConstitutionalReferenceBoundary? source endpoint partner = .absent ↔
      ∃ ranked, (source.aromaticCanonicalRule3Substituents endpoint partner).mapM
            (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) = some ranked ∧
          ranked.find? (fun candidate =>
            source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked) = none := by
  classical
  unfold aromaticCanonicalRule3ConstitutionalReferenceBoundary?
  cases (source.aromaticCanonicalRule3Substituents endpoint partner).mapM
      (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) with
  | none => simp
  | some ranked =>
      simp only [Option.some.injEq]
      cases seniorComputed : ranked.find? (fun candidate =>
          source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked) with
      | none =>
          constructor
          · intro _
            exact ⟨ranked, rfl, seniorComputed⟩
          · intro _
            rfl
      | some senior =>
          constructor
          · intro impossible
            cases impossible
          · rintro ⟨other, equality, notFound⟩
            subst other
            rw [seniorComputed] at notFound
            cases notFound

/-- **Constructive usability.**  `absent` certifies that the represented Rules-1a--2 frame is
*complete*: every represented branch key compiled.  Continuing into Rules 4a--5 requires separately valid later-rule keys; this theorem proves only
successful represented-key compilation, not geometry readiness. -/
theorem aromaticCanonicalRule3ConstitutionalReferenceBoundary?_absent_frame_complete
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (absent : aromaticCanonicalRule3ConstitutionalReferenceBoundary? source endpoint partner =
      .absent) :
    ∃ ranked, (source.aromaticCanonicalRule3Substituents endpoint partner).mapM
        (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) = some ranked := by
  obtain ⟨ranked, computed, _⟩ :=
    (aromaticCanonicalRule3ConstitutionalReferenceBoundary?_eq_absent_iff source
      endpoint partner).mp absent
  exact ⟨ranked, computed⟩

/-- `unresolved` conversely certifies an *incomplete* represented frame: genuine missing
evidence, distinct from a tie. -/
theorem aromaticCanonicalRule3ConstitutionalReferenceBoundary?_unresolved_frame_incomplete
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (unresolved : aromaticCanonicalRule3ConstitutionalReferenceBoundary? source endpoint partner =
      .unresolved) :
    (source.aromaticCanonicalRule3Substituents endpoint partner).mapM
      (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) = none :=
  (aromaticCanonicalRule3ConstitutionalReferenceBoundary?_eq_unresolved_iff source
    endpoint partner).mp unresolved

/-- The diagnostic never conflates absence of a strict represented senior with failed branch evaluation. -/
theorem aromaticCanonicalRule3ConstitutionalReferenceBoundary?_absent_ne_unresolved
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (absent : aromaticCanonicalRule3ConstitutionalReferenceBoundary? source endpoint partner =
      .absent) :
    aromaticCanonicalRule3ConstitutionalReferenceBoundary? source endpoint partner ≠
      .unresolved := by
  rw [absent]
  intro equality
  cases equality


theorem aromaticCanonicalRule3ConstitutionalReferenceBoundary?_eq_absent_of_substituents_eq_nil
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (empty : source.aromaticCanonicalRule3Substituents endpoint partner = []) :
    aromaticCanonicalRule3ConstitutionalReferenceBoundary? source endpoint partner = .absent := by
  classical
  unfold aromaticCanonicalRule3ConstitutionalReferenceBoundary?
  rw [empty, List.mapM_nil]
  rfl

/-- Emptiness of the represented neighbour list means exactly "no represented adjacency other than
the partner".  It is a statement about the represented source graph and says **nothing** about
implicit/virtual hydrogens: an empty list neither establishes `CH2` nor excludes a heavier tied
endpoint. -/
theorem aromaticCanonicalRule3Substituents_eq_nil_iff_no_represented_neighbor
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    source.aromaticCanonicalRule3Substituents endpoint partner = [] ↔
      ∀ substituent : source.AromaticCanonicalAtom,
        ¬ (source.AromaticCanonicalAdjacent endpoint substituent ∧ substituent ≠ partner) := by
  simp [List.eq_nil_iff_forall_not_mem]

/-- A refused constitutional reference at either endpoint is exactly what makes the legacy spatial
unit evaluator refuse an otherwise ordinary double bond.  This pins the evidence the diagnostic
*adds*: the old `none` does not distinguish a tie from a refusal, and neither is a chemical
non-stereogenicity claim. -/
theorem aromaticCanonicalRule3SpatialUnit?_eq_none_of_seniorReference?_eq_none
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom)
    (ordinary : source.AromaticCanonicalOrdinaryDoubleBond left right)
    (refused : source.aromaticCanonicalRule3ConstitutionalSeniorReference? left right = none) :
    source.aromaticCanonicalRule3SpatialUnit? left right = none := by
  classical
  unfold aromaticCanonicalRule3SpatialUnit?
  rw [if_pos ordinary]
  simp [refused]

/-- Rule 5 is consulted only after the complete physical Rule-4b/4c key ties.  When its
enantiomorphic bit is set, the comparison is decided by the common-reference readings -- so the
ordering is never `eq`. -/
theorem compareAromaticCanonicalRerootCompoundThroughRule5_pseudo_implies_ordering_ne_eq
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (pseudo : (source.compareAromaticCanonicalRerootCompoundThroughRule5 left right).pseudo =
      true) :
    (source.compareAromaticCanonicalRerootCompoundThroughRule5 left right).ordering ≠
      Ordering.eq := by
  unfold compareAromaticCanonicalRerootCompoundThroughRule5 at pseudo ⊢
  generalize priorEq : source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      left.prior right.prior = prior at pseudo ⊢
  cases prior with
  | lt => simp at pseudo ⊢
  | gt => simp at pseudo ⊢
  | eq =>
      generalize readingsEq : source.compareAromaticCanonicalRerootCompoundRule5Readings
          RS.R left.rule5Readings right.rule5Readings = cmpR at pseudo ⊢
      cases cmpR with
      | lt => simp at pseudo ⊢
      | gt => simp at pseudo ⊢
      | eq =>
          simp only at pseudo ⊢
          exact absurd pseudo (by decide)

/-- **Coexistence (safety) theorem.**  A positive enantiomorphic (`pseudoasymmetric`) Rule-5
outcome coexists with a complete Rule-3 tie: the existing
`compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5_pseudo_implies_rule3_eq` gives the
Rule-3 spatial-key tie, and the enantiomorphic bit forces the comparator's ordering to be decided
(`lt` or `gt`) by Rules 4a--5.

This theorem concerns compiled Rule-3 spatial keys and later comparator outcomes. It does not
prove that a spatial-key tie implies constitutional reference absence at an endpoint, or exhibit
a concrete molecule with that diagnostic. No such bridge is assumed here. -/
theorem compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5_pseudo_decides_later
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalOccurrenceRule3Through5Key)
    (pseudo : (source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
      left right).pseudo = true) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys left.rule3 right.rule3 =
        Ordering.eq ∧
      (source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
        left right).ordering ≠ Ordering.eq := by
  refine ⟨source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5_pseudo_implies_rule3_eq
    left right pseudo, ?_⟩
  unfold compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5 at pseudo ⊢
  generalize rule3Eq : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      left.rule3 right.rule3 = outcome at pseudo ⊢
  cases outcome with
  | lt => simp at pseudo ⊢
  | gt => simp at pseudo ⊢
  | eq =>
      exact compareAromaticCanonicalRerootCompoundThroughRule5_pseudo_implies_ordering_ne_eq source
        left.rule45 right.rule45 pseudo

end TetraStereo.UniversalProof.Rule3ConstitutionalReferenceBoundaryProofs
