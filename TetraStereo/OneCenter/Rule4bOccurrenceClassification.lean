import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo
namespace OneCenter

/-!
# Honest occurrence chirality classification for Rule-4b reference selection

This module supplies the missing evidence boundary between

* `OccurrenceAuxState.factAt?`, which returns `Option OccurrenceAuxFact` and therefore cannot
  distinguish "the authoritative dependency prefix failed to establish this occurrence" from
  "there is no relevant auxiliary label at this occurrence", and
* the typed Rule-4b reference-selection interface, which needs to distinguish an uppercase chiral
  occurrence, an occurrence that is known not to contribute an uppercase chiral descriptor, and an
  occurrence about which no source conclusion exists.

The central object is the tri-state resolver `occurrenceAuxiliaryEvidence?`:

* `some (some fact)` -- a *recorded* occurrence-keyed auxiliary fact for a real-atom occurrence.
  This is a lookup, not a validation: `factAt?` matches only the occurrence key and does not
  certify the fact's derivation, molecule, dependency prefix, or even its `atom` field;
* `some none` -- independently established *non-bearing* status, obtained here only through the
  structural route: canonical duplicate/phantom nodes (`provenance ≠ realAtom`) are not physical
  stereogenic units and never carry a relevant uppercase label;
* `none` -- unavailable.  In particular a real-atom occurrence whose key is absent from the state
  is `none`; annotation absence is not converted into a nonchirality verdict.

`occurrenceChiralityClassification?` then returns the requested `Option (Option RS)`:

* `none` -- unavailable (fuel / dependency / ranking refusal);
* `some none` -- known not to contribute an uppercase chiral descriptor (structural non-bearing or
  an actual lowercase pseudoasymmetric fact);
* `some (some d)` -- an actual uppercase chiral descriptor `d`.

The word "known nonchiral" in this module always means *known not to contribute an uppercase
chiral descriptor in the Rule-4b reference domain*.  It is not a claim of chemical achirality and
is not derived from the absence of an `@`/`@@` annotation alone.

Section 9 records the evaluator's structural prerequisites: a missing atom specification, a missing
tetrahedral annotation, or a missing four-ligand occurrence frame.  These are proved to force
`occurrenceFact? = none` at every fuel and state.  That fact is *evaluator unproductivity*, not a
chemical nonstereogenicity result: failed perception is not absence.  Consequently the
selector-facing classifier keeps every such real occurrence `unavailable`.  The only route to
`knownNonchiral` remains non-real provenance, an independent structural fact about canonical
duplicate/phantom nodes.

A second, legacy-path classifier (`occurrenceLegacyStatus`) keeps a *completed ranking tie*
distinct from both a successful fact and an operational refusal, using `legacyOccurrenceFact?` and
the actual `sortOccurrencesTracked?` / `compareOccurrenceAdjacentPairs?` computations.  The
distinction is justified by `legacyOccurrenceFact?_eq_none_of_rankingTie?`, not assumed.  A
completed legacy tie is nevertheless mapped to `unavailable` for Rule-4b selection: the legacy
comparison omits cursor-aware Rule 3 and treats missing occurrence facts as 0, so it is not
evidence of non-bearing status in the complete pre-Rule-4b ordering.

Rule-4a classes are preserved: `OccurrenceChiralityClass.rule4aKind` maps uppercase facts to
`OfficialStereogenicUnitKind.chiral`, lowercase facts to `pseudoasymmetric`, structural
non-bearing occurrences to `nonstereogenic`, and refusals to `none`, matching
`branchRule4aSequence`.

The complete pre-Rule-4b ordering (constitution, then applicable Rule 3, then Rule 4a) is *not*
defined here.  The raw production `CanonicalRerootCursor` has no cursor-aware Rule-3 producer in
the current source, and constructing one from the center/ligand-only
`CanonicalRule3Hierarchy.buildCanonicalRule3Key?` would silently change the previous-cut /
exclusion context.  That adapter remains an explicit integration obligation; this module makes no
claim of Rules 1--4a completeness for `compareCursorBranchAt` alone.
-/

/-! ## 1. Typed classification -/

/-- The Rule-4b-relevant reading of one occurrence.

* `uppercaseChiral d` -- the occurrence carries an actual uppercase auxiliary descriptor `d`.  Only
  this constructor can contribute a Rule-4b reference.
* `pseudoasymmetric d` -- the occurrence carries an actual lowercase auxiliary descriptor `d`.
  It is a genuine Rule-4a `pseudoasymmetric` unit but contributes no uppercase reference.
* `knownNonchiral` -- the occurrence is structurally non-bearing (a canonical phantom or
  duplicate node).  This is *not* a claim that the physical atom is achiral.
* `unavailable` -- no source conclusion exists. -/
inductive OccurrenceChiralityClass (Descriptor : Type) where
  | uppercaseChiral (descriptor : Descriptor)
  | pseudoasymmetric (descriptor : Descriptor)
  | knownNonchiral
  | unavailable
deriving DecidableEq, Repr

namespace OccurrenceChiralityClass

variable {Descriptor : Type}

/-- The requested three-way `Option (Option Descriptor)` projection.

`uppercaseChiral d ↦ some (some d)`, both non-uppercase certainties `↦ some none`, and refusal
`↦ none`.  The pseudoasymmetric distinction is retained in `OccurrenceChiralityClass` and in
`rule4aKind`, but deliberately collapses in this projection because a lowercase unit contributes
no uppercase Rule-4b reference. -/
def toOptionOption : OccurrenceChiralityClass Descriptor → Option (Option Descriptor)
  | uppercaseChiral descriptor => some (some descriptor)
  | pseudoasymmetric _ => some none
  | knownNonchiral => some none
  | unavailable => none

@[simp] theorem toOptionOption_uppercaseChiral (descriptor : Descriptor) :
    toOptionOption (uppercaseChiral descriptor) = some (some descriptor) := rfl

@[simp] theorem toOptionOption_pseudoasymmetric (descriptor : Descriptor) :
    toOptionOption (pseudoasymmetric descriptor) = some none := rfl

@[simp] theorem toOptionOption_knownNonchiral :
    toOptionOption (knownNonchiral : OccurrenceChiralityClass Descriptor) = some none := rfl

@[simp] theorem toOptionOption_unavailable :
    toOptionOption (unavailable : OccurrenceChiralityClass Descriptor) = none := rfl

theorem toOptionOption_eq_none_iff (value : OccurrenceChiralityClass Descriptor) :
    toOptionOption value = none ↔ value = unavailable := by
  cases value <;> simp [toOptionOption]

theorem toOptionOption_eq_some_some_iff (value : OccurrenceChiralityClass Descriptor)
    (descriptor : Descriptor) :
    toOptionOption value = some (some descriptor) ↔ value = uppercaseChiral descriptor := by
  cases value <;> simp [toOptionOption]

theorem toOptionOption_eq_some_none_iff (value : OccurrenceChiralityClass Descriptor) :
    toOptionOption value = some none ↔
      (∃ descriptor, value = pseudoasymmetric descriptor) ∨ value = knownNonchiral := by
  cases value <;> simp [toOptionOption]

/-- Rule-4a class of a classification.  This is the effective `branchRule4aSequence` class of the
classified occurrence: `chiral`, `pseudoasymmetric`, or `nonstereogenic`; a refusal has no class. -/
def rule4aKind :
    OccurrenceChiralityClass Descriptor → Option OfficialStereogenicUnitKind
  | uppercaseChiral _ => some OfficialStereogenicUnitKind.chiral
  | pseudoasymmetric _ => some OfficialStereogenicUnitKind.pseudoasymmetric
  | knownNonchiral => some OfficialStereogenicUnitKind.nonstereogenic
  | unavailable => none

@[simp] theorem rule4aKind_uppercaseChiral (descriptor : Descriptor) :
    rule4aKind (uppercaseChiral descriptor) = some OfficialStereogenicUnitKind.chiral := rfl

@[simp] theorem rule4aKind_pseudoasymmetric (descriptor : Descriptor) :
    rule4aKind (pseudoasymmetric descriptor) =
      some OfficialStereogenicUnitKind.pseudoasymmetric := rfl

@[simp] theorem rule4aKind_knownNonchiral :
    rule4aKind (knownNonchiral : OccurrenceChiralityClass Descriptor) =
      some OfficialStereogenicUnitKind.nonstereogenic := rfl

@[simp] theorem rule4aKind_unavailable :
    rule4aKind (unavailable : OccurrenceChiralityClass Descriptor) = none := rfl

theorem rule4aKind_eq_some_chiral_iff (value : OccurrenceChiralityClass Descriptor) :
    rule4aKind value = some OfficialStereogenicUnitKind.chiral ↔
      ∃ descriptor, value = uppercaseChiral descriptor := by
  cases value <;> simp [rule4aKind]

end OccurrenceChiralityClass

/-! ## 2. Tri-state auxiliary evidence -/

/-- Honest tri-state auxiliary evidence for one occurrence.

* `some (some fact)` -- `cursor.node` is a real-atom occurrence and the state carries its
  occurrence-keyed fact.
* `some none` -- structural non-bearing route.  The node is a canonical phantom or
  multiple-bond/ring duplicate (`provenance ≠ realAtom`), hence cannot be a physical stereogenic
  unit and cannot carry a relevant uppercase label.  A fact of a non-real node is deliberately
  ignored: the structural route dominates.
* `none` -- unavailable.  For a real-atom occurrence this is exactly `factAt? = none`.  The state
  does not record whether that absence came from a failed/incomplete authoritative prefix or from
  a checked non-bearing result, so the honest reading is refusal.

This is the resolver missing from `OccurrenceAuxState.factAt?`: the latter collapses `some none`
and `none`.

The positive case is deliberately stated as *recorded*, not *validated*.  `factAt?`
(`SmilesTetrahedral.lean:1708–1710`) matches `fact.key == canonicalOccurrenceKey node` only.  It
does not check that the fact was derived from this molecule, that its dependency prefix succeeded,
or that `fact.atom` equals the node's atom.  A soundness bridge from a particular builder to such
facts is a separate obligation; no theorem below claims it. -/
def occurrenceAuxiliaryEvidence? (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) : Option (Option OccurrenceAuxFact) :=
  match cursor.node.provenance with
  | RawMolecule.CanonicalNodeProvenance.realAtom =>
      match state.factAt? cursor.node with
      | some fact => some (some fact)
      | none => none
  | _ => some none

/-- Positive evidence is exactly a real-atom occurrence with a matching occurrence-keyed fact. -/
theorem occurrenceAuxiliaryEvidence?_eq_some_some_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (fact : OccurrenceAuxFact) :
    occurrenceAuxiliaryEvidence? state cursor = some (some fact) ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        state.factAt? cursor.node = some fact := by
  unfold occurrenceAuxiliaryEvidence?
  cases hProvenance : cursor.node.provenance with
  | realAtom =>
      cases hLookup : state.factAt? cursor.node with
      | none => simp [hProvenance, hLookup]
      | some other => simp [hProvenance, hLookup]
  | multipleBondDuplicate distance => simp [hProvenance]
  | ringDuplicate distance => simp [hProvenance]
  | phantom distance => simp [hProvenance]

/-- Structural non-bearing is exactly non-real provenance. -/
theorem occurrenceAuxiliaryEvidence?_eq_some_none_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceAuxiliaryEvidence? state cursor = some none ↔
      cursor.node.provenance ≠ RawMolecule.CanonicalNodeProvenance.realAtom := by
  unfold occurrenceAuxiliaryEvidence?
  cases hProvenance : cursor.node.provenance with
  | realAtom =>
      cases hLookup : state.factAt? cursor.node with
      | none => simp [hProvenance, hLookup]
      | some fact => simp [hProvenance, hLookup]
  | multipleBondDuplicate distance => simp [hProvenance]
  | ringDuplicate distance => simp [hProvenance]
  | phantom distance => simp [hProvenance]

/-- Unavailability is exactly a real-atom occurrence absent from the state. -/
theorem occurrenceAuxiliaryEvidence?_eq_none_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceAuxiliaryEvidence? state cursor = none ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        state.factAt? cursor.node = none := by
  unfold occurrenceAuxiliaryEvidence?
  cases hProvenance : cursor.node.provenance with
  | realAtom =>
      cases hLookup : state.factAt? cursor.node with
      | none => simp [hProvenance, hLookup]
      | some fact => simp [hProvenance, hLookup]
  | multipleBondDuplicate distance => simp [hProvenance]
  | ringDuplicate distance => simp [hProvenance]
  | phantom distance => simp [hProvenance]

/-- A real-atom occurrence with a state fact has positive evidence. -/
theorem occurrenceAuxiliaryEvidence?_eq_some_some_of_lookup
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (fact : OccurrenceAuxFact)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (hLookup : state.factAt? cursor.node = some fact) :
    occurrenceAuxiliaryEvidence? state cursor = some (some fact) :=
  (occurrenceAuxiliaryEvidence?_eq_some_some_iff state cursor fact).mpr
    ⟨hProvenance, hLookup⟩

/-! ## 3. Classification from honest evidence -/

/-- Turn the tri-state evidence into the typed classification.  No case invents source facts:
`some none` comes only from structural non-bearing or a real lowercase fact, and `none` is
propagated unchanged. -/
def occurrenceClassOfEvidence :
    Option (Option OccurrenceAuxFact) → OccurrenceChiralityClass RS
  | none => .unavailable
  | some none => .knownNonchiral
  | some (some fact) =>
      if fact.uppercase then .uppercaseChiral fact.descriptor
      else .pseudoasymmetric fact.descriptor

/-- Classify one occurrence from the occurrence-keyed auxiliary evidence. -/
def occurrenceChiralityClass (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) : OccurrenceChiralityClass RS :=
  occurrenceClassOfEvidence (occurrenceAuxiliaryEvidence? state cursor)

/-- **Positive classification uses an actual source fact.**  An `uppercaseChiral` verdict is
possible only from a real-atom occurrence whose state fact is uppercase. -/
theorem occurrenceChiralityClass_eq_uppercaseChiral_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) (descriptor : RS) :
    occurrenceChiralityClass state cursor = .uppercaseChiral descriptor ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        ∃ fact, state.factAt? cursor.node = some fact ∧
          fact.uppercase = true ∧ fact.descriptor = descriptor := by
  unfold occurrenceChiralityClass occurrenceClassOfEvidence
  cases hEvidence : occurrenceAuxiliaryEvidence? state cursor with
  | none =>
      have hNone := (occurrenceAuxiliaryEvidence?_eq_none_iff state cursor).mp hEvidence
      simp [hNone.2]
  | some inner =>
      cases inner with
      | none =>
          have hNonReal :=
            (occurrenceAuxiliaryEvidence?_eq_some_none_iff state cursor).mp hEvidence
          simp [hNonReal]
      | some fact =>
          have hSome :=
            (occurrenceAuxiliaryEvidence?_eq_some_some_iff state cursor fact).mp hEvidence
          cases hUpper : fact.uppercase
          · simp [hSome.1, hSome.2, hUpper]
          · simp [hSome.1, hSome.2, hUpper]

/-- A `pseudoasymmetric` verdict is possible only from a real-atom occurrence whose state fact is
lowercase. -/
theorem occurrenceChiralityClass_eq_pseudoasymmetric_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) (descriptor : RS) :
    occurrenceChiralityClass state cursor = .pseudoasymmetric descriptor ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        ∃ fact, state.factAt? cursor.node = some fact ∧
          fact.uppercase = false ∧ fact.descriptor = descriptor := by
  unfold occurrenceChiralityClass occurrenceClassOfEvidence
  cases hEvidence : occurrenceAuxiliaryEvidence? state cursor with
  | none =>
      have hNone := (occurrenceAuxiliaryEvidence?_eq_none_iff state cursor).mp hEvidence
      simp [hNone.2]
  | some inner =>
      cases inner with
      | none =>
          have hNonReal :=
            (occurrenceAuxiliaryEvidence?_eq_some_none_iff state cursor).mp hEvidence
          simp [hNonReal]
      | some fact =>
          have hSome :=
            (occurrenceAuxiliaryEvidence?_eq_some_some_iff state cursor fact).mp hEvidence
          cases hUpper : fact.uppercase
          · simp [hSome.1, hSome.2, hUpper]
          · simp [hSome.1, hSome.2, hUpper]

/-- **Structural non-bearing is the only route to `knownNonchiral` in the auxiliary-state
classifier.**  In particular `state.factAt? cursor.node = none` at a real node never produces
`knownNonchiral`; it produces `unavailable`. -/
theorem occurrenceChiralityClass_eq_knownNonchiral_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceChiralityClass state cursor = .knownNonchiral ↔
      cursor.node.provenance ≠ RawMolecule.CanonicalNodeProvenance.realAtom := by
  unfold occurrenceChiralityClass occurrenceClassOfEvidence
  cases hEvidence : occurrenceAuxiliaryEvidence? state cursor with
  | none =>
      have hNone := (occurrenceAuxiliaryEvidence?_eq_none_iff state cursor).mp hEvidence
      simp [hNone.1]
  | some inner =>
      cases inner with
      | none =>
          have hNonReal :=
            (occurrenceAuxiliaryEvidence?_eq_some_none_iff state cursor).mp hEvidence
          simp [hNonReal]
      | some fact =>
          have hSome :=
            (occurrenceAuxiliaryEvidence?_eq_some_some_iff state cursor fact).mp hEvidence
          cases hUpper : fact.uppercase
          · simp [hSome.1, hUpper]
          · simp [hSome.1, hUpper]

/-- **Absence cannot be erased.**  A real-atom occurrence missing from the state is `unavailable`,
not `knownNonchiral`. -/
theorem occurrenceChiralityClass_eq_unavailable_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceChiralityClass state cursor = .unavailable ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        state.factAt? cursor.node = none := by
  unfold occurrenceChiralityClass occurrenceClassOfEvidence
  cases hEvidence : occurrenceAuxiliaryEvidence? state cursor with
  | none =>
      have hNone := (occurrenceAuxiliaryEvidence?_eq_none_iff state cursor).mp hEvidence
      simp [hNone.1, hNone.2]
  | some inner =>
      cases inner with
      | none =>
          have hNonReal :=
            (occurrenceAuxiliaryEvidence?_eq_some_none_iff state cursor).mp hEvidence
          simp [hNonReal]
      | some fact =>
          have hSome :=
            (occurrenceAuxiliaryEvidence?_eq_some_some_iff state cursor fact).mp hEvidence
          cases hUpper : fact.uppercase <;> simp [hSome.1, hSome.2, hUpper]

/-- Structural non-bearing gives a definite nonchiral reading. -/
theorem occurrenceChiralityClass_eq_knownNonchiral_of_nonReal
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (hNonReal : cursor.node.provenance ≠
      RawMolecule.CanonicalNodeProvenance.realAtom) :
    occurrenceChiralityClass state cursor = .knownNonchiral :=
  (occurrenceChiralityClass_eq_knownNonchiral_iff state cursor).mpr hNonReal

/-- A real-atom occurrence absent from the state is unavailable. -/
theorem occurrenceChiralityClass_eq_unavailable_of_missing
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none) :
    occurrenceChiralityClass state cursor = .unavailable :=
  (occurrenceChiralityClass_eq_unavailable_iff state cursor).mpr
    ⟨hProvenance, hMissing⟩

/-! ## 4. The requested `Option (Option RS)` classification -/

/-- The typed three-way classification requested by the Rule-4b selection interface. -/
def occurrenceChiralityClassification? (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) : Option (Option RS) :=
  OccurrenceChiralityClass.toOptionOption (occurrenceChiralityClass state cursor)

theorem occurrenceChiralityClassification?_eq_some_some_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) (descriptor : RS) :
    occurrenceChiralityClassification? state cursor = some (some descriptor) ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        ∃ fact, state.factAt? cursor.node = some fact ∧
          fact.uppercase = true ∧ fact.descriptor = descriptor := by
  unfold occurrenceChiralityClassification?
  rw [OccurrenceChiralityClass.toOptionOption_eq_some_some_iff,
    occurrenceChiralityClass_eq_uppercaseChiral_iff]

theorem occurrenceChiralityClassification?_eq_some_none_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceChiralityClassification? state cursor = some none ↔
      cursor.node.provenance ≠ RawMolecule.CanonicalNodeProvenance.realAtom ∨
        ∃ fact, cursor.node.provenance =
            RawMolecule.CanonicalNodeProvenance.realAtom ∧
          state.factAt? cursor.node = some fact ∧ fact.uppercase = false := by
  unfold occurrenceChiralityClassification?
  rw [OccurrenceChiralityClass.toOptionOption_eq_some_none_iff]
  constructor
  · rintro (⟨descriptor, hClass⟩ | hClass)
    · rcases ((occurrenceChiralityClass_eq_pseudoasymmetric_iff
          state cursor descriptor).mp hClass) with
        ⟨hProvenance, fact, hLookup, hLower, _hDescriptor⟩
      exact Or.inr ⟨fact, hProvenance, hLookup, hLower⟩
    · exact Or.inl
        ((occurrenceChiralityClass_eq_knownNonchiral_iff state cursor).mp hClass)
  · rintro (hNonReal | ⟨fact, hProvenance, hLookup, hLower⟩)
    · exact Or.inr
        ((occurrenceChiralityClass_eq_knownNonchiral_iff state cursor).mpr hNonReal)
    · exact Or.inl ⟨fact.descriptor,
        (occurrenceChiralityClass_eq_pseudoasymmetric_iff state cursor fact.descriptor).mpr
          ⟨hProvenance, fact, hLookup, hLower, rfl⟩⟩

theorem occurrenceChiralityClassification?_eq_none_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceChiralityClassification? state cursor = none ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        state.factAt? cursor.node = none := by
  unfold occurrenceChiralityClassification?
  rw [OccurrenceChiralityClass.toOptionOption_eq_none_iff,
    occurrenceChiralityClass_eq_unavailable_iff]

/-- **Absence is not a nonchirality verdict.**  A real-atom occurrence missing from the state can
never be classified `some none` by the auxiliary-state classifier. -/
theorem occurrenceChiralityClassification?_ne_some_none_of_missing
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none) :
    occurrenceChiralityClassification? state cursor ≠ some none := by
  intro hSomeNone
  have hNone : occurrenceChiralityClassification? state cursor = none :=
    (occurrenceChiralityClassification?_eq_none_iff state cursor).mpr
      ⟨hProvenance, hMissing⟩
  rw [hNone] at hSomeNone
  cases hSomeNone

/-- The uppercase descriptor selected by the classification, if any. -/
def occurrenceUppercaseDescriptor? (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) : Option RS :=
  (occurrenceChiralityClassification? state cursor).join

theorem occurrenceUppercaseDescriptor?_eq_some_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) (descriptor : RS) :
    occurrenceUppercaseDescriptor? state cursor = some descriptor ↔
      occurrenceChiralityClassification? state cursor = some (some descriptor) := by
  unfold occurrenceUppercaseDescriptor?
  cases hClassification : occurrenceChiralityClassification? state cursor with
  | none => simp
  | some inner => cases inner <;> simp

/-- **Positive uppercase classification uses an actual source fact.** -/
theorem occurrenceUppercaseDescriptor?_eq_some_iff_source
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) (descriptor : RS) :
    occurrenceUppercaseDescriptor? state cursor = some descriptor ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        ∃ fact, state.factAt? cursor.node = some fact ∧
          fact.uppercase = true ∧ fact.descriptor = descriptor := by
  rw [occurrenceUppercaseDescriptor?_eq_some_iff,
    occurrenceChiralityClassification?_eq_some_some_iff]

theorem occurrenceUppercaseDescriptor?_eq_none_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceUppercaseDescriptor? state cursor = none ↔
      occurrenceChiralityClassification? state cursor = none ∨
        occurrenceChiralityClassification? state cursor = some none := by
  unfold occurrenceUppercaseDescriptor?
  cases hClassification : occurrenceChiralityClassification? state cursor with
  | none => simp
  | some inner => cases inner <;> simp

/-! ## 5. Rule-4a class preservation -/

/-- Explicit transport of a recorded occurrence-keyed fact to the descriptor-fact shape consumed
by `branchRule4aSequence`.

`OccurrenceAuxFact` and `RawDescriptorFact` are unrelated structures, so there is no coercion.
The projection copies the descriptor-bearing fields and leaves `atom` at the recorded value: the
key-based lookup does not check it, and this conversion makes no validation claim.  Only
`uppercase` is read by `branchRule4aSequence`, and that field is preserved definitionally. -/
def occurrenceAuxFactToRawDescriptorFact (fact : OccurrenceAuxFact) : RawDescriptorFact where
  atom := fact.atom
  descriptor := fact.descriptor
  uppercase := fact.uppercase
  priorityPositions := fact.priorityPositions

@[simp] theorem occurrenceAuxFactToRawDescriptorFact_uppercase (fact : OccurrenceAuxFact) :
    (occurrenceAuxFactToRawDescriptorFact fact).uppercase = fact.uppercase := rfl

@[simp] theorem occurrenceAuxFactToRawDescriptorFact_descriptor (fact : OccurrenceAuxFact) :
    (occurrenceAuxFactToRawDescriptorFact fact).descriptor = fact.descriptor := rfl

/-- `branchRule4aSequence` on one fact is the fact's uppercase/lowercase class. -/
theorem branchRule4aSequence_singleton (fact : RawDescriptorFact) :
    branchRule4aSequence [fact] =
      [if fact.uppercase then OfficialStereogenicUnitKind.chiral
        else OfficialStereogenicUnitKind.pseudoasymmetric] := rfl

/-- An uppercase auxiliary verdict is the Rule-4a `chiral` class of its source fact. -/
theorem occurrenceChiralityClass_uppercaseChiral_rule4a
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) (descriptor : RS)
    (hClass : occurrenceChiralityClass state cursor = .uppercaseChiral descriptor) :
    ∃ fact, state.factAt? cursor.node = some fact ∧ fact.uppercase = true ∧
      branchRule4aSequence [occurrenceAuxFactToRawDescriptorFact fact] =
        [OfficialStereogenicUnitKind.chiral] := by
  rcases (occurrenceChiralityClass_eq_uppercaseChiral_iff state cursor descriptor).mp hClass with
    ⟨_hProvenance, fact, hLookup, hUpper, _hDescriptor⟩
  exact ⟨fact, hLookup, hUpper, by
    rw [branchRule4aSequence_singleton]
    simp [occurrenceAuxFactToRawDescriptorFact, hUpper]⟩

/-- A lowercase auxiliary verdict is the Rule-4a `pseudoasymmetric` class of its source fact. -/
theorem occurrenceChiralityClass_pseudoasymmetric_rule4a
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) (descriptor : RS)
    (hClass : occurrenceChiralityClass state cursor = .pseudoasymmetric descriptor) :
    ∃ fact, state.factAt? cursor.node = some fact ∧ fact.uppercase = false ∧
      branchRule4aSequence [occurrenceAuxFactToRawDescriptorFact fact] =
        [OfficialStereogenicUnitKind.pseudoasymmetric] := by
  rcases (occurrenceChiralityClass_eq_pseudoasymmetric_iff state cursor descriptor).mp hClass with
    ⟨_hProvenance, fact, hLookup, hLower, _hDescriptor⟩
  exact ⟨fact, hLookup, hLower, by
    rw [branchRule4aSequence_singleton]
    simp [occurrenceAuxFactToRawDescriptorFact, hLower]⟩

/-! ## 6. The actual occurrence descriptor computation

This section records what the production occurrence evaluator itself can and cannot conclude.  It
is deliberately weaker than the auxiliary-state classifier: `occurrenceFact? = none` conflates a
completed tie with an operational refusal, so the computation alone never yields
`knownNonchiral`. -/

/-- Classification from the actual occurrence descriptor computation.  No `knownNonchiral` case:
a refusal is always reported as `unavailable`. -/
def occurrenceComputedChiralityClass (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    OccurrenceChiralityClass RS :=
  match occurrenceFact? mol fuel state node with
  | none => .unavailable
  | some fact =>
      if fact.uppercase then .uppercaseChiral fact.descriptor
      else .pseudoasymmetric fact.descriptor

theorem occurrenceComputedChiralityClass_eq_uppercaseChiral_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (descriptor : RS) :
    occurrenceComputedChiralityClass mol fuel state node = .uppercaseChiral descriptor ↔
      ∃ fact, occurrenceFact? mol fuel state node = some fact ∧
        fact.uppercase = true ∧ fact.descriptor = descriptor := by
  unfold occurrenceComputedChiralityClass
  cases hFact : occurrenceFact? mol fuel state node with
  | none => simp [hFact]
  | some fact => cases hUpper : fact.uppercase <;> simp [hFact, hUpper]

theorem occurrenceComputedChiralityClass_eq_pseudoasymmetric_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (descriptor : RS) :
    occurrenceComputedChiralityClass mol fuel state node = .pseudoasymmetric descriptor ↔
      ∃ fact, occurrenceFact? mol fuel state node = some fact ∧
        fact.uppercase = false ∧ fact.descriptor = descriptor := by
  unfold occurrenceComputedChiralityClass
  cases hFact : occurrenceFact? mol fuel state node with
  | none => simp [hFact]
  | some fact => cases hUpper : fact.uppercase <;> simp [hFact, hUpper]

/-- The actual computation never fabricates a definitive nonchirality verdict. -/
theorem occurrenceComputedChiralityClass_ne_knownNonchiral
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) :
    occurrenceComputedChiralityClass mol fuel state node ≠ .knownNonchiral := by
  unfold occurrenceComputedChiralityClass
  cases hFact : occurrenceFact? mol fuel state node with
  | none => simp [hFact]
  | some fact => cases hUpper : fact.uppercase <;> simp [hFact, hUpper]

/-- The actual computation is unavailable exactly when `occurrenceFact?` refuses. -/
theorem occurrenceComputedChiralityClass_eq_unavailable_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) :
    occurrenceComputedChiralityClass mol fuel state node = .unavailable ↔
      occurrenceFact? mol fuel state node = none := by
  unfold occurrenceComputedChiralityClass
  cases hFact : occurrenceFact? mol fuel state node with
  | none => simp [hFact]
  | some fact => cases hUpper : fact.uppercase <;> simp [hFact, hUpper]

/-- The typed `Option (Option RS)` reading of the actual occurrence computation. -/
def occurrenceComputedChiralityClassification? (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    Option (Option RS) :=
  OccurrenceChiralityClass.toOptionOption
    (occurrenceComputedChiralityClass mol fuel state node)

theorem occurrenceComputedChiralityClassification?_eq_some_some_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (descriptor : RS) :
    occurrenceComputedChiralityClassification? mol fuel state node = some (some descriptor) ↔
      ∃ fact, occurrenceFact? mol fuel state node = some fact ∧
        fact.uppercase = true ∧ fact.descriptor = descriptor := by
  unfold occurrenceComputedChiralityClassification?
  rw [OccurrenceChiralityClass.toOptionOption_eq_some_some_iff,
    occurrenceComputedChiralityClass_eq_uppercaseChiral_iff]

/-- `some none` is exactly an actual lowercase occurrence fact. -/
theorem occurrenceComputedChiralityClassification?_eq_some_none_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) :
    occurrenceComputedChiralityClassification? mol fuel state node = some none ↔
      ∃ fact, occurrenceFact? mol fuel state node = some fact ∧
        fact.uppercase = false := by
  unfold occurrenceComputedChiralityClassification?
  rw [OccurrenceChiralityClass.toOptionOption_eq_some_none_iff]
  constructor
  · rintro (⟨descriptor, hClass⟩ | hClass)
    · rcases ((occurrenceComputedChiralityClass_eq_pseudoasymmetric_iff
          mol fuel state node descriptor).mp hClass) with
        ⟨fact, hFact, hLower, _hDescriptor⟩
      exact ⟨fact, hFact, hLower⟩
    · exact absurd hClass
        (occurrenceComputedChiralityClass_ne_knownNonchiral mol fuel state node)
  · rintro ⟨fact, hFact, hLower⟩
    exact Or.inl ⟨fact.descriptor,
      (occurrenceComputedChiralityClass_eq_pseudoasymmetric_iff
        mol fuel state node fact.descriptor).mpr ⟨fact, hFact, hLower, rfl⟩⟩

/-- `none` is exactly a refusal of the actual occurrence computation. -/
theorem occurrenceComputedChiralityClassification?_eq_none_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) :
    occurrenceComputedChiralityClassification? mol fuel state node = none ↔
      occurrenceFact? mol fuel state node = none := by
  unfold occurrenceComputedChiralityClassification?
  rw [OccurrenceChiralityClass.toOptionOption_eq_none_iff,
    occurrenceComputedChiralityClass_eq_unavailable_iff]

/-! ## 7. Definitive ties versus operational refusals (legacy path)

`occurrenceFact?` selects the framed evaluator when a generated-real-tree profile exists and the
legacy evaluator otherwise.  The following tie detector is stated for the legacy evaluator's exact
component functions.  It re-runs the same `sortOccurrencesTracked?` and
`compareOccurrenceAdjacentPairs?` calls and reports whether the completed ranking contains a tie.
The soundness direction is proved below; no tie is assumed. -/

/-- Ranking-tie status of the legacy occurrence evaluator:
* `some true` -- every dependency of `legacyOccurrenceFact?` (atom, tetrahedral parity, ligand
  frame, ranking, position lookup, adjacent decisions) completed and the ranking contains an
  adjacent `eq` decision (definitive tie);
* `some false` -- every dependency completed with no adjacent tie;
* `none` -- at least one dependency (atom/parity/frame/sort/position/adjacency) is unavailable.

The position lookup is checked here deliberately.  Without it, `some true` could coexist with a
`mapM` refusal, and the classifier would attribute the refusal to a tie that was not the actual
gate. -/
def occurrenceLegacyRankingTie? (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) : Option Bool :=
  match mol.atomAt? node.atom with
  | none => none
  | some spec =>
      match spec.tetrahedral? with
      | none => none
      | some _ =>
          match occurrenceLigandFrame? mol node with
          | none => none
          | some roots =>
              match sortOccurrencesTracked? mol state fuel roots with
              | none => none
              | some sorted =>
                  match sorted.1.mapM (fun cursor =>
                      ((mol.ligandsWithLonePair node.atom).zipIdx.find?
                        fun entry => entry.1 == cursor.node.atom).map Prod.snd) with
                  | none => none
                  | some _ =>
                      match compareOccurrenceAdjacentPairs? mol state fuel sorted.1 with
                      | none => none
                      | some compared =>
                          some (compared.any fun comparison =>
                            comparison.decision.ordering == Ordering.eq)

/-- **A completed tie is a refusal of `legacyOccurrenceFact?`.**  This is the `strict` gate in the
legacy evaluator, derived rather than assumed. -/
theorem legacyOccurrenceFact?_eq_none_of_completed_tie
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (spec : AtomSpec) (parity : TetrahedralInputParity)
    (roots : List CanonicalRerootCursor)
    (sorted : List CanonicalRerootCursor × ℕ)
    (compared : List (OccurrenceComparedPair mol state fuel)) (positions : List ℕ)
    (hAtom : mol.atomAt? node.atom = some spec)
    (hParity : spec.tetrahedral? = some parity)
    (hFrame : occurrenceLigandFrame? mol node = some roots)
    (hSorted : sortOccurrencesTracked? mol state fuel roots = some sorted)
    (hCompared : compareOccurrenceAdjacentPairs? mol state fuel sorted.1 = some compared) (hPositions : sorted.1.mapM (fun cursor => ((mol.ligandsWithLonePair node.atom).zipIdx.find? fun entry => entry.1 == cursor.node.atom).map Prod.snd) = some positions)
    (tie : ∃ comparison ∈ compared, comparison.decision.ordering = Ordering.eq) :
    legacyOccurrenceFact? mol fuel state node = none := by
  have hStrict :
      (compared.map (fun comparison => comparison.decision)).all
          (fun decision => decision.ordering != Ordering.eq) = false := by
    rw [List.all_eq_false]
    rcases tie with ⟨comparison, hMember, hOrdering⟩
    exact ⟨comparison.decision,
      List.mem_map.mpr ⟨comparison, hMember, rfl⟩, by simp [hOrdering]⟩
  simp [legacyOccurrenceFact?, hAtom, hParity, hFrame, hSorted, hPositions, hCompared,
    hStrict]
  exact tie

/-- A detected legacy ranking tie makes `legacyOccurrenceFact?` refuse. -/
theorem legacyOccurrenceFact?_eq_none_of_rankingTie?
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (hTie : occurrenceLegacyRankingTie? mol fuel state node = some true) :
    legacyOccurrenceFact? mol fuel state node = none := by
  unfold occurrenceLegacyRankingTie? at hTie
  cases hAtom : mol.atomAt? node.atom with
  | none => simp [hAtom] at hTie
  | some spec =>
      cases hParity : spec.tetrahedral? with
      | none => simp [hAtom, hParity] at hTie
      | some parity =>
          cases hFrame : occurrenceLigandFrame? mol node with
          | none => simp [hAtom, hParity, hFrame] at hTie
          | some roots =>
              cases hSorted : sortOccurrencesTracked? mol state fuel roots with
              | none => simp [hAtom, hParity, hFrame, hSorted] at hTie
              | some sorted =>
                  cases hPositions : sorted.1.mapM (fun cursor =>
                      ((mol.ligandsWithLonePair node.atom).zipIdx.find?
                        fun entry => entry.1 == cursor.node.atom).map Prod.snd) with
                  | none =>
                      simp [hAtom, hParity, hFrame, hSorted, hPositions] at hTie
                  | some positions =>
                      cases hCompared :
                          compareOccurrenceAdjacentPairs? mol state fuel sorted.1 with
                      | none =>
                          simp [hAtom, hParity, hFrame, hSorted, hPositions,
                            hCompared] at hTie
                      | some compared =>
                          have hAny :
                              (compared.any fun comparison =>
                                comparison.decision.ordering == Ordering.eq) = true := by
                            simpa [hAtom, hParity, hFrame, hSorted, hPositions,
                              hCompared] using hTie
                          rw [List.any_eq_true] at hAny
                          rcases hAny with ⟨comparison, hMember, hEqual⟩
                          exact legacyOccurrenceFact?_eq_none_of_completed_tie
                            mol fuel state node spec parity roots sorted compared positions
                            hAtom hParity hFrame hSorted hCompared hPositions
                            ⟨comparison, hMember, beq_iff_eq.mp hEqual⟩

/-- Legacy evaluator outcome, retaining a completed ranking tie as a distinct status.

* `fact value` -- the evaluator produced an occurrence fact;
* `completedRankingTie` -- every dependency of `legacyOccurrenceFact?` completed and the ranking
  contained an adjacent `Ordering.eq`, so the evaluator's `strict` gate refuses;
* `refused` -- some dependency was unavailable.

The tie is a genuine computed outcome (`legacyOccurrenceFact?_eq_none_of_rankingTie?`), but it is
not evidence of non-bearing status in the complete pre-Rule-4b ordering: the legacy comparison
omits cursor-aware Rule 3 and treats missing occurrence facts as `0`.  It is kept here only as a
diagnostic status and is never converted to `knownNonchiral`. -/
inductive OccurrenceLegacyStatus where
  | fact (value : OccurrenceAuxFact)
  | completedRankingTie
  | refused
deriving DecidableEq, Repr

/-- Evaluate the legacy occurrence computation and retain the tie/refusal distinction. -/
def occurrenceLegacyStatus (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    OccurrenceLegacyStatus :=
  match legacyOccurrenceFact? mol fuel state node with
  | some fact => .fact fact
  | none =>
      match occurrenceLegacyRankingTie? mol fuel state node with
      | some true => .completedRankingTie
      | _ => .refused

theorem occurrenceLegacyStatus_eq_fact_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (value : OccurrenceAuxFact) :
    occurrenceLegacyStatus mol fuel state node = .fact value ↔
      legacyOccurrenceFact? mol fuel state node = some value := by
  unfold occurrenceLegacyStatus
  cases hFact : legacyOccurrenceFact? mol fuel state node with
  | none =>
      cases hTie : occurrenceLegacyRankingTie? mol fuel state node with
      | none => simp [hFact, hTie]
      | some tie => cases tie <;> simp [hFact, hTie]
  | some fact =>
      constructor
      · intro h
        injection h with hEq
        subst hEq
        rfl
      · intro h
        injection h with hEq
        subst hEq
        rfl

theorem occurrenceLegacyStatus_eq_completedRankingTie_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) :
    occurrenceLegacyStatus mol fuel state node = .completedRankingTie ↔
      legacyOccurrenceFact? mol fuel state node = none ∧
        occurrenceLegacyRankingTie? mol fuel state node = some true := by
  unfold occurrenceLegacyStatus
  cases hFact : legacyOccurrenceFact? mol fuel state node with
  | none =>
      cases hTie : occurrenceLegacyRankingTie? mol fuel state node with
      | none => simp [hFact, hTie]
      | some tie => cases tie <;> simp [hFact, hTie]
  | some fact => simp [hFact]

theorem occurrenceLegacyStatus_eq_refused_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) :
    occurrenceLegacyStatus mol fuel state node = .refused ↔
      legacyOccurrenceFact? mol fuel state node = none ∧
        occurrenceLegacyRankingTie? mol fuel state node ≠ some true := by
  unfold occurrenceLegacyStatus
  cases hFact : legacyOccurrenceFact? mol fuel state node with
  | none =>
      cases hTie : occurrenceLegacyRankingTie? mol fuel state node with
      | none => simp [hFact, hTie]
      | some tie => cases tie <;> simp [hFact, hTie]
  | some fact => simp [hFact]

/-- Classify the legacy evaluator outcome for Rule-4b use.

A successful fact is uppercase/lowercase as before.  Both `completedRankingTie` and `refused` map
to `unavailable`: a completed legacy tie is not a definite non-bearing result in the complete
pre-Rule-4b ordering, so selection must not treat it as `some none`. -/
def occurrenceLegacyChiralityClass (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    OccurrenceChiralityClass RS :=
  match occurrenceLegacyStatus mol fuel state node with
  | .fact fact =>
      if fact.uppercase then .uppercaseChiral fact.descriptor
      else .pseudoasymmetric fact.descriptor
  | .completedRankingTie => .unavailable
  | .refused => .unavailable

theorem occurrenceLegacyChiralityClass_eq_uppercaseChiral_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (descriptor : RS) :
    occurrenceLegacyChiralityClass mol fuel state node = .uppercaseChiral descriptor ↔
      ∃ fact, legacyOccurrenceFact? mol fuel state node = some fact ∧
        fact.uppercase = true ∧ fact.descriptor = descriptor := by
  constructor
  · intro hClass
    unfold occurrenceLegacyChiralityClass at hClass
    cases hStatus : occurrenceLegacyStatus mol fuel state node with
    | fact fact =>
        have hFact :=
          (occurrenceLegacyStatus_eq_fact_iff mol fuel state node fact).mp hStatus
        cases hUpper : fact.uppercase with
        | true =>
            simp only [hStatus, hUpper, if_true] at hClass
            injection hClass with hDescriptor
            exact ⟨fact, hFact, hUpper, hDescriptor⟩
        | false =>
            simp only [hStatus, hUpper, if_false] at hClass
            cases hClass
    | completedRankingTie => simp [hStatus] at hClass
    | refused => simp [hStatus] at hClass
  · rintro ⟨fact, hFact, hUpper, hDescriptor⟩
    unfold occurrenceLegacyChiralityClass
    have hStatus : occurrenceLegacyStatus mol fuel state node = .fact fact :=
      (occurrenceLegacyStatus_eq_fact_iff mol fuel state node fact).mpr hFact
    simp [hStatus, hUpper, hDescriptor]

theorem occurrenceLegacyChiralityClass_eq_pseudoasymmetric_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (descriptor : RS) :
    occurrenceLegacyChiralityClass mol fuel state node = .pseudoasymmetric descriptor ↔
      ∃ fact, legacyOccurrenceFact? mol fuel state node = some fact ∧
        fact.uppercase = false ∧ fact.descriptor = descriptor := by
  constructor
  · intro hClass
    unfold occurrenceLegacyChiralityClass at hClass
    cases hStatus : occurrenceLegacyStatus mol fuel state node with
    | fact fact =>
        have hFact :=
          (occurrenceLegacyStatus_eq_fact_iff mol fuel state node fact).mp hStatus
        cases hUpper : fact.uppercase with
        | true =>
            simp only [hStatus, hUpper, if_true] at hClass
            cases hClass
        | false =>
            simp only [hStatus, hUpper, if_false] at hClass
            injection hClass with hDescriptor
            exact ⟨fact, hFact, hUpper, hDescriptor⟩
    | completedRankingTie => simp [hStatus] at hClass
    | refused => simp [hStatus] at hClass
  · rintro ⟨fact, hFact, hLower, hDescriptor⟩
    unfold occurrenceLegacyChiralityClass
    have hStatus : occurrenceLegacyStatus mol fuel state node = .fact fact :=
      (occurrenceLegacyStatus_eq_fact_iff mol fuel state node fact).mpr hFact
    simp [hStatus, hLower, hDescriptor]

/-- **The legacy classifier never returns `knownNonchiral`.**  A completed tie is a real computed
outcome, but the legacy comparison is not the complete pre-Rule-4b ordering; both ties and bare
refusals are therefore `unavailable` for Rule-4b selection. -/
theorem occurrenceLegacyChiralityClass_ne_knownNonchiral
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) :
    occurrenceLegacyChiralityClass mol fuel state node ≠ .knownNonchiral := by
  unfold occurrenceLegacyChiralityClass occurrenceLegacyStatus
  cases hFact : legacyOccurrenceFact? mol fuel state node with
  | none =>
      cases hTie : occurrenceLegacyRankingTie? mol fuel state node with
      | none => simp [hFact, hTie]
      | some tie => cases tie <;> simp [hFact, hTie]
  | some fact => cases hUpper : fact.uppercase <;> simp [hFact, hUpper]

/-- A tie or a bare refusal is `unavailable`; only a successful fact is classified. -/
theorem occurrenceLegacyChiralityClass_eq_unavailable_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) :
    occurrenceLegacyChiralityClass mol fuel state node = .unavailable ↔
      legacyOccurrenceFact? mol fuel state node = none := by
  unfold occurrenceLegacyChiralityClass occurrenceLegacyStatus
  cases hFact : legacyOccurrenceFact? mol fuel state node with
  | none =>
      cases hTie : occurrenceLegacyRankingTie? mol fuel state node with
      | none => simp [hFact, hTie]
      | some tie => cases tie <;> simp [hFact, hTie]
  | some fact => cases hUpper : fact.uppercase <;> simp [hFact, hUpper]

/-- A completed ranking tie is retained in the status, and is a refusal for Rule-4b selection. -/
theorem occurrenceLegacyStatus_eq_completedRankingTie_of_rankingTie?
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (hTie : occurrenceLegacyRankingTie? mol fuel state node = some true) :
    occurrenceLegacyStatus mol fuel state node = .completedRankingTie := by
  have hFact := legacyOccurrenceFact?_eq_none_of_rankingTie? mol fuel state node hTie
  unfold occurrenceLegacyStatus
  simp [hFact, hTie]

/-- A completed ranking tie maps to `unavailable`, not to a nonchirality verdict. -/
theorem occurrenceLegacyChiralityClass_eq_unavailable_of_rankingTie?
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (hTie : occurrenceLegacyRankingTie? mol fuel state node = some true) :
    occurrenceLegacyChiralityClass mol fuel state node = .unavailable :=
  (occurrenceLegacyChiralityClass_eq_unavailable_iff mol fuel state node).mpr
    (legacyOccurrenceFact?_eq_none_of_rankingTie? mol fuel state node hTie)

/-- A bare refusal (no completed-tie certificate) is also `unavailable`. -/
theorem occurrenceLegacyChiralityClass_eq_unavailable_of_no_tie
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (hFact : legacyOccurrenceFact? mol fuel state node = none)
    (_hTie : occurrenceLegacyRankingTie? mol fuel state node ≠ some true) :
    occurrenceLegacyChiralityClass mol fuel state node = .unavailable :=
  (occurrenceLegacyChiralityClass_eq_unavailable_iff mol fuel state node).mpr hFact

/-- The typed `Option (Option RS)` reading of the legacy classifier.  `none` covers both a
completed tie and a bare refusal; the tie/refusal distinction is available through
`occurrenceLegacyStatus`, but is deliberately not exposed as a chirality verdict. -/
def occurrenceLegacyChiralityClassification? (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    Option (Option RS) :=
  OccurrenceChiralityClass.toOptionOption
    (occurrenceLegacyChiralityClass mol fuel state node)

theorem occurrenceLegacyChiralityClassification?_eq_some_some_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (descriptor : RS) :
    occurrenceLegacyChiralityClassification? mol fuel state node = some (some descriptor) ↔
      ∃ fact, legacyOccurrenceFact? mol fuel state node = some fact ∧
        fact.uppercase = true ∧ fact.descriptor = descriptor := by
  unfold occurrenceLegacyChiralityClassification?
  rw [OccurrenceChiralityClass.toOptionOption_eq_some_some_iff,
    occurrenceLegacyChiralityClass_eq_uppercaseChiral_iff]

/-- `some none` is exactly an actual lowercase legacy fact.  Neither a completed tie nor a bare
refusal may appear here. -/
theorem occurrenceLegacyChiralityClassification?_eq_some_none_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) :
    occurrenceLegacyChiralityClassification? mol fuel state node = some none ↔
      ∃ fact, legacyOccurrenceFact? mol fuel state node = some fact ∧
        fact.uppercase = false := by
  unfold occurrenceLegacyChiralityClassification?
  rw [OccurrenceChiralityClass.toOptionOption_eq_some_none_iff]
  constructor
  · rintro (⟨descriptor, hClass⟩ | hClass)
    · rcases ((occurrenceLegacyChiralityClass_eq_pseudoasymmetric_iff
          mol fuel state node descriptor).mp hClass) with
        ⟨fact, hFact, hLower, _hDescriptor⟩
      exact ⟨fact, hFact, hLower⟩
    · exact absurd hClass
        (occurrenceLegacyChiralityClass_ne_knownNonchiral mol fuel state node)
  · rintro ⟨fact, hFact, hLower⟩
    exact Or.inl ⟨fact.descriptor,
      (occurrenceLegacyChiralityClass_eq_pseudoasymmetric_iff
        mol fuel state node fact.descriptor).mpr ⟨fact, hFact, hLower, rfl⟩⟩

theorem occurrenceLegacyChiralityClassification?_eq_none_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) :
    occurrenceLegacyChiralityClassification? mol fuel state node = none ↔
      legacyOccurrenceFact? mol fuel state node = none := by
  unfold occurrenceLegacyChiralityClassification?
  rw [OccurrenceChiralityClass.toOptionOption_eq_none_iff,
    occurrenceLegacyChiralityClass_eq_unavailable_iff]

/-! ## 8. Rule-4a preservation for the legacy classifier -/

theorem occurrenceLegacyChiralityClass_uppercaseChiral_rule4a
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (descriptor : RS)
    (hClass : occurrenceLegacyChiralityClass mol fuel state node =
      .uppercaseChiral descriptor) :
    ∃ fact, legacyOccurrenceFact? mol fuel state node = some fact ∧ fact.uppercase = true ∧
      branchRule4aSequence [occurrenceAuxFactToRawDescriptorFact fact] =
        [OfficialStereogenicUnitKind.chiral] := by
  rcases (occurrenceLegacyChiralityClass_eq_uppercaseChiral_iff
    mol fuel state node descriptor).mp hClass with ⟨fact, hFact, hUpper, _hDescriptor⟩
  exact ⟨fact, hFact, hUpper, by
    rw [branchRule4aSequence_singleton]
    simp [occurrenceAuxFactToRawDescriptorFact, hUpper]⟩

theorem occurrenceLegacyChiralityClass_pseudoasymmetric_rule4a
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (descriptor : RS)
    (hClass : occurrenceLegacyChiralityClass mol fuel state node =
      .pseudoasymmetric descriptor) :
    ∃ fact, legacyOccurrenceFact? mol fuel state node = some fact ∧
      fact.uppercase = false ∧
      branchRule4aSequence [occurrenceAuxFactToRawDescriptorFact fact] =
        [OfficialStereogenicUnitKind.pseudoasymmetric] := by
  rcases (occurrenceLegacyChiralityClass_eq_pseudoasymmetric_iff
    mol fuel state node descriptor).mp hClass with ⟨fact, hFact, hLower, _hDescriptor⟩
  exact ⟨fact, hFact, hLower, by
    rw [branchRule4aSequence_singleton]
    simp [occurrenceAuxFactToRawDescriptorFact, hLower]⟩

/-! ## 9. Evaluator prerequisites are refusals, not nonchirality verdicts

The production evaluators have structural prerequisites: an atom specification, a tetrahedral
annotation, and a four-ligand occurrence frame.  The lemmas below prove that failing any of them
makes `legacyOccurrenceFact?`, `framedOccurrenceFact?`, and hence `occurrenceFact?` return `none`
at every fuel and state.

That is a statement about the evaluator, not about chemistry.  Failed perception is not evidence
of absence: an unannotated atom or a missing frame may still be a stereogenic unit that the
current pipeline cannot resolve.  The selector-facing classifier below therefore keeps every such
real occurrence `unavailable`; `knownNonchiral` is produced only by non-real provenance, the
independent structural route of §2. -/

/-- The atom's tetrahedral annotation: the first two `Option` prerequisites of both production
occurrence evaluators.  `none` means neither evaluator can produce a descriptor for this
occurrence, independently of fuel and of the auxiliary state.  This is evaluator unproductivity;
it is *not* evidence that the occurrence is non-bearing. -/
def occurrenceTetrahedralCandidate? (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode) : Option TetrahedralInputParity :=
  match mol.atomAt? node.atom with
  | none => none
  | some spec => spec.tetrahedral?

/-- `none` of the candidate lookup is exactly: no atom specification, or an atom specification
without a tetrahedral annotation. -/
theorem occurrenceTetrahedralCandidate?_eq_none_iff (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode) :
    occurrenceTetrahedralCandidate? mol node = none ↔
      mol.atomAt? node.atom = none ∨
        ∃ spec, mol.atomAt? node.atom = some spec ∧ spec.tetrahedral? = none := by
  unfold occurrenceTetrahedralCandidate?
  cases hAtom : mol.atomAt? node.atom with
  | none => simp [hAtom]
  | some spec => cases hParity : spec.tetrahedral? <;> simp [hAtom, hParity]

/-! ### Evaluator refusal from structural prerequisites -/

theorem legacyOccurrenceFact?_eq_none_of_atomAt?_eq_none
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (h : mol.atomAt? node.atom = none) :
    legacyOccurrenceFact? mol fuel state node = none := by
  simp [legacyOccurrenceFact?, h]

theorem legacyOccurrenceFact?_eq_none_of_tetrahedral?_eq_none
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (spec : AtomSpec)
    (hAtom : mol.atomAt? node.atom = some spec)
    (hParity : spec.tetrahedral? = none) :
    legacyOccurrenceFact? mol fuel state node = none := by
  simp [legacyOccurrenceFact?, hAtom, hParity]

theorem legacyOccurrenceFact?_eq_none_of_ligandFrame?_eq_none
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (h : occurrenceLigandFrame? mol node = none) :
    legacyOccurrenceFact? mol fuel state node = none := by
  simp [legacyOccurrenceFact?, h]

theorem framedOccurrenceFact?_eq_none_of_atomAt?_eq_none
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (h : mol.atomAt? node.atom = none) :
    framedOccurrenceFact? mol fuel state node = none := by
  unfold framedOccurrenceFact?
  cases hProfile : FrameRuntime.profile? mol node with
  | none => simp [hProfile, h]
  | some profile => simp [hProfile, h]

theorem framedOccurrenceFact?_eq_none_of_tetrahedral?_eq_none
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (spec : AtomSpec)
    (hAtom : mol.atomAt? node.atom = some spec)
    (hParity : spec.tetrahedral? = none) :
    framedOccurrenceFact? mol fuel state node = none := by
  unfold framedOccurrenceFact?
  cases hProfile : FrameRuntime.profile? mol node with
  | none => simp [hProfile, hAtom, hParity]
  | some profile => simp [hProfile, hAtom, hParity]

theorem framedOccurrenceFact?_eq_none_of_ligandFrame?_eq_none
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (h : occurrenceLigandFrame? mol node = none) :
    framedOccurrenceFact? mol fuel state node = none := by
  unfold framedOccurrenceFact?
  cases hProfile : FrameRuntime.profile? mol node with
  | none => simp [hProfile, h]
  | some profile => simp [hProfile, h]

theorem occurrenceFact?_eq_none_of_atomAt?_eq_none
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (h : mol.atomAt? node.atom = none) :
    occurrenceFact? mol fuel state node = none := by
  unfold occurrenceFact?
  cases hProfile : FrameRuntime.profile? mol node with
  | none => exact legacyOccurrenceFact?_eq_none_of_atomAt?_eq_none mol fuel state node h
  | some profile => exact framedOccurrenceFact?_eq_none_of_atomAt?_eq_none mol fuel state node h

theorem occurrenceFact?_eq_none_of_tetrahedral?_eq_none
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (spec : AtomSpec)
    (hAtom : mol.atomAt? node.atom = some spec)
    (hParity : spec.tetrahedral? = none) :
    occurrenceFact? mol fuel state node = none := by
  unfold occurrenceFact?
  cases hProfile : FrameRuntime.profile? mol node with
  | none =>
      exact legacyOccurrenceFact?_eq_none_of_tetrahedral?_eq_none mol fuel state node spec
        hAtom hParity
  | some profile =>
      exact framedOccurrenceFact?_eq_none_of_tetrahedral?_eq_none mol fuel state node spec
        hAtom hParity

theorem occurrenceFact?_eq_none_of_ligandFrame?_eq_none
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (h : occurrenceLigandFrame? mol node = none) :
    occurrenceFact? mol fuel state node = none := by
  unfold occurrenceFact?
  cases hProfile : FrameRuntime.profile? mol node with
  | none => exact legacyOccurrenceFact?_eq_none_of_ligandFrame?_eq_none mol fuel state node h
  | some profile => exact framedOccurrenceFact?_eq_none_of_ligandFrame?_eq_none mol fuel state node h

/-- A non-candidate occurrence cannot produce a fact, whatever the fuel and state.  This combines
the two structural prerequisites through `occurrenceTetrahedralCandidate?`. -/
theorem occurrenceFact?_eq_none_of_tetrahedralCandidate?_eq_none
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (h : occurrenceTetrahedralCandidate? mol node = none) :
    occurrenceFact? mol fuel state node = none := by
  rcases (occurrenceTetrahedralCandidate?_eq_none_iff mol node).mp h with
    hAtom | ⟨spec, hAtom, hParity⟩
  · exact occurrenceFact?_eq_none_of_atomAt?_eq_none mol fuel state node hAtom
  · exact occurrenceFact?_eq_none_of_tetrahedral?_eq_none mol fuel state node spec hAtom hParity

/-! ### The selector-facing classifier refuses failed perception -/

/-- The narrow selector-facing classifier for Rule-4b frontier traversal.

It is definitionally the honest state classifier of §3, repeated here as the selection entry
point: a recorded fact at a real-atom occurrence is uppercase/lowercase evidence; non-real
provenance is independent structural non-bearing; a real occurrence missing from the state is
`unavailable` whatever the evaluator's annotation/frame prerequisites say.  No failed-perception
branch produces `knownNonchiral`. -/
def occurrenceSelectorChiralityClass (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) : OccurrenceChiralityClass RS :=
  occurrenceChiralityClass state cursor

/-- Positive selector evidence is an actual state fact. -/
theorem occurrenceSelectorChiralityClass_eq_uppercaseChiral_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) (descriptor : RS) :
    occurrenceSelectorChiralityClass state cursor = .uppercaseChiral descriptor ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        ∃ fact, state.factAt? cursor.node = some fact ∧
          fact.uppercase = true ∧ fact.descriptor = descriptor := by
  simpa [occurrenceSelectorChiralityClass] using
    occurrenceChiralityClass_eq_uppercaseChiral_iff state cursor descriptor

/-- Lowercase selector evidence is an actual lowercase state fact. -/
theorem occurrenceSelectorChiralityClass_eq_pseudoasymmetric_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) (descriptor : RS) :
    occurrenceSelectorChiralityClass state cursor = .pseudoasymmetric descriptor ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        ∃ fact, state.factAt? cursor.node = some fact ∧
          fact.uppercase = false ∧ fact.descriptor = descriptor := by
  simpa [occurrenceSelectorChiralityClass] using
    occurrenceChiralityClass_eq_pseudoasymmetric_iff state cursor descriptor

/-- `knownNonchiral` is exactly non-real provenance.  A real occurrence with a missing annotation
or a missing occurrence frame is *not* nonchiral. -/
theorem occurrenceSelectorChiralityClass_eq_knownNonchiral_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceSelectorChiralityClass state cursor = .knownNonchiral ↔
      cursor.node.provenance ≠ RawMolecule.CanonicalNodeProvenance.realAtom := by
  simpa [occurrenceSelectorChiralityClass] using
    occurrenceChiralityClass_eq_knownNonchiral_iff state cursor

/-- `unavailable` is exactly a real occurrence missing from the state.  Evaluator prerequisites do
not enter this verdict. -/
theorem occurrenceSelectorChiralityClass_eq_unavailable_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceSelectorChiralityClass state cursor = .unavailable ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        state.factAt? cursor.node = none := by
  simpa [occurrenceSelectorChiralityClass] using
    occurrenceChiralityClass_eq_unavailable_iff state cursor

/-- Non-real provenance gives structural non-bearing. -/
theorem occurrenceSelectorChiralityClass_eq_knownNonchiral_of_nonReal
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (hNonReal : cursor.node.provenance ≠
      RawMolecule.CanonicalNodeProvenance.realAtom) :
    occurrenceSelectorChiralityClass state cursor = .knownNonchiral := by
  simpa [occurrenceSelectorChiralityClass] using
    occurrenceChiralityClass_eq_knownNonchiral_of_nonReal state cursor hNonReal

/-- A real occurrence missing from the state is a refusal. -/
theorem occurrenceSelectorChiralityClass_eq_unavailable_of_missing
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none) :
    occurrenceSelectorChiralityClass state cursor = .unavailable := by
  simpa [occurrenceSelectorChiralityClass] using
    occurrenceChiralityClass_eq_unavailable_of_missing state cursor hProvenance hMissing

/-- **Failed perception stays unavailable.**  A real occurrence with no recorded state fact and no
tetrahedral candidate is `unavailable`, not `knownNonchiral`, even though the evaluator is proved
to return `none` at every fuel. -/
theorem occurrenceSelectorChiralityClass_eq_unavailable_of_candidate?_eq_none
    (mol : RawMolecule) (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none)
    (_hCandidate : occurrenceTetrahedralCandidate? mol cursor.node = none) :
    occurrenceSelectorChiralityClass state cursor = .unavailable := by
  simpa [occurrenceSelectorChiralityClass] using
    occurrenceChiralityClass_eq_unavailable_of_missing state cursor hProvenance hMissing

/-- **Failed frame perception stays unavailable.**  The same for an absent four-ligand occurrence
frame. -/
theorem occurrenceSelectorChiralityClass_eq_unavailable_of_ligandFrame?_eq_none
    (mol : RawMolecule) (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none)
    (_hFrame : occurrenceLigandFrame? mol cursor.node = none) :
    occurrenceSelectorChiralityClass state cursor = .unavailable := by
  simpa [occurrenceSelectorChiralityClass] using
    occurrenceChiralityClass_eq_unavailable_of_missing state cursor hProvenance hMissing

/-- A real occurrence can never receive a selector `knownNonchiral` verdict. -/
theorem occurrenceSelectorChiralityClass_ne_knownNonchiral_of_real
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom) :
    occurrenceSelectorChiralityClass state cursor ≠ .knownNonchiral := by
  intro hClass
  exact ((occurrenceSelectorChiralityClass_eq_knownNonchiral_iff state cursor).mp hClass)
    hProvenance

/-- The typed `Option (Option RS)` selector interface. -/
def occurrenceSelectorChiralityClassification? (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) : Option (Option RS) :=
  occurrenceChiralityClassification? state cursor

theorem occurrenceSelectorChiralityClassification?_eq_some_some_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) (descriptor : RS) :
    occurrenceSelectorChiralityClassification? state cursor = some (some descriptor) ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        ∃ fact, state.factAt? cursor.node = some fact ∧
          fact.uppercase = true ∧ fact.descriptor = descriptor := by
  simpa [occurrenceSelectorChiralityClassification?] using
    occurrenceChiralityClassification?_eq_some_some_iff state cursor descriptor

/-- `some none` is non-real provenance or an actual lowercase state fact; never a real occurrence
whose perception failed. -/
theorem occurrenceSelectorChiralityClassification?_eq_some_none_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceSelectorChiralityClassification? state cursor = some none ↔
      cursor.node.provenance ≠ RawMolecule.CanonicalNodeProvenance.realAtom ∨
        ∃ fact, cursor.node.provenance =
            RawMolecule.CanonicalNodeProvenance.realAtom ∧
          state.factAt? cursor.node = some fact ∧ fact.uppercase = false := by
  simpa [occurrenceSelectorChiralityClassification?] using
    occurrenceChiralityClassification?_eq_some_none_iff state cursor

theorem occurrenceSelectorChiralityClassification?_eq_none_iff
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceSelectorChiralityClassification? state cursor = none ↔
      cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
        state.factAt? cursor.node = none := by
  simpa [occurrenceSelectorChiralityClassification?] using
    occurrenceChiralityClassification?_eq_none_iff state cursor

/-- Missing evidence at a real occurrence is a selector refusal, never `some none`. -/
theorem occurrenceSelectorChiralityClassification?_ne_some_none_of_missing
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor)
    (hProvenance : cursor.node.provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none) :
    occurrenceSelectorChiralityClassification? state cursor ≠ some none := by
  simpa [occurrenceSelectorChiralityClassification?] using
    occurrenceChiralityClassification?_ne_some_none_of_missing state cursor hProvenance hMissing

/-! ## 10. Kernel-authority guards

Each theorem below is checked to depend only on Lean's kernel and the standard logical
principles (`propext`, `Classical.choice`, `Quot.sound`) permitted by `assert_kernel_only`.
No `sorryAx`, native evaluator trust, or project axiom is used. -/

assert_kernel_only OccurrenceChiralityClass.toOptionOption_eq_none_iff
assert_kernel_only OccurrenceChiralityClass.toOptionOption_eq_some_some_iff
assert_kernel_only OccurrenceChiralityClass.toOptionOption_eq_some_none_iff
assert_kernel_only OccurrenceChiralityClass.rule4aKind_eq_some_chiral_iff
assert_kernel_only occurrenceAuxiliaryEvidence?_eq_some_some_iff
assert_kernel_only occurrenceAuxiliaryEvidence?_eq_some_none_iff
assert_kernel_only occurrenceAuxiliaryEvidence?_eq_none_iff
assert_kernel_only occurrenceAuxiliaryEvidence?_eq_some_some_of_lookup
assert_kernel_only occurrenceChiralityClass_eq_uppercaseChiral_iff
assert_kernel_only occurrenceChiralityClass_eq_pseudoasymmetric_iff
assert_kernel_only occurrenceChiralityClass_eq_knownNonchiral_iff
assert_kernel_only occurrenceChiralityClass_eq_unavailable_iff
assert_kernel_only occurrenceChiralityClass_eq_knownNonchiral_of_nonReal
assert_kernel_only occurrenceChiralityClass_eq_unavailable_of_missing
assert_kernel_only occurrenceChiralityClassification?_eq_some_some_iff
assert_kernel_only occurrenceChiralityClassification?_eq_some_none_iff
assert_kernel_only occurrenceChiralityClassification?_eq_none_iff
assert_kernel_only occurrenceChiralityClassification?_ne_some_none_of_missing
assert_kernel_only occurrenceUppercaseDescriptor?_eq_some_iff
assert_kernel_only occurrenceUppercaseDescriptor?_eq_some_iff_source
assert_kernel_only occurrenceUppercaseDescriptor?_eq_none_iff
assert_kernel_only branchRule4aSequence_singleton
assert_kernel_only occurrenceChiralityClass_uppercaseChiral_rule4a
assert_kernel_only occurrenceChiralityClass_pseudoasymmetric_rule4a
assert_kernel_only occurrenceComputedChiralityClass_eq_uppercaseChiral_iff
assert_kernel_only occurrenceComputedChiralityClass_eq_pseudoasymmetric_iff
assert_kernel_only occurrenceComputedChiralityClass_ne_knownNonchiral
assert_kernel_only occurrenceComputedChiralityClass_eq_unavailable_iff
assert_kernel_only occurrenceComputedChiralityClassification?_eq_some_some_iff
assert_kernel_only occurrenceComputedChiralityClassification?_eq_some_none_iff
assert_kernel_only occurrenceComputedChiralityClassification?_eq_none_iff
assert_kernel_only legacyOccurrenceFact?_eq_none_of_completed_tie
assert_kernel_only legacyOccurrenceFact?_eq_none_of_rankingTie?
assert_kernel_only occurrenceLegacyStatus_eq_fact_iff
assert_kernel_only occurrenceLegacyStatus_eq_completedRankingTie_iff
assert_kernel_only occurrenceLegacyStatus_eq_refused_iff
assert_kernel_only occurrenceLegacyChiralityClass_eq_uppercaseChiral_iff
assert_kernel_only occurrenceLegacyChiralityClass_eq_pseudoasymmetric_iff
assert_kernel_only occurrenceLegacyChiralityClass_ne_knownNonchiral
assert_kernel_only occurrenceLegacyChiralityClass_eq_unavailable_iff
assert_kernel_only occurrenceLegacyStatus_eq_completedRankingTie_of_rankingTie?
assert_kernel_only occurrenceLegacyChiralityClass_eq_unavailable_of_rankingTie?
assert_kernel_only occurrenceLegacyChiralityClass_eq_unavailable_of_no_tie
assert_kernel_only occurrenceLegacyChiralityClassification?_eq_some_some_iff
assert_kernel_only occurrenceLegacyChiralityClassification?_eq_some_none_iff
assert_kernel_only occurrenceLegacyChiralityClassification?_eq_none_iff
assert_kernel_only occurrenceLegacyChiralityClass_uppercaseChiral_rule4a
assert_kernel_only occurrenceLegacyChiralityClass_pseudoasymmetric_rule4a
assert_kernel_only occurrenceTetrahedralCandidate?_eq_none_iff
assert_kernel_only legacyOccurrenceFact?_eq_none_of_atomAt?_eq_none
assert_kernel_only legacyOccurrenceFact?_eq_none_of_tetrahedral?_eq_none
assert_kernel_only legacyOccurrenceFact?_eq_none_of_ligandFrame?_eq_none
assert_kernel_only framedOccurrenceFact?_eq_none_of_atomAt?_eq_none
assert_kernel_only framedOccurrenceFact?_eq_none_of_tetrahedral?_eq_none
assert_kernel_only framedOccurrenceFact?_eq_none_of_ligandFrame?_eq_none
assert_kernel_only occurrenceFact?_eq_none_of_atomAt?_eq_none
assert_kernel_only occurrenceFact?_eq_none_of_tetrahedral?_eq_none
assert_kernel_only occurrenceFact?_eq_none_of_ligandFrame?_eq_none
assert_kernel_only occurrenceFact?_eq_none_of_tetrahedralCandidate?_eq_none
assert_kernel_only occurrenceSelectorChiralityClass_eq_uppercaseChiral_iff
assert_kernel_only occurrenceSelectorChiralityClass_eq_pseudoasymmetric_iff
assert_kernel_only occurrenceSelectorChiralityClass_eq_knownNonchiral_iff
assert_kernel_only occurrenceSelectorChiralityClass_eq_unavailable_iff
assert_kernel_only occurrenceSelectorChiralityClass_eq_knownNonchiral_of_nonReal
assert_kernel_only occurrenceSelectorChiralityClass_eq_unavailable_of_missing
assert_kernel_only occurrenceSelectorChiralityClass_eq_unavailable_of_candidate?_eq_none
assert_kernel_only occurrenceSelectorChiralityClass_eq_unavailable_of_ligandFrame?_eq_none
assert_kernel_only occurrenceSelectorChiralityClass_ne_knownNonchiral_of_real
assert_kernel_only occurrenceSelectorChiralityClassification?_eq_some_some_iff
assert_kernel_only occurrenceSelectorChiralityClassification?_eq_some_none_iff
assert_kernel_only occurrenceSelectorChiralityClassification?_eq_none_iff
assert_kernel_only occurrenceSelectorChiralityClassification?_ne_some_none_of_missing

end OneCenter
end TetraStereo
